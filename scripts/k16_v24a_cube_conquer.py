#!/usr/bin/env python3
"""V24-A exact cube-and-conquer refinement of the 19 V22 open children.

The completed V22 refinement ledger is immutable input.  Every logical
UNKNOWN child is replaced by a complete three-level adaptive MOMS tree.
Both polarities of every selected directed-arc variable are retained.
Unit-inconsistent terminals are exact closures and all other terminals are
solved first by CaDiCaL and, only on UNKNOWN, by Kissat.

SAT is accepted only after the independent primitive K16 audit.  UNSAT closes
only the named signed child.  UNKNOWN remains in the resumable ledger.
"""

from __future__ import annotations

import argparse
import json
import shutil
import sys
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = REPO_ROOT / "scripts"
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from k16_smart_deepen import Dimacs, cube_hash, sha256, write_json  # noqa: E402
from k16_staged_cascade import (  # noqa: E402
    assignment_to_arcs,
    independent_audit,
    parse_cadical_assignment,
    run_limited,
    write_assumption_cnf,
)


MODEL_VERSION = "k16-pisa-v24a-v22-open-cube-conquer-20260730"
PLAN_SCHEMA = "k16-v24a-plan-v1"
RESULT_SCHEMA = "k16-v24a-result-v1"
CADICAL_LEDGER_SCHEMA = "k16-v24a-cadical-ledger-v1"
FINAL_LEDGER_SCHEMA = "k16-v24a-ledger-v1"
V22_PLAN_SCHEMA = "k16-v22-refine-plan-v1"
V22_LEDGER_SCHEMA = "k16-v22-refine-ledger-v1"

EXPECTED_SOURCE_OPEN_LEAVES = 19
EXPECTED_SOURCE_OPEN_PARENTS = 16
SPLIT_LEVELS = 3
CADICAL_SECONDS = 3600
KISSAT_SECONDS = 3600
BOXES = ("a1_z3", "a2p_z4p")


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def collect_records(root: Path) -> list[dict]:
    records = []
    for path in sorted(root.rglob("*.json")):
        record = load_json(path)
        if record.get("schema") == RESULT_SCHEMA:
            records.append(record)
    ids = [record["task_id"] for record in records]
    if len(ids) != len(set(ids)):
        raise RuntimeError("duplicate V24-A result identifiers")
    return records


def validate_source(source: Path, ledger_path: Path) -> tuple[dict, dict]:
    plan = load_json(source / "v22-refine-manifest.json")
    ledger = load_json(ledger_path)
    if plan.get("schema") != V22_PLAN_SCHEMA:
        raise RuntimeError("unexpected V22 plan schema")
    if ledger.get("schema") != V22_LEDGER_SCHEMA:
        raise RuntimeError("unexpected V22 ledger schema")
    if ledger.get("logical_conclusion") != "V22_REFINEMENT_COMPLETE_K16_OPEN":
        raise RuntimeError("V22 source is not a completed open frontier")
    if ledger.get("verified_sat_witnesses"):
        raise RuntimeError("V22 already contains a verified SAT witness")
    if (
        int(ledger.get("open_child_count", -1)) != EXPECTED_SOURCE_OPEN_LEAVES
        or int(ledger.get("open_parent_count", -1))
        != EXPECTED_SOURCE_OPEN_PARENTS
        or int(ledger.get("closed_parent_count", -1)) != 123
    ):
        raise RuntimeError("unexpected V22 open counts")

    plan_by_child = {
        task["root_id"]: task for task in plan.get("cadical_tasks", [])
    }
    open_leaves = ledger["open_child_leaves"]
    if len(open_leaves) != EXPECTED_SOURCE_OPEN_LEAVES:
        raise RuntimeError("V22 open-child list has the wrong size")
    for leaf in open_leaves:
        child_id = leaf["child_id"]
        source_task = plan_by_child.get(child_id)
        if source_task is None:
            raise RuntimeError(f"V22 open child missing from plan: {child_id}")
        if (
            source_task["box"] != leaf["box"]
            or source_task["cube_literals"] != leaf["cube_literals"]
            or source_task["cube_sha256"] != leaf["cube_sha256"]
            or cube_hash(leaf["cube_literals"]) != leaf["cube_sha256"]
        ):
            raise RuntimeError(f"V22 signed child mismatch: {child_id}")
    for box in BOXES:
        cnf = source / "boxes" / box / "enriched-theorem.cnf"
        expected = plan["source_hashes"]["theorem_cnf"][box]
        if sha256(cnf) != expected:
            raise RuntimeError(f"V22 theorem CNF hash mismatch: {box}")
    if sha256(source / "cadical" / "cadical") != (
        plan["source_hashes"]["cadical"]
    ):
        raise RuntimeError("V22 CaDiCaL binary hash mismatch")
    return plan, ledger


def expand_tree(
    *,
    dimacs: Dimacs,
    source_leaf_id: str,
    assumptions: list[int],
    levels: int,
    path_bits: str,
    nodes: list[dict],
    survivors: list[dict],
    unit_closed: list[dict],
) -> None:
    assignment, contradiction = dimacs.propagate(assumptions)
    node_id = f"{source_leaf_id}:{path_bits or 'root'}"
    if contradiction:
        item = {
            "node_id": node_id,
            "source_leaf_id": source_leaf_id,
            "path_bits": path_bits,
            "cube_literals": assumptions,
            "cube_depth": len(assumptions),
            "cube_sha256": cube_hash(assumptions),
            "status": "UNSAT",
            "method": "unit_propagation",
            "solver_level_exact": True,
        }
        unit_closed.append(item)
        nodes.append(
            {
                "node_id": node_id,
                "kind": "unit_closed",
                "cube_literals": assumptions,
            }
        )
        return
    if levels == 0:
        item = {
            "node_id": node_id,
            "source_leaf_id": source_leaf_id,
            "path_bits": path_bits,
            "cube_literals": assumptions,
            "cube_depth": len(assumptions),
            "cube_sha256": cube_hash(assumptions),
            "implied_assignments": len(assignment),
        }
        survivors.append(item)
        nodes.append(
            {
                "node_id": node_id,
                "kind": "survivor",
                "cube_literals": assumptions,
            }
        )
        return

    variable, moms = dimacs.moms_arc_variable(assumptions)
    if variable in {abs(literal) for literal in assumptions}:
        raise RuntimeError("MOMS selected an already decided variable")
    nodes.append(
        {
            "node_id": node_id,
            "kind": "branch",
            "variable": variable,
            "moms": moms,
            "cube_literals": assumptions,
            "zero_child": f"{source_leaf_id}:{path_bits}0",
            "one_child": f"{source_leaf_id}:{path_bits}1",
        }
    )
    expand_tree(
        dimacs=dimacs,
        source_leaf_id=source_leaf_id,
        assumptions=assumptions + [-variable],
        levels=levels - 1,
        path_bits=path_bits + "0",
        nodes=nodes,
        survivors=survivors,
        unit_closed=unit_closed,
    )
    expand_tree(
        dimacs=dimacs,
        source_leaf_id=source_leaf_id,
        assumptions=assumptions + [variable],
        levels=levels - 1,
        path_bits=path_bits + "1",
        nodes=nodes,
        survivors=survivors,
        unit_closed=unit_closed,
    )


def audit_tree(tree: dict, parent_literals: list[int]) -> dict:
    nodes = {item["node_id"]: item for item in tree["nodes"]}
    root = f"{tree['source_leaf_id']}:root"
    seen: set[str] = set()
    terminals: list[str] = []

    def walk(node_id: str, depth: int, expected_literals: list[int]) -> None:
        if node_id in seen:
            raise RuntimeError("V24-A split tree is not a tree")
        seen.add(node_id)
        node = nodes.get(node_id)
        if node is None:
            raise RuntimeError(f"missing split-tree node: {node_id}")
        if node["cube_literals"] != expected_literals:
            raise RuntimeError("split-tree cube does not match its path")
        if node["kind"] == "branch":
            if depth >= SPLIT_LEVELS:
                raise RuntimeError("branch below requested split depth")
            variable = int(node["variable"])
            if variable in {abs(literal) for literal in expected_literals}:
                raise RuntimeError("split-tree repeats a decided variable")
            walk(
                node["zero_child"],
                depth + 1,
                expected_literals + [-variable],
            )
            walk(
                node["one_child"],
                depth + 1,
                expected_literals + [variable],
            )
        elif node["kind"] in {"survivor", "unit_closed"}:
            terminals.append(node_id)
        else:
            raise RuntimeError("unknown split-tree node kind")

    walk(root, 0, list(parent_literals))
    if seen != set(nodes):
        raise RuntimeError("unreachable split-tree nodes")
    if len(terminals) > (1 << SPLIT_LEVELS):
        raise RuntimeError("too many split-tree terminals")
    return {
        "complete_binary_branching": True,
        "root_cube_sha256": cube_hash(parent_literals),
        "reachable_nodes": len(seen),
        "terminal_nodes": len(terminals),
        "maximum_terminal_nodes": 1 << SPLIT_LEVELS,
    }


def plan_campaign(
    *,
    v22_source: Path,
    v22_ledger_path: Path,
    kissat_binary: Path,
    output: Path,
    matrix_output: Path,
    v22_run_id: str,
) -> dict:
    prior_plan, ledger = validate_source(v22_source, v22_ledger_path)
    output.mkdir(parents=True, exist_ok=True)
    for name in ("boxes", "bundle", "cadical"):
        shutil.copytree(v22_source / name, output / name, dirs_exist_ok=True)
    (output / "kissat").mkdir(parents=True, exist_ok=True)
    shutil.copy2(kissat_binary, output / "kissat" / "kissat")

    dimacs_by_box = {
        box: Dimacs(output / "boxes" / box / "enriched-theorem.cnf")
        for box in BOXES
    }
    trees: dict[str, dict] = {}
    survivor_nodes: list[dict] = []
    unit_closed: list[dict] = []

    for leaf in sorted(
        ledger["open_child_leaves"], key=lambda item: item["child_id"]
    ):
        source_leaf_id = leaf["child_id"]
        box = leaf["box"]
        nodes: list[dict] = []
        survivors: list[dict] = []
        closed: list[dict] = []
        expand_tree(
            dimacs=dimacs_by_box[box],
            source_leaf_id=source_leaf_id,
            assumptions=list(leaf["cube_literals"]),
            levels=SPLIT_LEVELS,
            path_bits="",
            nodes=nodes,
            survivors=survivors,
            unit_closed=closed,
        )
        for child in survivors:
            child["box"] = box
            child["source_parent_root_id"] = leaf["parent_root_id"]
            survivor_nodes.append(child)
        for child in closed:
            child["box"] = box
            child["source_parent_root_id"] = leaf["parent_root_id"]
            unit_closed.append(child)
        tree = {
            "source_leaf_id": source_leaf_id,
            "source_parent_root_id": leaf["parent_root_id"],
            "box": box,
            "parent_cube_literals": list(leaf["cube_literals"]),
            "parent_cube_depth": int(leaf["cube_depth"]),
            "parent_cube_sha256": leaf["cube_sha256"],
            "split_levels": SPLIT_LEVELS,
            "nodes": nodes,
            "surviving_children": len(survivors),
            "unit_closed_children": len(closed),
        }
        tree["coverage_audit"] = audit_tree(tree, leaf["cube_literals"])
        trees[source_leaf_id] = tree

    tasks = []
    for index, child in enumerate(
        sorted(
            survivor_nodes,
            key=lambda item: (item["source_leaf_id"], item["path_bits"]),
        ),
        start=1,
    ):
        root_id = f"a{index:04d}"
        task_id = f"cadical{CADICAL_SECONDS}-{root_id}"
        tasks.append(
            {
                "task_id": task_id,
                "stage": "cadical",
                "method": f"cadical{CADICAL_SECONDS}",
                "solver": "cadical",
                "seconds": CADICAL_SECONDS,
                "box": child["box"],
                "root_id": root_id,
                "source_leaf_id": child["source_leaf_id"],
                "source_parent_root_id": child["source_parent_root_id"],
                "split_path": child["path_bits"],
                "cube_literals": child["cube_literals"],
                "cube_depth": child["cube_depth"],
                "cube_sha256": child["cube_sha256"],
            }
        )

    if len(trees) != EXPECTED_SOURCE_OPEN_LEAVES:
        raise RuntimeError("not every V22 open child was refined")
    if len(tasks) + len(unit_closed) > (
        EXPECTED_SOURCE_OPEN_LEAVES * (1 << SPLIT_LEVELS)
    ):
        raise RuntimeError("V24-A emitted too many terminal children")

    record = {
        "schema": PLAN_SCHEMA,
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "source_runs": {"v22": v22_run_id},
        "source_hashes": {
            "v22_ledger": sha256(v22_ledger_path),
            "v22_manifest": sha256(
                v22_source / "v22-refine-manifest.json"
            ),
            "cadical": sha256(output / "cadical" / "cadical"),
            "kissat": sha256(output / "kissat" / "kissat"),
            "theorem_cnf": {
                box: sha256(
                    output / "boxes" / box / "enriched-theorem.cnf"
                )
                for box in BOXES
            },
        },
        "baseline": {
            "v22_closed_parent_regions": int(ledger["closed_parent_count"]),
            "v22_open_parent_regions": int(ledger["open_parent_count"]),
            "v22_open_child_leaves": int(ledger["open_child_count"]),
        },
        "split_policy": {
            "levels": SPLIT_LEVELS,
            "maximum_children_per_leaf": 1 << SPLIT_LEVELS,
            "rule": (
                "adaptive MOMS after unit propagation; both polarities are "
                "retained at every internal node"
            ),
        },
        "v22_open_child_leaves": ledger["open_child_leaves"],
        "v22_closed_parent_ids": ledger["closed_parent_ids"],
        "v22_parent_records": ledger["parent_records"],
        "trees": trees,
        "unit_closed_children": unit_closed,
        "cadical_tasks": tasks,
        "coverage": {
            "source_leaves_refined": len(trees),
            "all_tree_audits_passed": all(
                tree["coverage_audit"]["complete_binary_branching"]
                for tree in trees.values()
            ),
            "statement": (
                "Each V22 UNKNOWN child is exactly replaced by a complete "
                "three-level binary decision tree. Unit contradictions are "
                "exact closures; every surviving terminal is queued."
            ),
        },
        "source_plan_model_version": prior_plan["model_version"],
    }
    write_json(output / "v24a-manifest.json", record)
    matrix_output.write_text(
        json.dumps(
            {
                "include": [
                    {
                        "task_id": task["task_id"],
                        "box": task["box"],
                        "seconds": task["seconds"],
                    }
                    for task in tasks
                ]
            },
            separators=(",", ":"),
        )
        + "\n",
        encoding="utf-8",
    )
    print(
        json.dumps(
            {
                "source_open_leaves": len(trees),
                "unit_closed_children": len(unit_closed),
                "queued_children": len(tasks),
                "by_box": dict(Counter(t["box"] for t in tasks)),
                "coverage_audits": sum(
                    t["coverage_audit"]["complete_binary_branching"]
                    for t in trees.values()
                ),
            },
            indent=2,
        ),
        flush=True,
    )
    return record


def solve_task(
    *,
    source: Path,
    manifest_path: Path,
    task_id: str,
    result_path: Path,
    log_path: Path,
    seconds_override: int | None = None,
) -> dict:
    manifest = load_json(manifest_path)
    tasks = manifest.get("cadical_tasks", []) + manifest.get(
        "kissat_tasks", []
    )
    matches = [task for task in tasks if task["task_id"] == task_id]
    if len(matches) != 1:
        raise RuntimeError(f"task lookup failed: {task_id}")
    task = matches[0]
    seconds = (
        int(seconds_override)
        if seconds_override is not None
        else int(task["seconds"])
    )
    box = task["box"]
    cnf = source / "boxes" / box / "enriched-theorem.cnf"
    work = result_path.parent.parent / "work" / task_id
    work.mkdir(parents=True, exist_ok=True)
    assumption_cnf = work / "assumption.cnf"
    write_assumption_cnf(cnf, assumption_cnf, task["cube_literals"])

    solver = task["solver"]
    binary = source / solver / solver
    returncode, text, timed_out, elapsed = run_limited(
        [str(binary), str(assumption_cnf)],
        timeout_seconds=seconds,
    )
    status = {10: "SAT", 20: "UNSAT"}.get(returncode, "UNKNOWN")
    if timed_out:
        status = "UNKNOWN"
    raw_result = returncode if returncode in {10, 20} else 0
    arcs = (
        assignment_to_arcs(parse_cadical_assignment(text))
        if status == "SAT"
        else None
    )
    log_path.parent.mkdir(parents=True, exist_ok=True)
    log_path.write_text(text, encoding="utf-8")
    record: dict = {
        "schema": RESULT_SCHEMA,
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "task_id": task_id,
        "stage": task["stage"],
        "method": task["method"],
        "solver": solver,
        "box": box,
        "root_id": task["root_id"],
        "source_leaf_id": task["source_leaf_id"],
        "source_parent_root_id": task["source_parent_root_id"],
        "split_path": task["split_path"],
        "cube_literals": task["cube_literals"],
        "cube_depth": task["cube_depth"],
        "cube_sha256": task["cube_sha256"],
        "status": status,
        "seconds": round(elapsed, 3),
        "time_limit_seconds": seconds,
        "returncode": returncode,
        "raw_result": raw_result,
        "timed_out": timed_out,
        "solver_level_exact": status == "UNSAT",
        "verified": False,
    }
    if status == "SAT":
        if arcs is None:
            write_json(result_path, record)
            raise RuntimeError("SAT result has no parseable tournament")
        verified, audit = independent_audit(
            arcs=arcs,
            box=box,
            directory=work,
        )
        record["candidate_arcs"] = arcs
        record["independent_audit"] = audit
        record["verified"] = verified
        if not verified:
            write_json(result_path, record)
            raise RuntimeError("SAT candidate failed independent verification")
    write_json(result_path, record)
    print(json.dumps(record, indent=2), flush=True)
    return record


def select_kissat(
    *,
    source: Path,
    cadical_results_root: Path,
    output: Path,
    matrix_output: Path,
) -> dict:
    plan = load_json(source / "v24a-manifest.json")
    expected = {task["task_id"]: task for task in plan["cadical_tasks"]}
    records = collect_records(cadical_results_root)
    by_id = {record["task_id"]: record for record in records}
    missing = sorted(set(expected) - set(by_id))
    unexpected = sorted(set(by_id) - set(expected))
    if missing or unexpected:
        raise RuntimeError(
            f"CaDiCaL result mismatch: missing={missing}, "
            f"unexpected={unexpected}"
        )
    bad_sat = [
        r["task_id"]
        for r in records
        if r["status"] == "SAT" and not r.get("verified")
    ]
    if bad_sat:
        raise RuntimeError(f"unverified CaDiCaL SAT: {bad_sat}")
    verified_sat = [
        r["task_id"]
        for r in records
        if r["status"] == "SAT" and r.get("verified")
    ]
    unknown = (
        []
        if verified_sat
        else sorted(
            (r for r in records if r["status"] == "UNKNOWN"),
            key=lambda item: item["root_id"],
        )
    )

    parent_by_root = {
        task["root_id"]: task for task in plan["cadical_tasks"]
    }
    kissat_tasks = []
    for record in unknown:
        parent = parent_by_root[record["root_id"]]
        kissat_tasks.append(
            {
                **parent,
                "task_id": f"kissat{KISSAT_SECONDS}-{record['root_id']}",
                "stage": "kissat",
                "method": f"kissat{KISSAT_SECONDS}",
                "solver": "kissat",
                "seconds": KISSAT_SECONDS,
            }
        )

    output.mkdir(parents=True, exist_ok=True)
    fallback_manifest = {
        "schema": PLAN_SCHEMA,
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "cadical_tasks": [],
        "kissat_tasks": kissat_tasks,
        "coverage": (
            "Kissat receives exactly CaDiCaL UNKNOWN children. Exact "
            "CaDiCaL closures and verified SAT children are not resubmitted."
        ),
    }
    write_json(output / "v24a-kissat-manifest.json", fallback_manifest)
    cadical_ledger = {
        "schema": CADICAL_LEDGER_SCHEMA,
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "expected_results": len(expected),
        "results_received": len(records),
        "missing_task_ids": missing,
        "statuses": dict(Counter(r["status"] for r in records)),
        "exact_closed_root_ids": sorted(
            r["root_id"] for r in records if r["status"] == "UNSAT"
        ),
        "unknown_root_ids": [r["root_id"] for r in unknown],
        "verified_sat_witnesses": verified_sat,
        "cpu_seconds": round(sum(float(r["seconds"]) for r in records), 3),
        "results": sorted(records, key=lambda item: item["task_id"]),
    }
    write_json(output / "v24a-cadical-ledger.json", cadical_ledger)
    matrix_output.write_text(
        json.dumps(
            {
                "include": [
                    {
                        "task_id": task["task_id"],
                        "box": task["box"],
                        "seconds": task["seconds"],
                    }
                    for task in kissat_tasks
                ]
            },
            separators=(",", ":"),
        )
        + "\n",
        encoding="utf-8",
    )
    print(
        json.dumps(
            {
                "cadical_statuses": cadical_ledger["statuses"],
                "kissat_tasks": len(kissat_tasks),
            },
            indent=2,
        ),
        flush=True,
    )
    return cadical_ledger


def aggregate(
    *,
    source: Path,
    cadical_ledger_path: Path,
    kissat_results_root: Path,
    output: Path,
    workflow_run_id: str | None,
) -> dict:
    plan = load_json(source / "v24a-manifest.json")
    cadical = load_json(cadical_ledger_path)
    if cadical.get("schema") != CADICAL_LEDGER_SCHEMA:
        raise RuntimeError("unexpected V24-A CaDiCaL ledger")
    kissat_records = collect_records(kissat_results_root)
    kissat_by_root = {record["root_id"]: record for record in kissat_records}
    expected_kissat = set(cadical["unknown_root_ids"])
    missing = sorted(expected_kissat - set(kissat_by_root))
    unexpected = sorted(set(kissat_by_root) - expected_kissat)
    if missing or unexpected:
        raise RuntimeError(
            f"Kissat result mismatch: missing={missing}, "
            f"unexpected={unexpected}"
        )
    bad_sat = [
        r["task_id"]
        for r in kissat_records
        if r["status"] == "SAT" and not r.get("verified")
    ]
    if bad_sat:
        raise RuntimeError(f"unverified Kissat SAT: {bad_sat}")

    cadical_by_root = {
        record["root_id"]: record for record in cadical["results"]
    }
    final_by_root = {}
    for task in plan["cadical_tasks"]:
        root_id = task["root_id"]
        first = cadical_by_root[root_id]
        final_by_root[root_id] = (
            kissat_by_root[root_id]
            if first["status"] == "UNKNOWN"
            else first
        )

    unit_by_leaf: dict[str, list[dict]] = defaultdict(list)
    for item in plan["unit_closed_children"]:
        unit_by_leaf[item["source_leaf_id"]].append(item)
    tasks_by_leaf: dict[str, list[dict]] = defaultdict(list)
    for task in plan["cadical_tasks"]:
        tasks_by_leaf[task["source_leaf_id"]].append(task)

    leaf_records = {}
    closed_source_leaves = []
    open_children = []
    verified_sat = []
    for source_leaf in plan["v22_open_child_leaves"]:
        leaf_id = source_leaf["child_id"]
        results = [
            final_by_root[task["root_id"]] for task in tasks_by_leaf[leaf_id]
        ]
        unknown = [r for r in results if r["status"] == "UNKNOWN"]
        sat = [
            r for r in results if r["status"] == "SAT" and r.get("verified")
        ]
        if not unknown and not sat:
            closed_source_leaves.append(leaf_id)
        verified_sat.extend(sat)
        for result in unknown:
            open_children.append(
                {
                    "root_id": result["root_id"],
                    "source_leaf_id": leaf_id,
                    "source_parent_root_id": result[
                        "source_parent_root_id"
                    ],
                    "box": result["box"],
                    "split_path": result["split_path"],
                    "cube_literals": result["cube_literals"],
                    "cube_depth": result["cube_depth"],
                    "cube_sha256": result["cube_sha256"],
                    "status": "UNKNOWN",
                }
            )
        leaf_records[leaf_id] = {
            "source_parent_root_id": source_leaf["parent_root_id"],
            "box": source_leaf["box"],
            "source_leaf_closed": not unknown and not sat,
            "unit_closed_children": len(unit_by_leaf[leaf_id]),
            "solver_closed_children": sum(
                r["status"] == "UNSAT" for r in results
            ),
            "open_children": len(unknown),
            "verified_sat_children": len(sat),
        }

    source_leaves_by_parent: dict[str, list[str]] = defaultdict(list)
    for leaf in plan["v22_open_child_leaves"]:
        source_leaves_by_parent[leaf["parent_root_id"]].append(
            leaf["child_id"]
        )
    newly_closed_parents = []
    for parent_id, leaf_ids in source_leaves_by_parent.items():
        if all(leaf_id in closed_source_leaves for leaf_id in leaf_ids):
            newly_closed_parents.append(parent_id)

    prior_closed = set(plan["v22_closed_parent_ids"])
    if len(prior_closed) != 123:
        raise RuntimeError("V24-A plan lost prior V22 parent closures")
    total_closed_parents = prior_closed | set(newly_closed_parents)
    if len(total_closed_parents) > 139:
        raise RuntimeError("V24-A parent closure count is impossible")

    logical_conclusion = (
        "V24A_VERIFIED_SAT"
        if verified_sat
        else (
            "V24A_V22_FRONT_EXACTLY_CLOSED"
            if not open_children
            else "V24A_CUBE_CONQUER_COMPLETE_K16_OPEN"
        )
    )
    record = {
        "schema": FINAL_LEDGER_SCHEMA,
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "workflow_run_id": workflow_run_id,
        "source_run_id": plan["source_runs"]["v22"],
        "logical_conclusion": logical_conclusion,
        "baseline": plan["baseline"],
        "refinement": {
            "source_open_leaves_refined": len(plan["trees"]),
            "unit_closed_children": len(plan["unit_closed_children"]),
            "solver_children": len(plan["cadical_tasks"]),
            "cadical_statuses": cadical["statuses"],
            "kissat_statuses": dict(
                Counter(r["status"] for r in kissat_records)
            ),
            "cadical_cpu_seconds": cadical["cpu_seconds"],
            "kissat_cpu_seconds": round(
                sum(float(r["seconds"]) for r in kissat_records), 3
            ),
        },
        "newly_closed_source_leaf_ids": sorted(closed_source_leaves),
        "newly_closed_source_leaf_count": len(closed_source_leaves),
        "remaining_source_leaf_count": (
            EXPECTED_SOURCE_OPEN_LEAVES - len(closed_source_leaves)
        ),
        "newly_closed_parent_ids": sorted(newly_closed_parents),
        "closed_parent_ids": sorted(total_closed_parents),
        "closed_parent_count": len(total_closed_parents),
        "open_parent_count": 139 - len(total_closed_parents),
        "open_child_leaves": sorted(
            open_children, key=lambda item: item["root_id"]
        ),
        "open_child_count": len(open_children),
        "leaf_records": leaf_records,
        "verified_sat_witnesses": verified_sat,
        "coverage_audit": plan["coverage"],
        "next_action": (
            "Reuse only open_child_leaves. UNKNOWN is not exclusion. "
            "Never resubmit a V22/V24-A closed leaf."
        ),
        "cadical_results": cadical["results"],
        "kissat_results": sorted(
            kissat_records, key=lambda item: item["task_id"]
        ),
    }
    write_json(output, record)
    print(
        json.dumps(
            {
                "logical_conclusion": logical_conclusion,
                "closed_v22_source_leaves": len(closed_source_leaves),
                "remaining_v24a_children": len(open_children),
                "closed_parent_regions": len(total_closed_parents),
                "verified_sat": len(verified_sat),
            },
            indent=2,
        ),
        flush=True,
    )
    return record


def parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser()
    mode = p.add_mutually_exclusive_group(required=True)
    mode.add_argument("--plan", action="store_true")
    mode.add_argument("--solve", action="store_true")
    mode.add_argument("--select-kissat", action="store_true")
    mode.add_argument("--aggregate", action="store_true")
    p.add_argument("--v22-source", type=Path)
    p.add_argument("--v22-ledger", type=Path)
    p.add_argument("--v22-run-id")
    p.add_argument("--kissat-binary", type=Path)
    p.add_argument("--output", type=Path)
    p.add_argument("--matrix-output", type=Path)
    p.add_argument("--source", type=Path)
    p.add_argument("--manifest", type=Path)
    p.add_argument("--task-id")
    p.add_argument("--result", type=Path)
    p.add_argument("--log", type=Path)
    p.add_argument("--seconds-override", type=int)
    p.add_argument("--cadical-results-root", type=Path)
    p.add_argument("--cadical-ledger", type=Path)
    p.add_argument("--kissat-results-root", type=Path)
    p.add_argument("--workflow-run-id")
    return p


def main() -> None:
    args = parser().parse_args()
    if args.plan:
        plan_campaign(
            v22_source=args.v22_source,
            v22_ledger_path=args.v22_ledger,
            kissat_binary=args.kissat_binary,
            output=args.output,
            matrix_output=args.matrix_output,
            v22_run_id=args.v22_run_id,
        )
    elif args.solve:
        solve_task(
            source=args.source,
            manifest_path=args.manifest,
            task_id=args.task_id,
            result_path=args.result,
            log_path=args.log,
            seconds_override=args.seconds_override,
        )
    elif args.select_kissat:
        select_kissat(
            source=args.source,
            cadical_results_root=args.cadical_results_root,
            output=args.output,
            matrix_output=args.matrix_output,
        )
    elif args.aggregate:
        aggregate(
            source=args.source,
            cadical_ledger_path=args.cadical_ledger,
            kissat_results_root=args.kissat_results_root,
            output=args.output,
            workflow_run_id=args.workflow_run_id,
        )


if __name__ == "__main__":
    main()
