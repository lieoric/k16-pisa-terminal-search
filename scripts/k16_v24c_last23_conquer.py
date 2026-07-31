#!/usr/bin/env python3
"""V24-C exact refinement of the 23 terminal UNKNOWN V24-B children."""

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

from k16_smart_deepen import (  # noqa: E402
    Dimacs,
    cube_hash,
    sha256,
    write_json,
)
from k16_staged_cascade import (  # noqa: E402
    assignment_to_arcs,
    independent_audit,
    parse_cadical_assignment,
    run_limited,
    write_assumption_cnf,
)
from k16_v24a_cube_conquer import audit_tree, expand_tree  # noqa: E402


MODEL_VERSION = "k16-pisa-v24c-last23-cube-conquer-20260731"
PLAN_SCHEMA = "k16-v24c-plan-v1"
RESULT_SCHEMA = "k16-v24c-result-v1"
CADICAL_LEDGER_SCHEMA = "k16-v24c-cadical-ledger-v1"
FINAL_LEDGER_SCHEMA = "k16-v24c-ledger-v1"
V24B_PLAN_SCHEMA = "k16-v24b-plan-v1"
V24B_LEDGER_SCHEMA = "k16-v24b-ledger-v1"

TARGET_BOXES = ("a0_z2", "a0_z3", "a0_z4p", "a1_z4p")
GROUPS = {
    "g1": ("a0_z2", "a1_z4p"),
    "g2": ("a0_z3",),
    "g3": ("a0_z4p",),
}
BOX_TO_GROUP = {
    box: group for group, boxes in GROUPS.items() for box in boxes
}
EXPECTED_TOTAL_PARTITION_LEAVES = 676
EXPECTED_PRIOR_EXACT = 656
EXPECTED_OPEN_V23_LEAVES = 20
EXPECTED_OPEN_V24B_CHILDREN = 23
EXPECTED_PRIOR_ROOTS = {"a1_z2", "a2p_z2", "a2p_z3"}
SPLIT_LEVELS = 3
CADICAL_SECONDS = 3600
KISSAT_SECONDS = 3600
PLAN_FILENAME = "v24c-manifest.json"
KISSAT_MANIFEST_FILENAME = "v24c-kissat-manifest.json"
CADICAL_LEDGER_FILENAME = "v24c-cadical-ledger.json"


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
        raise RuntimeError("duplicate V24-C result identifiers")
    return records


def write_group_matrices(
    directory: Path,
    prefix: str,
    tasks: list[dict],
) -> None:
    directory.mkdir(parents=True, exist_ok=True)
    for group in GROUPS:
        selected = [task for task in tasks if task["group"] == group]
        (directory / f"{prefix}-{group}.json").write_text(
            json.dumps(
                {
                    "include": [
                        {
                            "task_id": task["task_id"],
                            "box": task["box"],
                            "seconds": task["seconds"],
                        }
                        for task in selected
                    ]
                },
                separators=(",", ":"),
            )
            + "\n",
            encoding="utf-8",
        )


def validate_prior(
    source: Path,
    ledger_path: Path,
) -> tuple[dict, dict, list[dict]]:
    ledger = load_json(ledger_path)
    if ledger.get("schema") != V24B_LEDGER_SCHEMA:
        raise RuntimeError("unexpected V24-B ledger schema")
    if ledger.get("logical_conclusion") != (
        "V24B_CUBE_CONQUER_COMPLETE_K16_OPEN"
    ):
        raise RuntimeError("V24-B is not the completed open frontier")
    if ledger.get("verified_sat_witnesses"):
        raise RuntimeError("V24-B already contains a verified SAT witness")
    if (
        int(ledger.get("exact_partition_leaf_closures", -1))
        != EXPECTED_PRIOR_EXACT
        or int(ledger.get("open_partition_source_leaves", -1))
        != EXPECTED_OPEN_V23_LEAVES
        or int(ledger.get("open_child_count", -1))
        != EXPECTED_OPEN_V24B_CHILDREN
        or set(ledger.get("roots_exactly_excluded", []))
        != EXPECTED_PRIOR_ROOTS
    ):
        raise RuntimeError("unexpected V24-B endpoint counts")

    plan = load_json(source / "v24b-manifest.json")
    if plan.get("schema") != V24B_PLAN_SCHEMA:
        raise RuntimeError("unexpected V24-B source manifest")
    if plan.get("source_runs") != ledger.get("source_runs"):
        raise RuntimeError("V24-B source-run provenance mismatch")
    if not plan.get("coverage", {}).get("all_tree_audits_passed"):
        raise RuntimeError("V24-B source coverage was not audited")

    for solver in ("cadical", "kissat"):
        binary = source / solver / solver
        if (
            not binary.is_file()
            or sha256(binary) != plan["source_hashes"][solver]
        ):
            raise RuntimeError(f"V24-B {solver} binary mismatch")

    task_by_root = {
        task["root_id"]: task for task in plan["cadical_tasks"]
    }
    final_by_root = {
        record["root_id"]: record for record in ledger["cadical_results"]
    }
    for record in ledger["kissat_results"]:
        final_by_root[record["root_id"]] = record

    open_children = sorted(
        ledger["open_child_leaves"],
        key=lambda item: (item["box"], item["root_id"]),
    )
    if (
        len(open_children) != EXPECTED_OPEN_V24B_CHILDREN
        or len({item["root_id"] for item in open_children})
        != EXPECTED_OPEN_V24B_CHILDREN
    ):
        raise RuntimeError("V24-B open-child set is not exactly 23")
    if set(item["box"] for item in open_children) != set(TARGET_BOXES):
        raise RuntimeError("unexpected V24-B open boxes")

    for child in open_children:
        root_id = child["root_id"]
        task = task_by_root.get(root_id)
        result = final_by_root.get(root_id)
        if task is None or result is None:
            raise RuntimeError(f"missing V24-B signed child: {root_id}")
        for key in (
            "box",
            "source_leaf_id",
            "cube_literals",
            "cube_depth",
            "cube_sha256",
        ):
            if task[key] != child[key]:
                raise RuntimeError(
                    f"V24-B child/plan mismatch: {root_id}/{key}"
                )
        if (
            result["status"] != "UNKNOWN"
            or result["cube_sha256"] != child["cube_sha256"]
            or cube_hash(child["cube_literals"]) != child["cube_sha256"]
        ):
            raise RuntimeError(f"V24-B child is not a signed UNKNOWN: {root_id}")

    open_v23 = {item["source_leaf_id"] for item in open_children}
    if len(open_v23) != EXPECTED_OPEN_V23_LEAVES:
        raise RuntimeError("V24-B open children do not map to 20 V23 leaves")
    return ledger, plan, open_children


def plan_campaign(
    *,
    v24b_source: Path,
    v24b_ledger_path: Path,
    output: Path,
    matrix_dir: Path,
    v24b_run_id: str,
) -> dict:
    ledger, prior_plan, open_children = validate_prior(
        v24b_source,
        v24b_ledger_path,
    )
    output.mkdir(parents=True, exist_ok=True)
    (output / "boxes").mkdir(parents=True, exist_ok=True)

    for solver in ("cadical", "kissat"):
        (output / solver).mkdir(parents=True, exist_ok=True)
        shutil.copy2(
            v24b_source / solver / solver,
            output / solver / solver,
        )

    dimacs_by_box = {}
    box_hashes = {}
    for box in TARGET_BOXES:
        source_cnf = v24b_source / "boxes" / box / "enriched.cnf"
        expected = prior_plan["partition_provenance"][box][
            "enriched_cnf_sha256"
        ]
        if sha256(source_cnf) != expected:
            raise RuntimeError(f"V24-B CNF mismatch: {box}")
        destination = output / "boxes" / box
        destination.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source_cnf, destination / "enriched.cnf")
        source_manifest = (
            v24b_source / "boxes" / box / "partition-manifest.json"
        )
        shutil.copy2(
            source_manifest,
            destination / "partition-manifest.json",
        )
        dimacs_by_box[box] = Dimacs(destination / "enriched.cnf")
        box_hashes[box] = expected

    trees = {}
    survivors = []
    unit_closed = []
    for source in open_children:
        source_ref_id = f"v24b-{source['root_id']}"
        box = source["box"]
        nodes: list[dict] = []
        children: list[dict] = []
        closed: list[dict] = []
        expand_tree(
            dimacs=dimacs_by_box[box],
            source_leaf_id=source_ref_id,
            assumptions=list(source["cube_literals"]),
            levels=SPLIT_LEVELS,
            path_bits="",
            nodes=nodes,
            survivors=children,
            unit_closed=closed,
        )
        for child in children:
            child.update(
                box=box,
                group=BOX_TO_GROUP[box],
                source_ref_id=source_ref_id,
                v24b_root_id=source["root_id"],
                v23_source_leaf_id=source["source_leaf_id"],
                parent_split_path=source["split_path"],
            )
            survivors.append(child)
        for child in closed:
            child.update(
                box=box,
                group=BOX_TO_GROUP[box],
                source_ref_id=source_ref_id,
                v24b_root_id=source["root_id"],
                v23_source_leaf_id=source["source_leaf_id"],
                parent_split_path=source["split_path"],
            )
            unit_closed.append(child)
        tree = {
            "source_ref_id": source_ref_id,
            "source_leaf_id": source_ref_id,
            "v24b_root_id": source["root_id"],
            "v23_source_leaf_id": source["source_leaf_id"],
            "box": box,
            "group": BOX_TO_GROUP[box],
            "parent_split_path": source["split_path"],
            "parent_cube_literals": list(source["cube_literals"]),
            "parent_cube_depth": int(source["cube_depth"]),
            "parent_cube_sha256": source["cube_sha256"],
            "split_levels": SPLIT_LEVELS,
            "nodes": nodes,
            "surviving_children": len(children),
            "unit_closed_children": len(closed),
        }
        tree["coverage_audit"] = audit_tree(
            tree,
            source["cube_literals"],
            split_levels=SPLIT_LEVELS,
        )
        trees[source_ref_id] = tree

    tasks = []
    for index, child in enumerate(
        sorted(
            survivors,
            key=lambda item: (
                item["group"],
                item["box"],
                item["v24b_root_id"],
                item["path_bits"],
            ),
        ),
        start=1,
    ):
        root_id = f"c{index:04d}"
        tasks.append(
            {
                "task_id": f"cadical{CADICAL_SECONDS}-{root_id}",
                "stage": "cadical",
                "method": f"cadical{CADICAL_SECONDS}",
                "solver": "cadical",
                "seconds": CADICAL_SECONDS,
                "group": child["group"],
                "box": child["box"],
                "root_id": root_id,
                "source_ref_id": child["source_ref_id"],
                "v24b_root_id": child["v24b_root_id"],
                "v23_source_leaf_id": child["v23_source_leaf_id"],
                "parent_split_path": child["parent_split_path"],
                "split_path": child["path_bits"],
                "cube_literals": child["cube_literals"],
                "cube_depth": child["cube_depth"],
                "cube_sha256": child["cube_sha256"],
            }
        )

    record = {
        "schema": PLAN_SCHEMA,
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "source_run": v24b_run_id,
        "source_hashes": {
            "v24b_ledger": sha256(v24b_ledger_path),
            "cadical": sha256(output / "cadical" / "cadical"),
            "kissat": sha256(output / "kissat" / "kissat"),
            "theorem_cnf": box_hashes,
        },
        "baseline": {
            "total_partition_leaves": EXPECTED_TOTAL_PARTITION_LEAVES,
            "prior_exact_partition_leaves": EXPECTED_PRIOR_EXACT,
            "open_v23_source_leaves": EXPECTED_OPEN_V23_LEAVES,
            "open_v24b_child_leaves": EXPECTED_OPEN_V24B_CHILDREN,
            "prior_roots_exactly_excluded": sorted(EXPECTED_PRIOR_ROOTS),
        },
        "prior_per_box": ledger["per_box"],
        "v24b_open_child_records": open_children,
        "trees": trees,
        "unit_closed_children": unit_closed,
        "cadical_tasks": tasks,
        "coverage": {
            "source_children_refined": len(trees),
            "all_tree_audits_passed": all(
                tree["coverage_audit"]["complete_binary_branching"]
                for tree in trees.values()
            ),
            "statement": (
                "Every one of the 23 V24-B terminal UNKNOWN children is "
                "exactly replaced by a complete three-level binary tree."
            ),
        },
    }
    write_json(output / "v24c-manifest.json", record)
    write_group_matrices(matrix_dir, "cadical", tasks)
    print(
        json.dumps(
            {
                "source_v24b_children": len(trees),
                "source_v23_leaves": len(
                    {item["source_leaf_id"] for item in open_children}
                ),
                "unit_closed_children": len(unit_closed),
                "queued_children": len(tasks),
                "by_group": dict(Counter(t["group"] for t in tasks)),
                "by_box": dict(Counter(t["box"] for t in tasks)),
                "coverage_audits": sum(
                    tree["coverage_audit"]["complete_binary_branching"]
                    for tree in trees.values()
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
) -> dict:
    manifest = load_json(manifest_path)
    tasks = manifest.get("cadical_tasks", []) + manifest.get(
        "kissat_tasks", []
    )
    matches = [task for task in tasks if task["task_id"] == task_id]
    if len(matches) != 1:
        raise RuntimeError(f"task lookup failed: {task_id}")
    task = matches[0]
    solver = task["solver"]
    seconds = int(task["seconds"])
    cnf = source / "boxes" / task["box"] / "enriched.cnf"
    work = result_path.parent.parent / "work" / task_id
    work.mkdir(parents=True, exist_ok=True)
    assumption_cnf = work / "assumption.cnf"
    write_assumption_cnf(cnf, assumption_cnf, task["cube_literals"])
    returncode, text, timed_out, elapsed = run_limited(
        [str(source / solver / solver), str(assumption_cnf)],
        timeout_seconds=seconds,
    )
    status = {10: "SAT", 20: "UNSAT"}.get(returncode, "UNKNOWN")
    if timed_out:
        status = "UNKNOWN"
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
        **{
            key: task[key]
            for key in (
                "task_id",
                "stage",
                "method",
                "solver",
                "group",
                "box",
                "root_id",
                "source_ref_id",
                "v24b_root_id",
                "v23_source_leaf_id",
                "parent_split_path",
                "split_path",
                "cube_literals",
                "cube_depth",
                "cube_sha256",
            )
        },
        "status": status,
        "seconds": round(elapsed, 3),
        "time_limit_seconds": seconds,
        "returncode": returncode,
        "raw_result": returncode if returncode in {10, 20} else 0,
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
            box=task["box"],
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
    matrix_dir: Path,
) -> dict:
    plan = load_json(source / PLAN_FILENAME)
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
        record["task_id"]
        for record in records
        if record["status"] == "SAT" and not record.get("verified")
    ]
    if bad_sat:
        raise RuntimeError(f"unverified CaDiCaL SAT: {bad_sat}")
    verified_sat = [
        record["task_id"]
        for record in records
        if record["status"] == "SAT" and record.get("verified")
    ]
    unknown = (
        []
        if verified_sat
        else sorted(
            (
                record
                for record in records
                if record["status"] == "UNKNOWN"
            ),
            key=lambda item: item["root_id"],
        )
    )
    parent_by_root = {
        task["root_id"]: task for task in plan["cadical_tasks"]
    }
    tasks = []
    for result in unknown:
        parent = parent_by_root[result["root_id"]]
        tasks.append(
            {
                **parent,
                "task_id": f"kissat{KISSAT_SECONDS}-{result['root_id']}",
                "stage": "kissat",
                "method": f"kissat{KISSAT_SECONDS}",
                "solver": "kissat",
                "seconds": KISSAT_SECONDS,
            }
        )
    output.mkdir(parents=True, exist_ok=True)
    write_json(
        output / KISSAT_MANIFEST_FILENAME,
        {
            "schema": PLAN_SCHEMA,
            "model_version": MODEL_VERSION,
            "created_utc": utc_now(),
            "cadical_tasks": [],
            "kissat_tasks": tasks,
        },
    )
    ledger = {
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
        "cpu_seconds": round(
            sum(float(record["seconds"]) for record in records),
            3,
        ),
        "results": sorted(records, key=lambda item: item["task_id"]),
    }
    write_json(output / CADICAL_LEDGER_FILENAME, ledger)
    write_group_matrices(matrix_dir, "kissat", tasks)
    print(
        json.dumps(
            {
                "cadical_statuses": ledger["statuses"],
                "kissat_tasks": len(tasks),
                "kissat_by_group": dict(
                    Counter(task["group"] for task in tasks)
                ),
            },
            indent=2,
        ),
        flush=True,
    )
    return ledger


def aggregate(
    *,
    source: Path,
    cadical_ledger_path: Path,
    kissat_results_root: Path,
    output: Path,
    workflow_run_id: str | None,
) -> dict:
    plan = load_json(source / PLAN_FILENAME)
    cadical = load_json(cadical_ledger_path)
    if cadical.get("schema") != CADICAL_LEDGER_SCHEMA:
        raise RuntimeError("unexpected V24-C CaDiCaL ledger")
    kissat_records = collect_records(kissat_results_root)
    kissat_by_root = {
        record["root_id"]: record for record in kissat_records
    }
    expected_kissat = set(cadical["unknown_root_ids"])
    missing = sorted(expected_kissat - set(kissat_by_root))
    unexpected = sorted(set(kissat_by_root) - expected_kissat)
    if missing or unexpected:
        raise RuntimeError(
            f"Kissat result mismatch: missing={missing}, "
            f"unexpected={unexpected}"
        )
    bad_sat = [
        record["task_id"]
        for record in kissat_records
        if record["status"] == "SAT" and not record.get("verified")
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

    unit_by_source: dict[str, list[dict]] = defaultdict(list)
    for item in plan["unit_closed_children"]:
        unit_by_source[item["source_ref_id"]].append(item)
    tasks_by_source: dict[str, list[dict]] = defaultdict(list)
    for task in plan["cadical_tasks"]:
        tasks_by_source[task["source_ref_id"]].append(task)

    source_child_records = {}
    closed_v24b_children = []
    open_terminal_children = []
    verified_sat = []
    for source in plan["v24b_open_child_records"]:
        source_ref = f"v24b-{source['root_id']}"
        results = [
            final_by_root[task["root_id"]]
            for task in tasks_by_source[source_ref]
        ]
        unknown = [r for r in results if r["status"] == "UNKNOWN"]
        sat = [
            r for r in results if r["status"] == "SAT" and r.get("verified")
        ]
        if not unknown and not sat:
            closed_v24b_children.append(source["root_id"])
        verified_sat.extend(sat)
        for result in unknown:
            open_terminal_children.append(
                {
                    "root_id": result["root_id"],
                    "source_ref_id": source_ref,
                    "v24b_root_id": source["root_id"],
                    "v23_source_leaf_id": source["source_leaf_id"],
                    "group": result["group"],
                    "box": result["box"],
                    "parent_split_path": result["parent_split_path"],
                    "split_path": result["split_path"],
                    "cube_literals": result["cube_literals"],
                    "cube_depth": result["cube_depth"],
                    "cube_sha256": result["cube_sha256"],
                    "status": "UNKNOWN",
                }
            )
        source_child_records[source["root_id"]] = {
            "box": source["box"],
            "v23_source_leaf_id": source["source_leaf_id"],
            "source_child_closed": not unknown and not sat,
            "unit_closed_children": len(unit_by_source[source_ref]),
            "solver_closed_children": sum(
                result["status"] == "UNSAT" for result in results
            ),
            "open_children": len(unknown),
            "verified_sat_children": len(sat),
        }

    closed_child_set = set(closed_v24b_children)
    open_by_v23: dict[str, list[str]] = defaultdict(list)
    source_box = {}
    for source in plan["v24b_open_child_records"]:
        open_by_v23[source["source_leaf_id"]].append(source["root_id"])
        source_box[source["source_leaf_id"]] = source["box"]
    newly_closed_v23 = sorted(
        source_leaf
        for source_leaf, roots in open_by_v23.items()
        if all(root in closed_child_set for root in roots)
    )
    newly_closed_set = set(newly_closed_v23)

    per_box = {}
    roots_closed = []
    for box, prior in plan["prior_per_box"].items():
        candidate_sources = [
            source_leaf
            for source_leaf, candidate_box in source_box.items()
            if candidate_box == box
        ]
        newly_closed = sum(
            source_leaf in newly_closed_set
            for source_leaf in candidate_sources
        )
        exact = int(prior["exact_leaf_closures"]) + newly_closed
        total = int(prior["partition_cubes"])
        root_closed = exact == total
        if root_closed:
            roots_closed.append(box)
        per_box[box] = {
            "partition_cubes": total,
            "prior_exact_closures": int(prior["exact_leaf_closures"]),
            "newly_closed_v23_source_leaves": newly_closed,
            "exact_leaf_closures": exact,
            "open_v23_source_leaves": len(candidate_sources) - newly_closed,
            "open_terminal_child_leaves": sum(
                child["box"] == box for child in open_terminal_children
            ),
            "root_exactly_excluded": root_closed,
        }

    total_exact = EXPECTED_PRIOR_EXACT + len(newly_closed_v23)
    conclusion = (
        "V24C_VERIFIED_SAT"
        if verified_sat
        else (
            "V24C_ALL_676_PARTITION_LEAVES_EXACTLY_CLOSED"
            if total_exact == EXPECTED_TOTAL_PARTITION_LEAVES
            else "V24C_LAST23_REFINEMENT_COMPLETE_K16_OPEN"
        )
    )
    record = {
        "schema": FINAL_LEDGER_SCHEMA,
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "workflow_run_id": workflow_run_id,
        "source_run": plan["source_run"],
        "logical_conclusion": conclusion,
        "baseline": plan["baseline"],
        "refinement": {
            "v24b_source_children_refined": len(plan["trees"]),
            "unit_closed_children": len(plan["unit_closed_children"]),
            "solver_children": len(plan["cadical_tasks"]),
            "cadical_statuses": cadical["statuses"],
            "kissat_statuses": dict(
                Counter(record["status"] for record in kissat_records)
            ),
            "cadical_cpu_seconds": cadical["cpu_seconds"],
            "kissat_cpu_seconds": round(
                sum(float(record["seconds"]) for record in kissat_records),
                3,
            ),
        },
        "closed_v24b_child_ids": sorted(closed_v24b_children),
        "closed_v24b_child_count": len(closed_v24b_children),
        "remaining_v24b_child_count": (
            EXPECTED_OPEN_V24B_CHILDREN - len(closed_v24b_children)
        ),
        "newly_closed_v23_source_leaf_ids": newly_closed_v23,
        "newly_closed_v23_source_leaf_count": len(newly_closed_v23),
        "remaining_v23_source_leaf_count": (
            EXPECTED_OPEN_V23_LEAVES - len(newly_closed_v23)
        ),
        "exact_partition_leaf_closures": total_exact,
        "open_partition_source_leaves": (
            EXPECTED_TOTAL_PARTITION_LEAVES - total_exact
        ),
        "roots_exactly_excluded": sorted(roots_closed),
        "per_box": per_box,
        "open_terminal_leaves": sorted(
            open_terminal_children,
            key=lambda item: item["root_id"],
        ),
        "open_terminal_count": len(open_terminal_children),
        "source_child_records": source_child_records,
        "verified_sat_witnesses": verified_sat,
        "coverage_audit": plan["coverage"],
        "next_action": (
            "Reuse only open_terminal_leaves. UNKNOWN is not exclusion. "
            "Never resubmit any V24-C exact closure."
        ),
        "cadical_results": cadical["results"],
        "kissat_results": sorted(
            kissat_records,
            key=lambda item: item["task_id"],
        ),
    }
    write_json(output, record)
    print(
        json.dumps(
            {
                "logical_conclusion": conclusion,
                "closed_v24b_children": len(closed_v24b_children),
                "newly_closed_v23_leaves": len(newly_closed_v23),
                "exact_partition_closures": total_exact,
                "remaining_terminal_children": len(open_terminal_children),
                "roots_exactly_excluded": sorted(roots_closed),
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
    p.add_argument("--v24b-source", type=Path)
    p.add_argument("--v24b-ledger", type=Path)
    p.add_argument("--v24b-run-id")
    p.add_argument("--output", type=Path)
    p.add_argument("--matrix-dir", type=Path)
    p.add_argument("--source", type=Path)
    p.add_argument("--manifest", type=Path)
    p.add_argument("--task-id")
    p.add_argument("--result", type=Path)
    p.add_argument("--log", type=Path)
    p.add_argument("--cadical-results-root", type=Path)
    p.add_argument("--cadical-ledger", type=Path)
    p.add_argument("--kissat-results-root", type=Path)
    p.add_argument("--workflow-run-id")
    return p


def main() -> None:
    args = parser().parse_args()
    if args.plan:
        plan_campaign(
            v24b_source=args.v24b_source,
            v24b_ledger_path=args.v24b_ledger,
            output=args.output,
            matrix_dir=args.matrix_dir,
            v24b_run_id=args.v24b_run_id,
        )
    elif args.solve:
        solve_task(
            source=args.source,
            manifest_path=args.manifest,
            task_id=args.task_id,
            result_path=args.result,
            log_path=args.log,
        )
    elif args.select_kissat:
        select_kissat(
            source=args.source,
            cadical_results_root=args.cadical_results_root,
            output=args.output,
            matrix_dir=args.matrix_dir,
        )
    else:
        aggregate(
            source=args.source,
            cadical_ledger_path=args.cadical_ledger,
            kissat_results_root=args.kissat_results_root,
            output=args.output,
            workflow_run_id=args.workflow_run_id,
        )


if __name__ == "__main__":
    main()
