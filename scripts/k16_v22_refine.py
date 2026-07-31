#!/usr/bin/env python3
"""V22 exact refinement of the 35 logical UNKNOWN leaves left by V21.

The V21 theorem-strengthened formula is reused byte-for-byte.  Every open
parent is replaced by a complete adaptive binary decision tree over directed
arc variables:

* depth <= 6 parents receive three more decisions (at most eight children);
* depth == 7 parents receive two decisions (at most four children);
* deeper parents receive one decision (at most two children).

The decision variable at every internal node is chosen by MOMS after unit
propagation.  Both polarities are emitted, so the heuristic affects search
order only.  Unit-inconsistent children are permanent exact closures.

Surviving children receive 60 minutes of CaDiCaL followed, only on UNKNOWN,
by 90 minutes of SMS.  SAT is accepted only after the independent primitive
K16 verifier; UNKNOWN is retained in the resumable ledger.
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

from k16_smart_deepen import (  # noqa: E402
    CUBE_RESULT,
    Dimacs,
    N,
    cube_hash,
    cube_line,
    parse_sms_arcs,
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


MODEL_VERSION = "k16-pisa-v22-hard-leaf-adaptive-refinement-20260729"
PLAN_SCHEMA = "k16-v22-refine-plan-v1"
RESULT_SCHEMA = "k16-v22-refine-result-v1"
CADICAL_LEDGER_SCHEMA = "k16-v22-refine-cadical-ledger-v1"
FINAL_LEDGER_SCHEMA = "k16-v22-refine-ledger-v1"
V21_LEDGER_SCHEMA = "k16-v21-theorem-cascade-ledger-v1"

EXPECTED_FRONTIER = 139
EXPECTED_V21_CLOSED = 104
EXPECTED_V21_OPEN = 35
CADICAL_SECONDS = 3600
SMS_SECONDS = 5400


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
    task_ids = [record["task_id"] for record in records]
    if len(task_ids) != len(set(task_ids)):
        raise RuntimeError("duplicate V22 refinement result identifiers")
    return records


def split_levels(depth: int) -> int:
    if depth <= 6:
        return 3
    if depth == 7:
        return 2
    return 1


def validate_v21(
    ledger_path: Path,
) -> tuple[dict, dict[str, dict]]:
    ledger = load_json(ledger_path)
    if ledger.get("schema") != V21_LEDGER_SCHEMA:
        raise RuntimeError("unexpected V21 ledger schema")
    if ledger.get("logical_conclusion") != "V21_COMPLETE_K16_OPEN":
        raise RuntimeError("V21 is not a completed open frontier")
    if ledger.get("verified_sat_witnesses"):
        raise RuntimeError("V21 already contains a verified SAT witness")
    if (
        int(ledger.get("closed_count", -1)) != EXPECTED_V21_CLOSED
        or int(ledger.get("open_count", -1)) != EXPECTED_V21_OPEN
    ):
        raise RuntimeError("unexpected V21 closure/open counts")
    closed = set(ledger["closed_queue_ids"])
    open_ids = set(ledger["open_queue_ids"])
    if closed & open_ids or len(closed | open_ids) != EXPECTED_FRONTIER:
        raise RuntimeError("V21 ledger is not a disjoint complete frontier")
    by_root = {
        record["root_id"]: record
        for record in ledger["cadical_results"]
    }
    if not open_ids <= set(by_root):
        raise RuntimeError("V21 open leaf lacks its signed cube")
    return ledger, by_root


def _expand_tree(
    *,
    dimacs: Dimacs,
    parent_id: str,
    assumptions: list[int],
    levels: int,
    path: str,
    nodes: list[dict],
    survivors: list[dict],
    unit_closed: list[dict],
) -> None:
    assignment, contradiction = dimacs.propagate(assumptions)
    node_id = f"{parent_id}:{path or 'root'}"
    if contradiction:
        item = {
            "node_id": node_id,
            "parent_root_id": parent_id,
            "path": path,
            "cube_literals": assumptions,
            "cube_depth": len(assumptions),
            "cube_sha256": cube_hash(assumptions),
            "status": "UNSAT",
            "method": "unit_propagation",
            "solver_level_exact": True,
        }
        unit_closed.append(item)
        nodes.append({"node_id": node_id, "kind": "unit_closed"})
        return
    if levels == 0:
        item = {
            "node_id": node_id,
            "parent_root_id": parent_id,
            "path": path,
            "cube_literals": assumptions,
            "cube_depth": len(assumptions),
            "cube_sha256": cube_hash(assumptions),
            "implied_assignments": len(assignment),
        }
        survivors.append(item)
        nodes.append({"node_id": node_id, "kind": "survivor"})
        return

    variable, moms = dimacs.moms_arc_variable(assumptions)
    if variable in {abs(literal) for literal in assumptions}:
        raise RuntimeError("MOMS selected an already decided variable")
    positive_path = path + f"-v{variable:06d}p"
    negative_path = path + f"-v{variable:06d}n"
    nodes.append(
        {
            "node_id": node_id,
            "kind": "branch",
            "variable": variable,
            "moms": moms,
            "positive_child": f"{parent_id}:{positive_path}",
            "negative_child": f"{parent_id}:{negative_path}",
        }
    )
    _expand_tree(
        dimacs=dimacs,
        parent_id=parent_id,
        assumptions=assumptions + [variable],
        levels=levels - 1,
        path=positive_path,
        nodes=nodes,
        survivors=survivors,
        unit_closed=unit_closed,
    )
    _expand_tree(
        dimacs=dimacs,
        parent_id=parent_id,
        assumptions=assumptions + [-variable],
        levels=levels - 1,
        path=negative_path,
        nodes=nodes,
        survivors=survivors,
        unit_closed=unit_closed,
    )


def plan(
    *,
    v21_source: Path,
    v21_ledger_path: Path,
    output: Path,
    matrix_output: Path,
    v21_run_id: str,
) -> dict:
    ledger, by_root = validate_v21(v21_ledger_path)
    source_manifest = load_json(v21_source / "v21-manifest.json")
    if source_manifest.get("model_version") != (
        "k16-pisa-v21-theorem-long-cascade-20260728"
    ):
        raise RuntimeError("unexpected V21 theorem source")

    output.mkdir(parents=True, exist_ok=True)
    for name in ("boxes", "bundle", "cadical"):
        shutil.copytree(
            v21_source / name,
            output / name,
            dirs_exist_ok=True,
        )

    dimacs_by_box = {
        box: Dimacs(
            output / "boxes" / box / "enriched-theorem.cnf"
        )
        for box in ("a1_z3", "a2p_z4p")
    }
    trees: dict[str, dict] = {}
    survivor_nodes: list[dict] = []
    unit_closed: list[dict] = []

    for parent_id in sorted(ledger["open_queue_ids"]):
        parent = by_root[parent_id]
        box = parent["box"]
        depth = int(parent["cube_depth"])
        levels = split_levels(depth)
        nodes: list[dict] = []
        children: list[dict] = []
        closed_children: list[dict] = []
        _expand_tree(
            dimacs=dimacs_by_box[box],
            parent_id=parent_id,
            assumptions=list(parent["cube_literals"]),
            levels=levels,
            path="",
            nodes=nodes,
            survivors=children,
            unit_closed=closed_children,
        )
        expected_max = 1 << levels
        if len(children) + len(closed_children) > expected_max:
            raise RuntimeError("adaptive split emitted too many terminal nodes")
        if not children and not closed_children:
            raise RuntimeError("adaptive split emitted no terminal nodes")
        for child in children:
            child["box"] = box
            child["root_kind"] = "v22_refined_child"
            child["split_levels"] = levels
            survivor_nodes.append(child)
        for child in closed_children:
            child["box"] = box
            child["split_levels"] = levels
            unit_closed.append(child)
        trees[parent_id] = {
            "box": box,
            "parent_cube_literals": list(parent["cube_literals"]),
            "parent_cube_depth": depth,
            "parent_cube_sha256": cube_hash(parent["cube_literals"]),
            "split_levels": levels,
            "maximum_children": expected_max,
            "surviving_children": len(children),
            "unit_closed_children": len(closed_children),
            "nodes": nodes,
        }

    tasks = []
    for index, child in enumerate(
        sorted(survivor_nodes, key=lambda item: item["node_id"]),
        start=1,
    ):
        child_id = f"r{index:04d}"
        child["child_id"] = child_id
        task_id = f"cadical{CADICAL_SECONDS}-{child_id}"
        tasks.append(
            {
                "task_id": task_id,
                "stage": "cadical",
                "method": f"cadical{CADICAL_SECONDS}",
                "solver": "cadical",
                "seconds": CADICAL_SECONDS,
                "sms_seconds": SMS_SECONDS,
                "complexity_class": "refined",
                "box": child["box"],
                "root_id": child_id,
                "parent_root_id": child["parent_root_id"],
                "root_kind": child["root_kind"],
                "split_path": child["path"],
                "cube_literals": child["cube_literals"],
                "cube_depth": child["cube_depth"],
                "cube_sha256": child["cube_sha256"],
            }
        )

    if len(tasks) > 102:
        raise RuntimeError(f"expected at most 102 tasks, got {len(tasks)}")
    if len(trees) != EXPECTED_V21_OPEN:
        raise RuntimeError("not every V21 UNKNOWN parent was refined")

    record = {
        "schema": PLAN_SCHEMA,
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "source_runs": {"v21": v21_run_id},
        "source_hashes": {
            "v21_ledger": sha256(v21_ledger_path),
            "v21_manifest": sha256(v21_source / "v21-manifest.json"),
            "cadical": sha256(output / "cadical" / "cadical"),
            "theorem_cnf": {
                box: sha256(
                    output / "boxes" / box / "enriched-theorem.cnf"
                )
                for box in ("a1_z3", "a2p_z4p")
            },
        },
        "baseline": {
            "frontier_parent_leaves": EXPECTED_FRONTIER,
            "v21_closed_parent_leaves": EXPECTED_V21_CLOSED,
            "v21_open_parent_leaves": EXPECTED_V21_OPEN,
        },
        "split_policy": {
            "depth_le_6": 3,
            "depth_7": 2,
            "depth_ge_8": 1,
            "rule": (
                "adaptive MOMS after unit propagation; both polarities at "
                "every internal node"
            ),
        },
        "v21_closed_queue_ids": sorted(ledger["closed_queue_ids"]),
        "v21_open_queue_ids": sorted(ledger["open_queue_ids"]),
        "trees": trees,
        "unit_closed_children": unit_closed,
        "cadical_tasks": tasks,
        "coverage": (
            "Every one of the 35 V21 UNKNOWN parents is replaced by a "
            "structurally complete adaptive binary tree. Both signs of each "
            "chosen arc variable are retained. Unit contradictions are exact "
            "closures; every other terminal node is queued."
        ),
    }
    write_json(output / "v22-refine-manifest.json", record)
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
                "parents": len(trees),
                "unit_closed_children": len(unit_closed),
                "cadical_children": len(tasks),
                "by_box": dict(Counter(t["box"] for t in tasks)),
                "child_depths": dict(
                    Counter(t["cube_depth"] for t in tasks)
                ),
            },
            indent=2,
        ),
        flush=True,
    )
    return record


def solve(
    *,
    source: Path,
    manifest_path: Path,
    task_id: str,
    result_path: Path,
    log_path: Path,
) -> dict:
    manifest = load_json(manifest_path)
    tasks = manifest.get("cadical_tasks", []) + manifest.get("sms_tasks", [])
    matches = [task for task in tasks if task["task_id"] == task_id]
    if len(matches) != 1:
        raise RuntimeError(f"task lookup failed: {task_id}")
    task = matches[0]
    seconds = int(task["seconds"])
    box = task["box"]
    cnf = source / "boxes" / box / "enriched-theorem.cnf"
    work = result_path.parent.parent / "work" / task_id
    work.mkdir(parents=True, exist_ok=True)

    if task["solver"] == "cadical":
        assumption_cnf = work / "assumption.cnf"
        write_assumption_cnf(cnf, assumption_cnf, task["cube_literals"])
        command = [
            str(source / "cadical" / "cadical"),
            str(assumption_cnf),
        ]
        returncode, text, timed_out, elapsed = run_limited(
            command,
            timeout_seconds=seconds,
        )
        status = {10: "SAT", 20: "UNSAT"}.get(returncode, "UNKNOWN")
        raw_result = returncode if returncode in {10, 20} else 0
        arcs = (
            assignment_to_arcs(parse_cadical_assignment(text))
            if status == "SAT"
            else None
        )
    elif task["solver"] == "sms":
        queue_file = manifest_path.parent / task["queue_file"]
        command = [
            str(source / "bundle" / "smsg"),
            "--vertices",
            str(N),
            "--directed",
            "--dimacs",
            str(cnf),
            "--cube-file",
            str(queue_file),
            "--cube-line",
            str(task["queue_line"]),
            "--cube-timeout",
            str(seconds),
        ]
        returncode, text, timed_out, elapsed = run_limited(
            command,
            timeout_seconds=seconds + 120,
        )
        cube_results = CUBE_RESULT.findall(text)
        raw_result = int(cube_results[-1]) if cube_results else 0
        status = {10: "SAT", 20: "UNSAT"}.get(raw_result, "UNKNOWN")
        arcs = parse_sms_arcs(text) if status == "SAT" else None
    else:
        raise RuntimeError(f"unknown solver: {task['solver']}")

    if timed_out:
        status = "UNKNOWN"
    log_path.parent.mkdir(parents=True, exist_ok=True)
    log_path.write_text(text, encoding="utf-8")
    record: dict = {
        "schema": RESULT_SCHEMA,
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "task_id": task_id,
        "stage": task["stage"],
        "method": task["method"],
        "solver": task["solver"],
        "box": box,
        "root_id": task["root_id"],
        "parent_root_id": task["parent_root_id"],
        "root_kind": task["root_kind"],
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


def select_sms(
    *,
    source: Path,
    cadical_results_root: Path,
    output: Path,
    matrix_output: Path,
) -> dict:
    plan_record = load_json(source / "v22-refine-manifest.json")
    expected = {
        task["task_id"]: task
        for task in plan_record["cadical_tasks"]
    }
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
    unknown_records = (
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

    output.mkdir(parents=True, exist_ok=True)
    queue_path = output / "sms-refined.cubes"
    queue_path.write_text(
        "\n".join(cube_line(r["cube_literals"]) for r in unknown_records)
        + ("\n" if unknown_records else ""),
        encoding="utf-8",
    )
    parent_by_root = {
        task["root_id"]: task
        for task in plan_record["cadical_tasks"]
    }
    sms_tasks = []
    for queue_line, record in enumerate(unknown_records, start=1):
        parent = parent_by_root[record["root_id"]]
        sms_tasks.append(
            {
                **parent,
                "task_id": f"sms{SMS_SECONDS}-{record['root_id']}",
                "stage": "sms",
                "method": f"sms{SMS_SECONDS}",
                "solver": "sms",
                "seconds": SMS_SECONDS,
                "queue_file": "sms-refined.cubes",
                "queue_line": queue_line,
            }
        )

    sms_manifest = {
        "schema": PLAN_SCHEMA,
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "cadical_tasks": [],
        "sms_tasks": sms_tasks,
        "coverage": (
            "SMS receives exactly CaDiCaL UNKNOWN refined children. "
            "SAT and UNSAT children are never resubmitted."
        ),
    }
    write_json(output / "v22-sms-manifest.json", sms_manifest)
    cadical_ledger = {
        "schema": CADICAL_LEDGER_SCHEMA,
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "expected_results": len(expected),
        "results_received": len(records),
        "missing_task_ids": missing,
        "statuses": dict(Counter(r["status"] for r in records)),
        "exact_closed_child_ids": sorted(
            r["root_id"] for r in records if r["status"] == "UNSAT"
        ),
        "unknown_child_ids": [r["root_id"] for r in unknown_records],
        "verified_sat_witnesses": verified_sat,
        "cpu_seconds": round(sum(float(r["seconds"]) for r in records), 3),
        "results": sorted(records, key=lambda item: item["task_id"]),
    }
    write_json(output / "v22-cadical-ledger.json", cadical_ledger)
    matrix_output.write_text(
        json.dumps(
            {
                "include": [
                    {
                        "task_id": task["task_id"],
                        "box": task["box"],
                        "seconds": task["seconds"],
                    }
                    for task in sms_tasks
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
                "sms_tasks": len(sms_tasks),
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
    sms_results_root: Path,
    output: Path,
    workflow_run_id: str | None,
) -> dict:
    plan_record = load_json(source / "v22-refine-manifest.json")
    cadical = load_json(cadical_ledger_path)
    if cadical.get("schema") != CADICAL_LEDGER_SCHEMA:
        raise RuntimeError("unexpected V22 CaDiCaL ledger")
    sms_records = collect_records(sms_results_root)
    sms_by_root = {record["root_id"]: record for record in sms_records}
    expected_sms = set(cadical["unknown_child_ids"])
    missing_sms = sorted(expected_sms - set(sms_by_root))
    unexpected_sms = sorted(set(sms_by_root) - expected_sms)
    if missing_sms or unexpected_sms:
        raise RuntimeError(
            f"SMS result mismatch: missing={missing_sms}, "
            f"unexpected={unexpected_sms}"
        )
    bad_sat = [
        record["task_id"]
        for record in sms_records
        if record["status"] == "SAT" and not record.get("verified")
    ]
    if bad_sat:
        raise RuntimeError(f"unverified SMS SAT: {bad_sat}")

    cadical_by_child = {
        record["root_id"]: record for record in cadical["results"]
    }
    final_by_child = {}
    for task in plan_record["cadical_tasks"]:
        child_id = task["root_id"]
        cadical_record = cadical_by_child[child_id]
        final_by_child[child_id] = (
            sms_by_root[child_id]
            if cadical_record["status"] == "UNKNOWN"
            else cadical_record
        )

    unit_by_parent: dict[str, list[dict]] = defaultdict(list)
    for item in plan_record["unit_closed_children"]:
        unit_by_parent[item["parent_root_id"]].append(item)
    task_by_parent: dict[str, list[dict]] = defaultdict(list)
    for task in plan_record["cadical_tasks"]:
        task_by_parent[task["parent_root_id"]].append(task)

    parent_records = {}
    newly_closed_parents = []
    open_children = []
    for parent_id in plan_record["v21_open_queue_ids"]:
        children = task_by_parent[parent_id]
        results = [final_by_child[child["root_id"]] for child in children]
        closed_children = len(unit_by_parent[parent_id]) + sum(
            result["status"] == "UNSAT" for result in results
        )
        unknown = [
            result for result in results if result["status"] == "UNKNOWN"
        ]
        verified_sat = [
            result
            for result in results
            if result["status"] == "SAT" and result.get("verified")
        ]
        parent_closed = not unknown and not verified_sat
        if parent_closed:
            newly_closed_parents.append(parent_id)
        for result in unknown:
            open_children.append(
                {
                    "child_id": result["root_id"],
                    "parent_root_id": parent_id,
                    "box": result["box"],
                    "cube_literals": result["cube_literals"],
                    "cube_depth": result["cube_depth"],
                    "cube_sha256": result["cube_sha256"],
                    "status": "UNKNOWN",
                }
            )
        parent_records[parent_id] = {
            "box": plan_record["trees"][parent_id]["box"],
            "parent_closed": parent_closed,
            "unit_closed_children": len(unit_by_parent[parent_id]),
            "solver_closed_children": sum(
                result["status"] == "UNSAT" for result in results
            ),
            "open_children": len(unknown),
            "verified_sat_children": len(verified_sat),
        }

    verified_sat = list(cadical["verified_sat_witnesses"]) + [
        record["task_id"]
        for record in sms_records
        if record["status"] == "SAT" and record.get("verified")
    ]
    closed_parent_count = (
        EXPECTED_V21_CLOSED + len(newly_closed_parents)
    )
    if verified_sat:
        conclusion = "SAT_K16_VERIFIED"
    elif not open_children:
        conclusion = "V22_TWO_TARGET_ROOTS_EXACTLY_EXCLUDED_K16_OPEN"
    else:
        conclusion = "V22_REFINEMENT_COMPLETE_K16_OPEN"

    record = {
        "schema": FINAL_LEDGER_SCHEMA,
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "workflow_run_id": workflow_run_id,
        "logical_conclusion": conclusion,
        "baseline": plan_record["baseline"],
        "refinement": {
            "parents_refined": len(plan_record["trees"]),
            "unit_closed_children": len(
                plan_record["unit_closed_children"]
            ),
            "solver_children": len(plan_record["cadical_tasks"]),
            "cadical_statuses": cadical["statuses"],
            "sms_statuses": dict(
                Counter(record["status"] for record in sms_records)
            ),
            "cadical_cpu_seconds": cadical["cpu_seconds"],
            "sms_cpu_seconds": round(
                sum(float(record["seconds"]) for record in sms_records),
                3,
            ),
        },
        "newly_closed_parent_ids": sorted(newly_closed_parents),
        "closed_parent_ids": sorted(
            set(plan_record["v21_closed_queue_ids"])
            | set(newly_closed_parents)
        ),
        "closed_parent_count": closed_parent_count,
        "open_parent_count": EXPECTED_FRONTIER - closed_parent_count,
        "open_child_leaves": sorted(
            open_children, key=lambda item: item["child_id"]
        ),
        "open_child_count": len(open_children),
        "parent_records": parent_records,
        "verified_sat_witnesses": verified_sat,
        "next_action": (
            "Reuse only open_child_leaves. UNKNOWN is not exclusion. "
            "Never resubmit a closed child or V21-closed parent."
        ),
        "cadical_results": cadical["results"],
        "sms_results": sorted(
            sms_records, key=lambda item: item["task_id"]
        ),
    }
    write_json(output, record)
    print(
        json.dumps(
            {
                "conclusion": conclusion,
                "newly_closed_parents": len(newly_closed_parents),
                "closed_parents": closed_parent_count,
                "remaining_parent_regions": (
                    EXPECTED_FRONTIER - closed_parent_count
                ),
                "open_refined_children": len(open_children),
                "verified_sat": len(verified_sat),
            },
            indent=2,
        ),
        flush=True,
    )
    return record


def main() -> None:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--plan", action="store_true")
    mode.add_argument("--solve", action="store_true")
    mode.add_argument("--select-sms", action="store_true")
    mode.add_argument("--aggregate", action="store_true")
    parser.add_argument("--v21-source", type=Path)
    parser.add_argument("--v21-ledger", type=Path)
    parser.add_argument("--v21-run-id", default="30353707059")
    parser.add_argument("--source", type=Path)
    parser.add_argument("--manifest", type=Path)
    parser.add_argument("--task-id")
    parser.add_argument("--cadical-results-root", type=Path)
    parser.add_argument("--cadical-ledger", type=Path)
    parser.add_argument("--sms-results-root", type=Path)
    parser.add_argument("--matrix-output", type=Path)
    parser.add_argument("--result", type=Path)
    parser.add_argument("--log", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--workflow-run-id")
    args = parser.parse_args()

    if args.plan:
        required = (
            args.v21_source,
            args.v21_ledger,
            args.output,
            args.matrix_output,
        )
        if any(value is None for value in required):
            parser.error(
                "--plan requires --v21-source --v21-ledger --output "
                "--matrix-output"
            )
        plan(
            v21_source=args.v21_source,
            v21_ledger_path=args.v21_ledger,
            output=args.output,
            matrix_output=args.matrix_output,
            v21_run_id=args.v21_run_id,
        )
    elif args.solve:
        required = (
            args.source,
            args.manifest,
            args.task_id,
            args.result,
            args.log,
        )
        if any(value is None for value in required):
            parser.error(
                "--solve requires --source --manifest --task-id --result "
                "--log"
            )
        solve(
            source=args.source,
            manifest_path=args.manifest,
            task_id=args.task_id,
            result_path=args.result,
            log_path=args.log,
        )
    elif args.select_sms:
        required = (
            args.source,
            args.cadical_results_root,
            args.output,
            args.matrix_output,
        )
        if any(value is None for value in required):
            parser.error(
                "--select-sms requires --source --cadical-results-root "
                "--output --matrix-output"
            )
        select_sms(
            source=args.source,
            cadical_results_root=args.cadical_results_root,
            output=args.output,
            matrix_output=args.matrix_output,
        )
    else:
        required = (
            args.source,
            args.cadical_ledger,
            args.sms_results_root,
            args.output,
        )
        if any(value is None for value in required):
            parser.error(
                "--aggregate requires --source --cadical-ledger "
                "--sms-results-root --output"
            )
        aggregate(
            source=args.source,
            cadical_ledger_path=args.cadical_ledger,
            sms_results_root=args.sms_results_root,
            output=args.output,
            workflow_run_id=args.workflow_run_id,
        )


if __name__ == "__main__":
    main()
