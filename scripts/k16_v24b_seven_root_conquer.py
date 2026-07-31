#!/usr/bin/env python3
"""V24-B exact cube-and-conquer refinement of the 95 V23 UNKNOWN leaves.

The seven archived V22 lookahead partitions and the completed V23 ledger are
immutable inputs.  Every logical UNKNOWN leaf is replaced by a complete
two-level adaptive MOMS tree.  Both signs of every selected arc variable are
retained.  Surviving children receive CaDiCaL and, only on UNKNOWN, Kissat.
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
    Dimacs,
    cube_hash,
    read_cubes,
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


MODEL_VERSION = "k16-pisa-v24b-seven-root-cube-conquer-20260730"
PLAN_SCHEMA = "k16-v24b-plan-v1"
RESULT_SCHEMA = "k16-v24b-result-v1"
CADICAL_LEDGER_SCHEMA = "k16-v24b-cadical-ledger-v1"
FINAL_LEDGER_SCHEMA = "k16-v24b-ledger-v1"
V23_LEDGER_SCHEMA = "k16-v23-atlas-cleanup-ledger-v1"

TARGET_BOXES = (
    "a0_z2",
    "a0_z3",
    "a0_z4p",
    "a1_z2",
    "a1_z4p",
    "a2p_z2",
    "a2p_z3",
)
GROUPS = {
    "g1": ("a2p_z2", "a1_z2", "a0_z2"),
    "g2": ("a0_z3", "a0_z4p"),
    "g3": ("a1_z4p", "a2p_z3"),
}
BOX_TO_GROUP = {
    box: group for group, boxes in GROUPS.items() for box in boxes
}
EXPECTED_TOTAL_LEAVES = 676
EXPECTED_PRIOR_CLOSED = 581
EXPECTED_PRIOR_OPEN = 95
SPLIT_LEVELS = 2
CADICAL_SECONDS = 3600
KISSAT_SECONDS = 3600


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def parse_partition(value: str) -> tuple[str, Path]:
    box, separator, path = value.partition("=")
    if separator != "=" or box not in TARGET_BOXES:
        raise argparse.ArgumentTypeError(
            "--partition must be one of the seven BOX=PATH entries"
        )
    return box, Path(path)


def collect_records(root: Path) -> list[dict]:
    records = []
    for path in sorted(root.rglob("*.json")):
        record = load_json(path)
        if record.get("schema") == RESULT_SCHEMA:
            records.append(record)
    ids = [record["task_id"] for record in records]
    if len(ids) != len(set(ids)):
        raise RuntimeError("duplicate V24-B result identifiers")
    return records


def final_v23_results(ledger: dict) -> dict[str, dict]:
    final: dict[str, dict] = {}
    for record in ledger["prior_final_results"]:
        final[record["leaf_id"]] = record
    for record in ledger["cleanup_cadical_results"]:
        final[record["leaf_id"]] = record
    for record in ledger["cleanup_sms_results"]:
        final[record["leaf_id"]] = record
    if len(final) != EXPECTED_TOTAL_LEAVES:
        raise RuntimeError("V23 final result map does not contain 676 leaves")
    statuses = Counter(record["status"] for record in final.values())
    if dict(statuses) != ledger["statuses"]:
        raise RuntimeError("V23 final status reconstruction mismatch")
    return final


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


def validate_v23(ledger_path: Path) -> tuple[dict, dict[str, dict]]:
    ledger = load_json(ledger_path)
    if ledger.get("schema") != V23_LEDGER_SCHEMA:
        raise RuntimeError("unexpected V23 ledger schema")
    if ledger.get("logical_conclusion") != "V23_CLEANUP_COMPLETE_K16_OPEN":
        raise RuntimeError("V23 is not a completed open frontier")
    if ledger.get("verified_sat_witnesses"):
        raise RuntimeError("V23 already contains a verified SAT witness")
    if (
        int(ledger.get("total_partition_leaves", -1))
        != EXPECTED_TOTAL_LEAVES
        or int(ledger.get("exact_leaf_closures", -1))
        != EXPECTED_PRIOR_CLOSED
        or int(ledger.get("known_open_partition_leaves", -1))
        != EXPECTED_PRIOR_OPEN
        or ledger.get("statuses")
        != {"UNSAT": EXPECTED_PRIOR_CLOSED, "UNKNOWN": EXPECTED_PRIOR_OPEN}
    ):
        raise RuntimeError("unexpected V23 closure/open counts")
    if set(ledger.get("target_boxes", [])) != set(TARGET_BOXES):
        raise RuntimeError("unexpected V23 target boxes")
    return ledger, final_v23_results(ledger)


def plan_campaign(
    *,
    partitions: list[tuple[str, Path]],
    v23_ledger_path: Path,
    solver_source: Path,
    output: Path,
    matrix_dir: Path,
    v23_run_id: str,
    partition_run_id: str,
    solver_run_id: str,
) -> dict:
    ledger, final = validate_v23(v23_ledger_path)
    by_box = dict(partitions)
    if set(by_box) != set(TARGET_BOXES):
        raise RuntimeError("V24-B requires exactly seven partition artifacts")

    output.mkdir(parents=True, exist_ok=True)
    (output / "boxes").mkdir(parents=True, exist_ok=True)
    for solver in ("cadical", "kissat"):
        source_binary = solver_source / solver / solver
        if not source_binary.is_file():
            raise RuntimeError(f"missing audited solver binary: {solver}")
        (output / solver).mkdir(parents=True, exist_ok=True)
        shutil.copy2(source_binary, output / solver / solver)

    open_by_box: dict[str, list[dict]] = {}
    source_records: list[dict] = []
    partition_provenance = {}
    dimacs_by_box = {}
    for box in TARGET_BOXES:
        directory = by_box[box]
        manifest_path = directory / "manifest.json"
        manifest = load_json(manifest_path)
        if manifest.get("box") != box or not manifest.get("theorem_cuts"):
            raise RuntimeError(f"{box} partition provenance mismatch")
        partition = manifest.get("partitions", {}).get("lookahead")
        if not partition or not partition.get("generator_complete"):
            raise RuntimeError(f"{box} lacks a complete lookahead partition")
        if partition.get("coverage", {}).get("status") != "UNSAT":
            raise RuntimeError(f"{box} lacks exact partition coverage")
        cube_path = directory / partition["cube_file"]
        if sha256(cube_path) != partition["cube_sha256"]:
            raise RuntimeError(f"{box} cube hash mismatch")
        cubes = read_cubes(cube_path)
        if len(cubes) != int(partition["cubes"]):
            raise RuntimeError(f"{box} cube count mismatch")
        enriched = directory / "enriched.cnf"
        if sha256(enriched) != manifest["enriched_cnf"]["sha256"]:
            raise RuntimeError(f"{box} enriched CNF hash mismatch")
        destination = output / "boxes" / box
        destination.mkdir(parents=True, exist_ok=True)
        shutil.copy2(enriched, destination / "enriched.cnf")
        shutil.copy2(manifest_path, destination / "partition-manifest.json")

        box_results = sorted(
            (record for record in final.values() if record["box"] == box),
            key=lambda item: int(item["cube_line"]),
        )
        if len(box_results) != int(ledger["per_box"][box]["partition_cubes"]):
            raise RuntimeError(f"{box} final-result count mismatch")
        for record in box_results:
            line = int(record["cube_line"])
            cube = cubes[line - 1]
            if (
                cube != record["cube_literals"]
                or cube_hash(cube) != record["cube_sha256"]
            ):
                raise RuntimeError(f"{box} signed leaf mismatch at line {line}")
        open_records = [
            record for record in box_results if record["status"] == "UNKNOWN"
        ]
        if len(open_records) != int(ledger["per_box"][box]["unknown_leaves"]):
            raise RuntimeError(f"{box} UNKNOWN count mismatch")
        open_by_box[box] = open_records
        source_records.extend(open_records)
        dimacs_by_box[box] = Dimacs(destination / "enriched.cnf")
        partition_provenance[box] = {
            "manifest_sha256": sha256(manifest_path),
            "enriched_cnf_sha256": sha256(enriched),
            "cube_file_sha256": sha256(cube_path),
            "partition_cubes": len(cubes),
            "prior_exact_closures": int(
                ledger["per_box"][box]["exact_leaf_closures"]
            ),
            "prior_unknown_leaves": len(open_records),
            "coverage": partition["coverage"],
        }

    if len(source_records) != EXPECTED_PRIOR_OPEN:
        raise RuntimeError("V24-B did not recover exactly 95 open leaves")

    trees: dict[str, dict] = {}
    survivors: list[dict] = []
    unit_closed: list[dict] = []
    for source in sorted(source_records, key=lambda item: item["leaf_id"]):
        leaf_id = source["leaf_id"]
        box = source["box"]
        nodes: list[dict] = []
        children: list[dict] = []
        closed: list[dict] = []
        expand_tree(
            dimacs=dimacs_by_box[box],
            source_leaf_id=leaf_id,
            assumptions=list(source["cube_literals"]),
            levels=SPLIT_LEVELS,
            path_bits="",
            nodes=nodes,
            survivors=children,
            unit_closed=closed,
        )
        for child in children:
            child["box"] = box
            child["group"] = BOX_TO_GROUP[box]
            survivors.append(child)
        for child in closed:
            child["box"] = box
            child["group"] = BOX_TO_GROUP[box]
            unit_closed.append(child)
        tree = {
            "source_leaf_id": leaf_id,
            "box": box,
            "group": BOX_TO_GROUP[box],
            "source_cube_line": int(source["cube_line"]),
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
        trees[leaf_id] = tree

    tasks = []
    for index, child in enumerate(
        sorted(
            survivors,
            key=lambda item: (item["source_leaf_id"], item["path_bits"]),
        ),
        start=1,
    ):
        root_id = f"b{index:04d}"
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
                "source_leaf_id": child["source_leaf_id"],
                "split_path": child["path_bits"],
                "cube_literals": child["cube_literals"],
                "cube_depth": child["cube_depth"],
                "cube_sha256": child["cube_sha256"],
            }
        )

    if len(trees) != EXPECTED_PRIOR_OPEN:
        raise RuntimeError("not every V23 UNKNOWN leaf was refined")
    if len(tasks) + len(unit_closed) > (
        EXPECTED_PRIOR_OPEN * (1 << SPLIT_LEVELS)
    ):
        raise RuntimeError("V24-B emitted too many terminal children")

    record = {
        "schema": PLAN_SCHEMA,
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "source_runs": {
            "v23": v23_run_id,
            "partitions": partition_run_id,
            "solvers": solver_run_id,
        },
        "source_hashes": {
            "v23_ledger": sha256(v23_ledger_path),
            "cadical": sha256(output / "cadical" / "cadical"),
            "kissat": sha256(output / "kissat" / "kissat"),
        },
        "baseline": {
            "partition_leaves": EXPECTED_TOTAL_LEAVES,
            "prior_exact_closures": EXPECTED_PRIOR_CLOSED,
            "prior_unknown_leaves": EXPECTED_PRIOR_OPEN,
        },
        "groups": {
            group: {
                "boxes": list(boxes),
                "source_unknown_leaves": sum(
                    len(open_by_box[box]) for box in boxes
                ),
            }
            for group, boxes in GROUPS.items()
        },
        "partition_provenance": partition_provenance,
        "split_policy": {
            "levels": SPLIT_LEVELS,
            "maximum_children_per_leaf": 1 << SPLIT_LEVELS,
            "rule": (
                "adaptive MOMS after unit propagation; both polarities are "
                "retained at every internal node"
            ),
        },
        "v23_open_leaf_records": sorted(
            source_records, key=lambda item: item["leaf_id"]
        ),
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
                "Every one of the 95 final V23 UNKNOWN leaves is exactly "
                "replaced by a complete two-level binary decision tree."
            ),
        },
    }
    write_json(output / "v24b-manifest.json", record)
    write_group_matrices(matrix_dir, "cadical", tasks)
    print(
        json.dumps(
            {
                "source_open_leaves": len(trees),
                "unit_closed_children": len(unit_closed),
                "queued_children": len(tasks),
                "by_group": dict(Counter(t["group"] for t in tasks)),
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
) -> dict:
    manifest = load_json(manifest_path)
    tasks = manifest.get("cadical_tasks", []) + manifest.get(
        "kissat_tasks", []
    )
    matches = [task for task in tasks if task["task_id"] == task_id]
    if len(matches) != 1:
        raise RuntimeError(f"task lookup failed: {task_id}")
    task = matches[0]
    seconds = int(task["seconds"])
    solver = task["solver"]
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
        "task_id": task_id,
        "stage": task["stage"],
        "method": task["method"],
        "solver": solver,
        "group": task["group"],
        "box": task["box"],
        "root_id": task["root_id"],
        "source_leaf_id": task["source_leaf_id"],
        "split_path": task["split_path"],
        "cube_literals": task["cube_literals"],
        "cube_depth": task["cube_depth"],
        "cube_sha256": task["cube_sha256"],
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
    plan = load_json(source / "v24b-manifest.json")
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
    tasks = []
    for record in unknown:
        parent = parent_by_root[record["root_id"]]
        tasks.append(
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
    write_json(
        output / "v24b-kissat-manifest.json",
        {
            "schema": PLAN_SCHEMA,
            "model_version": MODEL_VERSION,
            "created_utc": utc_now(),
            "cadical_tasks": [],
            "kissat_tasks": tasks,
            "coverage": (
                "Kissat receives exactly CaDiCaL UNKNOWN children. Exact "
                "closures and verified SAT children are never resubmitted."
            ),
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
        "cpu_seconds": round(sum(float(r["seconds"]) for r in records), 3),
        "results": sorted(records, key=lambda item: item["task_id"]),
    }
    write_json(output / "v24b-cadical-ledger.json", ledger)
    write_group_matrices(matrix_dir, "kissat", tasks)
    print(
        json.dumps(
            {
                "cadical_statuses": ledger["statuses"],
                "kissat_tasks": len(tasks),
                "kissat_by_group": dict(Counter(t["group"] for t in tasks)),
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
    plan = load_json(source / "v24b-manifest.json")
    cadical = load_json(cadical_ledger_path)
    if cadical.get("schema") != CADICAL_LEDGER_SCHEMA:
        raise RuntimeError("unexpected V24-B CaDiCaL ledger")
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
    for source_leaf in plan["v23_open_leaf_records"]:
        leaf_id = source_leaf["leaf_id"]
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
                    "group": result["group"],
                    "box": result["box"],
                    "split_path": result["split_path"],
                    "cube_literals": result["cube_literals"],
                    "cube_depth": result["cube_depth"],
                    "cube_sha256": result["cube_sha256"],
                    "status": "UNKNOWN",
                }
            )
        leaf_records[leaf_id] = {
            "box": source_leaf["box"],
            "source_leaf_closed": not unknown and not sat,
            "unit_closed_children": len(unit_by_leaf[leaf_id]),
            "solver_closed_children": sum(
                r["status"] == "UNSAT" for r in results
            ),
            "open_children": len(unknown),
            "verified_sat_children": len(sat),
        }

    closed_set = set(closed_source_leaves)
    per_box = {}
    roots_closed = []
    for box in TARGET_BOXES:
        source_ids = [
            r["leaf_id"]
            for r in plan["v23_open_leaf_records"]
            if r["box"] == box
        ]
        newly_closed = sum(leaf_id in closed_set for leaf_id in source_ids)
        prior = int(
            plan["partition_provenance"][box]["prior_exact_closures"]
        )
        total = int(plan["partition_provenance"][box]["partition_cubes"])
        exact = prior + newly_closed
        root_closed = exact == total
        if root_closed:
            roots_closed.append(box)
        per_box[box] = {
            "partition_cubes": total,
            "prior_exact_closures": prior,
            "newly_closed_source_leaves": newly_closed,
            "exact_leaf_closures": exact,
            "open_source_leaves": len(source_ids) - newly_closed,
            "open_child_leaves": sum(
                child["box"] == box for child in open_children
            ),
            "root_exactly_excluded": root_closed,
        }

    total_exact = EXPECTED_PRIOR_CLOSED + len(closed_source_leaves)
    conclusion = (
        "V24B_VERIFIED_SAT"
        if verified_sat
        else (
            "V24B_SEVEN_ROOTS_EXACTLY_CLOSED"
            if total_exact == EXPECTED_TOTAL_LEAVES
            else "V24B_CUBE_CONQUER_COMPLETE_K16_OPEN"
        )
    )
    record = {
        "schema": FINAL_LEDGER_SCHEMA,
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "workflow_run_id": workflow_run_id,
        "source_runs": plan["source_runs"],
        "logical_conclusion": conclusion,
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
            EXPECTED_PRIOR_OPEN - len(closed_source_leaves)
        ),
        "exact_partition_leaf_closures": total_exact,
        "open_partition_source_leaves": (
            EXPECTED_TOTAL_LEAVES - total_exact
        ),
        "roots_exactly_excluded": roots_closed,
        "per_box": per_box,
        "open_child_leaves": sorted(
            open_children, key=lambda item: item["root_id"]
        ),
        "open_child_count": len(open_children),
        "leaf_records": leaf_records,
        "verified_sat_witnesses": verified_sat,
        "coverage_audit": plan["coverage"],
        "next_action": (
            "Reuse only open_child_leaves. UNKNOWN is not exclusion. "
            "Never resubmit a V23/V24-B closed leaf."
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
                "logical_conclusion": conclusion,
                "newly_closed_v23_leaves": len(closed_source_leaves),
                "exact_partition_closures": total_exact,
                "remaining_v24b_children": len(open_children),
                "roots_exactly_excluded": roots_closed,
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
    p.add_argument("--partition", action="append", type=parse_partition)
    p.add_argument("--v23-ledger", type=Path)
    p.add_argument("--solver-source", type=Path)
    p.add_argument("--v23-run-id")
    p.add_argument("--partition-run-id")
    p.add_argument("--solver-run-id")
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
            partitions=args.partition,
            v23_ledger_path=args.v23_ledger,
            solver_source=args.solver_source,
            output=args.output,
            matrix_dir=args.matrix_dir,
            v23_run_id=args.v23_run_id,
            partition_run_id=args.partition_run_id,
            solver_run_id=args.solver_run_id,
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
