#!/usr/bin/env python3
"""Build and certify the complete V23--V24D terminal proof forest.

The final 676-leaf accounting is hierarchical.  V23 closed 581 original
partition leaves directly.  The remaining 95 leaves were refined by V24-B,
then the 23 surviving V24-B children were refined by V24-C, and the sole
surviving V24-C child was refined by V24-D.

This module reconstructs that complete forest and emits one independently
checkable DRAT/LRAT task for every exact terminal formula.  Unit-propagation
terminals are deliberately re-solved and certified too, so the publication
bundle has one uniform certificate interface.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import subprocess
import tempfile
import time
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path

from k16_smart_deepen import cube_hash, sha256, write_json
from k16_staged_cascade import write_assumption_cnf
from k16_v24e_proof_certificates import compress_file, run_logged


MODEL_VERSION = "k16-pisa-v24f-complete-drat-lrat-forest-20260731"
PLAN_SCHEMA = "k16-v24f-complete-certificate-plan-v1"
RESULT_SCHEMA = "k16-v24f-complete-certificate-result-v1"
WAVE_SCHEMA = "k16-v24f-certificate-wave-ledger-v1"
FINAL_SCHEMA = "k16-v24f-complete-certificate-ledger-v1"
PLAN_FILENAME = "v24f-certificate-manifest.json"
WAVE_COUNT = 6

RUNS = {
    "v23": "30417759253",
    "v24b": "30490334948",
    "v24c": "30587970184",
    "v24d": "30602758451",
}
COMMITS = {
    "v23": "d25d25169f216f36da9c12766493049d376eb0d7",
    "v24b": "1ef79e1343ee510247fbfae566741ced4a4acc60",
    "v24c": "be45be4731385dfc8d34fa718fccd98b141bc00b",
    "v24d": "7e639de2d6b68ec903e375c8f05dfa593b89f5d2",
}
DRAT_TRIM_COMMIT = "2e3b2dc0ecf938addbd779d42877b6ed69d9a985"
EXPECTED_BOXES = {
    "a0_z2",
    "a0_z3",
    "a0_z4p",
    "a1_z2",
    "a1_z4p",
    "a2p_z2",
    "a2p_z3",
}
EXPECTED_STAGE_COUNTS = {
    "v23": 581,
    "v24b": 353,
    "v24b_unit": 3,
    "v24c": 177,
    "v24c_unit": 2,
    "v24d": 8,
}


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def object_sha256(value: object) -> str:
    payload = json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def collect_records(root: Path, schema: str) -> list[dict]:
    records = []
    for path in sorted(root.rglob("*.json")):
        record = load_json(path)
        if record.get("schema") == schema:
            records.append(record)
    identifiers = [record["certificate_task_id"] for record in records]
    if len(identifiers) != len(set(identifiers)):
        raise RuntimeError(f"duplicate {schema} identifiers")
    return records


def final_v23_records(ledger: dict) -> dict[str, dict]:
    records: dict[str, dict] = {}
    for key in (
        "prior_final_results",
        "cleanup_cadical_results",
        "cleanup_sms_results",
    ):
        for record in ledger[key]:
            records[record["leaf_id"]] = record
    if len(records) != 676:
        raise RuntimeError(f"V23 final leaf count is {len(records)}, not 676")
    statuses = Counter(record["status"] for record in records.values())
    if statuses != {"UNSAT": 581, "UNKNOWN": 95}:
        raise RuntimeError(f"unexpected V23 statuses: {statuses}")
    return records


def final_solver_records(ledger: dict) -> dict[str, dict]:
    records = {
        record["root_id"]: record for record in ledger["cadical_results"]
    }
    for record in ledger["kissat_results"]:
        records[record["root_id"]] = record
    return records


def require_exact_unsat(record: dict, label: str) -> None:
    if (
        record.get("status") != "UNSAT"
        or record.get("timed_out")
        or not record.get("solver_level_exact")
    ):
        raise RuntimeError(f"{label} is not an exact historical UNSAT")


def assert_same_cube(left: dict, right: dict, label: str) -> None:
    for key in ("box", "cube_literals", "cube_depth", "cube_sha256"):
        if left.get(key) != right.get(key):
            raise RuntimeError(f"{label} cube mismatch in {key}")
    if cube_hash(left["cube_literals"]) != left["cube_sha256"]:
        raise RuntimeError(f"{label} has an invalid cube hash")


def audit_tree(tree: dict, parent: dict, label: str) -> list[dict]:
    """Independently audit a stored complete binary refinement tree."""
    nodes = {node["node_id"]: node for node in tree["nodes"]}
    if len(nodes) != len(tree["nodes"]):
        raise RuntimeError(f"{label} has duplicate node identifiers")
    root_candidates = [
        node
        for node in nodes.values()
        if node["cube_literals"] == parent["cube_literals"]
    ]
    if len(root_candidates) != 1:
        raise RuntimeError(f"{label} does not have one exact parent root")
    root = root_candidates[0]
    reachable: set[str] = set()
    terminals: list[dict] = []

    def visit(node_id: str) -> None:
        if node_id in reachable:
            raise RuntimeError(f"{label} tree is not a tree at {node_id}")
        if node_id not in nodes:
            raise RuntimeError(f"{label} references missing node {node_id}")
        reachable.add(node_id)
        node = nodes[node_id]
        if cube_hash(node["cube_literals"]) != cube_hash(
            list(node["cube_literals"])
        ):
            raise RuntimeError(f"{label} malformed cube at {node_id}")
        kind = node["kind"]
        if kind == "branch":
            variable = int(node["variable"])
            if variable <= 0:
                raise RuntimeError(f"{label} nonpositive branch variable")
            if variable in {abs(value) for value in node["cube_literals"]}:
                raise RuntimeError(f"{label} repeats a decided variable")
            expected = {
                node["zero_child"]: node["cube_literals"] + [-variable],
                node["one_child"]: node["cube_literals"] + [variable],
            }
            for child_id, child_cube in expected.items():
                if nodes.get(child_id, {}).get("cube_literals") != child_cube:
                    raise RuntimeError(
                        f"{label} child polarity mismatch at {child_id}"
                    )
                visit(child_id)
        elif kind in {"survivor", "unit_closed"}:
            terminals.append(node)
        else:
            raise RuntimeError(f"{label} has unknown node kind {kind}")

    visit(root["node_id"])
    if reachable != set(nodes):
        raise RuntimeError(f"{label} contains unreachable nodes")
    audit = tree.get("coverage_audit", {})
    if (
        not audit.get("complete_binary_branching")
        or int(audit.get("reachable_nodes", -1)) != len(reachable)
        or int(audit.get("terminal_nodes", -1)) != len(terminals)
        or audit.get("root_cube_sha256") != parent["cube_sha256"]
    ):
        raise RuntimeError(f"{label} stored coverage audit mismatch")
    return terminals


def proof_task(
    *,
    certificate_task_id: str,
    stage: str,
    box: str,
    cube_literals: list[int],
    lineage: dict,
    historical: dict | None,
    historical_method: str,
) -> dict:
    task = {
        "certificate_task_id": certificate_task_id,
        "stage": stage,
        "box": box,
        "cube_literals": list(cube_literals),
        "cube_depth": len(cube_literals),
        "cube_sha256": cube_hash(cube_literals),
        "lineage": lineage,
        "historical_method": historical_method,
        "historical_seconds": round(
            float(historical.get("seconds", 0.001))
            if historical
            else 0.001,
            3,
        ),
        "historical_result_task_id": (
            historical.get("task_id") if historical else None
        ),
    }
    if historical:
        if historical["cube_literals"] != task["cube_literals"]:
            raise RuntimeError(
                f"{certificate_task_id} historical cube mismatch"
            )
        require_exact_unsat(historical, certificate_task_id)
    return task


def materialized_hash(base: Path, cube: list[int], scratch: Path) -> str:
    write_assumption_cnf(base, scratch, cube)
    digest = sha256(scratch)
    scratch.unlink()
    return digest


def balance_waves(tasks: list[dict]) -> None:
    """Balanced deterministic round-robin with a hard <= 188 task cap."""
    ordered = sorted(
        tasks,
        key=lambda item: (
            -float(item["historical_seconds"]),
            item["certificate_task_id"],
        ),
    )
    totals = [0.0] * WAVE_COUNT
    counts = [0] * WAVE_COUNT
    for task in ordered:
        candidates = [
            index for index in range(WAVE_COUNT) if counts[index] < 188
        ]
        wave = min(candidates, key=lambda index: (totals[index], counts[index]))
        task["wave"] = wave + 1
        counts[wave] += 1
        totals[wave] += max(0.001, float(task["historical_seconds"]))
    if max(counts) > 188 or sum(counts) != len(tasks):
        raise RuntimeError("invalid V24-F wave allocation")


def select_pilot(tasks: list[dict]) -> list[dict]:
    selected: list[dict] = []
    by_stage: dict[str, list[dict]] = {}
    for task in tasks:
        by_stage.setdefault(task["stage"], []).append(task)
    for stage in ("v23", "v24b", "v24c"):
        ordered = sorted(
            by_stage[stage],
            key=lambda item: (
                float(item["historical_seconds"]),
                item["certificate_task_id"],
            ),
        )
        selected.append(ordered[0])
        selected.append(ordered[len(ordered) // 2])
    selected.append(sorted(by_stage["v24b_unit"], key=lambda x: x["certificate_task_id"])[0])
    selected.append(sorted(by_stage["v24d"], key=lambda x: x["historical_seconds"])[0])
    unique = {task["certificate_task_id"]: task for task in selected}
    return sorted(unique.values(), key=lambda item: item["certificate_task_id"])


def validate_sources(
    *,
    v23_ledger: dict,
    v24b_source: Path,
    v24b_ledger: dict,
    v24c_source: Path,
    v24c_ledger: dict,
    v24d_source: Path,
    v24d_ledger: dict,
) -> tuple[dict, dict, dict]:
    b = load_json(v24b_source / "v24b-manifest.json")
    c = load_json(v24c_source / "v24c-manifest.json")
    d = load_json(v24d_source / "v24d-manifest.json")
    expected = (
        (v23_ledger, "k16-v23-atlas-cleanup-ledger-v1"),
        (b, "k16-v24b-plan-v1"),
        (v24b_ledger, "k16-v24b-ledger-v1"),
        (c, "k16-v24c-plan-v1"),
        (v24c_ledger, "k16-v24c-ledger-v1"),
        (d, "k16-v24d-plan-v1"),
        (v24d_ledger, "k16-v24d-ledger-v1"),
    )
    for record, schema in expected:
        if record.get("schema") != schema:
            raise RuntimeError(f"unexpected schema, wanted {schema}")
    if not (
        b["coverage"]["all_tree_audits_passed"]
        and c["coverage"]["all_tree_audits_passed"]
        and d["coverage"]["all_tree_audits_passed"]
    ):
        raise RuntimeError("a historical refinement lacks a coverage audit")
    if v24d_ledger.get("logical_conclusion") != (
        "V24D_ALL_676_PARTITION_LEAVES_EXACTLY_CLOSED"
    ):
        raise RuntimeError("V24-D is not the closed 676/676 endpoint")
    return b, c, d


def plan_campaign(
    *,
    v23_ledger_path: Path,
    v24b_source: Path,
    v24b_ledger_path: Path,
    v24c_source: Path,
    v24c_ledger_path: Path,
    v24d_source: Path,
    v24d_ledger_path: Path,
    checker_root: Path,
    output: Path,
    matrix_path: Path,
    mode: str,
    wave: int,
) -> dict:
    v23_ledger = load_json(v23_ledger_path)
    v24b_ledger = load_json(v24b_ledger_path)
    v24c_ledger = load_json(v24c_ledger_path)
    v24d_ledger = load_json(v24d_ledger_path)
    b, c, d = validate_sources(
        v23_ledger=v23_ledger,
        v24b_source=v24b_source,
        v24b_ledger=v24b_ledger,
        v24c_source=v24c_source,
        v24c_ledger=v24c_ledger,
        v24d_source=v24d_source,
        v24d_ledger=v24d_ledger,
    )
    if b["source_hashes"]["v23_ledger"] != sha256(v23_ledger_path):
        raise RuntimeError("V24-B/V23 ledger hash mismatch")
    if c["source_hashes"]["v24b_ledger"] != sha256(v24b_ledger_path):
        raise RuntimeError("V24-C/V24-B ledger hash mismatch")
    if d["source_hashes"]["v24c_ledger"] != sha256(v24c_ledger_path):
        raise RuntimeError("V24-D/V24-C ledger hash mismatch")

    final23 = final_v23_records(v23_ledger)
    final_b = final_solver_records(v24b_ledger)
    final_c = final_solver_records(v24c_ledger)
    final_d = final_solver_records(v24d_ledger)
    if Counter(x["status"] for x in final_b.values()) != {
        "UNSAT": 353,
        "UNKNOWN": 23,
    }:
        raise RuntimeError("unexpected V24-B endpoint")
    if Counter(x["status"] for x in final_c.values()) != {
        "UNSAT": 177,
        "UNKNOWN": 1,
    }:
        raise RuntimeError("unexpected V24-C endpoint")
    if Counter(x["status"] for x in final_d.values()) != {"UNSAT": 8}:
        raise RuntimeError("unexpected V24-D endpoint")

    output.mkdir(parents=True, exist_ok=True)
    boxes_out = output / "boxes"
    boxes_out.mkdir(exist_ok=True)
    formula_hashes = {}
    for box in sorted(EXPECTED_BOXES):
        source = v24b_source / "boxes" / box / "enriched.cnf"
        partition = load_json(
            v24b_source / "boxes" / box / "partition-manifest.json"
        )
        expected_hash = partition["enriched_cnf"]["sha256"]
        if sha256(source) != expected_hash:
            raise RuntimeError(f"{box} theorem CNF hash mismatch")
        destination = boxes_out / box / "enriched.cnf"
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, destination)
        shutil.copy2(
            v24b_source / "boxes" / box / "partition-manifest.json",
            boxes_out / box / "partition-manifest.json",
        )
        formula_hashes[box] = expected_hash

    (output / "solver").mkdir(exist_ok=True)
    (output / "checker").mkdir(exist_ok=True)
    shutil.copy2(v24b_source / "cadical" / "cadical", output / "solver/cadical")
    for name in ("drat-trim", "lrat-check"):
        source = checker_root / name
        if not source.is_file():
            raise RuntimeError(f"missing proof checker {name}")
        shutil.copy2(source, output / "checker" / name)

    tasks: list[dict] = []
    v23_unknown = {
        leaf_id: record
        for leaf_id, record in final23.items()
        if record["status"] == "UNKNOWN"
    }
    for leaf_id, historical in sorted(final23.items()):
        if historical["status"] == "UNSAT":
            tasks.append(
                proof_task(
                    certificate_task_id=f"v23-{leaf_id}",
                    stage="v23",
                    box=historical["box"],
                    cube_literals=historical["cube_literals"],
                    lineage={"v23_source_leaf_id": leaf_id},
                    historical=historical,
                    historical_method=historical["method"],
                )
            )

    b_open = {item["leaf_id"]: item for item in b["v23_open_leaf_records"]}
    if set(b_open) != set(v23_unknown):
        raise RuntimeError("V24-B roots are not exactly the 95 V23 UNKNOWNs")
    b_tasks = {task["root_id"]: task for task in b["cadical_tasks"]}
    b_unknown_roots: set[str] = set()
    for leaf_id, parent in sorted(b_open.items()):
        assert_same_cube(parent, v23_unknown[leaf_id], f"V24-B root {leaf_id}")
        tree = b["trees"][leaf_id]
        terminals = audit_tree(tree, parent, f"V24-B {leaf_id}")
        for node in terminals:
            if node["kind"] == "unit_closed":
                tasks.append(
                    proof_task(
                        certificate_task_id=(
                            "v24b-unit-" + node["node_id"].replace(":", "-")
                        ),
                        stage="v24b_unit",
                        box=parent["box"],
                        cube_literals=node["cube_literals"],
                        lineage={
                            "v23_source_leaf_id": leaf_id,
                            "terminal_node_id": node["node_id"],
                        },
                        historical=None,
                        historical_method="unit_propagation",
                    )
                )
                continue
            matches = [
                task
                for task in b_tasks.values()
                if task["source_leaf_id"] == leaf_id
                and task["cube_literals"] == node["cube_literals"]
            ]
            if len(matches) != 1:
                raise RuntimeError(f"V24-B survivor lookup failed: {node['node_id']}")
            source_task = matches[0]
            historical = final_b[source_task["root_id"]]
            if historical["status"] == "UNSAT":
                tasks.append(
                    proof_task(
                        certificate_task_id=f"v24b-{source_task['root_id']}",
                        stage="v24b",
                        box=source_task["box"],
                        cube_literals=source_task["cube_literals"],
                        lineage={
                            "v23_source_leaf_id": leaf_id,
                            "v24b_root_id": source_task["root_id"],
                            "split_path": source_task["split_path"],
                        },
                        historical=historical,
                        historical_method=historical["method"],
                    )
                )
            elif historical["status"] == "UNKNOWN":
                b_unknown_roots.add(source_task["root_id"])
            else:
                raise RuntimeError("unexpected V24-B terminal status")

    c_open = {item["root_id"]: item for item in c["v24b_open_child_records"]}
    if set(c_open) != b_unknown_roots:
        raise RuntimeError("V24-C roots are not exactly the V24-B UNKNOWNs")
    c_tasks = {task["root_id"]: task for task in c["cadical_tasks"]}
    c_unknown_roots: set[str] = set()
    for b_root, parent in sorted(c_open.items()):
        assert_same_cube(parent, b_tasks[b_root], f"V24-C root {b_root}")
        source_ref = f"v24b-{b_root}"
        tree = c["trees"][source_ref]
        terminals = audit_tree(tree, parent, f"V24-C {source_ref}")
        for node in terminals:
            if node["kind"] == "unit_closed":
                tasks.append(
                    proof_task(
                        certificate_task_id=(
                            "v24c-unit-" + node["node_id"].replace(":", "-")
                        ),
                        stage="v24c_unit",
                        box=parent["box"],
                        cube_literals=node["cube_literals"],
                        lineage={
                            "v23_source_leaf_id": parent["source_leaf_id"],
                            "v24b_root_id": b_root,
                            "terminal_node_id": node["node_id"],
                        },
                        historical=None,
                        historical_method="unit_propagation",
                    )
                )
                continue
            matches = [
                task
                for task in c_tasks.values()
                if task["v24b_root_id"] == b_root
                and task["cube_literals"] == node["cube_literals"]
            ]
            if len(matches) != 1:
                raise RuntimeError(f"V24-C survivor lookup failed: {node['node_id']}")
            source_task = matches[0]
            historical = final_c[source_task["root_id"]]
            if historical["status"] == "UNSAT":
                tasks.append(
                    proof_task(
                        certificate_task_id=f"v24c-{source_task['root_id']}",
                        stage="v24c",
                        box=source_task["box"],
                        cube_literals=source_task["cube_literals"],
                        lineage={
                            "v23_source_leaf_id": source_task[
                                "v23_source_leaf_id"
                            ],
                            "v24b_root_id": b_root,
                            "v24c_root_id": source_task["root_id"],
                            "split_path": source_task["split_path"],
                        },
                        historical=historical,
                        historical_method=historical["method"],
                    )
                )
            elif historical["status"] == "UNKNOWN":
                c_unknown_roots.add(source_task["root_id"])
            else:
                raise RuntimeError("unexpected V24-C terminal status")

    inherited = d["v24c_open_terminal_record"]
    if c_unknown_roots != {inherited["root_id"]}:
        raise RuntimeError("V24-D root is not the sole V24-C UNKNOWN")
    assert_same_cube(
        inherited,
        c_tasks[inherited["root_id"]],
        "V24-D inherited root",
    )
    d_tasks = {task["root_id"]: task for task in d["cadical_tasks"]}
    terminals = audit_tree(d["tree"], inherited, "V24-D final tree")
    for node in terminals:
        matches = [
            task
            for task in d_tasks.values()
            if task["cube_literals"] == node["cube_literals"]
        ]
        if len(matches) != 1:
            raise RuntimeError(f"V24-D survivor lookup failed: {node['node_id']}")
        source_task = matches[0]
        historical = final_d[source_task["root_id"]]
        tasks.append(
            proof_task(
                certificate_task_id=f"v24d-{source_task['root_id']}",
                stage="v24d",
                box=source_task["box"],
                cube_literals=source_task["cube_literals"],
                lineage={
                    "v23_source_leaf_id": source_task["v23_source_leaf_id"],
                    "v24b_root_id": source_task["v24b_root_id"],
                    "v24c_root_id": inherited["root_id"],
                    "v24d_root_id": source_task["root_id"],
                    "split_path": source_task["split_path"],
                },
                historical=historical,
                historical_method=historical["method"],
            )
        )

    identifiers = [task["certificate_task_id"] for task in tasks]
    if len(identifiers) != len(set(identifiers)):
        raise RuntimeError("duplicate full-forest certificate task")
    stage_counts = Counter(task["stage"] for task in tasks)
    if stage_counts != EXPECTED_STAGE_COUNTS:
        raise RuntimeError(
            f"unexpected proof-forest terminal counts: {stage_counts}"
        )
    if len(tasks) != 1124:
        raise RuntimeError(f"expected 1124 terminal proofs, got {len(tasks)}")

    balance_waves(tasks)
    with tempfile.TemporaryDirectory(prefix="v24f-hash-") as temporary:
        scratch = Path(temporary) / "assumption.cnf"
        for task in tasks:
            task["assumption_cnf_sha256"] = materialized_hash(
                boxes_out / task["box"] / "enriched.cnf",
                task["cube_literals"],
                scratch,
            )

    tasks.sort(key=lambda item: item["certificate_task_id"])
    source_hashes = {
        "v23_ledger": sha256(v23_ledger_path),
        "v24b_ledger": sha256(v24b_ledger_path),
        "v24c_ledger": sha256(v24c_ledger_path),
        "v24d_ledger": sha256(v24d_ledger_path),
        "theorem_cnfs": formula_hashes,
        "cadical": sha256(output / "solver/cadical"),
        "drat_trim": sha256(output / "checker/drat-trim"),
        "lrat_check": sha256(output / "checker/lrat-check"),
    }
    coverage = {
        "original_partition_leaves": 676,
        "v23_direct_unsat_leaves": 581,
        "v23_refined_leaves": 95,
        "v24b_refined_unknown_children": 23,
        "v24c_refined_unknown_children": 1,
        "terminal_certificate_tasks": len(tasks),
        "all_historical_tree_audits_passed": True,
        "logical_endpoint": (
            "The terminal proof forest is exhaustive over all 676 "
            "original V23 partition leaves."
        ),
    }
    forest_sha256 = object_sha256(
        {
            "historical_runs": RUNS,
            "historical_commits": COMMITS,
            "source_hashes": source_hashes,
            "coverage": coverage,
            "certificate_tasks": tasks,
        }
    )
    plan = {
        "schema": PLAN_SCHEMA,
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "forest_sha256": forest_sha256,
        "historical_runs": RUNS,
        "historical_commits": COMMITS,
        "drat_trim_commit": DRAT_TRIM_COMMIT,
        "source_hashes": source_hashes,
        "coverage": coverage,
        "stage_counts": dict(stage_counts),
        "wave_count": WAVE_COUNT,
        "wave_counts": {
            str(value): sum(task["wave"] == value for task in tasks)
            for value in range(1, WAVE_COUNT + 1)
        },
        "wave_historical_seconds": {
            str(value): round(
                sum(
                    task["historical_seconds"]
                    for task in tasks
                    if task["wave"] == value
                ),
                3,
            )
            for value in range(1, WAVE_COUNT + 1)
        },
        "certificate_tasks": tasks,
    }
    write_json(output / PLAN_FILENAME, plan)

    if mode == "pilot":
        selected = select_pilot(tasks)
    else:
        if wave not in range(1, WAVE_COUNT + 1):
            raise RuntimeError(f"formal wave must be 1..{WAVE_COUNT}")
        selected = [task for task in tasks if task["wave"] == wave]
    matrix = {
        "include": [
            {
                "certificate_task_id": task["certificate_task_id"],
                "stage": task["stage"],
                "box": task["box"],
            }
            for task in selected
        ]
    }
    matrix_path.parent.mkdir(parents=True, exist_ok=True)
    matrix_path.write_text(
        json.dumps(matrix, separators=(",", ":")),
        encoding="utf-8",
    )
    print(
        json.dumps(
            {
                "mode": mode,
                "wave": wave if mode == "formal" else None,
                "selected_tasks": len(selected),
                "full_terminal_tasks": len(tasks),
                "stage_counts": dict(stage_counts),
                "wave_counts": plan["wave_counts"],
                "wave_historical_seconds": plan["wave_historical_seconds"],
            },
            indent=2,
        ),
        flush=True,
    )
    return plan


def certify_task(
    *,
    source: Path,
    certificate_task_id: str,
    output: Path,
) -> dict:
    plan = load_json(source / PLAN_FILENAME)
    matches = [
        task
        for task in plan["certificate_tasks"]
        if task["certificate_task_id"] == certificate_task_id
    ]
    if len(matches) != 1:
        raise RuntimeError(f"certificate task lookup failed: {certificate_task_id}")
    task = matches[0]
    base = source / "boxes" / task["box"] / "enriched.cnf"
    for path, expected in (
        (base, plan["source_hashes"]["theorem_cnfs"][task["box"]]),
        (source / "solver/cadical", plan["source_hashes"]["cadical"]),
        (source / "checker/drat-trim", plan["source_hashes"]["drat_trim"]),
        (source / "checker/lrat-check", plan["source_hashes"]["lrat_check"]),
    ):
        if sha256(path) != expected:
            raise RuntimeError(f"certificate source hash mismatch: {path}")

    output.mkdir(parents=True, exist_ok=True)
    logs = output / "logs"
    logs.mkdir(exist_ok=True)
    cnf = output / "assumption.cnf"
    proof = output / "proof.drat"
    lrat = output / "proof.lrat"
    write_assumption_cnf(base, cnf, task["cube_literals"])
    if sha256(cnf) != task["assumption_cnf_sha256"]:
        raise RuntimeError("materialized assumption CNF hash mismatch")

    cadical_rc, cadical_seconds = run_logged(
        [str(source / "solver/cadical"), str(cnf), str(proof)],
        logs / "cadical.log",
    )
    if cadical_rc != 20 or not proof.is_file() or not proof.stat().st_size:
        raise RuntimeError("CaDiCaL did not emit an UNSAT proof")
    drat_rc, drat_seconds = run_logged(
        [
            str(source / "checker/drat-trim"),
            str(cnf),
            str(proof),
            "-L",
            str(lrat),
        ],
        logs / "drat-trim.log",
    )
    drat_log = (logs / "drat-trim.log").read_text(
        encoding="utf-8", errors="replace"
    )
    if (
        drat_rc != 0
        or "VERIFIED" not in drat_log
        or not lrat.is_file()
        or not lrat.stat().st_size
    ):
        raise RuntimeError("DRAT proof failed independent verification")
    lrat_rc, lrat_seconds = run_logged(
        [str(source / "checker/lrat-check"), str(cnf), str(lrat)],
        logs / "lrat-check.log",
    )
    lrat_log = (logs / "lrat-check.log").read_text(
        encoding="utf-8", errors="replace"
    )
    if lrat_rc != 0 or "VERIFIED" not in lrat_log:
        raise RuntimeError("LRAT proof failed independent verification")

    proof_raw_hash = sha256(proof)
    lrat_raw_hash = sha256(lrat)
    proof_raw_bytes = proof.stat().st_size
    lrat_raw_bytes = lrat.stat().st_size
    proof_zst, proof_compress_seconds = compress_file(proof)
    lrat_zst, lrat_compress_seconds = compress_file(lrat)
    proof.unlink()
    lrat.unlink()
    cnf.unlink()

    result = {
        "schema": RESULT_SCHEMA,
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        **task,
        "status": "VERIFIED_UNSAT",
        "cadical": {
            "returncode": cadical_rc,
            "seconds": round(cadical_seconds, 3),
            "binary_sha256": plan["source_hashes"]["cadical"],
            "proof_format": "binary DRAT",
        },
        "drat_trim": {
            "returncode": drat_rc,
            "seconds": round(drat_seconds, 3),
            "verified": True,
            "commit": plan["drat_trim_commit"],
            "binary_sha256": plan["source_hashes"]["drat_trim"],
        },
        "lrat_check": {
            "returncode": lrat_rc,
            "seconds": round(lrat_seconds, 3),
            "verified": True,
            "commit": plan["drat_trim_commit"],
            "binary_sha256": plan["source_hashes"]["lrat_check"],
        },
        "certificates": {
            "drat": {
                "raw_sha256": proof_raw_hash,
                "raw_bytes": proof_raw_bytes,
                "compressed_file": proof_zst.name,
                "compressed_sha256": sha256(proof_zst),
                "compressed_bytes": proof_zst.stat().st_size,
                "compression_seconds": round(proof_compress_seconds, 3),
            },
            "lrat": {
                "raw_sha256": lrat_raw_hash,
                "raw_bytes": lrat_raw_bytes,
                "compressed_file": lrat_zst.name,
                "compressed_sha256": sha256(lrat_zst),
                "compressed_bytes": lrat_zst.stat().st_size,
                "compression_seconds": round(lrat_compress_seconds, 3),
            },
        },
    }
    write_json(output / "certificate-result.json", result)
    print(json.dumps(result, indent=2), flush=True)
    return result


def aggregate_wave(
    *,
    source: Path,
    results_root: Path,
    output: Path,
    mode: str,
    wave: int,
    workflow_run_id: str,
) -> dict:
    plan = load_json(source / PLAN_FILENAME)
    if mode == "pilot":
        expected_tasks = select_pilot(plan["certificate_tasks"])
    else:
        expected_tasks = [
            task for task in plan["certificate_tasks"] if task["wave"] == wave
        ]
    expected = {
        task["certificate_task_id"]: task for task in expected_tasks
    }
    records = collect_records(results_root, RESULT_SCHEMA)
    by_id = {record["certificate_task_id"]: record for record in records}
    if set(by_id) != set(expected):
        raise RuntimeError(
            "wave certificate mismatch: "
            f"missing={sorted(set(expected) - set(by_id))}, "
            f"unexpected={sorted(set(by_id) - set(expected))}"
        )
    for task_id, task in expected.items():
        record = by_id[task_id]
        if (
            record.get("status") != "VERIFIED_UNSAT"
            or not record.get("drat_trim", {}).get("verified")
            or not record.get("lrat_check", {}).get("verified")
        ):
            raise RuntimeError(f"unverified certificate: {task_id}")
        for key in (
            "stage",
            "box",
            "cube_sha256",
            "assumption_cnf_sha256",
        ):
            if record[key] != task[key]:
                raise RuntimeError(f"certificate provenance mismatch: {task_id}")
    ledger = {
        "schema": WAVE_SCHEMA,
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "workflow_run_id": workflow_run_id,
        "mode": mode,
        "wave": wave if mode == "formal" else None,
        "logical_conclusion": (
            "V24F_PILOT_CERTIFICATES_VERIFIED"
            if mode == "pilot"
            else f"V24F_WAVE_{wave}_CERTIFICATES_VERIFIED"
        ),
        "expected_count": len(expected),
        "certificate_count": len(records),
        "drat_verified": len(records),
        "lrat_verified": len(records),
        "statuses": dict(Counter(record["status"] for record in records)),
        "source_plan_sha256": sha256(source / PLAN_FILENAME),
        "forest_sha256": plan["forest_sha256"],
        "results": sorted(records, key=lambda item: item["certificate_task_id"]),
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    write_json(output, ledger)
    print(
        json.dumps(
            {
                "logical_conclusion": ledger["logical_conclusion"],
                "certificate_count": ledger["certificate_count"],
                "drat_verified": ledger["drat_verified"],
                "lrat_verified": ledger["lrat_verified"],
            },
            indent=2,
        ),
        flush=True,
    )
    return ledger


def aggregate_final(
    *,
    source: Path,
    wave_ledgers_root: Path,
    output: Path,
) -> dict:
    plan = load_json(source / PLAN_FILENAME)
    ledgers = []
    for path in sorted(wave_ledgers_root.rglob("*.json")):
        record = load_json(path)
        if record.get("schema") == WAVE_SCHEMA and record.get("mode") == "formal":
            ledgers.append(record)
    waves = [record["wave"] for record in ledgers]
    if sorted(waves) != list(range(1, WAVE_COUNT + 1)):
        raise RuntimeError(f"need exactly formal waves 1..{WAVE_COUNT}: {waves}")
    if {record.get("forest_sha256") for record in ledgers} != {
        plan["forest_sha256"]
    }:
        raise RuntimeError("formal waves do not share one frozen proof forest")
    records = [
        result for ledger in ledgers for result in ledger["results"]
    ]
    expected = {
        task["certificate_task_id"]: task
        for task in plan["certificate_tasks"]
    }
    by_id = {record["certificate_task_id"]: record for record in records}
    if len(by_id) != len(records) or set(by_id) != set(expected):
        raise RuntimeError("the six waves do not exactly cover the full forest")
    if not all(
        record["status"] == "VERIFIED_UNSAT"
        and record["drat_trim"]["verified"]
        and record["lrat_check"]["verified"]
        for record in records
    ):
        raise RuntimeError("the final forest contains an unverified result")
    ledger = {
        "schema": FINAL_SCHEMA,
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "logical_conclusion": (
            "V24F_COMPLETE_676_LEAF_TERMINAL_FOREST_CERTIFIED_UNSAT"
        ),
        "historical_runs": plan["historical_runs"],
        "historical_commits": plan["historical_commits"],
        "coverage": plan["coverage"],
        "wave_run_ids": {
            str(record["wave"]): record["workflow_run_id"]
            for record in ledgers
        },
        "terminal_certificate_count": len(records),
        "drat_verified": len(records),
        "lrat_verified": len(records),
        "stage_counts": dict(Counter(record["stage"] for record in records)),
        "source_hashes": plan["source_hashes"],
        "source_plan_sha256": sha256(source / PLAN_FILENAME),
        "forest_sha256": plan["forest_sha256"],
        "certificate_receipts": sorted(
            records, key=lambda item: item["certificate_task_id"]
        ),
        "claim_boundary": (
            "This ledger certifies every exact terminal formula in the "
            "audited refinement forest over all 676 original V23 partition "
            "leaves.  Correctness of the root CNF encoding and the seven-box "
            "mathematical partition is a separate model-audit obligation."
        ),
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    write_json(output, ledger)
    print(
        json.dumps(
            {
                "logical_conclusion": ledger["logical_conclusion"],
                "terminal_certificate_count": len(records),
                "stage_counts": ledger["stage_counts"],
                "wave_run_ids": ledger["wave_run_ids"],
            },
            indent=2,
        ),
        flush=True,
    )
    return ledger


def parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser()
    mode = p.add_mutually_exclusive_group(required=True)
    mode.add_argument("--plan", action="store_true")
    mode.add_argument("--certify", action="store_true")
    mode.add_argument("--aggregate-wave", action="store_true")
    mode.add_argument("--aggregate-final", action="store_true")
    p.add_argument("--v23-ledger", type=Path)
    p.add_argument("--v24b-source", type=Path)
    p.add_argument("--v24b-ledger", type=Path)
    p.add_argument("--v24c-source", type=Path)
    p.add_argument("--v24c-ledger", type=Path)
    p.add_argument("--v24d-source", type=Path)
    p.add_argument("--v24d-ledger", type=Path)
    p.add_argument("--checker-root", type=Path)
    p.add_argument("--source", type=Path)
    p.add_argument("--certificate-task-id")
    p.add_argument("--results-root", type=Path)
    p.add_argument("--wave-ledgers-root", type=Path)
    p.add_argument("--matrix", type=Path)
    p.add_argument("--mode", choices=("pilot", "formal"), default="pilot")
    p.add_argument("--wave", type=int, default=1)
    p.add_argument("--workflow-run-id")
    p.add_argument("--output", type=Path, required=True)
    return p


def main() -> None:
    args = parser().parse_args()
    if args.plan:
        plan_campaign(
            v23_ledger_path=args.v23_ledger,
            v24b_source=args.v24b_source,
            v24b_ledger_path=args.v24b_ledger,
            v24c_source=args.v24c_source,
            v24c_ledger_path=args.v24c_ledger,
            v24d_source=args.v24d_source,
            v24d_ledger_path=args.v24d_ledger,
            checker_root=args.checker_root,
            output=args.output,
            matrix_path=args.matrix,
            mode=args.mode,
            wave=args.wave,
        )
    elif args.certify:
        certify_task(
            source=args.source,
            certificate_task_id=args.certificate_task_id,
            output=args.output,
        )
    elif args.aggregate_wave:
        aggregate_wave(
            source=args.source,
            results_root=args.results_root,
            output=args.output,
            mode=args.mode,
            wave=args.wave,
            workflow_run_id=args.workflow_run_id,
        )
    else:
        aggregate_final(
            source=args.source,
            wave_ledgers_root=args.wave_ledgers_root,
            output=args.output,
        )


if __name__ == "__main__":
    main()
