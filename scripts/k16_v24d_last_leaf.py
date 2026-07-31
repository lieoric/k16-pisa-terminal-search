#!/usr/bin/env python3
"""V24-D exact eight-way refinement of the sole V24-C UNKNOWN leaf."""

from __future__ import annotations

import argparse
import json
import shutil
import sys
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = REPO_ROOT / "scripts"
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from k16_smart_deepen import Dimacs, cube_hash, sha256, write_json  # noqa: E402
from k16_v24a_cube_conquer import audit_tree, expand_tree  # noqa: E402
import k16_v24c_last23_conquer as runtime  # noqa: E402


MODEL_VERSION = "k16-pisa-v24d-last-leaf-eight-way-20260731"
PLAN_SCHEMA = "k16-v24d-plan-v1"
RESULT_SCHEMA = "k16-v24d-result-v1"
CADICAL_LEDGER_SCHEMA = "k16-v24d-cadical-ledger-v1"
FINAL_LEDGER_SCHEMA = "k16-v24d-ledger-v1"
V24C_PLAN_SCHEMA = "k16-v24c-plan-v1"
V24C_LEDGER_SCHEMA = "k16-v24c-ledger-v1"
PLAN_FILENAME = "v24d-manifest.json"
KISSAT_MANIFEST_FILENAME = "v24d-kissat-manifest.json"
CADICAL_LEDGER_FILENAME = "v24d-cadical-ledger.json"
BOX = "a0_z4p"
GROUP = "g1"
EXPECTED_TOTAL = 676
EXPECTED_PRIOR_EXACT = 675
EXPECTED_OPEN_SOURCE = "a0_z4p-c000081"
EXPECTED_OPEN_V24B_ROOT = "b0184"
EXPECTED_OPEN_V24C_ROOT = "c0138"
SPLIT_LEVELS = 3
CADICAL_SECONDS = 3600
KISSAT_SECONDS = 3600

# Reuse the already exercised exact solver/select implementation with V24-D
# provenance and filenames. These values are resolved by the runtime functions
# when they are called, not when the module is imported.
runtime.MODEL_VERSION = MODEL_VERSION
runtime.PLAN_SCHEMA = PLAN_SCHEMA
runtime.RESULT_SCHEMA = RESULT_SCHEMA
runtime.CADICAL_LEDGER_SCHEMA = CADICAL_LEDGER_SCHEMA
runtime.GROUPS = {GROUP: (BOX,)}
runtime.PLAN_FILENAME = PLAN_FILENAME
runtime.KISSAT_MANIFEST_FILENAME = KISSAT_MANIFEST_FILENAME
runtime.CADICAL_LEDGER_FILENAME = CADICAL_LEDGER_FILENAME
runtime.CADICAL_SECONDS = CADICAL_SECONDS
runtime.KISSAT_SECONDS = KISSAT_SECONDS


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def validate_prior(
    source: Path,
    ledger_path: Path,
) -> tuple[dict, dict, dict]:
    ledger = load_json(ledger_path)
    if ledger.get("schema") != V24C_LEDGER_SCHEMA:
        raise RuntimeError("unexpected V24-C ledger schema")
    if ledger.get("logical_conclusion") != (
        "V24C_LAST23_REFINEMENT_COMPLETE_K16_OPEN"
    ):
        raise RuntimeError("V24-C is not the completed open frontier")
    if ledger.get("verified_sat_witnesses"):
        raise RuntimeError("V24-C already contains a verified SAT witness")
    if (
        int(ledger.get("exact_partition_leaf_closures", -1))
        != EXPECTED_PRIOR_EXACT
        or int(ledger.get("open_partition_source_leaves", -1)) != 1
        or int(ledger.get("open_terminal_count", -1)) != 1
        or len(ledger.get("roots_exactly_excluded", [])) != 6
    ):
        raise RuntimeError("unexpected V24-C endpoint counts")

    plan = load_json(source / "v24c-manifest.json")
    if plan.get("schema") != V24C_PLAN_SCHEMA:
        raise RuntimeError("unexpected V24-C source manifest")
    if not plan.get("coverage", {}).get("all_tree_audits_passed"):
        raise RuntimeError("V24-C coverage was not audited")
    for solver in ("cadical", "kissat"):
        binary = source / solver / solver
        if (
            not binary.is_file()
            or sha256(binary) != plan["source_hashes"][solver]
        ):
            raise RuntimeError(f"V24-C {solver} binary mismatch")

    child = ledger["open_terminal_leaves"][0]
    if (
        child["root_id"] != EXPECTED_OPEN_V24C_ROOT
        or child["v24b_root_id"] != EXPECTED_OPEN_V24B_ROOT
        or child["v23_source_leaf_id"] != EXPECTED_OPEN_SOURCE
        or child["box"] != BOX
        or cube_hash(child["cube_literals"]) != child["cube_sha256"]
    ):
        raise RuntimeError("unexpected final V24-C signed leaf")

    task = next(
        (
            candidate
            for candidate in plan["cadical_tasks"]
            if candidate["root_id"] == child["root_id"]
        ),
        None,
    )
    final = {
        result["root_id"]: result for result in ledger["cadical_results"]
    }
    for result in ledger["kissat_results"]:
        final[result["root_id"]] = result
    result = final.get(child["root_id"])
    if task is None or result is None or result["status"] != "UNKNOWN":
        raise RuntimeError("V24-C final leaf is not a solver UNKNOWN")
    for key in (
        "box",
        "v24b_root_id",
        "v23_source_leaf_id",
        "cube_literals",
        "cube_depth",
        "cube_sha256",
    ):
        if task[key] != child[key]:
            raise RuntimeError(f"V24-C leaf/plan mismatch: {key}")
    return ledger, plan, child


def plan_campaign(
    *,
    v24c_source: Path,
    v24c_ledger_path: Path,
    output: Path,
    matrix_dir: Path,
    v24c_run_id: str,
) -> dict:
    ledger, prior_plan, source = validate_prior(
        v24c_source,
        v24c_ledger_path,
    )
    output.mkdir(parents=True, exist_ok=True)
    for solver in ("cadical", "kissat"):
        (output / solver).mkdir(parents=True, exist_ok=True)
        shutil.copy2(
            v24c_source / solver / solver,
            output / solver / solver,
        )
    destination = output / "boxes" / BOX
    destination.mkdir(parents=True, exist_ok=True)
    source_cnf = v24c_source / "boxes" / BOX / "enriched.cnf"
    expected_cnf = prior_plan["source_hashes"]["theorem_cnf"][BOX]
    if sha256(source_cnf) != expected_cnf:
        raise RuntimeError("V24-C final theorem CNF mismatch")
    shutil.copy2(source_cnf, destination / "enriched.cnf")
    shutil.copy2(
        v24c_source / "boxes" / BOX / "partition-manifest.json",
        destination / "partition-manifest.json",
    )

    source_ref = f"v24c-{source['root_id']}"
    nodes: list[dict] = []
    survivors: list[dict] = []
    unit_closed: list[dict] = []
    expand_tree(
        dimacs=Dimacs(destination / "enriched.cnf"),
        source_leaf_id=source_ref,
        assumptions=list(source["cube_literals"]),
        levels=SPLIT_LEVELS,
        path_bits="",
        nodes=nodes,
        survivors=survivors,
        unit_closed=unit_closed,
    )
    tree = {
        "source_ref_id": source_ref,
        "source_leaf_id": source_ref,
        "v24c_root_id": source["root_id"],
        "v24b_root_id": source["v24b_root_id"],
        "v23_source_leaf_id": source["v23_source_leaf_id"],
        "box": BOX,
        "group": GROUP,
        "parent_split_path": source["split_path"],
        "parent_cube_literals": list(source["cube_literals"]),
        "parent_cube_depth": int(source["cube_depth"]),
        "parent_cube_sha256": source["cube_sha256"],
        "split_levels": SPLIT_LEVELS,
        "nodes": nodes,
        "surviving_children": len(survivors),
        "unit_closed_children": len(unit_closed),
    }
    tree["coverage_audit"] = audit_tree(
        tree,
        source["cube_literals"],
        split_levels=SPLIT_LEVELS,
    )

    for child in survivors:
        child.update(
            source_ref_id=source_ref,
            v24b_root_id=source["v24b_root_id"],
            v23_source_leaf_id=source["v23_source_leaf_id"],
            parent_split_path=source["split_path"],
            box=BOX,
            group=GROUP,
        )
    for child in unit_closed:
        child.update(
            source_ref_id=source_ref,
            v24b_root_id=source["v24b_root_id"],
            v23_source_leaf_id=source["v23_source_leaf_id"],
            parent_split_path=source["split_path"],
            box=BOX,
            group=GROUP,
        )

    tasks = []
    for index, child in enumerate(
        sorted(survivors, key=lambda item: item["path_bits"]),
        start=1,
    ):
        root_id = f"d{index:02d}"
        tasks.append(
            {
                "task_id": f"cadical{CADICAL_SECONDS}-{root_id}",
                "stage": "cadical",
                "method": f"cadical{CADICAL_SECONDS}",
                "solver": "cadical",
                "seconds": CADICAL_SECONDS,
                "group": GROUP,
                "box": BOX,
                "root_id": root_id,
                "source_ref_id": source_ref,
                "v24b_root_id": source["v24b_root_id"],
                "v23_source_leaf_id": source["v23_source_leaf_id"],
                "parent_split_path": source["split_path"],
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
        "source_run": v24c_run_id,
        "source_hashes": {
            "v24c_ledger": sha256(v24c_ledger_path),
            "cadical": sha256(output / "cadical" / "cadical"),
            "kissat": sha256(output / "kissat" / "kissat"),
            "theorem_cnf": {BOX: expected_cnf},
        },
        "baseline": {
            "total_partition_leaves": EXPECTED_TOTAL,
            "prior_exact_partition_leaves": EXPECTED_PRIOR_EXACT,
            "open_v23_source_leaf": EXPECTED_OPEN_SOURCE,
            "open_v24b_child": EXPECTED_OPEN_V24B_ROOT,
            "open_v24c_child": EXPECTED_OPEN_V24C_ROOT,
            "prior_roots_exactly_excluded": ledger[
                "roots_exactly_excluded"
            ],
        },
        "prior_per_box": ledger["per_box"],
        "v24c_open_terminal_record": source,
        "tree": tree,
        "unit_closed_children": unit_closed,
        "cadical_tasks": tasks,
        "coverage": {
            "source_children_refined": 1,
            "all_tree_audits_passed": tree["coverage_audit"][
                "complete_binary_branching"
            ],
            "statement": (
                "The sole final V24-C UNKNOWN is exactly replaced by a "
                "complete three-level (eight-way) binary tree."
            ),
        },
    }
    write_json(output / PLAN_FILENAME, record)
    runtime.write_group_matrices(matrix_dir, "cadical", tasks)
    print(
        json.dumps(
            {
                "source_terminal_children": 1,
                "unit_closed_children": len(unit_closed),
                "queued_children": len(tasks),
                "coverage_audit": record["coverage"],
            },
            indent=2,
        ),
        flush=True,
    )
    return record


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
        raise RuntimeError("unexpected V24-D CaDiCaL ledger")
    kissat_records = runtime.collect_records(kissat_results_root)
    kissat_by_root = {
        result["root_id"]: result for result in kissat_records
    }
    expected_kissat = set(cadical["unknown_root_ids"])
    if (
        set(kissat_by_root) != expected_kissat
        or any(
            result["status"] == "SAT" and not result.get("verified")
            for result in kissat_records
        )
    ):
        raise RuntimeError("V24-D Kissat result set is not auditable")

    cadical_by_root = {
        result["root_id"]: result for result in cadical["results"]
    }
    final_results = []
    for task in plan["cadical_tasks"]:
        first = cadical_by_root[task["root_id"]]
        final_results.append(
            kissat_by_root[task["root_id"]]
            if first["status"] == "UNKNOWN"
            else first
        )
    unknown = [
        result for result in final_results if result["status"] == "UNKNOWN"
    ]
    verified_sat = [
        result
        for result in final_results
        if result["status"] == "SAT" and result.get("verified")
    ]
    final_leaf_closed = not unknown and not verified_sat
    total_exact = EXPECTED_PRIOR_EXACT + int(final_leaf_closed)

    open_terminals = [
        {
            "root_id": result["root_id"],
            "source_ref_id": result["source_ref_id"],
            "v24c_root_id": EXPECTED_OPEN_V24C_ROOT,
            "v24b_root_id": result["v24b_root_id"],
            "v23_source_leaf_id": result["v23_source_leaf_id"],
            "box": result["box"],
            "parent_split_path": result["parent_split_path"],
            "split_path": result["split_path"],
            "cube_literals": result["cube_literals"],
            "cube_depth": result["cube_depth"],
            "cube_sha256": result["cube_sha256"],
            "status": "UNKNOWN",
        }
        for result in unknown
    ]

    per_box = {}
    roots = []
    for box, prior in plan["prior_per_box"].items():
        added = int(final_leaf_closed and box == BOX)
        exact = int(prior["exact_leaf_closures"]) + added
        total = int(prior["partition_cubes"])
        closed = exact == total
        if closed:
            roots.append(box)
        per_box[box] = {
            "partition_cubes": total,
            "prior_exact_closures": int(prior["exact_leaf_closures"]),
            "newly_closed_partition_leaves": added,
            "exact_leaf_closures": exact,
            "open_partition_leaves": total - exact,
            "open_terminal_child_leaves": sum(
                child["box"] == box for child in open_terminals
            ),
            "root_exactly_excluded": closed,
        }

    conclusion = (
        "V24D_VERIFIED_SAT"
        if verified_sat
        else (
            "V24D_ALL_676_PARTITION_LEAVES_EXACTLY_CLOSED"
            if total_exact == EXPECTED_TOTAL
            else "V24D_EIGHT_WAY_COMPLETE_K16_OPEN"
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
            "unit_closed_children": len(plan["unit_closed_children"]),
            "solver_children": len(plan["cadical_tasks"]),
            "cadical_statuses": cadical["statuses"],
            "kissat_statuses": dict(
                Counter(result["status"] for result in kissat_records)
            ),
            "cadical_cpu_seconds": cadical["cpu_seconds"],
            "kissat_cpu_seconds": round(
                sum(float(result["seconds"]) for result in kissat_records),
                3,
            ),
        },
        "final_v24c_leaf_closed": final_leaf_closed,
        "exact_partition_leaf_closures": total_exact,
        "open_partition_source_leaves": EXPECTED_TOTAL - total_exact,
        "roots_exactly_excluded": sorted(roots),
        "per_box": per_box,
        "open_terminal_leaves": open_terminals,
        "open_terminal_count": len(open_terminals),
        "verified_sat_witnesses": verified_sat,
        "coverage_audit": plan["coverage"],
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
                "final_v24c_leaf_closed": final_leaf_closed,
                "exact_partition_closures": total_exact,
                "remaining_terminal_children": len(open_terminals),
                "roots_exactly_excluded": sorted(roots),
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
    p.add_argument("--v24c-source", type=Path)
    p.add_argument("--v24c-ledger", type=Path)
    p.add_argument("--v24c-run-id")
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
            v24c_source=args.v24c_source,
            v24c_ledger_path=args.v24c_ledger,
            output=args.output,
            matrix_dir=args.matrix_dir,
            v24c_run_id=args.v24c_run_id,
        )
    elif args.solve:
        runtime.solve_task(
            source=args.source,
            manifest_path=args.manifest,
            task_id=args.task_id,
            result_path=args.result,
            log_path=args.log,
        )
    elif args.select_kissat:
        runtime.select_kissat(
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
