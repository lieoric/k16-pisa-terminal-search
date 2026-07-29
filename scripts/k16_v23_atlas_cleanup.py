#!/usr/bin/env python3
"""Exact cleanup of every leaf left unselected by the V22 seven-root atlas.

The first V22 atlas pass searched 24 stratified leaves in each of seven exact
lookahead partitions.  This continuation validates the archived partition
hashes and V22 ledger, selects exactly the complementary 508 leaves, and runs
them without resubmitting any of the 168 sampled leaves.

GitHub limits and runner lifetimes are handled by batching exact leaf queries:

* at most eight 30-minute CaDiCaL leaves per job;
* only CaDiCaL UNKNOWN leaves advance;
* at most four 60-minute SMS leaves per fallback job.

Each leaf still receives its own JSON result and solver log.  A batch is only
an execution container; it is never treated as a mathematical unit.
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = REPO_ROOT / "scripts"
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

import k16_v22_atlas as atlas  # noqa: E402
from k16_smart_deepen import (  # noqa: E402
    cube_hash,
    read_cubes,
    sha256,
    write_json,
)


MODEL_VERSION = "k16-pisa-v23-seven-root-exact-cleanup-20260729"
PLAN_SCHEMA = "k16-v23-atlas-cleanup-plan-v1"
CADICAL_LEDGER_SCHEMA = "k16-v23-atlas-cleanup-cadical-ledger-v1"
FINAL_LEDGER_SCHEMA = "k16-v23-atlas-cleanup-ledger-v1"
BATCH_SCHEMA = "k16-v23-atlas-cleanup-batch-v1"

PRIOR_LEDGER_SCHEMA = atlas.FINAL_LEDGER_SCHEMA
TARGET_BOXES = atlas.TARGET_BOXES
STRATEGY = atlas.STRATEGY
CADICAL_SECONDS = atlas.CADICAL_SECONDS
SMS_SECONDS = atlas.SMS_SECONDS
CADICAL_BATCH_SIZE = 8
SMS_BATCH_SIZE = 4


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


def chunks(items: list[dict], size: int) -> list[list[dict]]:
    return [items[index : index + size] for index in range(0, len(items), size)]


def write_matrix(path: Path, batches: list[dict]) -> None:
    path.write_text(
        json.dumps(
            {
                "include": [
                    {
                        "batch_id": batch["batch_id"],
                        "box": batch["box"],
                        "leaf_count": len(batch["task_ids"]),
                    }
                    for batch in batches
                ]
            },
            separators=(",", ":"),
        )
        + "\n",
        encoding="utf-8",
    )


def make_batches(
    tasks: list[dict],
    *,
    stage: str,
    batch_size: int,
) -> list[dict]:
    by_box: dict[str, list[dict]] = {box: [] for box in TARGET_BOXES}
    for task in tasks:
        by_box[task["box"]].append(task)
    batches = []
    for box in TARGET_BOXES:
        ordered = sorted(
            by_box[box],
            key=lambda task: (int(task["cube_line"]), task["task_id"]),
        )
        for index, group in enumerate(chunks(ordered, batch_size), start=1):
            batches.append(
                {
                    "batch_id": f"{stage}-batch-{box}-{index:03d}",
                    "stage": stage,
                    "box": box,
                    "task_ids": [task["task_id"] for task in group],
                }
            )
    return batches


def plan(
    *,
    partitions: list[tuple[str, Path]],
    prior_ledger_path: Path,
    output: Path,
    matrix_output: Path,
    prior_run_id: str | None,
) -> dict:
    prior = load_json(prior_ledger_path)
    if prior.get("schema") != PRIOR_LEDGER_SCHEMA:
        raise RuntimeError("unexpected prior V22 atlas ledger schema")
    if set(prior.get("target_boxes", [])) != set(TARGET_BOXES):
        raise RuntimeError("prior V22 atlas target-box mismatch")
    if prior.get("verified_sat_witnesses"):
        raise RuntimeError("prior V22 atlas already contains a verified SAT")

    by_box = dict(partitions)
    if set(by_box) != set(TARGET_BOXES):
        raise RuntimeError(
            f"cleanup requires exactly seven partitions: {sorted(by_box)}"
        )

    boxes = {}
    tasks: list[dict] = []
    prior_final_by_leaf = {
        record["leaf_id"]: record for record in prior["cadical_results"]
    }
    for record in prior["sms_results"]:
        prior_final_by_leaf[record["leaf_id"]] = record

    for box in TARGET_BOXES:
        work = by_box[box]
        manifest_path = work / "manifest.json"
        manifest = load_json(manifest_path)
        if manifest.get("box") != box or not manifest.get("theorem_cuts"):
            raise RuntimeError(f"{box} partition provenance mismatch")
        partition = manifest.get("partitions", {}).get(STRATEGY)
        if not partition or not partition.get("generator_complete"):
            raise RuntimeError(f"{box} lacks a complete lookahead partition")
        if partition.get("coverage", {}).get("status") != "UNSAT":
            raise RuntimeError(f"{box} partition lacks exact coverage")

        cube_path = work / partition["cube_file"]
        if sha256(cube_path) != partition["cube_sha256"]:
            raise RuntimeError(f"{box} cube hash mismatch")
        cubes = read_cubes(cube_path)
        total = int(partition["cubes"])
        if len(cubes) != total:
            raise RuntimeError(f"{box} cube count mismatch")

        prior_box = prior["per_box"][box]
        if int(prior_box["partition_cubes"]) != total:
            raise RuntimeError(f"{box} prior partition size mismatch")
        if prior_box["partition_cube_sha256"] != sha256(cube_path):
            raise RuntimeError(f"{box} prior partition hash mismatch")
        selected = {int(line) for line in prior_box["selected_lines"]}
        if len(selected) != int(prior_box["selected_count"]):
            raise RuntimeError(f"{box} prior selected-line mismatch")
        expected_selected = {
            int(record["cube_line"])
            for record in prior_final_by_leaf.values()
            if record["box"] == box
        }
        if selected != expected_selected:
            raise RuntimeError(f"{box} prior result coverage mismatch")

        cleanup_lines = [line for line in range(1, total + 1) if line not in selected]
        if len(cleanup_lines) != int(prior_box["unselected_count"]):
            raise RuntimeError(f"{box} cleanup complement mismatch")
        boxes[box] = {
            "partition_cubes": total,
            "partition_cube_sha256": sha256(cube_path),
            "prior_selected_lines": sorted(selected),
            "prior_selected_count": len(selected),
            "cleanup_lines": cleanup_lines,
            "cleanup_count": len(cleanup_lines),
            "coverage": partition["coverage"],
        }
        for line in cleanup_lines:
            cube = cubes[line - 1]
            leaf_id = f"{box}-c{line:06d}"
            tasks.append(
                {
                    "task_id": f"cadical{CADICAL_SECONDS}-cleanup-{leaf_id}",
                    "stage": "cadical",
                    "method": f"cadical{CADICAL_SECONDS}",
                    "solver": "cadical",
                    "seconds": CADICAL_SECONDS,
                    "sms_seconds": SMS_SECONDS,
                    "box": box,
                    "leaf_id": leaf_id,
                    "strategy": STRATEGY,
                    "cube_line": line,
                    "cube_literals": cube,
                    "cube_depth": len(cube),
                    "cube_sha256": cube_hash(cube),
                }
            )

    if len(tasks) != 508:
        raise RuntimeError(f"expected exactly 508 cleanup leaves, got {len(tasks)}")
    batches = make_batches(
        tasks,
        stage="cadical",
        batch_size=CADICAL_BATCH_SIZE,
    )
    if len(batches) > 224:
        raise RuntimeError("cleanup CaDiCaL batch matrix exceeds GitHub limit")
    record = {
        "schema": PLAN_SCHEMA,
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "prior_run_id": prior_run_id,
        "prior_ledger_sha256": sha256(prior_ledger_path),
        "target_boxes": list(TARGET_BOXES),
        "boxes": boxes,
        "cadical_tasks": tasks,
        "cadical_batches": batches,
        "coverage": (
            "The prior 168 selected leaves and these 508 complementary leaves "
            "are disjoint and together equal every leaf in all seven exact "
            "lookahead partitions."
        ),
    }
    output.mkdir(parents=True, exist_ok=True)
    write_json(output / "v23-cleanup-manifest.json", record)
    write_matrix(matrix_output, batches)
    print(
        json.dumps(
            {
                "cleanup_leaves": len(tasks),
                "cadical_batches": len(batches),
                "maximum_batch_size": max(
                    len(batch["task_ids"]) for batch in batches
                ),
                "by_box": {
                    box: info["cleanup_count"] for box, info in boxes.items()
                },
            },
            indent=2,
        ),
        flush=True,
    )
    return record


def solve_batch(
    *,
    solver_source: Path,
    prepared: Path,
    manifest_path: Path,
    batch_id: str,
    output: Path,
) -> dict:
    manifest = load_json(manifest_path)
    batches = manifest.get("cadical_batches", []) + manifest.get("sms_batches", [])
    matches = [batch for batch in batches if batch["batch_id"] == batch_id]
    if len(matches) != 1:
        raise RuntimeError(f"batch lookup failed: {batch_id}")
    batch = matches[0]
    task_ids = list(batch["task_ids"])
    output.mkdir(parents=True, exist_ok=True)
    results_dir = output / "results"
    logs_dir = output / "logs"
    records = []
    for task_id in task_ids:
        records.append(
            atlas.solve(
                solver_source=solver_source,
                prepared=prepared,
                manifest_path=manifest_path,
                task_id=task_id,
                result_path=results_dir / f"{task_id}.json",
                log_path=logs_dir / f"{task_id}.log",
            )
        )
    summary = {
        "schema": BATCH_SCHEMA,
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "batch_id": batch_id,
        "box": batch["box"],
        "expected_results": len(task_ids),
        "results_received": len(records),
        "statuses": dict(Counter(record["status"] for record in records)),
        "cpu_seconds": round(
            sum(float(record["seconds"]) for record in records),
            3,
        ),
        "task_ids": task_ids,
    }
    write_json(output / "batch-summary.json", summary)
    print(json.dumps(summary, indent=2), flush=True)
    return summary


def select_sms(
    *,
    manifest_path: Path,
    cadical_results_root: Path,
    output: Path,
    matrix_output: Path,
) -> dict:
    plan_record = load_json(manifest_path)
    if plan_record.get("schema") != PLAN_SCHEMA:
        raise RuntimeError("unexpected cleanup plan schema")
    expected = {
        task["task_id"]: task for task in plan_record["cadical_tasks"]
    }
    records = atlas.collect_records(cadical_results_root)
    by_id = {record["task_id"]: record for record in records}
    missing = sorted(set(expected) - set(by_id))
    unexpected = sorted(set(by_id) - set(expected))
    if missing or unexpected:
        raise RuntimeError(
            f"cleanup CaDiCaL mismatch: missing={missing}, unexpected={unexpected}"
        )
    bad_sat = [
        record["task_id"]
        for record in records
        if record["status"] == "SAT" and not record.get("verified")
    ]
    if bad_sat:
        raise RuntimeError(f"unverified cleanup SAT: {bad_sat}")
    verified_sat = [
        record["task_id"]
        for record in records
        if record["status"] == "SAT" and record.get("verified")
    ]
    task_by_leaf = {
        task["leaf_id"]: task for task in plan_record["cadical_tasks"]
    }
    unknown_records = (
        []
        if verified_sat
        else sorted(
            (
                record
                for record in records
                if record["status"] == "UNKNOWN"
            ),
            key=lambda record: (record["box"], record["cube_line"]),
        )
    )
    sms_tasks = []
    for record in unknown_records:
        parent = task_by_leaf[record["leaf_id"]]
        sms_tasks.append(
            {
                **parent,
                "task_id": f"sms{SMS_SECONDS}-cleanup-{record['leaf_id']}",
                "stage": "sms",
                "method": f"sms{SMS_SECONDS}",
                "solver": "sms",
                "seconds": SMS_SECONDS,
            }
        )
    sms_batches = make_batches(
        sms_tasks,
        stage="sms",
        batch_size=SMS_BATCH_SIZE,
    )
    if len(sms_batches) > 224:
        raise RuntimeError("cleanup SMS batch matrix exceeds GitHub limit")
    sms_manifest = {
        "schema": PLAN_SCHEMA,
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "cadical_tasks": [],
        "sms_tasks": sms_tasks,
        "sms_batches": sms_batches,
    }
    ledger = {
        "schema": CADICAL_LEDGER_SCHEMA,
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "expected_results": len(expected),
        "results_received": len(records),
        "statuses": dict(Counter(record["status"] for record in records)),
        "verified_sat_witnesses": verified_sat,
        "unknown_leaf_ids": [
            record["leaf_id"] for record in unknown_records
        ],
        "cpu_seconds": round(
            sum(float(record["seconds"]) for record in records),
            3,
        ),
        "results": sorted(records, key=lambda record: record["task_id"]),
    }
    output.mkdir(parents=True, exist_ok=True)
    write_json(output / "v23-cleanup-sms-manifest.json", sms_manifest)
    write_json(output / "v23-cleanup-cadical-ledger.json", ledger)
    write_matrix(matrix_output, sms_batches)
    print(
        json.dumps(
            {
                "cadical_statuses": ledger["statuses"],
                "sms_leaves": len(sms_tasks),
                "sms_batches": len(sms_batches),
            },
            indent=2,
        ),
        flush=True,
    )
    return ledger


def final_leaf_results(ledger: dict) -> dict[str, dict]:
    by_leaf = {
        record["leaf_id"]: record for record in ledger["cadical_results"]
    }
    for record in ledger["sms_results"]:
        by_leaf[record["leaf_id"]] = record
    return by_leaf


def aggregate(
    *,
    plan_manifest_path: Path,
    prior_ledger_path: Path,
    cadical_ledger_path: Path,
    sms_results_root: Path,
    output: Path,
    workflow_run_id: str | None,
) -> dict:
    plan_record = load_json(plan_manifest_path)
    prior = load_json(prior_ledger_path)
    cadical = load_json(cadical_ledger_path)
    if plan_record.get("schema") != PLAN_SCHEMA:
        raise RuntimeError("unexpected cleanup plan schema")
    if prior.get("schema") != PRIOR_LEDGER_SCHEMA:
        raise RuntimeError("unexpected prior V22 ledger schema")
    if cadical.get("schema") != CADICAL_LEDGER_SCHEMA:
        raise RuntimeError("unexpected cleanup CaDiCaL ledger schema")

    sms_records = atlas.collect_records(sms_results_root)
    sms_by_leaf = {record["leaf_id"]: record for record in sms_records}
    expected_sms = set(cadical["unknown_leaf_ids"])
    missing = sorted(expected_sms - set(sms_by_leaf))
    unexpected = sorted(set(sms_by_leaf) - expected_sms)
    if missing or unexpected:
        raise RuntimeError(
            f"cleanup SMS mismatch: missing={missing}, unexpected={unexpected}"
        )
    bad_sat = [
        record["task_id"]
        for record in sms_records
        if record["status"] == "SAT" and not record.get("verified")
    ]
    if bad_sat:
        raise RuntimeError(f"unverified cleanup SMS SAT: {bad_sat}")

    prior_by_leaf = final_leaf_results(prior)
    cleanup_by_leaf = {
        record["leaf_id"]: record for record in cadical["results"]
    }
    cleanup_by_leaf.update(sms_by_leaf)
    overlap = sorted(set(prior_by_leaf) & set(cleanup_by_leaf))
    if overlap:
        raise RuntimeError(f"cleanup resubmitted prior leaves: {overlap}")
    final_by_leaf = {**prior_by_leaf, **cleanup_by_leaf}
    expected_total = sum(
        int(info["partition_cubes"]) for info in plan_record["boxes"].values()
    )
    if expected_total != 676 or len(final_by_leaf) != expected_total:
        raise RuntimeError(
            f"full atlas mismatch: expected={expected_total}, "
            f"received={len(final_by_leaf)}"
        )

    per_box = {}
    root_unsat = []
    for box in TARGET_BOXES:
        records = [
            record
            for record in final_by_leaf.values()
            if record["box"] == box
        ]
        statuses = Counter(record["status"] for record in records)
        total = int(plan_record["boxes"][box]["partition_cubes"])
        if len(records) != total:
            raise RuntimeError(f"{box} final leaf-count mismatch")
        root_closed = statuses.get("UNSAT", 0) == total
        if root_closed:
            root_unsat.append(box)
        per_box[box] = {
            "partition_cubes": total,
            "statuses": dict(statuses),
            "exact_leaf_closures": statuses.get("UNSAT", 0),
            "unknown_leaves": statuses.get("UNKNOWN", 0),
            "verified_sat_leaves": sum(
                record["status"] == "SAT" and record.get("verified")
                for record in records
            ),
            "root_exactly_excluded": root_closed,
        }

    verified_sat = [
        record["task_id"]
        for record in final_by_leaf.values()
        if record["status"] == "SAT" and record.get("verified")
    ]
    if verified_sat:
        conclusion = "SAT_K16_VERIFIED"
    elif len(root_unsat) == len(TARGET_BOXES):
        conclusion = "V23_SEVEN_ROOTS_EXACTLY_EXCLUDED"
    else:
        conclusion = "V23_CLEANUP_COMPLETE_K16_OPEN"
    statuses = Counter(record["status"] for record in final_by_leaf.values())
    record = {
        "schema": FINAL_LEDGER_SCHEMA,
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "workflow_run_id": workflow_run_id,
        "prior_run_id": plan_record.get("prior_run_id"),
        "logical_conclusion": conclusion,
        "target_boxes": list(TARGET_BOXES),
        "total_partition_leaves": expected_total,
        "statuses": dict(statuses),
        "exact_leaf_closures": statuses.get("UNSAT", 0),
        "known_open_partition_leaves": statuses.get("UNKNOWN", 0),
        "root_unsat": root_unsat,
        "verified_sat_witnesses": verified_sat,
        "prior_cpu_seconds": round(
            float(prior["cadical_cpu_seconds"])
            + float(prior["sms_cpu_seconds"]),
            3,
        ),
        "cleanup_cadical_cpu_seconds": cadical["cpu_seconds"],
        "cleanup_sms_cpu_seconds": round(
            sum(float(record["seconds"]) for record in sms_records),
            3,
        ),
        "per_box": per_box,
        "next_action": (
            "Preserve every exact closure. Recursively split only final "
            "UNKNOWN leaves; UNKNOWN is not exclusion."
        ),
        "prior_final_results": sorted(
            prior_by_leaf.values(), key=lambda record: record["leaf_id"]
        ),
        "cleanup_cadical_results": cadical["results"],
        "cleanup_sms_results": sorted(
            sms_records, key=lambda record: record["task_id"]
        ),
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    write_json(output, record)
    print(
        json.dumps(
            {
                "conclusion": conclusion,
                "statuses": dict(statuses),
                "root_unsat": root_unsat,
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
    mode.add_argument("--solve-batch", action="store_true")
    mode.add_argument("--select-sms", action="store_true")
    mode.add_argument("--aggregate", action="store_true")
    parser.add_argument("--partition", action="append", type=parse_partition)
    parser.add_argument("--prior-ledger", type=Path)
    parser.add_argument("--prior-run-id")
    parser.add_argument("--solver-source", type=Path)
    parser.add_argument("--prepared", type=Path)
    parser.add_argument("--manifest", type=Path)
    parser.add_argument("--plan-manifest", type=Path)
    parser.add_argument("--cadical-results-root", type=Path)
    parser.add_argument("--cadical-ledger", type=Path)
    parser.add_argument("--sms-results-root", type=Path)
    parser.add_argument("--batch-id")
    parser.add_argument("--matrix-output", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--workflow-run-id")
    args = parser.parse_args()

    if args.plan:
        plan(
            partitions=args.partition or [],
            prior_ledger_path=args.prior_ledger,
            output=args.output,
            matrix_output=args.matrix_output,
            prior_run_id=args.prior_run_id,
        )
    elif args.solve_batch:
        solve_batch(
            solver_source=args.solver_source,
            prepared=args.prepared,
            manifest_path=args.manifest,
            batch_id=args.batch_id,
            output=args.output,
        )
    elif args.select_sms:
        select_sms(
            manifest_path=args.manifest,
            cadical_results_root=args.cadical_results_root,
            output=args.output,
            matrix_output=args.matrix_output,
        )
    else:
        aggregate(
            plan_manifest_path=args.plan_manifest,
            prior_ledger_path=args.prior_ledger,
            cadical_ledger_path=args.cadical_ledger,
            sms_results_root=args.sms_results_root,
            output=args.output,
            workflow_run_id=args.workflow_run_id,
        )


if __name__ == "__main__":
    main()
