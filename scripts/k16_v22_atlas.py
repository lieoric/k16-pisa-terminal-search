#!/usr/bin/env python3
"""V22 first exact atlas pass over the seven previously unopened root boxes.

Each root is partitioned by the theorem-strengthened SMS lookahead cuber and
must pass an independent exact coverage query.  This script selects a
stratified sample from every complete partition, runs 30 minutes of CaDiCaL,
then sends only logical UNKNOWN leaves to a 60-minute SMS fallback.

The final ledger distinguishes:

* complete-root SAT or UNSAT discovered during the prerun;
* sampled leaves closed exactly by CaDiCaL or SMS;
* sampled UNKNOWN leaves;
* unselected leaves that remain open without having been searched.

No sampled result is ever promoted to a whole-root conclusion.
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

from k16_primitive_sms import (  # noqa: E402
    LANES,
    independent_audit,
)
from k16_smart_cubing import (  # noqa: E402
    CUBE_RESULT,
    parse_sms_arcs,
    stratified_lines,
)
from k16_smart_deepen import (  # noqa: E402
    N,
    cube_hash,
    read_cubes,
    sha256,
    write_json,
)
from k16_staged_cascade import (  # noqa: E402
    assignment_to_arcs,
    parse_cadical_assignment,
    run_limited,
    write_assumption_cnf,
)


MODEL_VERSION = "k16-pisa-v22-seven-root-theorem-atlas-20260729"
PLAN_SCHEMA = "k16-v22-atlas-plan-v1"
RESULT_SCHEMA = "k16-v22-atlas-result-v1"
CADICAL_LEDGER_SCHEMA = "k16-v22-atlas-cadical-ledger-v1"
FINAL_LEDGER_SCHEMA = "k16-v22-atlas-ledger-v1"

TARGET_BOXES = (
    "a0_z2",
    "a0_z3",
    "a0_z4p",
    "a1_z2",
    "a1_z4p",
    "a2p_z2",
    "a2p_z3",
)
STRATEGY = "lookahead"
CADICAL_SECONDS = 1800
SMS_SECONDS = 3600


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
    task_ids = [record["task_id"] for record in records]
    if len(task_ids) != len(set(task_ids)):
        raise RuntimeError("duplicate V22 atlas result identifiers")
    return records


def plan(
    *,
    partitions: list[tuple[str, Path]],
    output: Path,
    matrix_output: Path,
    sample_size: int,
    source_run_id: str | None,
) -> dict:
    by_box = dict(partitions)
    if set(by_box) != set(TARGET_BOXES):
        raise RuntimeError(
            f"atlas requires exactly seven partitions: {sorted(by_box)}"
        )
    if not 1 <= sample_size <= 32:
        raise ValueError("sample size must be between 1 and 32")

    boxes = {}
    tasks = []
    verified_root_sat = []
    root_unsat = []
    for box in TARGET_BOXES:
        work = by_box[box]
        manifest_path = work / "manifest.json"
        manifest = load_json(manifest_path)
        if manifest.get("box") != box:
            raise RuntimeError(f"{box} partition manifest mismatch")
        if not manifest.get("theorem_cuts"):
            raise RuntimeError(f"{box} was partitioned without theorem cuts")
        root_status = manifest.get("root_status")
        box_record = {
            "root_status": root_status,
            "manifest_sha256": sha256(manifest_path),
            "selected_lines": [],
        }
        if root_status == "SAT":
            prerun = manifest["prerun"]
            if not prerun.get("verified"):
                raise RuntimeError(f"{box} has unverified prerun SAT")
            verified_root_sat.append(box)
            boxes[box] = box_record
            continue
        if root_status == "UNSAT":
            root_unsat.append(box)
            boxes[box] = box_record
            continue
        if root_status != "PARTITIONED":
            raise RuntimeError(f"{box} has unusable root status {root_status}")

        partition = manifest["partitions"].get(STRATEGY)
        if not partition or not partition.get("generator_complete"):
            raise RuntimeError(f"{box} has no complete lookahead partition")
        if partition["coverage"].get("status") != "UNSAT":
            raise RuntimeError(f"{box} partition lacks exact coverage")
        cube_path = work / partition["cube_file"]
        if sha256(cube_path) != partition["cube_sha256"]:
            raise RuntimeError(f"{box} cube hash mismatch")
        cubes = read_cubes(cube_path)
        total = int(partition["cubes"])
        if len(cubes) != total:
            raise RuntimeError(f"{box} cube count mismatch")
        selected = stratified_lines(total, min(sample_size, total))
        box_record.update(
            {
                "partition_strategy": STRATEGY,
                "partition_cubes": total,
                "partition_cube_sha256": sha256(cube_path),
                "selected_lines": selected,
                "selected_count": len(selected),
                "unselected_count": total - len(selected),
                "coverage": partition["coverage"],
            }
        )
        boxes[box] = box_record
        for line in selected:
            cube = cubes[line - 1]
            leaf_id = f"{box}-c{line:06d}"
            tasks.append(
                {
                    "task_id": f"cadical{CADICAL_SECONDS}-{leaf_id}",
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

    if len(tasks) > 224:
        raise RuntimeError("atlas matrix exceeds the GitHub limit")
    record = {
        "schema": PLAN_SCHEMA,
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "source_run_id": source_run_id,
        "target_boxes": list(TARGET_BOXES),
        "sample_size_per_box": sample_size,
        "boxes": boxes,
        "verified_root_sat": verified_root_sat,
        "root_unsat": root_unsat,
        "cadical_tasks": tasks,
        "coverage": (
            "Every searched leaf belongs to a complete, exactly covered SMS "
            "lookahead partition. Unselected leaves stay explicitly open. "
            "No sample is promoted to a whole-root exclusion."
        ),
    }
    output.mkdir(parents=True, exist_ok=True)
    write_json(output / "v22-atlas-manifest.json", record)
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
                "boxes": {
                    box: {
                        "status": info["root_status"],
                        "cubes": info.get("partition_cubes", 0),
                        "selected": info.get("selected_count", 0),
                    }
                    for box, info in boxes.items()
                },
                "cadical_tasks": len(tasks),
                "verified_root_sat": verified_root_sat,
                "root_unsat": root_unsat,
            },
            indent=2,
        ),
        flush=True,
    )
    return record


def _task_from_manifest(manifest: dict, task_id: str) -> dict:
    tasks = manifest.get("cadical_tasks", []) + manifest.get("sms_tasks", [])
    matches = [task for task in tasks if task["task_id"] == task_id]
    if len(matches) != 1:
        raise RuntimeError(f"task lookup failed: {task_id}")
    return matches[0]


def solve(
    *,
    solver_source: Path,
    prepared: Path,
    manifest_path: Path,
    task_id: str,
    result_path: Path,
    log_path: Path,
) -> dict:
    manifest = load_json(manifest_path)
    task = _task_from_manifest(manifest, task_id)
    box = task["box"]
    seconds = int(task["seconds"])
    prepared_manifest = load_json(prepared / "manifest.json")
    if prepared_manifest.get("box") != box:
        raise RuntimeError("prepared root does not match task box")
    cnf = prepared / "enriched.cnf"
    cube_file = prepared / prepared_manifest["partitions"][
        task["strategy"]
    ]["cube_file"]
    cubes = read_cubes(cube_file)
    cube = cubes[int(task["cube_line"]) - 1]
    if cube != task["cube_literals"] or cube_hash(cube) != task["cube_sha256"]:
        raise RuntimeError("atlas task cube does not match partition")
    work = result_path.parent.parent / "work" / task_id
    work.mkdir(parents=True, exist_ok=True)

    if task["solver"] == "cadical":
        assumption_cnf = work / "assumption.cnf"
        write_assumption_cnf(cnf, assumption_cnf, cube)
        command = [
            str(solver_source / "cadical" / "cadical"),
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
        command = [
            str(solver_source / "bundle" / "smsg"),
            "--vertices",
            str(N),
            "--directed",
            "--dimacs",
            str(cnf),
            "--cube-file",
            str(cube_file),
            "--cube-line",
            str(task["cube_line"]),
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
        arcs = parse_sms_arcs(text, N) if status == "SAT" else None
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
        "leaf_id": task["leaf_id"],
        "strategy": task["strategy"],
        "cube_line": task["cube_line"],
        "cube_literals": cube,
        "cube_depth": len(cube),
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
        audit = independent_audit(
            arcs,
            lane=LANES["full_s16"],
            box=box,
            directory=work,
        )
        record["candidate_arcs"] = arcs
        record["independent_audit"] = audit
        record["verified"] = bool(audit.get("valid"))
        if not record["verified"]:
            write_json(result_path, record)
            raise RuntimeError("SAT candidate failed independent verification")
    write_json(result_path, record)
    print(json.dumps(record, indent=2), flush=True)
    return record


def select_sms(
    *,
    manifest_path: Path,
    cadical_results_root: Path,
    output: Path,
    matrix_output: Path,
) -> dict:
    plan_record = load_json(manifest_path)
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
        raise RuntimeError(f"unverified atlas SAT: {bad_sat}")
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
            key=lambda item: item["leaf_id"],
        )
    )
    task_by_leaf = {
        task["leaf_id"]: task for task in plan_record["cadical_tasks"]
    }
    sms_tasks = []
    for record in unknown_records:
        parent = task_by_leaf[record["leaf_id"]]
        sms_tasks.append(
            {
                **parent,
                "task_id": f"sms{SMS_SECONDS}-{record['leaf_id']}",
                "stage": "sms",
                "method": f"sms{SMS_SECONDS}",
                "solver": "sms",
                "seconds": SMS_SECONDS,
            }
        )
    sms_manifest = {
        "schema": PLAN_SCHEMA,
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "cadical_tasks": [],
        "sms_tasks": sms_tasks,
    }
    output.mkdir(parents=True, exist_ok=True)
    write_json(output / "v22-atlas-sms-manifest.json", sms_manifest)
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
            sum(float(record["seconds"]) for record in records), 3
        ),
        "results": sorted(records, key=lambda item: item["task_id"]),
    }
    write_json(output / "v22-atlas-cadical-ledger.json", ledger)
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
                "cadical_statuses": ledger["statuses"],
                "sms_tasks": len(sms_tasks),
            },
            indent=2,
        ),
        flush=True,
    )
    return ledger


def aggregate(
    *,
    plan_manifest_path: Path,
    cadical_ledger_path: Path,
    sms_results_root: Path,
    output: Path,
    workflow_run_id: str | None,
) -> dict:
    plan_record = load_json(plan_manifest_path)
    cadical = load_json(cadical_ledger_path)
    if cadical.get("schema") != CADICAL_LEDGER_SCHEMA:
        raise RuntimeError("unexpected V22 atlas CaDiCaL ledger")
    sms_records = collect_records(sms_results_root)
    sms_by_leaf = {record["leaf_id"]: record for record in sms_records}
    expected_sms = set(cadical["unknown_leaf_ids"])
    missing = sorted(expected_sms - set(sms_by_leaf))
    unexpected = sorted(set(sms_by_leaf) - expected_sms)
    if missing or unexpected:
        raise RuntimeError(
            f"SMS result mismatch: missing={missing}, unexpected={unexpected}"
        )
    bad_sat = [
        record["task_id"]
        for record in sms_records
        if record["status"] == "SAT" and not record.get("verified")
    ]
    if bad_sat:
        raise RuntimeError(f"unverified SMS SAT: {bad_sat}")

    final_by_leaf = {
        record["leaf_id"]: record for record in cadical["results"]
    }
    for leaf_id, record in sms_by_leaf.items():
        final_by_leaf[leaf_id] = record
    per_box = {}
    for box in TARGET_BOXES:
        box_plan = plan_record["boxes"][box]
        selected = [
            record
            for record in final_by_leaf.values()
            if record["box"] == box
        ]
        statuses = Counter(record["status"] for record in selected)
        per_box[box] = {
            **box_plan,
            "sampled_statuses": dict(statuses),
            "exact_sampled_closures": statuses.get("UNSAT", 0),
            "sampled_unknown": statuses.get("UNKNOWN", 0),
            "sampled_verified_sat": sum(
                record["status"] == "SAT" and record.get("verified")
                for record in selected
            ),
            "known_open_partition_leaves": (
                int(box_plan.get("unselected_count", 0))
                + statuses.get("UNKNOWN", 0)
            ),
            "root_exactly_excluded": (
                box_plan["root_status"] == "UNSAT"
            ),
        }

    verified_sat = (
        list(plan_record["verified_root_sat"])
        + list(cadical["verified_sat_witnesses"])
        + [
            record["task_id"]
            for record in sms_records
            if record["status"] == "SAT" and record.get("verified")
        ]
    )
    root_unsat = list(plan_record["root_unsat"])
    total_partition_leaves = sum(
        int(info.get("partition_cubes", 0))
        for info in plan_record["boxes"].values()
    )
    exact_sampled_closures = sum(
        info["exact_sampled_closures"] for info in per_box.values()
    )
    known_open_partition_leaves = sum(
        info["known_open_partition_leaves"] for info in per_box.values()
    )
    if verified_sat:
        conclusion = "SAT_K16_VERIFIED"
    elif len(root_unsat) == len(TARGET_BOXES):
        conclusion = "V22_SEVEN_ROOTS_EXACTLY_EXCLUDED"
    else:
        conclusion = "V22_ATLAS_PASS_COMPLETE_K16_OPEN"
    record = {
        "schema": FINAL_LEDGER_SCHEMA,
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "workflow_run_id": workflow_run_id,
        "logical_conclusion": conclusion,
        "target_boxes": list(TARGET_BOXES),
        "total_partition_leaves": total_partition_leaves,
        "sampled_leaves": len(plan_record["cadical_tasks"]),
        "exact_sampled_closures": exact_sampled_closures,
        "known_open_partition_leaves": known_open_partition_leaves,
        "root_unsat": root_unsat,
        "verified_sat_witnesses": verified_sat,
        "cadical_statuses": cadical["statuses"],
        "sms_statuses": dict(
            Counter(record["status"] for record in sms_records)
        ),
        "cadical_cpu_seconds": cadical["cpu_seconds"],
        "sms_cpu_seconds": round(
            sum(float(record["seconds"]) for record in sms_records), 3
        ),
        "per_box": per_box,
        "next_action": (
            "Preserve every exact sampled closure. Queue unselected and "
            "sampled UNKNOWN partition leaves only; UNKNOWN is not exclusion."
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
                "partition_leaves": total_partition_leaves,
                "sampled": len(plan_record["cadical_tasks"]),
                "sampled_closed": exact_sampled_closures,
                "known_open": known_open_partition_leaves,
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
    parser.add_argument(
        "--partition",
        action="append",
        type=parse_partition,
        default=[],
    )
    parser.add_argument("--sample-size", type=int, default=24)
    parser.add_argument("--source-run-id")
    parser.add_argument("--solver-source", type=Path)
    parser.add_argument("--prepared", type=Path)
    parser.add_argument("--manifest", type=Path)
    parser.add_argument("--plan-manifest", type=Path)
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
        if not args.partition or args.output is None or args.matrix_output is None:
            parser.error(
                "--plan requires seven --partition BOX=PATH entries, "
                "--output, and --matrix-output"
            )
        plan(
            partitions=args.partition,
            output=args.output,
            matrix_output=args.matrix_output,
            sample_size=args.sample_size,
            source_run_id=args.source_run_id,
        )
    elif args.solve:
        required = (
            args.solver_source,
            args.prepared,
            args.manifest,
            args.task_id,
            args.result,
            args.log,
        )
        if any(value is None for value in required):
            parser.error(
                "--solve requires --solver-source --prepared --manifest "
                "--task-id --result --log"
            )
        solve(
            solver_source=args.solver_source,
            prepared=args.prepared,
            manifest_path=args.manifest,
            task_id=args.task_id,
            result_path=args.result,
            log_path=args.log,
        )
    elif args.select_sms:
        required = (
            args.manifest,
            args.cadical_results_root,
            args.output,
            args.matrix_output,
        )
        if any(value is None for value in required):
            parser.error(
                "--select-sms requires --manifest "
                "--cadical-results-root --output --matrix-output"
            )
        select_sms(
            manifest_path=args.manifest,
            cadical_results_root=args.cadical_results_root,
            output=args.output,
            matrix_output=args.matrix_output,
        )
    else:
        required = (
            args.plan_manifest,
            args.cadical_ledger,
            args.sms_results_root,
            args.output,
        )
        if any(value is None for value in required):
            parser.error(
                "--aggregate requires --plan-manifest --cadical-ledger "
                "--sms-results-root --output"
            )
        aggregate(
            plan_manifest_path=args.plan_manifest,
            cadical_ledger_path=args.cadical_ledger,
            sms_results_root=args.sms_results_root,
            output=args.output,
            workflow_run_id=args.workflow_run_id,
        )


if __name__ == "__main__":
    main()
