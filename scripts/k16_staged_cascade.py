#!/usr/bin/env python3
"""V20 staged exact cascade over the surviving V18 K16 frontier.

The campaign is deliberately sequential:

1. remove every leaf already closed by the complete V19 strategy ledger;
2. run CaDiCaL for 720 seconds on each remaining leaf;
3. build a new matrix containing only CaDiCaL UNKNOWN leaves;
4. run SMS for 900 seconds on that reduced matrix;
5. publish a resumable ledger that never treats UNKNOWN as exclusion.

Each solver exits immediately on SAT or UNSAT.  The time limit is only a
ceiling for still-inconclusive searches.
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
import time
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = REPO_ROOT / "scripts"
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from k16_smart_deepen import (  # noqa: E402
    CUBE_RESULT,
    N,
    cube_hash,
    cube_line,
    parse_sms_arcs,
    sha256,
    write_json,
)


MODEL_VERSION = "k16-pisa-v20-cadical12-sms15-cascade-20260728"
PLAN_SCHEMA = "k16-v20-cascade-plan-v1"
RESULT_SCHEMA = "k16-v20-cascade-result-v1"
CADICAL_LEDGER_SCHEMA = "k16-v20-cadical-stage-ledger-v1"
FINAL_LEDGER_SCHEMA = "k16-v20-cascade-ledger-v1"
CADICAL_VERSION = "3.0.1"
CADICAL_COMMIT = "c60730422e758ef1cebe7aeddf2dda31c996bf04"
CADICAL_SECONDS = 720
SMS_SECONDS = 900
INDEPENDENT_VERIFIER = SCRIPTS / "verify_primitive_witness.py"


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def locate_one(root: Path, name: str) -> Path:
    matches = sorted(root.rglob(name))
    if len(matches) != 1:
        raise RuntimeError(f"expected one {name} below {root}, got {matches}")
    return matches[0]


def copy_file_tree(source: Path, destination: Path) -> None:
    if destination.exists():
        shutil.rmtree(destination)
    shutil.copytree(source, destination)


def collect_records(root: Path) -> list[dict]:
    records = []
    for path in sorted(root.rglob("*.json")):
        record = load_json(path)
        if record.get("schema") == RESULT_SCHEMA:
            records.append(record)
    ids = [record["task_id"] for record in records]
    if len(ids) != len(set(ids)):
        raise RuntimeError("duplicate V20 result identifiers")
    return records


def run_limited(
    command: list[str],
    *,
    timeout_seconds: int,
) -> tuple[int, str, bool, float]:
    started = time.monotonic()
    try:
        completed = subprocess.run(
            command,
            capture_output=True,
            text=True,
            check=False,
            timeout=timeout_seconds,
        )
        return (
            completed.returncode,
            completed.stdout + completed.stderr,
            False,
            time.monotonic() - started,
        )
    except subprocess.TimeoutExpired as exc:
        stdout = (
            exc.stdout.decode()
            if isinstance(exc.stdout, bytes)
            else (exc.stdout or "")
        )
        stderr = (
            exc.stderr.decode()
            if isinstance(exc.stderr, bytes)
            else (exc.stderr or "")
        )
        return (
            0,
            stdout + stderr + "\nV20 WRAPPER TIMEOUT\n",
            True,
            time.monotonic() - started,
        )


def write_assumption_cnf(
    source: Path,
    destination: Path,
    cube: list[int],
) -> None:
    destination.parent.mkdir(parents=True, exist_ok=True)
    with source.open("r", encoding="utf-8") as reader:
        header = reader.readline().strip()
        match = re.fullmatch(r"p cnf (\d+) (\d+)", header)
        if not match:
            raise RuntimeError(f"invalid DIMACS header: {header}")
        variables = int(match.group(1))
        clauses = int(match.group(2))
        with destination.open("w", encoding="utf-8") as writer:
            writer.write(f"p cnf {variables} {clauses + len(cube)}\n")
            shutil.copyfileobj(reader, writer)
            for literal in cube:
                writer.write(f"{literal} 0\n")


def parse_cadical_assignment(text: str) -> dict[int, bool]:
    assignment: dict[int, bool] = {}
    for raw in text.splitlines():
        line = raw.strip()
        if not line.startswith("v "):
            continue
        for field in line.split()[1:]:
            literal = int(field)
            if literal:
                assignment[abs(literal)] = literal > 0
    return assignment


def arc_variable(u: int, v: int) -> int:
    if u == v:
        raise ValueError((u, v))
    offset = v + 1 if v < u else v
    return u * (N - 1) + offset


def assignment_to_arcs(assignment: dict[int, bool]) -> list[list[int]]:
    arcs: list[list[int]] = []
    for u in range(N):
        for v in range(u + 1, N):
            forward = arc_variable(u, v)
            reverse = arc_variable(v, u)
            if forward not in assignment or reverse not in assignment:
                raise RuntimeError("CaDiCaL model omitted an arc variable")
            if assignment[forward] == assignment[reverse]:
                raise RuntimeError("CaDiCaL model violates tournament orientation")
            arcs.append([u, v] if assignment[forward] else [v, u])
    return arcs


def independent_audit(
    *,
    arcs: list[list[int]],
    box: str,
    directory: Path,
) -> tuple[bool, dict]:
    candidate = directory / "candidate.json"
    audit_path = directory / "audit.json"
    write_json(candidate, {"n": N, "arcs": arcs})
    completed = subprocess.run(
        [
            sys.executable,
            str(INDEPENDENT_VERIFIER),
            "--input",
            str(candidate),
            "--output",
            str(audit_path),
            "--box",
            box,
        ],
        capture_output=True,
        text=True,
        check=False,
    )
    audit = (
        load_json(audit_path)
        if audit_path.exists()
        else {"valid": False, "error": "standalone verifier wrote no audit"}
    )
    audit["process_exit_code"] = completed.returncode
    return completed.returncode == 0 and bool(audit.get("valid")), audit


def validate_v18(
    *,
    v18_source: Path,
    v18_ledger_path: Path,
) -> tuple[dict, dict, list[dict], dict[str, dict]]:
    queue_manifest_path = v18_source / "queue-manifest.json"
    queue_manifest = load_json(queue_manifest_path)
    ledger = load_json(v18_ledger_path)
    if ledger.get("logical_conclusion") != "V18_COMPLETE_TARGETS_STILL_OPEN":
        raise RuntimeError("unexpected V18 ledger conclusion")
    if ledger.get("results_received") != 237 or ledger.get("missing_queue_ids"):
        raise RuntimeError("V18 ledger is incomplete")
    if ledger.get("verified_sat_witnesses"):
        raise RuntimeError("V18 already contains a verified SAT witness")
    open_results = [
        result for result in ledger["results"] if result["status"] == "UNKNOWN"
    ]
    if len(open_results) != 139:
        raise RuntimeError(f"expected 139 V18 UNKNOWN leaves, got {len(open_results)}")
    queue_by_id = {
        item["queue_id"]: item for item in queue_manifest["queue"]
    }
    for result in open_results:
        item = queue_by_id.get(result["queue_id"])
        if item is None:
            raise RuntimeError(f"missing V18 queue item {result['queue_id']}")
        if item["cube_literals"] != result["cube_literals"]:
            raise RuntimeError(f"cube mismatch for {result['queue_id']}")
    return queue_manifest, ledger, open_results, queue_by_id


def plan(
    *,
    v18_source: Path,
    v18_ledger_path: Path,
    v19_ledger_path: Path,
    cadical_source: Path | None,
    resume_ledger_path: Path | None,
    output: Path,
    matrix_output: Path,
    v18_run_id: str,
    v19_run_id: str,
) -> dict:
    queue_manifest, _, open_results, queue_by_id = validate_v18(
        v18_source=v18_source,
        v18_ledger_path=v18_ledger_path,
    )
    v19 = load_json(v19_ledger_path)
    if v19.get("logical_conclusion") != "V19_PILOT_COMPLETE_K16_OPEN":
        raise RuntimeError("unexpected V19 ledger conclusion")
    if v19.get("results_received") != 141 or v19.get("missing_task_ids"):
        raise RuntimeError("V19 ledger is incomplete")
    if v19.get("verified_sat_witnesses"):
        raise RuntimeError("V19 already contains a verified SAT witness")
    v19_closed = set(v19["parent_ids_closed_by_any_method"])
    if len(v19_closed) != 13:
        raise RuntimeError(f"expected 13 V19 exact closures, got {len(v19_closed)}")

    resume_closed: set[str] = set()
    resume_run_id = None
    resume_sha256 = None
    if resume_ledger_path is not None:
        resume = load_json(resume_ledger_path)
        if resume.get("schema") != FINAL_LEDGER_SCHEMA:
            raise RuntimeError("unexpected V20 resume ledger schema")
        if resume.get("verified_sat_witnesses"):
            raise RuntimeError("resume ledger already contains a verified SAT")
        resume_closed = set(resume.get("closed_queue_ids", []))
        resume_run_id = resume.get("workflow_run_id")
        resume_sha256 = sha256(resume_ledger_path)

    v18_open_ids = {result["queue_id"] for result in open_results}
    prior_closed = v19_closed | resume_closed
    unexpected = prior_closed - v18_open_ids
    if unexpected:
        raise RuntimeError(f"prior closures are outside V18 UNKNOWN: {unexpected}")

    remaining_ids = sorted(v18_open_ids - prior_closed)
    remaining = [queue_by_id[queue_id] for queue_id in remaining_ids]
    if resume_ledger_path is None and len(remaining) != 126:
        raise RuntimeError(f"fresh V20 should start with 126 leaves, got {len(remaining)}")

    output.mkdir(parents=True, exist_ok=True)
    copy_file_tree(v18_source / "bundle", output / "bundle")
    for box in ("a1_z3", "a2p_z4p"):
        destination = output / "boxes" / box
        destination.mkdir(parents=True, exist_ok=True)
        for name in ("enriched.cnf", "manifest.json"):
            shutil.copy2(v18_source / "boxes" / box / name, destination / name)
    if cadical_source is not None:
        cadical = locate_one(cadical_source, "cadical")
        destination = output / "cadical"
        destination.mkdir(parents=True, exist_ok=True)
        shutil.copy2(cadical, destination / "cadical")

    tasks = []
    for item in remaining:
        root_id = item["queue_id"]
        cube = list(item["cube_literals"])
        tasks.append(
            {
                "task_id": f"cadical720-{root_id}",
                "stage": "cadical",
                "method": "cadical720",
                "solver": "cadical",
                "seconds": CADICAL_SECONDS,
                "box": item["box"],
                "root_id": root_id,
                "root_kind": item["kind"],
                "cube_literals": cube,
                "cube_depth": len(cube),
                "cube_sha256": cube_hash(cube),
            }
        )
    tasks.sort(key=lambda task: task["task_id"])

    record = {
        "schema": PLAN_SCHEMA,
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "source_runs": {
            "v18": v18_run_id,
            "v19": v19_run_id,
            "resume_v20": resume_run_id,
        },
        "source_hashes": {
            "v18_queue_manifest": sha256(v18_source / "queue-manifest.json"),
            "v18_ledger": sha256(v18_ledger_path),
            "v19_ledger": sha256(v19_ledger_path),
            "resume_v20_ledger": resume_sha256,
        },
        "cadical": {
            "version": CADICAL_VERSION,
            "commit": CADICAL_COMMIT,
            "binary_sha256": (
                sha256(output / "cadical" / "cadical")
                if cadical_source is not None
                else None
            ),
        },
        "baseline": {
            "v18_unknown_leaves": len(open_results),
            "v19_exact_closed_leaves": len(v19_closed),
            "resume_exact_closed_leaves": len(resume_closed),
            "prior_exact_closed_union": len(prior_closed),
            "open_before_cadical": len(remaining),
        },
        "v18_open_queue_ids": sorted(v18_open_ids),
        "prior_closed_queue_ids": sorted(prior_closed),
        "cadical_tasks": tasks,
        "coverage": (
            "The CaDiCaL task cubes are exactly the V18 UNKNOWN queue minus "
            "every exact closure recorded by V19 and any supplied V20 resume "
            "ledger."
        ),
    }
    write_json(output / "v20-manifest.json", record)
    matrix = {
        "include": [
            {
                "task_id": task["task_id"],
                "box": task["box"],
            }
            for task in tasks
        ]
    }
    matrix_output.write_text(
        json.dumps(matrix, separators=(",", ":")) + "\n",
        encoding="utf-8",
    )
    print(
        json.dumps(
            {
                "v18_unknown": len(open_results),
                "prior_closed": len(prior_closed),
                "cadical_tasks": len(tasks),
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
    cnf = source / "boxes" / box / "enriched.cnf"
    work = result_path.parent.parent / "work" / task_id
    work.mkdir(parents=True, exist_ok=True)

    if task["solver"] == "cadical":
        assumption_cnf = work / "assumption.cnf"
        write_assumption_cnf(cnf, assumption_cnf, task["cube_literals"])
        command = [str(source / "cadical" / "cadical"), str(assumption_cnf)]
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
            timeout_seconds=seconds + 90,
        )
        matches = CUBE_RESULT.findall(text)
        raw_result = int(matches[-1]) if matches else 0
        status = {10: "SAT", 20: "UNSAT"}.get(raw_result, "UNKNOWN")
        arcs = parse_sms_arcs(text) if status == "SAT" else None
    else:
        raise RuntimeError(f"unknown solver {task['solver']}")

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
        "root_kind": task["root_kind"],
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
    plan_record = load_json(source / "v20-manifest.json")
    expected = {
        task["task_id"]: task for task in plan_record["cadical_tasks"]
    }
    records = collect_records(cadical_results_root)
    by_id = {record["task_id"]: record for record in records}
    missing = sorted(set(expected) - set(by_id))
    unexpected = sorted(set(by_id) - set(expected))
    if missing or unexpected:
        raise RuntimeError(
            f"CaDiCaL result mismatch: missing={missing}, unexpected={unexpected}"
        )
    verified_sat = [
        record["task_id"]
        for record in records
        if record["status"] == "SAT" and record.get("verified")
    ]
    bad_sat = [
        record["task_id"]
        for record in records
        if record["status"] == "SAT" and not record.get("verified")
    ]
    if bad_sat:
        raise RuntimeError(f"unverified CaDiCaL SAT records: {bad_sat}")

    unknown_roots = (
        []
        if verified_sat
        else sorted(
            record["root_id"]
            for record in records
            if record["status"] == "UNKNOWN"
        )
    )
    tasks_by_root = {
        task["root_id"]: task for task in plan_record["cadical_tasks"]
    }
    output.mkdir(parents=True, exist_ok=True)
    queue_path = output / "sms900.cubes"
    queue_path.write_text(
        (
            "\n".join(
                cube_line(tasks_by_root[root_id]["cube_literals"])
                for root_id in unknown_roots
            )
            + ("\n" if unknown_roots else "")
        ),
        encoding="utf-8",
    )
    sms_tasks = []
    for queue_line, root_id in enumerate(unknown_roots, start=1):
        parent = tasks_by_root[root_id]
        sms_tasks.append(
            {
                "task_id": f"sms900-{root_id}",
                "stage": "sms",
                "method": "sms900",
                "solver": "sms",
                "seconds": SMS_SECONDS,
                "box": parent["box"],
                "root_id": root_id,
                "root_kind": parent["root_kind"],
                "cube_literals": parent["cube_literals"],
                "cube_depth": parent["cube_depth"],
                "cube_sha256": parent["cube_sha256"],
                "queue_file": "sms900.cubes",
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
            "SMS tasks are exactly the CaDiCaL UNKNOWN records. SAT and "
            "UNSAT leaves are never resubmitted."
        ),
    }
    write_json(output / "v20-sms-manifest.json", sms_manifest)
    cadical_ledger = {
        "schema": CADICAL_LEDGER_SCHEMA,
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "expected_results": len(expected),
        "results_received": len(records),
        "missing_task_ids": missing,
        "statuses": dict(Counter(record["status"] for record in records)),
        "exact_closed_queue_ids": sorted(
            record["root_id"]
            for record in records
            if record["status"] == "UNSAT"
        ),
        "unknown_queue_ids": unknown_roots,
        "verified_sat_witnesses": verified_sat,
        "cpu_seconds": round(sum(float(r["seconds"]) for r in records), 3),
        "results": sorted(records, key=lambda record: record["task_id"]),
    }
    write_json(output / "v20-cadical-stage-ledger.json", cadical_ledger)
    matrix = {
        "include": [
            {"task_id": task["task_id"], "box": task["box"]}
            for task in sms_tasks
        ]
    }
    matrix_output.write_text(
        json.dumps(matrix, separators=(",", ":")) + "\n",
        encoding="utf-8",
    )
    print(
        json.dumps(
            {
                "cadical_statuses": cadical_ledger["statuses"],
                "sms_tasks": len(sms_tasks),
                "verified_sat": len(verified_sat),
            },
            indent=2,
        ),
        flush=True,
    )
    return cadical_ledger


def aggregate(
    *,
    source: Path,
    cadical_stage_ledger_path: Path,
    sms_results_root: Path,
    output: Path,
    workflow_run_id: str | None,
) -> dict:
    plan_record = load_json(source / "v20-manifest.json")
    cadical = load_json(cadical_stage_ledger_path)
    if cadical.get("schema") != CADICAL_LEDGER_SCHEMA:
        raise RuntimeError("unexpected CaDiCaL stage ledger")
    sms_records = collect_records(sms_results_root)
    sms_by_root = {record["root_id"]: record for record in sms_records}
    expected_sms = set(cadical["unknown_queue_ids"])
    missing_sms = sorted(expected_sms - set(sms_by_root))
    unexpected_sms = sorted(set(sms_by_root) - expected_sms)
    if missing_sms or unexpected_sms:
        raise RuntimeError(
            f"SMS result mismatch: missing={missing_sms}, unexpected={unexpected_sms}"
        )

    prior_closed = set(plan_record["prior_closed_queue_ids"])
    cadical_closed = set(cadical["exact_closed_queue_ids"])
    sms_closed = {
        record["root_id"]
        for record in sms_records
        if record["status"] == "UNSAT"
    }
    closed = prior_closed | cadical_closed | sms_closed
    all_open = set(plan_record["v18_open_queue_ids"])
    if not closed <= all_open:
        raise RuntimeError("V20 closure set escapes the V18 UNKNOWN frontier")
    remaining_open = sorted(all_open - closed)

    verified_sat = list(cadical["verified_sat_witnesses"]) + [
        record["task_id"]
        for record in sms_records
        if record["status"] == "SAT" and record.get("verified")
    ]
    bad_sms_sat = [
        record["task_id"]
        for record in sms_records
        if record["status"] == "SAT" and not record.get("verified")
    ]
    if bad_sms_sat:
        raise RuntimeError(f"unverified SMS SAT records: {bad_sms_sat}")

    if verified_sat:
        conclusion = "SAT_K16_VERIFIED"
    elif not remaining_open:
        conclusion = "V20_COMPLETE_FRONTIER_UNSAT"
    else:
        conclusion = "V20_COMPLETE_K16_OPEN"
    record = {
        "schema": FINAL_LEDGER_SCHEMA,
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "workflow_run_id": workflow_run_id,
        "source_runs": plan_record["source_runs"],
        "logical_conclusion": conclusion,
        "baseline": plan_record["baseline"],
        "cadical_stage": {
            "expected_results": cadical["expected_results"],
            "results_received": cadical["results_received"],
            "statuses": cadical["statuses"],
            "new_exact_closures": len(cadical_closed),
            "cpu_seconds": cadical["cpu_seconds"],
        },
        "sms_stage": {
            "expected_results": len(expected_sms),
            "results_received": len(sms_records),
            "missing_task_ids": missing_sms,
            "statuses": dict(Counter(r["status"] for r in sms_records)),
            "new_exact_closures": len(sms_closed),
            "cpu_seconds": round(
                sum(float(record["seconds"]) for record in sms_records),
                3,
            ),
        },
        "prior_closed_queue_ids": sorted(prior_closed),
        "cadical_closed_queue_ids": sorted(cadical_closed),
        "sms_closed_queue_ids": sorted(sms_closed),
        "closed_queue_ids": sorted(closed),
        "open_queue_ids": remaining_open,
        "closed_count": len(closed),
        "open_count": len(remaining_open),
        "verified_sat_witnesses": verified_sat,
        "next_action": (
            "If K16 remains open, pass only open_queue_ids to the next "
            "orthogonal solver or exact refinement. Reuse this ledger with "
            "--resume-ledger; never resubmit closed_queue_ids."
        ),
        "cadical_results": cadical["results"],
        "sms_results": sorted(sms_records, key=lambda item: item["task_id"]),
    }
    write_json(output, record)
    print(
        json.dumps(
            {
                "conclusion": conclusion,
                "prior_closed": len(prior_closed),
                "cadical_new_closed": len(cadical_closed),
                "sms_new_closed": len(sms_closed),
                "total_closed": len(closed),
                "remaining_open": len(remaining_open),
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
    parser.add_argument("--v18-source", type=Path)
    parser.add_argument("--v18-ledger", type=Path)
    parser.add_argument("--v19-ledger", type=Path)
    parser.add_argument("--resume-ledger", type=Path)
    parser.add_argument("--cadical-source", type=Path)
    parser.add_argument("--source", type=Path)
    parser.add_argument("--manifest", type=Path)
    parser.add_argument("--cadical-results-root", type=Path)
    parser.add_argument("--cadical-stage-ledger", type=Path)
    parser.add_argument("--sms-results-root", type=Path)
    parser.add_argument("--task-id")
    parser.add_argument("--result", type=Path)
    parser.add_argument("--log", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--matrix-output", type=Path)
    parser.add_argument("--v18-run-id", default="")
    parser.add_argument("--v19-run-id", default="")
    parser.add_argument("--workflow-run-id")
    args = parser.parse_args()

    if args.plan:
        plan(
            v18_source=args.v18_source,
            v18_ledger_path=args.v18_ledger,
            v19_ledger_path=args.v19_ledger,
            cadical_source=args.cadical_source,
            resume_ledger_path=args.resume_ledger,
            output=args.output,
            matrix_output=args.matrix_output,
            v18_run_id=args.v18_run_id,
            v19_run_id=args.v19_run_id,
        )
    elif args.solve:
        solve(
            source=args.source,
            manifest_path=args.manifest,
            task_id=args.task_id,
            result_path=args.result,
            log_path=args.log,
        )
    elif args.select_sms:
        select_sms(
            source=args.source,
            cadical_results_root=args.cadical_results_root,
            output=args.output,
            matrix_output=args.matrix_output,
        )
    else:
        aggregate(
            source=args.source,
            cadical_stage_ledger_path=args.cadical_stage_ledger,
            sms_results_root=args.sms_results_root,
            output=args.output,
            workflow_run_id=args.workflow_run_id,
        )


if __name__ == "__main__":
    main()
