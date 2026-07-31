#!/usr/bin/env python3
"""Generate and independently check proofs for the eight V24-D leaves."""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import time
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path

from k16_smart_deepen import sha256, write_json
from k16_staged_cascade import write_assumption_cnf


MODEL_VERSION = "k16-pisa-v24e-drat-lrat-certificates-20260731"
PLAN_SCHEMA = "k16-v24e-certificate-plan-v1"
RESULT_SCHEMA = "k16-v24e-certificate-result-v1"
LEDGER_SCHEMA = "k16-v24e-certificate-ledger-v1"
V24D_PLAN_SCHEMA = "k16-v24d-plan-v1"
V24D_LEDGER_SCHEMA = "k16-v24d-ledger-v1"
V24D_MODEL_VERSION = "k16-pisa-v24d-last-leaf-eight-way-20260731"
V24D_CONCLUSION = "V24D_ALL_676_PARTITION_LEAVES_EXACTLY_CLOSED"
EXPECTED_V24D_RUN = "30602758451"
EXPECTED_V24D_COMMIT = "7e639de2d6b68ec903e375c8f05dfa593b89f5d2"
DRAT_TRIM_COMMIT = "2e3b2dc0ecf938addbd779d42877b6ed69d9a985"
EXPECTED_PATHS = {
    "000",
    "001",
    "010",
    "011",
    "100",
    "101",
    "110",
    "111",
}
PLAN_FILENAME = "v24e-certificate-manifest.json"


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def collect_records(root: Path, schema: str) -> list[dict]:
    records = []
    for path in sorted(root.rglob("*.json")):
        record = load_json(path)
        if record.get("schema") == schema:
            records.append(record)
    identifiers = [record["task_id"] for record in records]
    if len(identifiers) != len(set(identifiers)):
        raise RuntimeError(f"duplicate {schema} identifiers")
    return records


def find_original_results(root: Path) -> list[dict]:
    return collect_records(root, "k16-v24d-result-v1")


def validate_v24d(
    source: Path,
    ledger_path: Path,
    original_results_root: Path,
) -> tuple[dict, dict, list[dict]]:
    plan = load_json(source / "v24d-manifest.json")
    ledger = load_json(ledger_path)
    if (
        plan.get("schema") != V24D_PLAN_SCHEMA
        or plan.get("model_version") != V24D_MODEL_VERSION
    ):
        raise RuntimeError("unexpected V24-D source manifest")
    if (
        ledger.get("schema") != V24D_LEDGER_SCHEMA
        or ledger.get("model_version") != V24D_MODEL_VERSION
        or ledger.get("logical_conclusion") != V24D_CONCLUSION
    ):
        raise RuntimeError("V24-D final ledger is not the closed endpoint")
    if (
        int(ledger.get("exact_partition_leaf_closures", -1)) != 676
        or int(ledger.get("open_partition_source_leaves", -1)) != 0
        or int(ledger.get("open_terminal_count", -1)) != 0
        or len(ledger.get("roots_exactly_excluded", [])) != 7
        or ledger.get("verified_sat_witnesses")
        or not ledger.get("final_v24c_leaf_closed")
    ):
        raise RuntimeError("unexpected V24-D final accounting")
    coverage = plan.get("coverage", {})
    if (
        not coverage.get("all_tree_audits_passed")
        or not ledger.get("coverage_audit", {}).get(
            "all_tree_audits_passed"
        )
    ):
        raise RuntimeError("V24-D eight-way coverage was not audited")

    tasks = sorted(plan["cadical_tasks"], key=lambda item: item["root_id"])
    if (
        len(tasks) != 8
        or {task["split_path"] for task in tasks} != EXPECTED_PATHS
        or len({task["cube_sha256"] for task in tasks}) != 8
    ):
        raise RuntimeError("V24-D is not the complete signed eight-way tree")

    embedded = {
        result["task_id"]: result for result in ledger["cadical_results"]
    }
    originals = find_original_results(original_results_root)
    original_by_id = {result["task_id"]: result for result in originals}
    expected_ids = {task["task_id"] for task in tasks}
    if set(embedded) != expected_ids or set(original_by_id) != expected_ids:
        raise RuntimeError("V24-D result set is incomplete")
    for task in tasks:
        for result in (embedded[task["task_id"]], original_by_id[task["task_id"]]):
            if (
                result.get("status") != "UNSAT"
                or result.get("returncode") != 20
                or result.get("raw_result") != 20
                or result.get("timed_out")
                or not result.get("solver_level_exact")
            ):
                raise RuntimeError(
                    f"V24-D result is not exact UNSAT: {task['task_id']}"
                )
            for key in (
                "root_id",
                "box",
                "split_path",
                "cube_literals",
                "cube_depth",
                "cube_sha256",
            ):
                if result[key] != task[key]:
                    raise RuntimeError(
                        f"V24-D task/result mismatch: {task['task_id']} {key}"
                    )
    if ledger.get("kissat_results"):
        raise RuntimeError("unexpected V24-D fallback results")
    return plan, ledger, tasks


def plan_campaign(
    *,
    v24d_source: Path,
    v24d_ledger: Path,
    original_results_root: Path,
    checker_root: Path,
    output: Path,
    matrix_path: Path,
    v24d_run_id: str,
    source_commit: str,
) -> dict:
    prior_plan, ledger, prior_tasks = validate_v24d(
        v24d_source,
        v24d_ledger,
        original_results_root,
    )
    if v24d_run_id != EXPECTED_V24D_RUN:
        raise RuntimeError("unexpected V24-D source run")
    if source_commit != EXPECTED_V24D_COMMIT:
        raise RuntimeError("unexpected V24-D source commit")
    output.mkdir(parents=True, exist_ok=True)
    (output / "solver").mkdir(parents=True, exist_ok=True)
    (output / "checker").mkdir(parents=True, exist_ok=True)
    (output / "assumptions").mkdir(parents=True, exist_ok=True)
    shutil.copy2(
        v24d_source / "cadical" / "cadical",
        output / "solver" / "cadical",
    )
    for name in ("drat-trim", "lrat-check"):
        source_binary = checker_root / name
        if not source_binary.is_file():
            raise RuntimeError(f"missing proof checker: {name}")
        shutil.copy2(source_binary, output / "checker" / name)
    box = prior_tasks[0]["box"]
    base_cnf = v24d_source / "boxes" / box / "enriched.cnf"
    if sha256(base_cnf) != prior_plan["source_hashes"]["theorem_cnf"][box]:
        raise RuntimeError("V24-D theorem CNF hash mismatch")

    tasks = []
    for prior in prior_tasks:
        assumption = output / "assumptions" / f"{prior['root_id']}.cnf"
        write_assumption_cnf(base_cnf, assumption, prior["cube_literals"])
        tasks.append(
            {
                "task_id": f"certificate-{prior['root_id']}",
                "root_id": prior["root_id"],
                "box": prior["box"],
                "split_path": prior["split_path"],
                "cube_literals": prior["cube_literals"],
                "cube_depth": prior["cube_depth"],
                "cube_sha256": prior["cube_sha256"],
                "assumption_cnf": f"assumptions/{prior['root_id']}.cnf",
                "assumption_cnf_sha256": sha256(assumption),
                "source_result_task_id": prior["task_id"],
                "artifact_name": f"v24e-certificate-{prior['root_id']}",
            }
        )

    original_files = sorted(
        path for path in original_results_root.rglob("*") if path.is_file()
    )
    frozen = output / "frozen-v24d"
    frozen.mkdir(parents=True, exist_ok=True)
    shutil.copy2(
        v24d_source / "v24d-manifest.json",
        frozen / "v24d-manifest.json",
    )
    shutil.copy2(v24d_ledger, frozen / "v24d-ledger.json")
    shutil.copytree(
        original_results_root,
        frozen / "original-results-and-logs",
        dirs_exist_ok=True,
    )
    record = {
        "schema": PLAN_SCHEMA,
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "v24d_run_id": v24d_run_id,
        "v24d_source_commit": source_commit,
        "drat_trim_commit": DRAT_TRIM_COMMIT,
        "source_hashes": {
            "v24d_manifest": sha256(v24d_source / "v24d-manifest.json"),
            "v24d_ledger": sha256(v24d_ledger),
            "theorem_cnf": sha256(base_cnf),
            "cadical": sha256(output / "solver" / "cadical"),
            "drat_trim": sha256(output / "checker" / "drat-trim"),
            "lrat_check": sha256(output / "checker" / "lrat-check"),
            "original_v24d_files": {
                str(path.relative_to(original_results_root)): sha256(path)
                for path in original_files
            },
        },
        "baseline": {
            "logical_conclusion": ledger["logical_conclusion"],
            "exact_partition_leaf_closures": 676,
            "roots_exactly_excluded": ledger["roots_exactly_excluded"],
            "open_terminal_count": 0,
        },
        "coverage": {
            "paths": sorted(EXPECTED_PATHS),
            "complete_binary_tree": True,
            "statement": (
                "The eight formulas are the complete three-level refinement "
                "of the sole V24-C UNKNOWN leaf."
            ),
        },
        "certificate_tasks": tasks,
    }
    write_json(output / PLAN_FILENAME, record)
    matrix_path.parent.mkdir(parents=True, exist_ok=True)
    matrix_path.write_text(
        json.dumps(
            {
                "include": [
                    {
                        "task_id": task["task_id"],
                        "root_id": task["root_id"],
                    }
                    for task in tasks
                ]
            },
            separators=(",", ":"),
        ),
        encoding="utf-8",
    )
    print(
        json.dumps(
            {
                "certificate_tasks": len(tasks),
                "paths": sorted(task["split_path"] for task in tasks),
                "v24d_exact_partition_leaves": 676,
                "checker_commit": DRAT_TRIM_COMMIT,
            },
            indent=2,
        ),
        flush=True,
    )
    return record


def run_logged(command: list[str], log: Path) -> tuple[int, float]:
    log.parent.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    with log.open("wb") as stream:
        completed = subprocess.run(
            command,
            stdout=stream,
            stderr=subprocess.STDOUT,
            check=False,
        )
    return completed.returncode, time.monotonic() - started


def compress_file(path: Path) -> tuple[Path, float]:
    compressed = path.with_suffix(path.suffix + ".zst")
    started = time.monotonic()
    completed = subprocess.run(
        ["zstd", "-T0", "-3", "-f", str(path), "-o", str(compressed)],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
    )
    if completed.returncode:
        raise RuntimeError(f"zstd failed for {path}: {completed.stdout}")
    return compressed, time.monotonic() - started


def certify_task(
    *,
    source: Path,
    task_id: str,
    output: Path,
) -> dict:
    plan = load_json(source / PLAN_FILENAME)
    matches = [
        task for task in plan["certificate_tasks"] if task["task_id"] == task_id
    ]
    if len(matches) != 1:
        raise RuntimeError(f"certificate task lookup failed: {task_id}")
    task = matches[0]
    for relative, expected in (
        ("solver/cadical", plan["source_hashes"]["cadical"]),
        ("checker/drat-trim", plan["source_hashes"]["drat_trim"]),
        ("checker/lrat-check", plan["source_hashes"]["lrat_check"]),
        (task["assumption_cnf"], task["assumption_cnf_sha256"]),
    ):
        if sha256(source / relative) != expected:
            raise RuntimeError(f"certificate source hash mismatch: {relative}")

    output.mkdir(parents=True, exist_ok=True)
    logs = output / "logs"
    proof = output / f"{task['root_id']}.drat"
    lrat = output / f"{task['root_id']}.lrat"
    cnf = source / task["assumption_cnf"]
    cadical_rc, cadical_seconds = run_logged(
        [str(source / "solver" / "cadical"), str(cnf), str(proof)],
        logs / "cadical.log",
    )
    if cadical_rc != 20 or not proof.is_file() or not proof.stat().st_size:
        raise RuntimeError("CaDiCaL did not emit an UNSAT proof")

    drat_rc, drat_seconds = run_logged(
        [
            str(source / "checker" / "drat-trim"),
            str(cnf),
            str(proof),
            "-L",
            str(lrat),
        ],
        logs / "drat-trim.log",
    )
    drat_log = (logs / "drat-trim.log").read_text(
        encoding="utf-8",
        errors="replace",
    )
    if (
        drat_rc != 0
        or "VERIFIED" not in drat_log
        or not lrat.is_file()
        or not lrat.stat().st_size
    ):
        raise RuntimeError("DRAT proof failed independent verification")

    lrat_rc, lrat_seconds = run_logged(
        [str(source / "checker" / "lrat-check"), str(cnf), str(lrat)],
        logs / "lrat-check.log",
    )
    lrat_log = (logs / "lrat-check.log").read_text(
        encoding="utf-8",
        errors="replace",
    )
    if lrat_rc != 0 or "VERIFIED" not in lrat_log:
        raise RuntimeError("LRAT proof failed independent verification")

    raw_proof_hash = sha256(proof)
    raw_lrat_hash = sha256(lrat)
    proof_bytes = proof.stat().st_size
    lrat_bytes = lrat.stat().st_size
    proof_zst, proof_compress_seconds = compress_file(proof)
    lrat_zst, lrat_compress_seconds = compress_file(lrat)
    proof.unlink()
    lrat.unlink()
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
                "raw_sha256": raw_proof_hash,
                "raw_bytes": proof_bytes,
                "compressed_file": proof_zst.name,
                "compressed_sha256": sha256(proof_zst),
                "compressed_bytes": proof_zst.stat().st_size,
                "compression_seconds": round(proof_compress_seconds, 3),
            },
            "lrat": {
                "raw_sha256": raw_lrat_hash,
                "raw_bytes": lrat_bytes,
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


def aggregate(
    *,
    source: Path,
    results_root: Path,
    output: Path,
    workflow_run_id: str,
) -> dict:
    plan = load_json(source / PLAN_FILENAME)
    expected = {
        task["task_id"]: task for task in plan["certificate_tasks"]
    }
    records = collect_records(results_root, RESULT_SCHEMA)
    by_id = {record["task_id"]: record for record in records}
    if set(by_id) != set(expected):
        raise RuntimeError(
            "certificate result mismatch: "
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
            "root_id",
            "split_path",
            "cube_sha256",
            "assumption_cnf_sha256",
        ):
            if record[key] != task[key]:
                raise RuntimeError(f"certificate provenance mismatch: {task_id}")

    record = {
        "schema": LEDGER_SCHEMA,
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "workflow_run_id": workflow_run_id,
        "logical_conclusion": "V24E_ALL_EIGHT_CERTIFICATES_VERIFIED",
        "v24d_run_id": plan["v24d_run_id"],
        "v24d_source_commit": plan["v24d_source_commit"],
        "v24d_computational_conclusion": plan["baseline"],
        "coverage": plan["coverage"],
        "certificate_statuses": dict(
            Counter(item["status"] for item in records)
        ),
        "certified_paths": sorted(item["split_path"] for item in records),
        "certificate_count": len(records),
        "drat_verified": sum(
            item["drat_trim"]["verified"] for item in records
        ),
        "lrat_verified": sum(
            item["lrat_check"]["verified"] for item in records
        ),
        "source_hashes": plan["source_hashes"],
        "results": sorted(records, key=lambda item: item["task_id"]),
        "scope_note": (
            "This ledger independently certifies the eight V24-D children "
            "that close the final original partition leaf. Publication-grade "
            "certification of the complete 676-leaf computation additionally "
            "requires certificates for the 675 previously closed leaves."
        ),
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    write_json(output, record)
    print(
        json.dumps(
            {
                "logical_conclusion": record["logical_conclusion"],
                "certificate_count": record["certificate_count"],
                "drat_verified": record["drat_verified"],
                "lrat_verified": record["lrat_verified"],
                "paths": record["certified_paths"],
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
    mode.add_argument("--certify", action="store_true")
    mode.add_argument("--aggregate", action="store_true")
    p.add_argument("--v24d-source", type=Path)
    p.add_argument("--v24d-ledger", type=Path)
    p.add_argument("--original-results-root", type=Path)
    p.add_argument("--checker-root", type=Path)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--matrix", type=Path)
    p.add_argument("--v24d-run-id")
    p.add_argument("--source-commit")
    p.add_argument("--source", type=Path)
    p.add_argument("--task-id")
    p.add_argument("--results-root", type=Path)
    p.add_argument("--workflow-run-id")
    return p


def main() -> None:
    args = parser().parse_args()
    if args.plan:
        plan_campaign(
            v24d_source=args.v24d_source,
            v24d_ledger=args.v24d_ledger,
            original_results_root=args.original_results_root,
            checker_root=args.checker_root,
            output=args.output,
            matrix_path=args.matrix,
            v24d_run_id=args.v24d_run_id,
            source_commit=args.source_commit,
        )
    elif args.certify:
        certify_task(
            source=args.source,
            task_id=args.task_id,
            output=args.output,
        )
    else:
        aggregate(
            source=args.source,
            results_root=args.results_root,
            output=args.output,
            workflow_run_id=args.workflow_run_id,
        )


if __name__ == "__main__":
    main()
