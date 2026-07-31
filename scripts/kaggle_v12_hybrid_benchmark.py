#!/usr/bin/env python3
"""Short Kaggle CPU benchmark for the v12 hybrid K16 search.

The hybrid keeps the permutation-invariant v11 SAT formula and SMS
canonical cubing, then adds the exact v5/v6 endpoint closure:

* a remaining zero-margin endpoint has degree 7 and total B >= 16; or
* it has degree 6 and total B >= 20.

This is a benchmark, not a formal exhaustion.  It builds complete SMS
partitions at several deeper cutoffs and times a small stratified sample from
every complete partition.  SAT is independently verified; timeout is UNKNOWN.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

import kaggle_v11_cpu_benchmark as base


REPO_ROOT = Path(__file__).resolve().parents[1]
WORK_ROOT = Path(
    os.environ.get("K16_KAGGLE_WORK", "/kaggle/working/k16-v12-hybrid")
)
RESULT_ROOT = Path(
    os.environ.get("K16_KAGGLE_RESULTS", "/kaggle/working/k16-v12-results")
)
FORMULA_ROOT = WORK_ROOT / "formula"
CUBE_ROOT = WORK_ROOT / "cubes"

CUTOFFS = [32, 40, 48, 56, 64]
PARTITION_TIMEOUT_SECONDS = 180
CUBE_TIMEOUT_SECONDS = 30
CUBE_SAMPLE_SIZE = 8
MAX_PARALLEL_CUBES = max(1, min(4, os.cpu_count() or 2))

# Reuse the pinned dependency/SMS build and correctness-gate implementation,
# but keep v12 artifacts separate from the earlier benchmark.
base.WORK_ROOT = WORK_ROOT
base.RESULT_ROOT = RESULT_ROOT
base.TOOLS_ROOT = WORK_ROOT / "tools"
base.FORMULA_ROOT = FORMULA_ROOT
base.CUBE_ROOT = CUBE_ROOT
base.PARTITION_TIMEOUT_SECONDS = PARTITION_TIMEOUT_SECONDS
base.MAX_PARALLEL_CUBES = MAX_PARALLEL_CUBES


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def generate_k16_formula(
    name: str,
    *,
    minimum: int,
    endpoint_closures: bool,
) -> tuple[Path, dict]:
    FORMULA_ROOT.mkdir(parents=True, exist_ok=True)
    cnf = FORMULA_ROOT / f"{name}.cnf"
    metadata = FORMULA_ROOT / f"{name}.json"
    command = [
        sys.executable,
        str(REPO_ROOT / "scripts" / "pisa_sat_v11.py"),
        "--n",
        "16",
        "--min-total-blockers",
        str(minimum),
        "--cnf",
        str(cnf),
        "--metadata",
        str(metadata),
    ]
    if endpoint_closures:
        command.append("--endpoint-closures")
    completed = base.run(command, timeout=900)
    print(completed.stdout[-2000:], flush=True)
    record = load_json(metadata)
    if bool(record["cnf"]["endpoint_closures"]) != endpoint_closures:
        raise RuntimeError("endpoint closure metadata gate failed")
    return cnf, record


def solve_sample(
    cnf: Path,
    cube_file: Path,
    cutoff: int,
    line_number: int,
) -> dict:
    directory = RESULT_ROOT / f"cutoff-{cutoff}"
    directory.mkdir(parents=True, exist_ok=True)
    output = directory / f"cube-{line_number:06d}.json"
    command = [
        sys.executable,
        str(REPO_ROOT / "scripts" / "solve_cube_v11.py"),
        "--cnf",
        str(cnf),
        "--cube-file",
        str(cube_file),
        "--cube-line",
        str(line_number),
        "--n",
        "16",
        "--model-version",
        "k16-pisa-v12-hybrid-canonical-cube-cadical-20260727",
        "--result",
        str(output),
    ]
    started = time.perf_counter()
    try:
        completed = subprocess.run(
            command,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=CUBE_TIMEOUT_SECONDS,
            check=False,
        )
    except subprocess.TimeoutExpired:
        record = {
            "model_version": "k16-pisa-v12-hybrid-benchmark-20260727",
            "status": "UNKNOWN",
            "reason": "TIMEOUT",
            "seconds": CUBE_TIMEOUT_SECONDS,
            "cutoff": cutoff,
            "cube_line": line_number,
        }
        output.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
        return record

    if completed.returncode != 0 or not output.exists():
        record = {
            "model_version": "k16-pisa-v12-hybrid-benchmark-20260727",
            "status": "ERROR",
            "seconds": round(time.perf_counter() - started, 3),
            "cutoff": cutoff,
            "cube_line": line_number,
            "returncode": completed.returncode,
            "tail": completed.stdout[-2000:],
        }
        output.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
        return record

    record = load_json(output)
    record["cutoff"] = cutoff
    return record


def benchmark_partition(cnf: Path, partition: dict) -> dict:
    cutoff = int(partition["cutoff"])
    cube_file = Path(partition["cube_file"])
    lines = base.stratified_lines(partition["cubes"], CUBE_SAMPLE_SIZE)
    records: list[dict] = []
    print(
        f"BENCH cutoff={cutoff}: {len(lines)} cubes, "
        f"{MAX_PARALLEL_CUBES} workers, {CUBE_TIMEOUT_SECONDS}s each",
        flush=True,
    )
    with ThreadPoolExecutor(max_workers=MAX_PARALLEL_CUBES) as executor:
        futures = {
            executor.submit(
                solve_sample,
                cnf,
                cube_file,
                cutoff,
                line_number,
            ): line_number
            for line_number in lines
        }
        for future in as_completed(futures):
            record = future.result()
            records.append(record)
            print(
                "cube",
                cutoff,
                record.get("cube_line"),
                record.get("status"),
                record.get("seconds"),
                flush=True,
            )
            if record.get("status") == "SAT":
                for pending in futures:
                    pending.cancel()
                break

    records.sort(key=lambda record: int(record.get("cube_line", 0)))
    counts = {
        status.lower(): sum(record.get("status") == status for record in records)
        for status in ("SAT", "UNSAT", "UNKNOWN", "ERROR")
    }
    return {
        "cutoff": cutoff,
        "partition_cubes": partition["cubes"],
        "sample": records,
        "counts": counts,
    }


def choose_partition(benchmarks: list[dict]) -> dict | None:
    if not benchmarks:
        return None

    # Prefer a partition that proves more sampled cubes UNSAT.  Ties prefer
    # fewer timeouts, then the deeper split.
    return max(
        benchmarks,
        key=lambda item: (
            item["counts"]["unsat"],
            -item["counts"]["unknown"],
            item["cutoff"],
        ),
    )


def main() -> None:
    started = time.perf_counter()
    for directory in (WORK_ROOT, RESULT_ROOT, FORMULA_ROOT, CUBE_ROOT):
        directory.mkdir(parents=True, exist_ok=True)

    print("=" * 88)
    print("K16 PISA v12 hybrid: SMS symmetry + exact endpoint closures")
    print("GPU: not used")
    print("CPU workers:", MAX_PARALLEL_CUBES)
    print("cutoffs:", CUTOFFS)
    print("=" * 88, flush=True)

    base.ensure_dependencies()
    base.ensure_system_packages()
    sms = base.ensure_sms()

    # Base correctness gates remain closure-free so known K14/K15 witnesses
    # continue to exercise the underlying exact Pisa encoding.
    gates = [base.direct_gate(n) for n in (8, 14, 15)]
    k8_cnf, _ = base.generate_formula(8, opb=False)
    gates.append(base.sms_gate(sms, k8_cnf, 8))

    baseline_cnf, baseline_meta = generate_k16_formula(
        "k16-v11-baseline",
        minimum=10,
        endpoint_closures=False,
    )
    hybrid_cnf, hybrid_meta = generate_k16_formula(
        "k16-v12-hybrid",
        minimum=16,
        endpoint_closures=True,
    )

    partitions = [
        base.canonical_partition(sms, hybrid_cnf, cutoff)
        for cutoff in CUTOFFS
    ]
    complete = [
        partition
        for partition in partitions
        if partition["complete"] and partition["cubes"]
    ]
    benchmarks = [
        benchmark_partition(hybrid_cnf, partition)
        for partition in complete
    ]
    selected = choose_partition(benchmarks)

    all_samples = [
        record
        for benchmark in benchmarks
        for record in benchmark["sample"]
    ]
    status = (
        "SAT"
        if any(record.get("status") == "SAT" for record in all_samples)
        else "BENCHMARK_COMPLETE"
    )
    summary = {
        "model_version": "k16-pisa-v12-hybrid-benchmark-20260727",
        "status": status,
        "gpu_used": False,
        "cpu_workers": MAX_PARALLEL_CUBES,
        "sms_commit": base.SMS_COMMIT,
        "closure_basis": {
            "remaining_zero_types": [
                {"degree": 7, "blockers": 1, "minimum_total_blockers": 16},
                {"degree": 6, "blockers": 3, "minimum_total_blockers": 20},
            ],
            "vertex_label_invariant": True,
        },
        "gates": gates,
        "formula_comparison": {
            "v11_baseline": baseline_meta["cnf"],
            "v12_hybrid": hybrid_meta["cnf"],
            "baseline_path": str(baseline_cnf),
            "hybrid_path": str(hybrid_cnf),
        },
        "partitions": partitions,
        "benchmarks": benchmarks,
        "recommended_partition": selected,
        "wall_seconds": round(time.perf_counter() - started, 3),
    }
    output = RESULT_ROOT / "v12-hybrid-summary.json"
    output.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print("=" * 88)
    print("Recommended cutoff:", None if selected is None else selected["cutoff"])
    print("Final status:", status)
    print("Saved:", output)
    print("=" * 88, flush=True)


if __name__ == "__main__":
    main()
