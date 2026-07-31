#!/usr/bin/env python3
"""Kaggle CPU pilot: refine only the six still-open v12 sample cubes.

The v12 cutoff-64 SMS partition is rebuilt and checked to contain exactly
9,788 canonical cubes. Two sample parents were already proved UNSAT by v12;
this campaign never reruns them. Each of the six UNKNOWN parents is split on
six still-free unordered tournament edges, giving 64 mutually exclusive and
exhaustive children per parent (384 total).

SAT is independently verified. A parent is closed only when all 64 children
are proved UNSAT. Timeout remains UNKNOWN and closes nothing.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import time
from pathlib import Path

import kaggle_v11_cpu_benchmark as base


REPO_ROOT = Path(__file__).resolve().parents[1]
WORK_ROOT = Path(
    os.environ.get("K16_KAGGLE_WORK", "/kaggle/working/k16-v13-adaptive")
)
RESULT_ROOT = Path(
    os.environ.get("K16_KAGGLE_RESULTS", "/kaggle/working/k16-v13-results")
)
FORMULA_ROOT = WORK_ROOT / "formula"
CUBE_ROOT = WORK_ROOT / "cubes"

PARENT_LINES = [1, 1399, 2797, 4195, 5594, 6992]
ALREADY_UNSAT_PARENT_LINES = [8390, 9788]
CUTOFF = 64
EXPECTED_CUBES = 9788
SPLIT_DEPTH = 6
CHILD_TIMEOUT_SECONDS = 12
WORKERS = max(1, min(4, os.cpu_count() or 2))

base.WORK_ROOT = WORK_ROOT
base.RESULT_ROOT = RESULT_ROOT
base.TOOLS_ROOT = WORK_ROOT / "tools"
base.FORMULA_ROOT = FORMULA_ROOT
base.CUBE_ROOT = CUBE_ROOT
base.PARTITION_TIMEOUT_SECONDS = 180
base.MAX_PARALLEL_CUBES = WORKERS


def run(command: list[str], *, timeout: int | None = None) -> None:
    print("+", " ".join(command), flush=True)
    completed = subprocess.run(
        command,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
        check=False,
    )
    if completed.stdout:
        print(completed.stdout, flush=True)
    if completed.returncode:
        raise RuntimeError(
            f"command failed with exit code {completed.returncode}: "
            + " ".join(command)
        )


def generate_hybrid_formula() -> tuple[Path, Path]:
    FORMULA_ROOT.mkdir(parents=True, exist_ok=True)
    cnf = FORMULA_ROOT / "k16-v12-hybrid.cnf"
    metadata = FORMULA_ROOT / "k16-v12-hybrid.json"
    run(
        [
            sys.executable,
            str(REPO_ROOT / "scripts" / "pisa_sat_v11.py"),
            "--n",
            "16",
            "--min-total-blockers",
            "16",
            "--endpoint-closures",
            "--cnf",
            str(cnf),
            "--metadata",
            str(metadata),
        ],
        timeout=900,
    )
    record = json.loads(metadata.read_text(encoding="utf-8"))
    if not record["cnf"]["endpoint_closures"]:
        raise RuntimeError("hybrid endpoint-closure metadata gate failed")
    if record["cnf"]["min_total_blockers"] != 16:
        raise RuntimeError("hybrid blocker-floor metadata gate failed")
    return cnf, metadata


def main() -> None:
    started = time.perf_counter()
    for directory in (WORK_ROOT, RESULT_ROOT, FORMULA_ROOT, CUBE_ROOT):
        directory.mkdir(parents=True, exist_ok=True)

    print("=" * 88)
    print("K16 PISA v13 adaptive UNKNOWN-cube pilot")
    print("GPU: not used")
    print("CPU workers:", WORKERS)
    print("parents:", PARENT_LINES)
    print(
        "refinement:",
        f"2^{SPLIT_DEPTH}={1 << SPLIT_DEPTH} children/parent,",
        f"{len(PARENT_LINES) << SPLIT_DEPTH} children total",
    )
    print("child timeout:", CHILD_TIMEOUT_SECONDS, "seconds")
    print("=" * 88, flush=True)

    base.ensure_dependencies()
    base.ensure_system_packages()
    sms = base.ensure_sms()

    # Two cheap, independent known-answer gates for the underlying encoding.
    gates = [base.direct_gate(8), base.direct_gate(15)]
    cnf, metadata = generate_hybrid_formula()
    partition = base.canonical_partition(sms, cnf, CUTOFF)
    if not partition["complete"]:
        raise RuntimeError("cutoff-64 SMS partition did not complete")
    if int(partition["cubes"]) != EXPECTED_CUBES:
        raise RuntimeError(
            f"expected {EXPECTED_CUBES} cutoff-64 cubes, "
            f"got {partition['cubes']}"
        )

    adaptive_output = RESULT_ROOT / "v13-adaptive-children.json"
    run(
        [
            sys.executable,
            str(REPO_ROOT / "scripts" / "adaptive_split_v13.py"),
            "--cnf",
            str(cnf),
            "--cube-file",
            str(partition["cube_file"]),
            "--parent-lines",
            ",".join(str(value) for value in PARENT_LINES),
            "--split-depth",
            str(SPLIT_DEPTH),
            "--child-timeout",
            str(CHILD_TIMEOUT_SECONDS),
            "--workers",
            str(WORKERS),
            "--output",
            str(adaptive_output),
        ],
        timeout=3600,
    )
    adaptive = json.loads(adaptive_output.read_text(encoding="utf-8"))

    counts = {
        status: sum(parent["counts"][status] for parent in adaptive["parents"])
        for status in ("sat", "unsat", "unknown", "error")
    }
    closed = [
        parent["parent_line"]
        for parent in adaptive["parents"]
        if parent["parent_closed"]
    ]
    summary = {
        "model_version": "k16-pisa-v13-kaggle-adaptive-pilot-20260727",
        "status": "SAT" if counts["sat"] else "PILOT_COMPLETE",
        "coverage": {
            "cutoff": CUTOFF,
            "canonical_partition_complete": True,
            "canonical_partition_cubes": EXPECTED_CUBES,
            "already_unsat_parent_lines": ALREADY_UNSAT_PARENT_LINES,
            "refined_parent_lines": PARENT_LINES,
            "split_depth": SPLIT_DEPTH,
            "children_per_parent": 1 << SPLIT_DEPTH,
            "children_total": len(PARENT_LINES) << SPLIT_DEPTH,
            "parents_closed_this_run": closed,
        },
        "gates": gates,
        "formula_metadata": json.loads(metadata.read_text(encoding="utf-8")),
        "counts": counts,
        "adaptive_result": str(adaptive_output),
        "wall_seconds": round(time.perf_counter() - started, 3),
    }
    output = RESULT_ROOT / "v13-kaggle-summary.json"
    output.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")

    print("=" * 88)
    print("FINAL COUNTS:", counts)
    print("PARENTS CLOSED:", closed)
    print("Saved:", output)
    print("Wall seconds:", summary["wall_seconds"])
    print("=" * 88, flush=True)


if __name__ == "__main__":
    main()
