#!/usr/bin/env python3
"""Kaggle CPU benchmark for the v11 symmetry-safe K16 Pisa encoding.

This is deliberately a benchmark, not a formal K16 campaign.  It:

1. installs the exact Python dependencies;
2. builds SAT Modulo Symmetries (SMS) and RoundingSat at pinned commits;
3. runs K8/K14/K15 correctness gates;
4. asks SMS for complete canonical K16 partitions at several edge depths;
5. times a stratified sample of residual cubes with ordinary CaDiCaL.

Every SAT result is independently verified.  A timed-out cube is recorded as
UNKNOWN and never counted as excluded.
"""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
WORK_ROOT = Path(os.environ.get("K16_KAGGLE_WORK", "/kaggle/working/k16-v11-benchmark"))
RESULT_ROOT = Path(os.environ.get("K16_KAGGLE_RESULTS", "/kaggle/working/k16-v11-results"))
TOOLS_ROOT = WORK_ROOT / "tools"
FORMULA_ROOT = WORK_ROOT / "formula"
CUBE_ROOT = WORK_ROOT / "cubes"

SMS_COMMIT = "464f12f1fd36b496e7ba9dcbb622b079de02dce4"
ROUNDINGSAT_COMMIT = "c445d271309201f4e08bd31b15997f9331afca53"
SIMPLE_CUTOFFS = [20, 24, 28, 32]
PARTITION_TIMEOUT_SECONDS = 180
CUBE_TIMEOUT_SECONDS = 120
CUBE_SAMPLE_SIZE = 16
MAX_PARALLEL_CUBES = max(1, min(4, os.cpu_count() or 2))


def run(
    command: list[str],
    *,
    cwd: Path | None = None,
    timeout: int | None = None,
    check: bool = True,
) -> subprocess.CompletedProcess[str]:
    print("+", " ".join(command), flush=True)
    return subprocess.run(
        command,
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
        check=check,
    )


def ensure_dependencies() -> None:
    run(
        [
            sys.executable,
            "-m",
            "pip",
            "install",
            "-q",
            "-r",
            str(REPO_ROOT / "requirements.txt"),
            "-r",
            str(REPO_ROOT / "requirements-sat.txt"),
        ],
        timeout=600,
    )


def ensure_system_packages() -> None:
    """Install the small native build toolchain used by SMS on Kaggle."""
    if not shutil.which("apt-get"):
        return
    run(["apt-get", "update", "-qq"], timeout=600)
    run(
        [
            "apt-get",
            "install",
            "-y",
            "-qq",
            "build-essential",
            "cmake",
            "libboost-graph-dev",
            "libboost-program-options-dev",
        ],
        timeout=900,
    )


def ensure_sms() -> Path:
    sms_root = TOOLS_ROOT / "sms"
    binary = sms_root / "build" / "smsg"
    if binary.exists():
        return binary

    TOOLS_ROOT.mkdir(parents=True, exist_ok=True)
    if not sms_root.exists():
        run(
            [
                "git",
                "clone",
                "--recursive",
                "https://github.com/markirch/sat-modulo-symmetries.git",
                str(sms_root),
            ],
            timeout=600,
        )
    run(["git", "checkout", SMS_COMMIT], cwd=sms_root, timeout=120)
    run(["git", "submodule", "update", "--init", "--recursive"], cwd=sms_root, timeout=300)

    cadical_root = sms_root / "cadical_sms"
    run(["./configure", "-fPIC"], cwd=cadical_root, timeout=120)
    run(["make", f"-j{MAX_PARALLEL_CUBES}"], cwd=cadical_root, timeout=900)
    run(
        ["cmake", "-S", ".", "-B", "build", "-DCMAKE_BUILD_TYPE=Release"],
        cwd=sms_root,
        timeout=300,
    )
    run(
        ["cmake", "--build", "build", f"-j{MAX_PARALLEL_CUBES}"],
        cwd=sms_root,
        timeout=900,
    )
    if not binary.exists():
        raise RuntimeError("SMS build did not create smsg")
    return binary


def ensure_roundingsat() -> Path:
    source = TOOLS_ROOT / "roundingsat"
    binary = source / "roundingsat"
    if binary.exists():
        return binary

    TOOLS_ROOT.mkdir(parents=True, exist_ok=True)
    if not source.exists():
        run(
            [
                "git",
                "clone",
                "https://github.com/StephanGocht/RoundingSat.git",
                str(source),
            ],
            timeout=600,
        )
    run(["git", "checkout", ROUNDINGSAT_COMMIT], cwd=source, timeout=120)

    # Current GCC exposes a missing direct <cstdint> include in the pinned tree.
    run(
        [
            "make",
            f"-j{MAX_PARALLEL_CUBES}",
            "CXXFLAGS=-O3 -DNDEBUG -include cstdint",
        ],
        cwd=source,
        timeout=900,
    )
    if not binary.exists():
        candidates = [
            candidate
            for candidate in source.rglob("roundingsat")
            if candidate.is_file()
        ]
        if candidates:
            shutil.copy2(candidates[0], binary)
    if not binary.exists():
        raise RuntimeError("RoundingSat build did not create roundingsat")
    return binary


def generate_formula(n: int, *, opb: bool = False) -> tuple[Path, Path]:
    FORMULA_ROOT.mkdir(parents=True, exist_ok=True)
    cnf = FORMULA_ROOT / f"k{n}.cnf"
    opb_path = FORMULA_ROOT / f"k{n}.opb"
    meta = FORMULA_ROOT / f"k{n}.json"
    command = [
        sys.executable,
        str(REPO_ROOT / "scripts" / "pisa_sat_v11.py"),
        "--n",
        str(n),
        "--min-total-blockers",
        "10" if n == 16 else "0",
        "--cnf",
        str(cnf),
        "--metadata",
        str(meta),
    ]
    if opb:
        command += ["--opb", str(opb_path)]
    completed = run(command, timeout=600)
    print(completed.stdout[-2000:], flush=True)
    return cnf, opb_path


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def direct_gate(n: int) -> dict:
    output = RESULT_ROOT / f"gate-k{n}-cadical.json"
    started = time.perf_counter()
    completed = run(
        [
            sys.executable,
            str(REPO_ROOT / "scripts" / "pisa_sat_v11.py"),
            "--n",
            str(n),
            "--min-total-blockers",
            "0",
            "--solve",
            "--solver",
            "cadical195",
            "--result",
            str(output),
        ],
        timeout=300,
    )
    print(completed.stdout[-3000:], flush=True)
    record = load_json(output)
    record["wall_seconds"] = round(time.perf_counter() - started, 3)
    expected = "UNSAT" if n == 8 else "SAT"
    if record["status"] != expected:
        raise RuntimeError(f"K{n} direct gate expected {expected}, got {record['status']}")
    if expected == "SAT" and not record.get("verified"):
        raise RuntimeError(f"K{n} direct SAT gate was not verified")
    return record


def sms_gate(binary: Path, cnf: Path, n: int) -> dict:
    started = time.perf_counter()
    completed = run(
        [str(binary), "--vertices", str(n), "--directed", "--dimacs", str(cnf)],
        timeout=300,
        check=False,
    )
    text = completed.stdout
    (RESULT_ROOT / f"gate-k{n}-sms.log").write_text(text, encoding="utf-8")
    if re.search(r"\bs UNSATISFIABLE\b", text):
        status = "UNSAT"
    elif re.search(r"\bs SATISFIABLE\b", text) or re.search(r"\bResult:\s*10\b", text):
        status = "SAT"
    elif re.search(r"\bResult:\s*20\b", text):
        status = "UNSAT"
    else:
        status = "UNKNOWN"
    expected = "UNSAT" if n == 8 else "SAT"
    if status != expected:
        raise RuntimeError(f"K{n} SMS gate expected {expected}, got {status}")
    return {
        "solver": "sms",
        "n": n,
        "status": status,
        "seconds": round(time.perf_counter() - started, 3),
        "returncode": completed.returncode,
    }


def pb_gate(binary: Path, opb: Path, n: int) -> dict:
    started = time.perf_counter()
    completed = run([str(binary), str(opb)], timeout=300, check=False)
    text = completed.stdout
    (RESULT_ROOT / f"gate-k{n}-roundingsat.log").write_text(text, encoding="utf-8")
    if "UNSATISFIABLE" in text:
        status = "UNSAT"
    elif "SATISFIABLE" in text:
        status = "SAT"
    else:
        status = "UNKNOWN"
    expected = "UNSAT" if n == 8 else "SAT"
    if status != expected:
        raise RuntimeError(f"K{n} RoundingSat gate expected {expected}, got {status}")
    return {
        "solver": "roundingsat",
        "n": n,
        "status": status,
        "seconds": round(time.perf_counter() - started, 3),
        "returncode": completed.returncode,
    }


def extract_cubes(text: str) -> list[str]:
    return [
        line.strip().lstrip("\ufeff")
        for line in text.splitlines()
        if line.strip().lstrip("\ufeff").startswith("a ")
        and line.strip().endswith(" 0")
    ]


def canonical_partition(binary: Path, cnf: Path, cutoff: int) -> dict:
    CUBE_ROOT.mkdir(parents=True, exist_ok=True)
    started = time.perf_counter()
    command = [
        str(binary),
        "--vertices",
        "16",
        "--directed",
        "--dimacs",
        str(cnf),
        "--simple-assignment-cutoff",
        str(cutoff),
        "--timeout",
        str(PARTITION_TIMEOUT_SECONDS),
    ]
    completed = run(
        command,
        timeout=PARTITION_TIMEOUT_SECONDS + 30,
        check=False,
    )
    seconds = time.perf_counter() - started
    log = CUBE_ROOT / f"simple-{cutoff}.log"
    log.write_text(completed.stdout, encoding="utf-8")
    cubes = extract_cubes(completed.stdout)
    cube_file = CUBE_ROOT / f"simple-{cutoff}.cubes"
    cube_file.write_text("\n".join(cubes) + ("\n" if cubes else ""), encoding="utf-8")
    complete = bool(re.search(r"\bResult:\s*20\b", completed.stdout))
    record = {
        "cutoff": cutoff,
        "status": "COMPLETE_PARTITION" if complete else "UNKNOWN",
        "complete": complete,
        "cubes": len(cubes),
        "seconds": round(seconds, 3),
        "returncode": completed.returncode,
        "cube_file": str(cube_file),
    }
    print(json.dumps(record, indent=2), flush=True)
    return record


def stratified_lines(total: int, wanted: int) -> list[int]:
    if total <= wanted:
        return list(range(1, total + 1))
    indices = {
        1 + round(position * (total - 1) / (wanted - 1))
        for position in range(wanted)
    }
    return sorted(indices)


def solve_sample(cnf: Path, cube_file: Path, line_number: int) -> dict:
    output = RESULT_ROOT / f"cube-{line_number:06d}.json"
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
            "model_version": "k16-pisa-v11-kaggle-cube-benchmark-20260727",
            "status": "UNKNOWN",
            "reason": "TIMEOUT",
            "seconds": CUBE_TIMEOUT_SECONDS,
            "cube_line": line_number,
        }
        output.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
        return record
    if completed.returncode != 0 or not output.exists():
        record = {
            "model_version": "k16-pisa-v11-kaggle-cube-benchmark-20260727",
            "status": "ERROR",
            "seconds": round(time.perf_counter() - started, 3),
            "cube_line": line_number,
            "returncode": completed.returncode,
            "tail": completed.stdout[-2000:],
        }
        output.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
        return record
    return load_json(output)


def benchmark_cubes(cnf: Path, partition: dict) -> list[dict]:
    cube_file = Path(partition["cube_file"])
    lines = stratified_lines(partition["cubes"], CUBE_SAMPLE_SIZE)
    print(
        f"Benchmarking {len(lines)} stratified cubes at cutoff "
        f"{partition['cutoff']} with {MAX_PARALLEL_CUBES} CPU workers",
        flush=True,
    )
    records: list[dict] = []
    with ThreadPoolExecutor(max_workers=MAX_PARALLEL_CUBES) as executor:
        futures = {
            executor.submit(solve_sample, cnf, cube_file, line): line
            for line in lines
        }
        for future in as_completed(futures):
            record = future.result()
            records.append(record)
            print(
                "cube",
                record.get("cube_line"),
                record.get("status"),
                record.get("seconds"),
                flush=True,
            )
            if record.get("status") == "SAT":
                # One independently verified witness settles the user's goal.
                for pending in futures:
                    pending.cancel()
                break
    return sorted(records, key=lambda record: int(record.get("cube_line", 0)))


def main() -> None:
    started = time.perf_counter()
    for directory in (WORK_ROOT, RESULT_ROOT, FORMULA_ROOT, CUBE_ROOT):
        directory.mkdir(parents=True, exist_ok=True)

    print("=" * 88)
    print("K16 PISA v11 — Kaggle CPU symmetry/cubing benchmark")
    print("GPU: not used")
    print("CPU workers:", MAX_PARALLEL_CUBES)
    print("cube timeout:", CUBE_TIMEOUT_SECONDS, "seconds")
    print("=" * 88, flush=True)

    ensure_dependencies()
    ensure_system_packages()
    sms = ensure_sms()
    roundingsat = ensure_roundingsat()

    gates = [direct_gate(n) for n in (8, 14, 15)]
    k8_cnf, k8_opb = generate_formula(8, opb=True)
    gates.append(sms_gate(sms, k8_cnf, 8))
    gates.append(pb_gate(roundingsat, k8_opb, 8))

    k16_cnf, _ = generate_formula(16, opb=False)
    partitions = [
        canonical_partition(sms, k16_cnf, cutoff)
        for cutoff in SIMPLE_CUTOFFS
    ]
    complete = [record for record in partitions if record["complete"] and record["cubes"]]
    if not complete:
        cube_results: list[dict] = []
        selected = None
    else:
        # Prefer the deepest complete partition unless it grows beyond a
        # practical artifact size.
        practical = [record for record in complete if record["cubes"] <= 20_000]
        selected = max(practical or complete, key=lambda record: record["cutoff"])
        cube_results = benchmark_cubes(k16_cnf, selected)

    summary = {
        "model_version": "k16-pisa-v11-kaggle-cpu-benchmark-20260727",
        "status": (
            "SAT"
            if any(record.get("status") == "SAT" for record in cube_results)
            else "BENCHMARK_COMPLETE"
        ),
        "gpu_used": False,
        "cpu_workers": MAX_PARALLEL_CUBES,
        "sms_commit": SMS_COMMIT,
        "roundingsat_commit": ROUNDINGSAT_COMMIT,
        "gates": gates,
        "partitions": partitions,
        "selected_partition": selected,
        "cube_sample": cube_results,
        "cube_counts": {
            "sat": sum(record.get("status") == "SAT" for record in cube_results),
            "unsat": sum(record.get("status") == "UNSAT" for record in cube_results),
            "unknown": sum(record.get("status") == "UNKNOWN" for record in cube_results),
            "error": sum(record.get("status") == "ERROR" for record in cube_results),
        },
        "wall_seconds": round(time.perf_counter() - started, 3),
    }
    summary_path = RESULT_ROOT / "benchmark-summary.json"
    summary_path.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print("=" * 88)
    print(json.dumps(summary["cube_counts"], indent=2))
    print("Saved:", summary_path)
    print("Final status:", summary["status"])
    print("=" * 88, flush=True)


if __name__ == "__main__":
    main()
