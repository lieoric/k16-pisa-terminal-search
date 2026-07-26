#!/usr/bin/env python3
"""Prepare and run the Kaggle half of the v14 resumable 8-hour campaign."""

from __future__ import annotations

import json
import shutil
import subprocess
import sys
import time
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
WORK_ROOT = Path("/kaggle/working/k16-pisa-v14")
INPUT_ROOT = Path("/kaggle/input")
SMS_COMMIT = "464f12f1fd36b496e7ba9dcbb622b079de02dce4"
TOTAL_BUDGET_SECONDS = 8 * 60 * 60
SHUTDOWN_RESERVE_SECONDS = 15 * 60


def run(command: list[str], *, cwd: Path | None = None) -> None:
    print("+", " ".join(command), flush=True)
    subprocess.run(command, cwd=cwd, check=True)


def find_resume_checkpoint() -> Path | None:
    if not INPUT_ROOT.exists():
        return None
    candidates = sorted(
        INPUT_ROOT.rglob("kaggle-v14-checkpoint.json"),
        key=lambda path: path.stat().st_mtime,
        reverse=True,
    )
    return candidates[0] if candidates else None


def build_sms(binary: Path) -> None:
    if binary.exists():
        return
    tools = WORK_ROOT / "tools"
    source = tools / "sms"
    tools.mkdir(parents=True, exist_ok=True)
    if not source.exists():
        run(
            [
                "git",
                "clone",
                "--recursive",
                "https://github.com/markirch/sat-modulo-symmetries.git",
                str(source),
            ]
        )
    run(["git", "checkout", SMS_COMMIT], cwd=source)
    run(["git", "submodule", "update", "--init", "--recursive"], cwd=source)
    run(["bash", "-lc", "./configure -fPIC && make -j4"], cwd=source / "cadical_sms")
    run(
        [
            "cmake",
            "-S",
            str(source),
            "-B",
            str(source / "build"),
            "-DCMAKE_BUILD_TYPE=Release",
        ]
    )
    run(["cmake", "--build", str(source / "build"), "-j4"])


def ensure_system_packages() -> None:
    if not shutil.which("apt-get"):
        return
    run(["apt-get", "update", "-qq"])
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
        ]
    )


def prepare_exact_inputs(cnf: Path, cubes: Path) -> None:
    prepared = cnf.parent
    prepared.mkdir(parents=True, exist_ok=True)
    if not cnf.exists():
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
                str(prepared / "k16-v12-hybrid.json"),
            ]
        )
    if cubes.exists():
        return
    log_path = prepared / "cutoff-64.log"
    binary = WORK_ROOT / "tools" / "sms" / "build" / "src" / "smsg"
    with log_path.open("w", encoding="utf-8") as stream:
        completed = subprocess.run(
            [
                str(binary),
                "--vertices",
                "16",
                "--directed",
                "--dimacs",
                str(cnf),
                "--simple-assignment-cutoff",
                "64",
                "--timeout",
                "180",
            ],
            stdout=stream,
            stderr=subprocess.STDOUT,
            check=False,
        )
    if completed.returncode != 20:
        raise RuntimeError(
            f"SMS partition returned {completed.returncode}, expected 20"
        )
    log = log_path.read_text(encoding="utf-8")
    cube_lines = [
        line.strip().lstrip("\ufeff")
        for line in log.splitlines()
        if line.strip().lstrip("\ufeff").startswith("a ")
        and line.strip().endswith(" 0")
    ]
    if "Result: 20" not in log or len(cube_lines) != 9788:
        raise RuntimeError(
            f"incomplete partition: result20={'Result: 20' in log} "
            f"cubes={len(cube_lines)}"
        )
    cubes.write_text("\n".join(cube_lines) + "\n", encoding="utf-8")


def main() -> int:
    campaign_started = time.monotonic()
    WORK_ROOT.mkdir(parents=True, exist_ok=True)
    prepared = WORK_ROOT / "prepared"
    result_dir = WORK_ROOT / "results"
    result_dir.mkdir(parents=True, exist_ok=True)

    run(
        [
            sys.executable,
            "-m",
            "pip",
            "install",
            "-q",
            "-r",
            str(REPO_ROOT / "requirements-sat.txt"),
        ]
    )
    ensure_system_packages()
    binary = WORK_ROOT / "tools" / "sms" / "build" / "src" / "smsg"
    build_sms(binary)

    cnf = prepared / "k16-v12-hybrid.cnf"
    cubes = prepared / "cutoff-64.cubes"
    prepare_exact_inputs(cnf, cubes)

    checkpoint = result_dir / "kaggle-v14-checkpoint.json"
    resume_source = find_resume_checkpoint()
    if resume_source and not checkpoint.exists():
        shutil.copy2(resume_source, checkpoint)
        print("RESUME_FROM", resume_source, flush=True)
    else:
        print("RESUME_FROM", "new campaign", flush=True)

    setup_seconds = time.monotonic() - campaign_started
    solver_wall = int(
        TOTAL_BUDGET_SECONDS
        - SHUTDOWN_RESERVE_SECONDS
        - setup_seconds
    )
    if solver_wall <= 300:
        raise RuntimeError(
            f"setup consumed too much of the 8-hour budget: {setup_seconds:.1f}s"
        )

    summary = result_dir / "kaggle-v14-summary.json"
    print(
        "KAGGLE_V14_START",
        json.dumps(
            {
                "total_budget_seconds": TOTAL_BUDGET_SECONDS,
                "setup_seconds": round(setup_seconds, 3),
                "solver_wall_seconds": solver_wall,
                "partition": "odd source indexes (disjoint from GitHub)",
                "workers": 4,
                "slice_seconds": 180,
            }
        ),
        flush=True,
    )
    run(
        [
            sys.executable,
            str(REPO_ROOT / "scripts" / "resumable_refinement_v14.py"),
            "--cnf",
            str(cnf),
            "--cube-file",
            str(cubes),
            "--manifest",
            str(
                REPO_ROOT
                / "campaigns"
                / "v14-kaggle-338156810-residuals.json"
            ),
            "--checkpoint",
            str(checkpoint),
            "--output",
            str(summary),
            "--partition-count",
            "2",
            "--partition-index",
            "1",
            "--shard-count",
            "1",
            "--shard-index",
            "0",
            "--pre-split-depth",
            "3",
            "--slice-seconds",
            "180",
            "--wall-seconds",
            str(solver_wall),
            "--workers",
            "4",
        ]
    )

    continuation = {
        "model_version": "k16-pisa-v14-kaggle-resumable-8h-20260727",
        "status": json.loads(summary.read_text())["status"],
        "checkpoint_file": str(checkpoint),
        "summary_file": str(summary),
        "how_to_continue": (
            "Add the previous notebook output as a Kaggle input and run "
            "this notebook again. It scans /kaggle/input for "
            "kaggle-v14-checkpoint.json and resumes only pending leaves."
        ),
        "campaign_wall_seconds": round(time.monotonic() - campaign_started, 3),
    }
    (result_dir / "continuation.json").write_text(
        json.dumps(continuation, indent=2) + "\n",
        encoding="utf-8",
    )
    print("KAGGLE_V14_DONE", json.dumps(continuation), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
