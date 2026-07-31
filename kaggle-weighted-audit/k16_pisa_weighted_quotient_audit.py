"""Kaggle launcher for the independent K16 weighted quotient audit."""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path


REPOSITORY = "https://github.com/lieoric/k16-pisa-terminal-search.git"
BRANCH = "agent/k16-endpoint-endgame"
SOURCE = Path("/kaggle/temp/k16-pisa-terminal-search")


def run(command: list[str], cwd: Path | None = None) -> None:
    print("+", " ".join(command), flush=True)
    subprocess.run(command, cwd=cwd, check=True)


if SOURCE.exists():
    run(["git", "fetch", "origin", BRANCH], cwd=SOURCE)
    run(["git", "checkout", "-f", BRANCH], cwd=SOURCE)
    run(["git", "reset", "--hard", f"origin/{BRANCH}"], cwd=SOURCE)
else:
    run(
        [
            "git",
            "clone",
            "--depth",
            "1",
            "--branch",
            BRANCH,
            REPOSITORY,
            str(SOURCE),
        ]
    )

run(
    [
        sys.executable,
        str(SOURCE / "scripts" / "weighted_quotient_audit.py"),
        "--repo-root",
        str(SOURCE),
        "--output-dir",
        "/kaggle/working",
        "--threads",
        "4",
    ],
    cwd=SOURCE,
)
