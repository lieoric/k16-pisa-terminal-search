#!/usr/bin/env python3
"""Kaggle CPU benchmark for the h=15 and h=14 weighted frontier."""

from __future__ import annotations

import json
import subprocess
import sys
import urllib.request
from pathlib import Path


BRANCH = "agent/k16-endpoint-endgame"
RAW_ROOT = (
    "https://raw.githubusercontent.com/lieoric/"
    f"k16-pisa-terminal-search/{BRANCH}"
)
WORK = Path("/kaggle/working/k16-weighted-ladder")
WORK.mkdir(parents=True, exist_ok=True)

subprocess.run(
    [
        sys.executable,
        "-m",
        "pip",
        "install",
        "--disable-pip-version-check",
        "-q",
        "ortools==9.15.6755",
    ],
    check=True,
)

for relative in [
    "scripts/weighted_quotient_ladder.py",
    "pisa_verify.py",
]:
    target = WORK / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    urllib.request.urlretrieve(f"{RAW_ROOT}/{relative}", target)

results = []
for box in ["h15_p00", "h14_p00", "h14_p01"]:
    output = WORK / f"{box}.json"
    log = WORK / f"{box}.log"
    command = [
        sys.executable,
        str(WORK / "scripts" / "weighted_quotient_ladder.py"),
        "--box",
        box,
        "--seconds",
        "1800",
        "--workers",
        "4",
        "--output",
        str(output),
    ]
    with log.open("w", encoding="utf-8") as handle:
        completed = subprocess.run(
            command,
            stdout=handle,
            stderr=subprocess.STDOUT,
            text=True,
        )
    if output.exists():
        result = json.loads(output.read_text(encoding="utf-8"))
    else:
        result = {
            "box": box,
            "status": "ERROR",
            "returncode": completed.returncode,
        }
    results.append(result)
    print(
        f"{box}: {result['status']} "
        f"({result.get('wall_seconds', '?')}s)",
        flush=True,
    )
    if result["status"] == "SAT":
        break

summary = {
    "schema": "k16-weighted-ladder-kaggle-frontier-v1",
    "engine": "OR-Tools CP-SAT 9.15.6755",
    "accelerator": "None (CPU)",
    "boxes": results,
}
(Path("/kaggle/working") / "weighted_ladder_frontier_summary.json").write_text(
    json.dumps(summary, indent=2),
    encoding="utf-8",
)
print(json.dumps(summary, indent=2), flush=True)
