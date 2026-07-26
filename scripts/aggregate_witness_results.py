#!/usr/bin/env python3
"""Aggregate witness-hunter shard artifacts without treating misses as errors."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("root", type=Path)
    parser.add_argument("--output", type=Path, default=Path("witness-summary.json"))
    args = parser.parse_args()

    records = []
    for path in sorted(args.root.rglob("*.json")):
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        if data.get("campaign") != "K16-PISA-v5":
            continue
        data["_artifact_path"] = str(path)
        records.append(data)

    witnesses = [record for record in records if record.get("status") == "WITNESS"]
    best = min(records, key=lambda record: record.get("best_loss", 10**18), default=None)
    summary = {
        "campaign": "K16-PISA-v5",
        "shards_collected": len(records),
        "witnesses": len(witnesses),
        "status": "WITNESS" if witnesses else "NO_WITNESS_IN_COMPLETED_SHARDS",
        "states_evaluated": sum(int(r.get("states_evaluated", 0)) for r in records),
        "best": best,
        "witness_records": witnesses,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")

    print("## K16 Pisa witness campaign")
    print()
    print(f"- Shards collected: **{len(records)}**")
    print(f"- States evaluated: **{summary['states_evaluated']:,}**")
    print(f"- Verified witnesses: **{len(witnesses)}**")
    if best:
        print(
            f"- Best loss: **{best.get('best_loss')}** "
            f"({best.get('strategy')}, shard {best.get('shard')})"
        )
    print()
    if witnesses:
        print("**A verified K16 Pisa witness was found.**")
    else:
        print("No witness was found in the completed heuristic shards; this is not an UNSAT proof.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
