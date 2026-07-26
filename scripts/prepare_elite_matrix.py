#!/usr/bin/env python3
"""Collect the 64 v7 elite records into one deterministic matrix artifact."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("root", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--matrix-output", type=Path, required=True)
    return parser.parse_args()


def main():
    args = parse_args()
    records = []
    for path in args.root.rglob("result.json"):
        record = json.loads(path.read_text(encoding="utf-8"))
        if record.get("campaign") != "K16-PISA-v7-blocker-breakout-repair":
            continue
        records.append(record)
    records.sort(key=lambda record: int(record["shard"]))
    shards = [int(record["shard"]) for record in records]
    if shards != list(range(64)):
        raise RuntimeError(f"expected shards 0..63, got {shards}")

    payload = {
        "source_run": 30190571931,
        "records": records,
    }
    matrix = {
        "include": [{"shard": shard} for shard in shards],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.matrix_output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    args.matrix_output.write_text(
        json.dumps(matrix, separators=(",", ":")),
        encoding="utf-8",
    )
    print(
        f"ELITE_MATRIX_READY records={len(records)} "
        f"states={sum(int(record['states_evaluated']) for record in records)}"
    )


if __name__ == "__main__":
    main()
