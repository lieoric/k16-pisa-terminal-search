#!/usr/bin/env python3
"""Aggregate logical SAT/UNSAT/UNKNOWN states without conflating CI success."""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("root", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--label", required=True)
    parser.add_argument("--expected", type=int)
    return parser.parse_args()


def main():
    args = parse_args()
    records = []
    for path in args.root.rglob("result.json"):
        record = json.loads(path.read_text(encoding="utf-8"))
        if "status" in record:
            records.append(record)
    counts = Counter(record["status"] for record in records)
    witnesses = [
        record for record in records if record["status"] == "SAT"
    ]
    summary = {
        "label": args.label,
        "records": len(records),
        "expected_records": args.expected,
        "complete": args.expected is None or len(records) == args.expected,
        "status_counts": dict(sorted(counts.items())),
        "witnesses": witnesses,
        "all_exactly_closed": bool(records)
        and (args.expected is None or len(records) == args.expected)
        and all(record["status"] == "UNSAT" for record in records),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(summary, indent=2), encoding="utf-8")

    print(f"## {args.label}")
    print()
    print(f"- Records: **{len(records)}**")
    if args.expected is not None:
        print(f"- Expected records: **{args.expected}**")
        print(f"- Complete artifact set: **{summary['complete']}**")
    for status, count in sorted(counts.items()):
        print(f"- {status}: **{count}**")
    print(f"- Verified witnesses: **{len(witnesses)}**")
    print(
        "- All submitted boxes exactly closed: "
        f"**{summary['all_exactly_closed']}**"
    )
    if witnesses:
        print()
        print("**A verified K16 Pisa witness was found.**")
    elif counts.get("UNKNOWN"):
        print()
        print("UNKNOWN boxes remain open; CI success is not an UNSAT result.")


if __name__ == "__main__":
    main()
