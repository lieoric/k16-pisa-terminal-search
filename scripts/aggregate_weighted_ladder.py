#!/usr/bin/env python3
"""Aggregate the 29 exact weighted-quotient pattern results."""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path

from weighted_quotient_ladder import pattern_table


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input_dir", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    expected = {record["box"] for record in pattern_table()}
    by_box = {}
    duplicates = []
    for path in sorted(args.input_dir.rglob("result.json")):
        record = json.loads(path.read_text(encoding="utf-8"))
        box = record.get("box")
        if box in by_box:
            duplicates.append(box)
        by_box[box] = record

    returned = set(by_box) & expected
    missing = sorted(expected - returned)
    unexpected = sorted(set(by_box) - expected)
    statuses = Counter(
        by_box[box].get("status", "ERROR")
        for box in returned
    )
    sat_boxes = sorted(
        box for box in returned if by_box[box].get("status") == "SAT"
    )
    unknown_boxes = sorted(
        box for box in returned if by_box[box].get("status") == "UNKNOWN"
    )
    error_boxes = sorted(
        box for box in returned if by_box[box].get("status") == "ERROR"
    )

    if sat_boxes:
        overall = "SAT"
    elif (
        len(returned) == 29
        and statuses.get("UNSAT", 0) == 29
        and not missing
        and not duplicates
    ):
        overall = "UNSAT_H10_TO_H15"
    else:
        overall = "INCOMPLETE"

    summary = {
        "schema": "k16-weighted-quotient-ladder-summary-v1",
        "status": overall,
        "expected_patterns": 29,
        "returned_patterns": len(returned),
        "status_counts": dict(statuses),
        "sat_boxes": sat_boxes,
        "unknown_boxes": unknown_boxes,
        "error_boxes": error_boxes,
        "missing_boxes": missing,
        "unexpected_boxes": unexpected,
        "duplicate_boxes": sorted(set(duplicates)),
        "logical_scope": (
            "Quotient orders h=10..15 only. Primitive h=16 tournaments "
            "are outside this phase."
        ),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(summary, indent=2, sort_keys=True),
        encoding="utf-8",
    )
    print(json.dumps(summary, indent=2))
    return 1 if error_boxes or missing or duplicates or unexpected else 0


if __name__ == "__main__":
    raise SystemExit(main())
