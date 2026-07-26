#!/usr/bin/env python3
"""Rebalance completed v14 checkpoints without splitting any residual root.

Every root, all of its pending descendant leaves, and all of its proved UNSAT
leaves move together.  The output checkpoints therefore remain disjoint, keep
root-closure accounting meaningful, and preserve the exact union of the input
coverage.
"""

from __future__ import annotations

import argparse
import copy
import json
from pathlib import Path
from typing import Any

from resumable_refinement_v14 import (
    MODEL_VERSION,
    atomic_json,
    config_fingerprint,
    item_id,
    root_key,
    utc_now,
)


def parse_schedule(value: str) -> list[int]:
    schedule = [int(piece.strip()) for piece in value.split(",") if piece.strip()]
    if not schedule or any(seconds < 1 for seconds in schedule):
        raise ValueError("schedule budgets must be positive")
    return schedule


def leaf_weight(
    item: dict[str, Any],
    initial_depth: int,
    schedule: list[int],
) -> int:
    generation = max(0, int(item["depth"]) - initial_depth)
    return schedule[min(generation, len(schedule) - 1)]


def load_sources(source_dir: Path) -> list[dict[str, Any]]:
    paths = sorted(source_dir.rglob("checkpoint.json"))
    if not paths:
        raise ValueError(f"no checkpoint.json files under {source_dir}")
    checkpoints = [json.loads(path.read_text(encoding="utf-8")) for path in paths]
    if any(checkpoint.get("found") for checkpoint in checkpoints):
        raise ValueError("a source checkpoint already contains a SAT witness")
    if any(checkpoint["stats"].get("errors", 0) for checkpoint in checkpoints):
        raise ValueError("source checkpoint contains solver errors")
    return checkpoints


def unique_by_id(
    records: list[dict[str, Any]],
    identity,
) -> list[dict[str, Any]]:
    indexed = {}
    for record in records:
        key = identity(record)
        if key in indexed:
            raise ValueError(f"duplicate checkpoint record {key}")
        indexed[key] = record
    return list(indexed.values())


def rebalance(args: argparse.Namespace) -> dict[str, Any]:
    checkpoints = load_sources(args.source_dir)
    first_config = checkpoints[0]["config"]
    invariant_fields = (
        "model_version",
        "n",
        "manifest_sha256",
        "source_split_depth",
        "pre_split_depth",
        "partition_count",
        "partition_index",
    )
    invariants = {
        field: first_config[field]
        for field in invariant_fields
        if field in first_config
    }
    for checkpoint in checkpoints:
        config = checkpoint["config"]
        observed = {
            field: config[field]
            for field in invariant_fields
            if field in config
        }
        if observed != invariants:
            raise ValueError("source checkpoint configurations disagree")

    roots = {}
    queue = unique_by_id(
        [
            item
            for checkpoint in checkpoints
            for item in checkpoint["queue"]
        ],
        item_id,
    )
    closed = unique_by_id(
        [
            item
            for checkpoint in checkpoints
            for item in checkpoint["closed_unsat"]
        ],
        lambda item: str(item["id"]),
    )
    for checkpoint in checkpoints:
        for root in checkpoint["selected_roots"]:
            key = f"{int(root['parent_line'])}:{int(root['pattern'])}"
            if key in roots and roots[key] != root:
                raise ValueError(f"inconsistent root metadata {key}")
            roots[key] = root

    queue_by_root = {key: [] for key in roots}
    closed_by_root = {key: [] for key in roots}
    for item in queue:
        queue_by_root[root_key(item)].append(item)
    for item in closed:
        key = f"{int(item['parent_line'])}:{int(item['pattern'])}"
        closed_by_root[key].append(item)

    schedule = parse_schedule(args.slice_schedule)
    initial_depth = int(first_config["source_split_depth"]) + int(
        first_config["pre_split_depth"]
    )
    groups = []
    for key, root in roots.items():
        pending = queue_by_root[key]
        weight = sum(
            leaf_weight(item, initial_depth, schedule)
            for item in pending
        )
        groups.append(
            {
                "key": key,
                "root": root,
                "queue": pending,
                "closed": closed_by_root[key],
                "weight": weight,
            }
        )
    groups.sort(
        key=lambda group: (
            -int(group["weight"]),
            group["key"],
        )
    )

    bins = [
        {"weight": 0, "groups": []}
        for _ in range(args.target_shards)
    ]
    for group in groups:
        target = min(
            range(args.target_shards),
            key=lambda index: (
                int(bins[index]["weight"]),
                len(bins[index]["groups"]),
                index,
            ),
        )
        bins[target]["groups"].append(group)
        bins[target]["weight"] += int(group["weight"])

    args.output_dir.mkdir(parents=True, exist_ok=True)
    output_queue_ids = set()
    output_closed_ids = set()
    shard_summaries = []
    for index, bucket in enumerate(bins):
        config = copy.deepcopy(first_config)
        config["shard_count"] = args.target_shards
        config["shard_index"] = index
        selected_roots = [
            group["root"] for group in bucket["groups"]
        ]
        shard_queue = [
            item
            for group in bucket["groups"]
            for item in group["queue"]
        ]
        shard_closed = [
            item
            for group in bucket["groups"]
            for item in group["closed"]
        ]
        output_queue_ids.update(item_id(item) for item in shard_queue)
        output_closed_ids.update(str(item["id"]) for item in shard_closed)
        checkpoint = {
            "model_version": MODEL_VERSION,
            "config": config,
            "config_fingerprint": config_fingerprint(config),
            "created_at": utc_now(),
            "updated_at": utc_now(),
            "selected_roots": selected_roots,
            "queue": shard_queue,
            "closed_unsat": shard_closed,
            "errors": [],
            "found": None,
            "stats": {
                "attempts": 0,
                "unsat_leaves": len(shard_closed),
                "timeouts_split": 0,
                "errors": 0,
                "solver_seconds": 0.0,
                "sessions": 0,
                "attempts_by_budget": {},
                "timeouts_by_budget": {},
                "batches": 0,
                "unit_unsat_children": 0,
            },
            "sessions": [],
            "rebalance_source": {
                "source_checkpoint_count": len(checkpoints),
                "schedule": schedule,
            },
        }
        shard_dir = args.output_dir / f"shard-{index}"
        atomic_json(shard_dir / "checkpoint.json", checkpoint)
        shard_summaries.append(
            {
                "shard": index,
                "roots": len(selected_roots),
                "pending_leaves": len(shard_queue),
                "closed_unsat_leaves": len(shard_closed),
                "estimated_seconds": int(bucket["weight"]),
            }
        )

    expected_queue_ids = {item_id(item) for item in queue}
    expected_closed_ids = {str(item["id"]) for item in closed}
    if output_queue_ids != expected_queue_ids:
        raise ValueError("rebalanced pending cover is not exact")
    if output_closed_ids != expected_closed_ids:
        raise ValueError("rebalanced UNSAT records are not exact")

    result = {
        "status": "PASS",
        "source_checkpoints": len(checkpoints),
        "roots": len(roots),
        "roots_closed": sum(not queue_by_root[key] for key in roots),
        "roots_open": sum(bool(queue_by_root[key]) for key in roots),
        "pending_leaves": len(queue),
        "closed_unsat_leaves": len(closed),
        "target_shards": args.target_shards,
        "slice_schedule": schedule,
        "shards": shard_summaries,
    }
    atomic_json(args.output_dir / "rebalance-summary.json", result)
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-dir", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--target-shards", type=int, default=16)
    parser.add_argument("--slice-schedule", default="180,1800,7200")
    args = parser.parse_args()
    if args.target_shards < 1:
        raise SystemExit("--target-shards must be positive")
    result = rebalance(args)
    print(json.dumps(result, indent=2), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
