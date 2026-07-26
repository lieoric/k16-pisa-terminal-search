#!/usr/bin/env python3
"""Progressively concentrate Kaggle GPU time on the best K16 near-witnesses.

This is a witness-only companion to the exact GitHub v15 campaign.  A miss is
never reported as UNSAT.  Every witness is independently verified by the
existing CUDA hunter before it is accepted.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import math
from pathlib import Path
from typing import Any

import torch


REPO_ROOT = Path(__file__).resolve().parents[1]
HUNTER_PATH = REPO_ROOT / "kaggle" / "k16_pisa_gpu_hunter.py"


def load_hunter():
    spec = importlib.util.spec_from_file_location("gpu_hunter", HUNTER_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import {HUNTER_PATH}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def atomic_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(payload, indent=2) + "\n",
        encoding="utf-8",
    )
    temporary.replace(path)


def parse_ints(value: str) -> list[int]:
    result = [int(piece.strip()) for piece in value.split(",") if piece.strip()]
    if not result or any(number < 1 for number in result):
        raise ValueError("budgets must be positive integers")
    return result


def parse_fractions(value: str) -> list[float]:
    result = [
        float(piece.strip()) for piece in value.split(",") if piece.strip()
    ]
    if any(not 0 < number <= 1 for number in result):
        raise ValueError("keep fractions must be in (0, 1]")
    return result


def ranking_key(record: dict[str, Any]) -> tuple[int, int, int]:
    return (
        int(record["best_loss"]),
        int(record["best_positive_defect_sum"]),
        int(record["shard"]),
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--device", required=True)
    parser.add_argument("--worker-index", type=int, required=True)
    parser.add_argument("--worker-count", type=int, required=True)
    parser.add_argument("--budgets", default="180,900,3600")
    parser.add_argument("--keep-fractions", default="0.4,0.3")
    parser.add_argument("--batch-size", type=int, default=16384)
    parser.add_argument("--min-total-b", type=int, default=16)
    parser.add_argument("--seed-offset", type=int, default=1500000)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("/kaggle/working/k16_gpu_v15"),
    )
    args = parser.parse_args()
    if not 0 <= args.worker_index < args.worker_count:
        raise SystemExit("bad worker index/count")

    budgets = parse_ints(args.budgets)
    keep_fractions = parse_fractions(args.keep_fractions)
    if len(keep_fractions) != len(budgets) - 1:
        raise SystemExit("need one keep fraction between every budget round")

    hunter = load_hunter()
    device = torch.device(args.device)
    torch.cuda.set_device(device)
    worker_dir = args.output_dir / f"gpu-{args.worker_index}"
    checkpoint_path = worker_dir / "checkpoint.json"
    checkpoint = {
        "campaign": "K16-PISA-v15-progressive-gpu-islands",
        "worker_index": args.worker_index,
        "worker_count": args.worker_count,
        "completed": {},
        "rounds": [],
        "witness": None,
    }
    if checkpoint_path.exists():
        checkpoint = json.loads(checkpoint_path.read_text(encoding="utf-8"))

    targets = [
        index
        for index, endpoint in enumerate(hunter.ENDPOINT_TARGETS)
        if int(endpoint["total_b"]) >= args.min_total_b
        and index % args.worker_count == args.worker_index
    ]
    active = targets
    original_seed = int(hunter.BASE_SEED)
    for round_index, budget in enumerate(budgets):
        records = []
        for shard in active:
            key = f"{round_index}:{shard}"
            output = worker_dir / f"round-{round_index}" / f"target-{shard}.json"
            if key in checkpoint["completed"] and output.exists():
                record = json.loads(output.read_text(encoding="utf-8"))
            else:
                hunter.BASE_SEED = (
                    original_seed
                    ^ int(args.seed_offset)
                    ^ ((round_index + 1) * 0x9E3779B97F4A7C15)
                ) & ((1 << 63) - 1)
                record = hunter.run_shard(
                    shard,
                    budget,
                    args.batch_size,
                    device,
                    output,
                )
                checkpoint["completed"][key] = {
                    "status": record["status"],
                    "best_loss": int(record["best_loss"]),
                    "best_positive_defect_sum": int(
                        record["best_positive_defect_sum"]
                    ),
                }
                if record["status"] == "WITNESS":
                    checkpoint["witness"] = record
                atomic_json(checkpoint_path, checkpoint)
            records.append(record)
            if record["status"] == "WITNESS":
                print("### VERIFIED K16 PISA WITNESS FOUND ###", flush=True)
                return 0

        records.sort(key=ranking_key)
        round_summary = {
            "round": round_index,
            "budget_seconds": budget,
            "targets": len(records),
            "best": [
                {
                    "target": int(record["shard"]),
                    "best_loss": int(record["best_loss"]),
                    "best_positive_defect_sum": int(
                        record["best_positive_defect_sum"]
                    ),
                }
                for record in records[:10]
            ],
        }
        checkpoint["rounds"] = [
            item
            for item in checkpoint["rounds"]
            if int(item["round"]) != round_index
        ] + [round_summary]
        atomic_json(checkpoint_path, checkpoint)
        if round_index < len(keep_fractions):
            keep = max(
                1,
                math.ceil(len(records) * keep_fractions[round_index]),
            )
            active = [
                int(record["shard"]) for record in records[:keep]
            ]
            print(
                f"GPU_ROUND_{round_index}_DONE targets={len(records)} "
                f"keep={keep} next_budget={budgets[round_index + 1]}",
                flush=True,
            )

    print(
        "GPU_PROGRESSIVE_DONE no witness; this is not an UNSAT conclusion",
        flush=True,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
