#!/usr/bin/env python3
"""Batched CUDA witness search for K16 Pisa tournaments.

This is a heuristic SAT witness hunter, not an UNSAT solver.  Every reported
witness is independently rechecked by scripts.verify_witness.verify_masks.
"""

from __future__ import annotations

import argparse
import json
import random
import sys
import time
from pathlib import Path

import torch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.verify_witness import verify_masks

N = 16
BASE_SEED = 0x4B31365049534135


def edge_data() -> tuple[list[tuple[int, int]], list[tuple[int, int]], list[int]]:
    all_edges = [(u, v) for u in range(N) for v in range(u + 1, N)]
    ring = {(i, i + 1) for i in range(N - 1)} | {(0, N - 1)}
    free = [edge for edge in all_edges if edge not in ring]
    zero_indices = [i for i, (u, _) in enumerate(free) if u == 0]
    assert len(all_edges) == 120 and len(free) == 104 and len(zero_indices) == 13
    return all_edges, free, zero_indices


ALL_EDGES, FREE_EDGES, ZERO_FREE_INDICES = edge_data()
NONZERO_FREE_INDICES = [
    i for i, (u, v) in enumerate(FREE_EDGES) if u != 0 and v != 0
]
FREE_INDEX = {edge: i for i, edge in enumerate(FREE_EDGES)}
FREE_TRIANGLES = [
    (FREE_INDEX[(a, b)], FREE_INDEX[(a, c)], FREE_INDEX[(b, c)])
    for a in range(1, N)
    for b in range(a + 1, N)
    for c in range(b + 1, N)
    if (a, b) in FREE_INDEX and (a, c) in FREE_INDEX and (b, c) in FREE_INDEX
]


def initial_population(
    batch: int, target_degree: int, device: torch.device, generator: torch.Generator
) -> torch.Tensor:
    bits = torch.randint(
        0, 2, (batch, len(FREE_EDGES)), device=device, dtype=torch.bool, generator=generator
    )
    # The fixed cycle contributes 0->1 and 15->0.  Choose the remaining
    # out-neighbours of vertex 0 exactly, so every walker stays in its branch.
    scores = torch.rand(
        (batch, len(ZERO_FREE_INDICES)), device=device, generator=generator
    )
    chosen = scores.topk(target_degree - 1, dim=1).indices
    zero_values = torch.zeros_like(scores, dtype=torch.bool)
    zero_values.scatter_(1, chosen, True)
    bits[:, ZERO_FREE_INDICES] = zero_values
    return bits


def adjacency(bits: torch.Tensor) -> torch.Tensor:
    batch = bits.shape[0]
    adj = torch.zeros((batch, N, N), dtype=torch.bool, device=bits.device)
    u = torch.tensor([edge[0] for edge in FREE_EDGES], device=bits.device)
    v = torch.tensor([edge[1] for edge in FREE_EDGES], device=bits.device)
    adj[:, u, v] = bits
    adj[:, v, u] = ~bits
    for x in range(N - 1):
        adj[:, x, x + 1] = True
        adj[:, x + 1, x] = False
    adj[:, N - 1, 0] = True
    adj[:, 0, N - 1] = False
    return adj


@torch.inference_mode()
def evaluate(bits: torch.Tensor, target_degree: int, target_blockers: int) -> dict:
    adj = adjacency(bits)
    degree = adj.sum(dim=2, dtype=torch.int16)
    # All entries are <= 15, so fp16 matrix multiplication is exact here.
    paths = torch.bmm(adj.to(torch.float16), adj.to(torch.float16)) > 0
    eye = torch.eye(N, dtype=torch.bool, device=bits.device).unsqueeze(0)
    second_mask = paths & ~adj & ~eye
    second = second_mask.sum(dim=2, dtype=torch.int16)
    margin = second - degree
    blockers = (N - 1) - degree - second
    positive = torch.clamp(margin, min=0).to(torch.int32)
    branch_gap = (
        (degree[:, 0] - target_degree).abs()
        + (blockers[:, 0] - target_blockers).abs()
    ).to(torch.int32)
    loss = (
        100000 * branch_gap
        + 10000 * (positive > 0).sum(dim=1)
        + 200 * positive.sum(dim=1)
        + (positive * positive).sum(dim=1)
    )
    return {
        "loss": loss,
        "degree": degree,
        "second": second,
        "margin": margin,
        "blockers": blockers,
    }


def mutate_edges(
    parents: torch.Tensor, generator: torch.Generator, mixed: bool
) -> torch.Tensor:
    children = parents.clone()
    device = children.device
    batch = children.shape[0]
    rows = torch.arange(batch, device=device)
    allowed = torch.tensor(NONZERO_FREE_INDICES, device=device)

    edge_positions = torch.randint(
        0, len(NONZERO_FREE_INDICES), (batch,), device=device, generator=generator
    )
    children[rows, allowed[edge_positions]] ^= True

    # Some walkers get a second edge flip to cross wider local barriers.
    second_rows = rows[torch.rand(batch, device=device, generator=generator) < 0.20]
    if second_rows.numel():
        second_positions = torch.randint(
            0,
            len(NONZERO_FREE_INDICES),
            (second_rows.numel(),),
            device=device,
            generator=generator,
        )
        children[second_rows, allowed[second_positions]] ^= True

    if mixed:
        tri_rows = rows[torch.rand(batch, device=device, generator=generator) < 0.55]
        if tri_rows.numel():
            triples = torch.tensor(FREE_TRIANGLES, device=device)
            picked = triples[
                torch.randint(
                    0, len(FREE_TRIANGLES), (tri_rows.numel(),), device=device, generator=generator
                )
            ]
            ab = children[tri_rows, picked[:, 0]]
            ac = children[tri_rows, picked[:, 1]]
            bc = children[tri_rows, picked[:, 2]]
            cyclic = (ab & ~ac & bc) | (~ab & ac & ~bc)
            active_rows = tri_rows[cyclic]
            active = picked[cyclic]
            if active_rows.numel():
                children[active_rows, active[:, 0]] ^= True
                children[active_rows, active[:, 1]] ^= True
                children[active_rows, active[:, 2]] ^= True
    return children


def bits_to_masks(bits: torch.Tensor) -> list[int]:
    values = bits.detach().cpu().tolist()
    out = [0] * N
    for value, (u, v) in zip(values, FREE_EDGES):
        if value:
            out[u] |= 1 << v
        else:
            out[v] |= 1 << u
    for v in range(N - 1):
        out[v] |= 1 << (v + 1)
    out[N - 1] |= 1
    return out


def save_record(
    path: Path,
    shard: int,
    strategy: str,
    seconds: float,
    generations: int,
    candidates: int,
    best_bits: torch.Tensor,
    best_loss: int,
) -> dict:
    masks = bits_to_masks(best_bits)
    check = verify_masks(masks)
    record = {
        "campaign": "K16-PISA-v5",
        "platform": "kaggle-gpu",
        "status": "WITNESS" if check["is_pisa"] else "NO_WITNESS",
        "shard": shard,
        "strategy": strategy,
        "wall_seconds": round(seconds, 3),
        "generations": generations,
        "states_evaluated": candidates,
        "best_loss": best_loss,
        "out_masks": masks,
        "outdegrees": check["outdegrees"],
        "second_sizes": check["second_sizes"],
        "margins": check["margins"],
        "blockers": check["blockers"],
        "independent_verification": check,
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    return record


def run_shard(
    shard: int,
    seconds: int,
    batch: int,
    device: torch.device,
    output: Path,
) -> dict:
    lane = shard % 4
    target_degree = 7 if lane < 2 else 6
    target_blockers = 1 if target_degree == 7 else 3
    mixed = lane % 2 == 1
    strategy = f"d{target_degree}_b{target_blockers}_{'mixed' if mixed else 'edge'}"
    seed = (BASE_SEED ^ (shard << 32) ^ 0x475055) & ((1 << 63) - 1)
    torch.manual_seed(seed)
    random.seed(seed)
    generator = torch.Generator(device=device)
    generator.manual_seed(seed)

    population = initial_population(batch, target_degree, device, generator)
    metrics = evaluate(population, target_degree, target_blockers)
    # evaluate() runs under inference_mode for speed. Clone the persistent
    # population scores into ordinary storage before steady-state updates.
    losses = metrics["loss"].clone()
    best_index = int(losses.argmin())
    best_bits = population[best_index].clone()
    best_loss = int(losses[best_index])
    start = time.monotonic()
    generations = 0
    candidates = batch

    while time.monotonic() - start < seconds and best_loss != 0:
        children = mutate_edges(population, generator, mixed)
        child_metrics = evaluate(children, target_degree, target_blockers)
        child_losses = child_metrics["loss"]
        candidates += batch

        # Greedy steady-state replacement with a small diversity allowance.
        noise = torch.rand(batch, device=device, generator=generator) < 0.01
        accept = (child_losses <= losses) | noise
        population[accept] = children[accept]
        losses[accept] = child_losses[accept]

        generation_best = int(losses.argmin())
        generation_loss = int(losses[generation_best])
        if generation_loss < best_loss:
            best_loss = generation_loss
            best_bits = population[generation_best].clone()
            print(
                f"shard={shard} generation={generations} best_loss={best_loss} "
                f"candidates={candidates}",
                flush=True,
            )

        # Re-seed the worst quarter around elite walkers every 32 generations.
        generations += 1
        if generations % 32 == 0:
            elite_count = max(16, batch // 128)
            worst_count = batch // 4
            elite = losses.topk(elite_count, largest=False).indices
            worst = losses.topk(worst_count, largest=True).indices
            parents = elite[
                torch.randint(
                    0, elite_count, (worst_count,), device=device, generator=generator
                )
            ]
            population[worst] = mutate_edges(population[parents], generator, mixed)
            refreshed = evaluate(population[worst], target_degree, target_blockers)
            losses[worst] = refreshed["loss"]
            candidates += worst_count

    elapsed = time.monotonic() - start
    return save_record(
        output, shard, strategy, elapsed, generations, candidates, best_bits, best_loss
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--shard-start", type=int, default=0)
    parser.add_argument("--shard-count", type=int, default=64)
    parser.add_argument("--seconds-per-shard", type=int, default=300)
    parser.add_argument("--batch-size", type=int, default=16384)
    parser.add_argument("--output-dir", type=Path, default=Path("/kaggle/working/k16_gpu_results"))
    parser.add_argument("--allow-cpu", action="store_true")
    args = parser.parse_args()

    if torch.cuda.is_available():
        device = torch.device("cuda")
        print(f"CUDA device: {torch.cuda.get_device_name(0)}")
    elif args.allow_cpu:
        device = torch.device("cpu")
        print("WARNING: CPU fallback is for smoke testing only")
    else:
        raise SystemExit("CUDA is unavailable. In Kaggle select Accelerator: GPU.")

    args.output_dir.mkdir(parents=True, exist_ok=True)
    checkpoint = args.output_dir / "checkpoint.json"
    completed: set[int] = set()
    if checkpoint.exists():
        data = json.loads(checkpoint.read_text(encoding="utf-8"))
        completed = {int(value) for value in data.get("completed_shards", [])}

    for shard in range(args.shard_start, args.shard_start + args.shard_count):
        if shard in completed:
            print(f"skip completed shard {shard}")
            continue
        result = run_shard(
            shard,
            args.seconds_per_shard,
            args.batch_size,
            device,
            args.output_dir / f"shard-{shard:02d}.json",
        )
        completed.add(shard)
        checkpoint.write_text(
            json.dumps(
                {
                    "campaign": "K16-PISA-v5",
                    "completed_shards": sorted(completed),
                    "witness_found": result["status"] == "WITNESS",
                },
                indent=2,
            )
            + "\n",
            encoding="utf-8",
        )
        print(
            f"completed shard={shard} status={result['status']} "
            f"best_loss={result['best_loss']}",
            flush=True,
        )
        if result["status"] == "WITNESS":
            print("### VERIFIED K16 PISA WITNESS FOUND ###", flush=True)
            return 0
    print("No witness in completed GPU shards. This is not an UNSAT result.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
