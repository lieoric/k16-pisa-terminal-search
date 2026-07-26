#!/usr/bin/env python3
"""K16 Pisa v8 endpoint-aware CUDA witness search.

This is a heuristic SAT witness hunter, not an UNSAT solver.  Every reported
witness is independently rechecked by scripts.verify_witness.verify_masks.

Unlike v7's 64 superficially similar zero-neighbour buckets, v8 assigns each
walker campaign to one of the 54 genuinely different exact endpoint subboxes
left by the v5/v6 map.  Directed 3-cycle reversals preserve the score sequence
and now form a first-class move rather than an add-on after an edge flip.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import random
import sys
import time
from pathlib import Path

import torch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.verify_witness import verify_masks

N = 16
PARTITION_BUCKETS = 32
BASE_SEED = 0x4B31365049534137


def endpoint_targets() -> list[dict]:
    """The same 54 open structural targets used by exact GitHub v6."""
    targets: list[dict] = []
    d7_layers = {
        14: range(9, 11),
        15: range(9, 12),
        16: range(8, 13),
        17: range(8, 14),
        18: range(8, 14),
        19: range(8, 15),
        20: range(8, 15),
    }
    for total_b, degrees in d7_layers.items():
        for anchor_degree in degrees:
            targets.append(
                {
                    "name": (
                        f"d7_b1_B{'20plus' if total_b == 20 else total_b}_"
                        f"anchorD{anchor_degree}"
                    ),
                    "degree": 7,
                    "blockers": 1,
                    "total_b": total_b,
                    "total_b_is_floor": total_b == 20,
                    "anchor_degree": anchor_degree,
                    "pattern_ones": 0,
                }
            )
    for anchor_degree in range(7, 14):
        for pattern in ((0, 0), (0, 1), (1, 1)):
            if not 0 <= anchor_degree - 7 - sum(pattern) <= 6:
                continue
            label = "".join(map(str, pattern))
            targets.append(
                {
                    "name": (
                        f"d6_b3_B20plus_anchorD{anchor_degree}_pattern{label}"
                    ),
                    "degree": 6,
                    "blockers": 3,
                    "total_b": 20,
                    "total_b_is_floor": True,
                    "anchor_degree": anchor_degree,
                    "pattern_ones": sum(pattern),
                }
            )
    assert len(targets) == 54
    return targets


ENDPOINT_TARGETS = endpoint_targets()


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
NONZERO_FREE_EDGES = [FREE_EDGES[i] for i in NONZERO_FREE_INDICES]
FREE_INDEX = {edge: i for i, edge in enumerate(FREE_EDGES)}
FREE_TRIANGLES = [
    (FREE_INDEX[(a, b)], FREE_INDEX[(a, c)], FREE_INDEX[(b, c)])
    for a in range(1, N)
    for b in range(a + 1, N)
    for c in range(b + 1, N)
    if (a, b) in FREE_INDEX and (a, c) in FREE_INDEX and (b, c) in FREE_INDEX
]


def colex_rank_from_positions(positions: tuple[int, ...] | list[int]) -> int:
    return sum(math.comb(position, index + 1) for index, position in enumerate(positions))


def zero_patterns(
    target_degree: int, bucket: int | None = None
) -> list[list[bool]]:
    patterns: list[list[bool]] = []
    for positions in itertools.combinations(range(13), target_degree - 1):
        if (
            bucket is not None
            and colex_rank_from_positions(positions) % PARTITION_BUCKETS
            != bucket
        ):
            continue
        row = [False] * 13
        for position in positions:
            row[position] = True
        patterns.append(row)
    if not patterns:
        raise RuntimeError(f"empty partition bucket: d={target_degree}, bucket={bucket}")
    return patterns


def zero_partition_from_masks(masks: list[int]) -> tuple[int, int, int]:
    positions = [
        position for position in range(13) if (masks[0] >> (position + 2)) & 1
    ]
    rank = colex_rank_from_positions(positions)
    subset = sum(1 << position for position in positions)
    return subset, rank, rank % PARTITION_BUCKETS


def partition_self_test() -> None:
    for degree in (7, 6):
        seen: set[tuple[bool, ...]] = set()
        expected = math.comb(13, degree - 1)
        for bucket in range(PARTITION_BUCKETS):
            patterns = zero_patterns(degree, bucket)
            for pattern in patterns:
                key = tuple(pattern)
                if key in seen:
                    raise AssertionError("partition overlap")
                positions = tuple(i for i, value in enumerate(pattern) if value)
                assert len(positions) == degree - 1
                assert colex_rank_from_positions(positions) % PARTITION_BUCKETS == bucket
                seen.add(key)
        assert len(seen) == expected


def initial_population(
    batch: int,
    target_degree: int,
    bucket: int | None,
    device: torch.device,
    generator: torch.Generator,
) -> torch.Tensor:
    bits = torch.randint(
        0, 2, (batch, len(FREE_EDGES)), device=device, dtype=torch.bool, generator=generator
    )
    # The fixed cycle contributes 0->1 and 15->0.  The remaining 13
    # zero-neighbour choices are sampled across the full role orbit. Mutations
    # never touch these edges, but independent walkers cover every pattern;
    # v8 shards are structural endpoint targets, not arbitrary colex buckets.
    pattern_values = zero_patterns(target_degree, bucket)
    pattern_tensor = torch.tensor(pattern_values, dtype=torch.bool, device=device)
    chosen = torch.randint(
        0, len(pattern_values), (batch,), device=device, generator=generator
    )
    bits[:, ZERO_FREE_INDICES] = pattern_tensor[chosen]
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
def evaluate(
    bits: torch.Tensor,
    target_degree: int,
    target_blockers: int,
    endpoint: dict | None = None,
) -> dict:
    adj = adjacency(bits)
    degree = adj.sum(dim=2, dtype=torch.int16)
    # All entries are <= 15, so fp16 matrix multiplication is exact here.
    path_counts = torch.bmm(adj.to(torch.float16), adj.to(torch.float16))
    paths = path_counts > 0
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
    raw_loss = (
        100000 * branch_gap
        + 10000 * (positive > 0).sum(dim=1)
        + 200 * positive.sum(dim=1)
        + (positive * positive).sum(dim=1)
    )
    total_b = blockers.sum(dim=1, dtype=torch.int32)
    zero_blocker_mask = adj[:, :, 0] & ~paths[:, 0, :]
    vertex_ids = torch.arange(N, device=bits.device).unsqueeze(0)
    anchor_rank = (
        degree.to(torch.int32) * 32 + vertex_ids
    ).masked_fill(~zero_blocker_mask, 10000)
    anchor = anchor_rank.argmin(dim=1)
    rows = torch.arange(bits.shape[0], device=bits.device)
    anchor_degree = degree[rows, anchor].to(torch.int32)
    pattern_ones = (
        adj[rows, anchor, :] & zero_blocker_mask
    ).sum(dim=1, dtype=torch.int32)

    endpoint_gap = torch.zeros(
        bits.shape[0], dtype=torch.int32, device=bits.device
    )
    if endpoint is not None:
        if endpoint["total_b_is_floor"]:
            total_gap = torch.clamp(endpoint["total_b"] - total_b, min=0)
        else:
            total_gap = (total_b - endpoint["total_b"]).abs()
        endpoint_gap = (
            8 * total_gap
            + 3 * (anchor_degree - endpoint["anchor_degree"]).abs()
            + (pattern_ones - endpoint["pattern_ones"]).abs()
        )
    # Feasibility remains primary, but endpoint distance breaks the v7 10201
    # plateau and steers independent shards toward genuinely different strata.
    loss = raw_loss.to(torch.int64) * 1000 + endpoint_gap.to(torch.int64)
    incoming = adj.transpose(1, 2)
    positive_defect = incoming & (path_counts > 0)
    defect_values = path_counts.to(torch.int16).masked_fill(~positive_defect, N)
    extra_defect = defect_values.min(dim=2).values
    return {
        "loss": loss,
        "raw_loss": raw_loss,
        "endpoint_gap": endpoint_gap,
        "total_b": total_b,
        "zero_anchor_degree": anchor_degree,
        "zero_anchor_pattern_ones": pattern_ones,
        "degree": degree,
        "second": second,
        "margin": margin,
        "blockers": blockers,
        "extra_defect": extra_defect,
        "positive_defect_sum": (
            extra_defect.to(torch.int32) * (margin > 0)
        ).sum(dim=1),
        "adj": adj,
        "path_counts": path_counts.to(torch.int16),
        "target_degree": target_degree,
        "target_blockers": target_blockers,
    }


def dynamic_score(metrics: dict, weights: torch.Tensor) -> torch.Tensor:
    margin = metrics["margin"].to(torch.int32)
    positive = torch.clamp(margin, min=0)
    defect = metrics["extra_defect"].to(torch.int32)
    vertex_cost = (
        20000
        + 800 * positive
        + 40 * positive * positive
        + 120 * defect
    )
    return (
        100000000 * (
            (metrics["degree"][:, 0].to(torch.int32) - metrics["target_degree"]).abs()
            + (metrics["blockers"][:, 0].to(torch.int32) - metrics["target_blockers"]).abs()
        )
        + (weights.to(torch.int32) * vertex_cost * (positive > 0)).sum(dim=1)
        + 2000 * metrics["endpoint_gap"].to(torch.int32)
    )


def mutate_edges(
    parents: torch.Tensor, generator: torch.Generator, mixed: bool
) -> torch.Tensor:
    """Mixture with genuine score-preserving triangle moves.

    v7 always flipped an edge before trying a triangle, so it almost never
    explored the fixed-score state graph.  Here 45% of walkers perform only a
    directed 3-cycle reversal, 40% perform one edge flip, and 15% a wider
    two-edge move.  Focused blocker repairs may still replace these proposals.
    """
    children = parents.clone()
    device = children.device
    batch = children.shape[0]
    rows = torch.arange(batch, device=device)
    allowed = torch.tensor(NONZERO_FREE_INDICES, device=device)

    mode = torch.rand(batch, device=device, generator=generator)
    edge_rows = rows[mode >= 0.45]
    edge_positions = torch.randint(
        0,
        len(NONZERO_FREE_INDICES),
        (edge_rows.numel(),),
        device=device,
        generator=generator,
    )
    children[edge_rows, allowed[edge_positions]] ^= True

    second_rows = rows[mode >= 0.85]
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
        tri_rows = rows[mode < 0.45]
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


def mutation_data(device: torch.device) -> dict:
    lookup = torch.full((N, N), -1, dtype=torch.long, device=device)
    for index in NONZERO_FREE_INDICES:
        u, v = FREE_EDGES[index]
        lookup[u, v] = lookup[v, u] = index
    return {
        "lookup": lookup,
        "indices": torch.tensor(NONZERO_FREE_INDICES, dtype=torch.long, device=device),
        "a": torch.tensor(
            [FREE_EDGES[i][0] for i in NONZERO_FREE_INDICES],
            dtype=torch.long,
            device=device,
        ),
        "b": torch.tensor(
            [FREE_EDGES[i][1] for i in NONZERO_FREE_INDICES],
            dtype=torch.long,
            device=device,
        ),
    }


def focused_mutation(
    parents: torch.Tensor,
    metrics: dict,
    weights: torch.Tensor,
    generator: torch.Generator,
    data: dict,
) -> torch.Tensor:
    """Mix random moves with vectorized degree and blocker completion."""
    children = mutate_edges(parents, generator, mixed=True)
    device = parents.device
    batch = parents.shape[0]
    rows = torch.arange(batch, device=device)
    positive = torch.clamp(metrics["margin"].to(torch.int32), min=0)
    offender = (positive * weights.to(torch.int32)).argmax(dim=1)
    has_offender = positive.sum(dim=1) > 0
    focused = has_offender & (
        torch.rand(batch, device=device, generator=generator) < 0.72
    )
    degree_mode = focused & (
        torch.rand(batch, device=device, generator=generator) < 0.42
    )
    blocker_mode = focused & ~degree_mode
    adj = metrics["adj"]

    # Degree repair: reverse one mutable x->v edge into v->x.
    incoming = adj[rows, :, offender]
    lookup_rows = data["lookup"][offender]
    degree_valid = incoming & (lookup_rows >= 0)
    random_choice = torch.rand(
        (batch, N), device=device, generator=generator
    ).masked_fill(~degree_valid, -1.0)
    degree_x = random_choice.argmax(dim=1)
    degree_has = degree_valid.any(dim=1)
    degree_rows = degree_mode & degree_has
    degree_indices = lookup_rows[rows, degree_x]
    children[degree_rows] = parents[degree_rows]
    children[rows[degree_rows], degree_indices[degree_rows]] ^= True

    # Blocker completion. For a candidate x->v, path_counts[v,x] is exactly
    # the number of defect edges u->x with u in N+(v). Count how many of those
    # edges are mutable, retain only fully mutable candidates, and reverse the
    # entire defect set in one parallel move.
    out_v = adj[rows, offender, :]
    idx, a, b = data["indices"], data["a"], data["b"]
    edge_bits = parents[:, idx]
    defect_to_a = out_v[:, b] & ~edge_bits
    defect_to_b = out_v[:, a] & edge_bits
    mutable_count = torch.zeros(
        (batch, N), dtype=torch.int16, device=device
    )
    mutable_count.scatter_add_(
        1, a.unsqueeze(0).expand(batch, -1), defect_to_a.to(torch.int16)
    )
    mutable_count.scatter_add_(
        1, b.unsqueeze(0).expand(batch, -1), defect_to_b.to(torch.int16)
    )
    path_v = metrics["path_counts"][rows, offender, :]
    blocker_valid = (
        incoming
        & (path_v > 0)
        & (path_v <= 6)
        & (mutable_count == path_v)
    )
    blocker_cost = path_v.to(torch.float32) + 0.20 * torch.rand(
        (batch, N), device=device, generator=generator
    )
    blocker_cost.masked_fill_(~blocker_valid, 1000.0)
    blocker_x = blocker_cost.argmin(dim=1)
    blocker_has = blocker_valid.any(dim=1)
    blocker_rows = blocker_mode & blocker_has
    flip_mask = (
        ((blocker_x[:, None] == a[None, :]) & defect_to_a)
        | ((blocker_x[:, None] == b[None, :]) & defect_to_b)
    )
    children[blocker_rows] = parents[blocker_rows]
    children[:, idx] ^= flip_mask & blocker_rows[:, None]
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


@torch.inference_mode()
def exact_local_repair(
    best_bits: torch.Tensor,
    target_degree: int,
    target_blockers: int,
    device: torch.device,
    endpoint: dict | None = None,
    chunk_size: int = 4096,
) -> tuple[torch.Tensor, int, int, int, bool]:
    """Exhaust radius <= 6 in a 20-edge offender/blocker kernel on the GPU."""
    masks = bits_to_masks(best_bits)
    check = verify_masks(masks)
    offenders = [
        v for v, margin in enumerate(check["margins"]) if margin > 0
    ]
    current_metrics = evaluate(
        best_bits.unsqueeze(0),
        target_degree,
        target_blockers,
        endpoint,
    )
    current_loss = int(current_metrics["loss"][0])
    current_defect = int(current_metrics["positive_defect_sum"][0])
    if len(offenders) != 1 or check["margins"][offenders[0]] != 1:
        return best_bits, current_loss, current_defect, 0, False
    offender = offenders[0]
    allowed = set(NONZERO_FREE_INDICES)
    ranked: dict[int, int] = {}

    def add(priority: int, u: int, v: int) -> bool:
        edge = (min(u, v), max(u, v))
        index = FREE_INDEX.get(edge, -1)
        if index not in allowed:
            return False
        ranked[index] = min(priority, ranked.get(index, 999))
        return True

    for x in range(1, N):
        if x != offender:
            add(30, offender, x)
    blocker_candidates: list[tuple[int, list[int]]] = []
    for x in range(1, N):
        if x == offender or not ((masks[x] >> offender) & 1):
            continue
        defects = [
            u
            for u in range(N)
            if ((masks[offender] >> u) & 1) and ((masks[u] >> x) & 1)
        ]
        if not defects:
            continue
        indices = []
        mutable = True
        for u in defects:
            edge = (min(u, x), max(u, x))
            index = FREE_INDEX.get(edge, -1)
            if index not in allowed:
                mutable = False
                break
            indices.append(index)
        if mutable:
            blocker_candidates.append((len(indices), indices))
    blocker_candidates.sort(key=lambda item: item[0])
    for defect, indices in blocker_candidates[:6]:
        for index in indices:
            ranked[index] = min(defect, ranked.get(index, 999))
    kernel = [
        index
        for index, _ in sorted(ranked.items(), key=lambda item: (item[1], item[0]))
    ][:20]
    if not kernel:
        return best_bits, current_loss, current_defect, 0, False

    best = best_bits.clone()
    best_key = (current_loss, current_defect)
    checked = 0
    for radius in range(1, 7):
        combos = list(itertools.combinations(kernel, radius))
        for start in range(0, len(combos), chunk_size):
            part = combos[start : start + chunk_size]
            candidates = best_bits.unsqueeze(0).repeat(len(part), 1)
            flip_rows, flip_cols = [], []
            for row, combo in enumerate(part):
                flip_rows.extend([row] * len(combo))
                flip_cols.extend(combo)
            candidates[
                torch.tensor(flip_rows, device=device),
                torch.tensor(flip_cols, device=device),
            ] ^= True
            metrics = evaluate(
                candidates, target_degree, target_blockers, endpoint
            )
            checked += len(part)
            order = torch.argsort(
                metrics["loss"].to(torch.int64) * 100
                + metrics["positive_defect_sum"].to(torch.int64)
            )
            index = int(order[0])
            key = (
                int(metrics["loss"][index]),
                int(metrics["positive_defect_sum"][index]),
            )
            if key < best_key:
                best_key = key
                best = candidates[index].clone()
            witness_rows = torch.nonzero(metrics["raw_loss"] == 0).flatten()
            if witness_rows.numel():
                witness = candidates[int(witness_rows[0])].clone()
                independent = verify_masks(bits_to_masks(witness))
                if independent["is_pisa"]:
                    return witness, 0, 0, checked, True
    return best, best_key[0], best_key[1], checked, False


def save_record(
    path: Path,
    shard: int,
    strategy: str,
    seconds: float,
    generations: int,
    candidates: int,
    best_bits: torch.Tensor,
    best_loss: int,
    best_defect: int,
    repair_attempts: int,
    repair_states: int,
    target_degree: int,
    target_blockers: int,
    bucket: int | None,
    endpoint: dict,
) -> dict:
    masks = bits_to_masks(best_bits)
    check = verify_masks(masks)
    subset, rank, actual_bucket = zero_partition_from_masks(masks)
    partition_valid = check["outdegrees"][0] == target_degree
    valid_witness = (
        check["is_pisa"]
        and partition_valid
        and check["blockers"][0] == target_blockers
    )
    record = {
        "campaign": "K16-PISA-v8-endpoint-aware-triangle-search",
        "platform": "kaggle-gpu",
        "status": "WITNESS" if valid_witness else "NO_WITNESS",
        "shard": shard,
        "strategy": strategy,
        "partition_scheme": "full-zero-out-neighbour-orbit-per-endpoint",
        "partition_bucket": "all" if bucket is None else bucket,
        "partition_bucket_count": PARTITION_BUCKETS,
        "partition_pattern_count": len(zero_patterns(target_degree, bucket)),
        "zero_out_subset": subset,
        "zero_out_rank": rank,
        "partition_valid": partition_valid,
        "target_degree": target_degree,
        "target_blockers": target_blockers,
        "target_endpoint": endpoint,
        "wall_seconds": round(seconds, 3),
        "generations": generations,
        "states_evaluated": candidates,
        "best_loss": best_loss,
        "best_positive_defect_sum": best_defect,
        "repair_attempts": repair_attempts,
        "repair_states": repair_states,
        "out_masks": masks,
        "outdegrees": check["outdegrees"],
        "second_sizes": check["second_sizes"],
        "margins": check["margins"],
        "blockers": check["blockers"],
        "extra_blocker_defects": check["extra_blocker_defects"],
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
    if shard < 0 or shard >= len(ENDPOINT_TARGETS):
        raise ValueError(f"shard must be in [0, {len(ENDPOINT_TARGETS) - 1}]")
    endpoint = ENDPOINT_TARGETS[shard]
    target_degree = endpoint["degree"]
    target_blockers = endpoint["blockers"]
    bucket = None
    strategy = f"{endpoint['name']}_full_orbit_triangle_endpoint"
    seed = (BASE_SEED ^ (shard << 32) ^ 0x475055) & ((1 << 63) - 1)
    torch.manual_seed(seed)
    random.seed(seed)
    generator = torch.Generator(device=device)
    generator.manual_seed(seed)

    population = initial_population(
        batch, target_degree, bucket, device, generator
    )
    data = mutation_data(device)
    weights = torch.ones((batch, N), dtype=torch.int16, device=device)
    metrics = evaluate(
        population, target_degree, target_blockers, endpoint
    )
    # evaluate() runs under inference_mode. Persistent population metrics are
    # updated in place, so detach them from inference storage first.
    metrics = {
        key: value.clone() if isinstance(value, torch.Tensor) else value
        for key, value in metrics.items()
    }
    losses = metrics["loss"].clone()
    scores = dynamic_score(metrics, weights)
    initial_key = (
        losses.to(torch.int64) * 100
        + metrics["positive_defect_sum"].to(torch.int64)
    )
    best_index = int(initial_key.argmin())
    best_bits = population[best_index].clone()
    best_loss = int(losses[best_index])
    best_defect = int(metrics["positive_defect_sum"][best_index])
    start = time.monotonic()
    generations = 0
    candidates = batch
    repair_attempts = 0
    repair_states = 0
    repair_seen: set[tuple[bool, ...]] = set()

    witness_found = bool((metrics["raw_loss"] == 0).any())
    if witness_found:
        best_index = int(torch.nonzero(metrics["raw_loss"] == 0)[0])
        best_bits = population[best_index].clone()
    while time.monotonic() - start < seconds and not witness_found:
        children = focused_mutation(
            population, metrics, weights, generator, data
        )
        child_metrics = evaluate(
            children, target_degree, target_blockers, endpoint
        )
        child_losses = child_metrics["loss"]
        child_scores = dynamic_score(child_metrics, weights)
        candidates += batch
        witness_rows = torch.nonzero(child_metrics["raw_loss"] == 0).flatten()
        if witness_rows.numel():
            candidate = children[int(witness_rows[0])].clone()
            independent = verify_masks(bits_to_masks(candidate))
            if independent["is_pisa"]:
                best_bits = candidate
                best_loss = 0
                best_defect = 0
                witness_found = True
                break

        # Dynamic weighted local search: persistent walkers accept fine-score
        # improvements, with sparse noise for basin escape.
        noise = torch.rand(batch, device=device, generator=generator) < 0.006
        accept = (child_scores <= scores) | noise
        population[accept] = children[accept]
        losses[accept] = child_losses[accept]
        scores[accept] = child_scores[accept]
        for key, value in metrics.items():
            child_value = child_metrics.get(key)
            if (
                isinstance(value, torch.Tensor)
                and isinstance(child_value, torch.Tensor)
                and value.ndim > 0
                and value.shape[0] == batch
            ):
                value[accept] = child_value[accept]

        combined_key = (
            losses.to(torch.int64) * 100
            + metrics["positive_defect_sum"].to(torch.int64)
        )
        generation_best = int(combined_key.argmin())
        generation_loss = int(losses[generation_best])
        generation_defect = int(metrics["positive_defect_sum"][generation_best])
        if (generation_loss, generation_defect) < (best_loss, best_defect):
            best_loss, best_defect = generation_loss, generation_defect
            best_bits = population[generation_best].clone()
            print(
                f"shard={shard} generation={generations} best_loss={best_loss} "
                f"blocker_defect={best_defect} "
                f"candidates={candidates}",
                flush=True,
            )

        generations += 1
        # NuWLS-style persistent constraint weights distinguish states that
        # all had the same v6 score 10201.
        if generations % 16 == 0:
            violated = metrics["margin"] > 0
            weights = torch.clamp(
                weights + violated.to(torch.int16), max=64
            )
            scores = dynamic_score(metrics, weights)

        # Exact GPU local repair is invoked only on the true one-offender,
        # margin-one plateau. It checks all subsets up to radius six in the
        # offender/blocker kernel, rather than waiting for random mutations.
        best_raw_loss = int(metrics["raw_loss"][generation_best])
        if best_raw_loss == 10201:
            signature = tuple(best_bits.detach().cpu().tolist())
            if signature not in repair_seen and len(repair_seen) < 64:
                repair_seen.add(signature)
                repair_attempts += 1
                (
                    repaired_bits,
                    repaired_loss,
                    repaired_defect,
                    checked,
                    found,
                ) = exact_local_repair(
                    best_bits,
                    target_degree,
                    target_blockers,
                    device,
                    endpoint,
                )
                repair_states += checked
                candidates += checked
                if (repaired_loss, repaired_defect) < (best_loss, best_defect):
                    best_bits = repaired_bits
                    best_loss, best_defect = repaired_loss, repaired_defect
                    worst = int(scores.argmax())
                    population[worst] = repaired_bits
                    weights[worst].fill_(1)
                    refreshed = evaluate(
                        population[worst : worst + 1],
                        target_degree,
                        target_blockers,
                        endpoint,
                    )
                    for key, value in metrics.items():
                        new_value = refreshed.get(key)
                        if (
                            isinstance(value, torch.Tensor)
                            and isinstance(new_value, torch.Tensor)
                            and value.ndim > 0
                            and value.shape[0] == batch
                        ):
                            value[worst] = new_value[0]
                    losses[worst] = refreshed["loss"][0]
                    scores[worst] = dynamic_score(
                        refreshed, weights[worst : worst + 1]
                    )[0]
                if found:
                    best_loss = 0
                    witness_found = True
                    break

        # Maintain a broad elite source and periodically inject fresh random
        # walkers. This prevents the whole batch from cloning one 10201 basin.
        if generations % 32 == 0:
            elite_count = max(64, batch // 64)
            worst_count = batch // 4
            elite = scores.topk(elite_count, largest=False).indices
            worst = scores.topk(worst_count, largest=True).indices
            parents = elite[
                torch.randint(
                    0, elite_count, (worst_count,), device=device, generator=generator
                )
            ]
            population[worst] = mutate_edges(
                population[parents], generator, mixed=True
            )
            weights[worst] = weights[parents]
            refreshed = evaluate(
                population[worst], target_degree, target_blockers, endpoint
            )
            losses[worst] = refreshed["loss"]
            for key, value in metrics.items():
                new_value = refreshed.get(key)
                if (
                    isinstance(value, torch.Tensor)
                    and isinstance(new_value, torch.Tensor)
                    and value.ndim > 0
                    and value.shape[0] == batch
                ):
                    value[worst] = new_value
            scores[worst] = dynamic_score(refreshed, weights[worst])
            candidates += worst_count
        if generations % 64 == 0:
            fresh_count = batch // 8
            worst = scores.topk(fresh_count, largest=True).indices
            population[worst] = initial_population(
                fresh_count, target_degree, bucket, device, generator
            )
            weights[worst].fill_(1)
            refreshed = evaluate(
                population[worst], target_degree, target_blockers, endpoint
            )
            losses[worst] = refreshed["loss"]
            for key, value in metrics.items():
                new_value = refreshed.get(key)
                if (
                    isinstance(value, torch.Tensor)
                    and isinstance(new_value, torch.Tensor)
                    and value.ndim > 0
                    and value.shape[0] == batch
                ):
                    value[worst] = new_value
            scores[worst] = dynamic_score(refreshed, weights[worst])
            candidates += fresh_count

    elapsed = time.monotonic() - start
    return save_record(
        output,
        shard,
        strategy,
        elapsed,
        generations,
        candidates,
        best_bits,
        best_loss,
        best_defect,
        repair_attempts,
        repair_states,
        target_degree,
        target_blockers,
        bucket,
        endpoint,
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--shard-start", type=int, default=0)
    parser.add_argument("--shard-count", type=int, default=54)
    parser.add_argument("--seconds-per-shard", type=int, default=300)
    parser.add_argument("--batch-size", type=int, default=16384)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("/kaggle/working/k16_gpu_results_v8"),
    )
    parser.add_argument("--device", default="cuda:0")
    parser.add_argument("--allow-cpu", action="store_true")
    args = parser.parse_args()

    partition_self_test()
    print(
        "V8_ENDPOINT_GATE_PASS "
        f"distinct_endpoint_targets={len(ENDPOINT_TARGETS)} "
        f"d7_patterns={math.comb(13, 6)} "
        f"d6_patterns={math.comb(13, 5)} "
        "each_target_samples_full_zero_pattern_orbit=true",
        flush=True,
    )

    if torch.cuda.is_available():
        device = torch.device(args.device)
        torch.cuda.set_device(device)
        print(f"CUDA device: {device} {torch.cuda.get_device_name(device)}")
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
                    "campaign": "K16-PISA-v8-endpoint-aware-triangle-search",
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
