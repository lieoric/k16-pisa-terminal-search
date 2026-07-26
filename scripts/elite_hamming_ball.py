#!/usr/bin/env python3
"""Exact Hamming-ball repair around one v7 near-witness elite."""

from __future__ import annotations

import argparse
import json
import os
import sys
import time
from pathlib import Path

N = 16
MODEL_VERSION = "k16-pisa-v5-elite-exact-ball-20260726"


def arc(out: list[int], u: int, v: int) -> bool:
    return bool((out[u] >> v) & 1)


def relabel(out: list[int], order: list[int]) -> list[int]:
    old_to_new = {old: new for new, old in enumerate(order)}
    new_out = [0] * len(out)
    for old_u in range(len(out)):
        new_u = old_to_new[old_u]
        bits = out[old_u]
        while bits:
            bit = bits & -bits
            old_v = bit.bit_length() - 1
            new_out[new_u] |= 1 << old_to_new[old_v]
            bits ^= bit
    return new_out


def canonicalize_near_zero(out: list[int], degree: int, blockers: int):
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
    from k16_pisa_solver import verify

    check = verify(out)
    if check["outdegrees"][0] != degree:
        raise ValueError("elite zero degree does not match its branch")
    if len(check["blocker_sets"][0]) != blockers:
        raise ValueError("elite zero blocker count does not match its branch")
    if check["margins"][0] != 0:
        raise ValueError("elite vertex 0 is not zero-margin")

    out_neighbors = [v for v in range(1, N) if arc(out, 0, v)]
    blocker_vertices = list(check["blocker_sets"][0])
    blocker_set = set(blocker_vertices)
    other_in = [
        v
        for v in range(1, N)
        if not arc(out, 0, v) and v not in blocker_set
    ]

    def key(v):
        return (check["outdegrees"][v], v)

    out_neighbors.sort(key=key)
    blocker_vertices.sort(key=key)
    other_in.sort(key=key)
    order = [0] + out_neighbors + blocker_vertices + other_in
    return relabel(out, order)


def closed_center_reason(record: dict) -> list[str]:
    reasons = []
    degrees = [int(value) for value in record["outdegrees"]]
    total_b = sum(int(value) for value in record["blockers"])
    if min(degrees) < 2:
        reasons.append("minimum degree below proved floor 2")
    if int(record["target_degree"]) == 7 and total_b <= 11:
        reasons.append("d7 terminal layer B<=11 already closed")
    if int(record["target_degree"]) == 6 and total_b <= 14:
        reasons.append("d6 terminal layer B<=14 already closed")
    return reasons


def solve(
    record: dict,
    radius: int,
    seconds: int,
    workers: int,
    seed: int,
) -> dict:
    from ortools.sat.python import cp_model

    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
    from k16_pisa_solver import (
        EXCLUDED_PROFILES,
        TerminalTournamentModel,
        extract_full,
        verify,
    )

    degree = int(record["target_degree"])
    blockers = int(record["target_blockers"])
    center = canonicalize_near_zero(
        [int(value) for value in record["out_masks"]],
        degree,
        blockers,
    )
    total_b_floor = 12 if degree == 7 else 15
    tm = TerminalTournamentModel(
        N,
        zero_partition=(degree, blockers),
        min_degree=2,
        total_b_min=total_b_floor,
        excluded_profiles=EXCLUDED_PROFILES,
    )

    differences = []
    for u in range(N):
        for v in range(u + 1, N):
            edge = tm.edge[(u, v)]
            center_value = int(arc(center, u, v))
            differences.append(edge.Not() if center_value else edge)
            tm.model.AddHint(edge, center_value)
    tm.model.Add(sum(differences) <= radius)

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = seconds
    solver.parameters.num_search_workers = workers
    solver.parameters.random_seed = seed
    solver.parameters.randomize_search = True
    solver.parameters.stop_after_first_solution = True
    solver.parameters.cp_model_presolve = True
    solver.parameters.symmetry_level = 2

    started = time.time()
    status = solver.Solve(tm.model)
    elapsed = time.time() - started
    status_name = solver.StatusName(status)
    logical_status = (
        "SAT"
        if status in (cp_model.OPTIMAL, cp_model.FEASIBLE)
        else "UNSAT"
        if status == cp_model.INFEASIBLE
        else status_name
    )
    result = {
        "model_version": MODEL_VERSION,
        "source_run": 30190571931,
        "source_shard": int(record["shard"]),
        "status": logical_status,
        "solver_status": status_name,
        "solver_level_exact": status == cp_model.INFEASIBLE,
        "radius": radius,
        "seconds": round(elapsed, 3),
        "time_limit_seconds": seconds,
        "workers": workers,
        "seed": seed,
        "zero_type": [degree, blockers],
        "total_b_floor": total_b_floor,
        "center_loss": int(record["best_loss"]),
        "center_positive_count": int(record["best_positive_count"]),
        "center_known_closed_reasons": closed_center_reason(record),
        "coverage": (
            f"All role-canonical tournaments within Hamming radius {radius} "
            f"of v7 elite shard {record['shard']}"
        ),
    }
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        out = extract_full(solver, tm)
        check = verify(out)
        if not check["is_pisa"]:
            raise RuntimeError("solver candidate failed independent verifier")
        result["verified"] = True
        result["witness"] = check
    return result


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--elites", type=Path, required=True)
    parser.add_argument("--shard", type=int, choices=range(64), required=True)
    parser.add_argument("--radius", type=int, default=4)
    parser.add_argument("--seconds", type=int, default=300)
    parser.add_argument(
        "--workers",
        type=int,
        default=max(1, min(4, os.cpu_count() or 4)),
    )
    parser.add_argument("--seed", type=int, default=20260726)
    parser.add_argument("--output", type=Path)
    return parser.parse_args()


def main():
    args = parse_args()
    payload = json.loads(args.elites.read_text(encoding="utf-8"))
    by_shard = {
        int(record["shard"]): record for record in payload["records"]
    }
    record = by_shard[args.shard]
    result = solve(
        record,
        args.radius,
        args.seconds,
        args.workers,
        args.seed,
    )
    print(
        f"ELITE_BALL_RESULT shard={args.shard} status={result['status']} "
        f"radius={args.radius} seconds={result['seconds']}",
        flush=True,
    )
    if result["status"] == "SAT":
        print("K16_PISA_WITNESS_FOUND_AND_VERIFIED", flush=True)
        print(
            " ".join(
                f"{u}>{v}" for u, v in result["witness"]["arcs"]
            ),
            flush=True,
        )
    elif result["status"] == "UNSAT":
        print("THIS_EXACT_ELITE_HAMMING_BALL_IS_UNSAT", flush=True)
    else:
        print("NO_CONCLUSION_FOR_THIS_ELITE_BALL", flush=True)

    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2), encoding="utf-8")


if __name__ == "__main__":
    main()
