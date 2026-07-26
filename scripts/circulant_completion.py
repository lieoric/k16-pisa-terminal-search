#!/usr/bin/env python3
"""Exact completion search around the C16(1,7,8) Pisa carrier.

The carrier is the lexicographic cycle of eight ordered pairs.  Pair i
dominates pair i-1 (mod 8), and the high member of each pair dominates its low
member.  Its underlying graph is exactly C16(1,7,8); low vertices have
(outdegree, margin)=(2,0) and high vertices have (3,-1).

Any automorphism rotating the eight pair modules preserves this orientation.
Consequently, if a tournament completion has a zero-margin vertex, it can be
rotated to either L_0 or H_0.  The eleven boxes

    low:  d=2,...,7
    high: d=3,...,7

therefore cover every tournament completion of this fixed carrier orientation.
SAT is an unconditional K16 Pisa witness.  INFEASIBLE closes only the named
completion box; all eleven INFEASIBLE results close this carrier completion
family, not all K16 tournaments.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import time
from pathlib import Path

from ortools.sat.python import cp_model

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from k16_pisa_solver import TerminalTournamentModel, extract_full, verify

N = 16
MODULES = 8
MODEL_VERSION = "k16-pisa-c16-1-7-8-completion-v1-20260726"


def carrier_out() -> list[int]:
    out = [0] * N
    for i in range(MODULES):
        low_i, high_i = i, i + MODULES
        prev = (i - 1) % MODULES
        low_prev, high_prev = prev, prev + MODULES

        # Internal ordered pair.
        out[high_i] |= 1 << low_i

        # Directed quotient cycle: module i -> module i-1.
        for u in (low_i, high_i):
            for v in (low_prev, high_prev):
                out[u] |= 1 << v
    return out


def carrier_edges() -> set[tuple[int, int]]:
    steps = (1, 7, 8)
    return {
        tuple(sorted((u, (u + step) % N)))
        for u in range(N)
        for step in steps
        if u != (u + step) % N
    }


def verify_sparse_carrier(out: list[int]) -> dict:
    edges = carrier_edges()
    if len(edges) != 40:
        raise AssertionError(f"expected 40 carrier edges, got {len(edges)}")

    for u in range(N):
        if (out[u] >> u) & 1:
            raise AssertionError("carrier loop")
        for v in range(u + 1, N):
            uv = (out[u] >> v) & 1
            vu = (out[v] >> u) & 1
            expected = (u, v) in edges
            if expected and uv + vu != 1:
                raise AssertionError(f"bad carrier orientation {u},{v}")
            if not expected and uv + vu != 0:
                raise AssertionError(f"non-carrier edge present {u},{v}")

    def reach(reverse: bool) -> int:
        graph = [0] * N
        if reverse:
            for u in range(N):
                bits = out[u]
                while bits:
                    bit = bits & -bits
                    graph[bit.bit_length() - 1] |= 1 << u
                    bits ^= bit
        else:
            graph = out
        seen = frontier = 1
        while frontier:
            nxt = 0
            bits = frontier
            while bits:
                bit = bits & -bits
                nxt |= graph[bit.bit_length() - 1]
                bits ^= bit
            nxt &= ((1 << N) - 1) ^ seen
            seen |= nxt
            frontier = nxt
        return seen

    degrees, second_sizes, margins = [], [], []
    for v in range(N):
        n2 = 0
        bits = out[v]
        while bits:
            bit = bits & -bits
            n2 |= out[bit.bit_length() - 1]
            bits ^= bit
        n2 &= ((1 << N) - 1) ^ out[v]
        n2 &= ((1 << N) - 1) ^ (1 << v)
        d = out[v].bit_count()
        s = n2.bit_count()
        degrees.append(d)
        second_sizes.append(s)
        margins.append(s - d)

    strong = (
        reach(False) == (1 << N) - 1
        and reach(True) == (1 << N) - 1
    )
    expected_degrees = [2] * MODULES + [3] * MODULES
    expected_margins = [0] * MODULES + [-1] * MODULES
    valid = (
        strong
        and degrees == expected_degrees
        and margins == expected_margins
    )
    return {
        "valid": valid,
        "strong": strong,
        "degrees": degrees,
        "second_sizes": second_sizes,
        "margins": margins,
        "edges": sorted(edges),
    }


def fixed_carrier_edges(out: list[int]) -> dict[tuple[int, int], int]:
    return {
        (u, v): int((out[u] >> v) & 1)
        for u, v in sorted(carrier_edges())
    }


def box_specs() -> dict[str, dict]:
    specs = {}
    for orbit, zero_vertex, minimum in (
        ("low", 0, 2),
        ("high", MODULES, 3),
    ):
        for degree in range(minimum, 8):
            blockers = (N - 1) - 2 * degree
            key = f"{orbit}_d{degree}_b{blockers}"
            specs[key] = {
                "orbit": orbit,
                "zero_vertex": zero_vertex,
                "degree": degree,
                "blockers": blockers,
            }
    return specs


BOXES = box_specs()


def build_box(spec: dict) -> TerminalTournamentModel:
    tm = TerminalTournamentModel(
        N,
        fixed=fixed_carrier_edges(carrier_out()),
        min_degree=2,
        total_b_min=8,
    )
    zero = spec["zero_vertex"]
    tm.model.Add(tm.degree[zero] == spec["degree"])
    tm.model.Add(tm.bcount[zero] == spec["blockers"])
    return tm


def solve_box(box: str, seconds: int, workers: int, seed: int) -> dict:
    spec = BOXES[box]
    tm = build_box(spec)
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
    record = {
        "model_version": MODEL_VERSION,
        "box": box,
        **spec,
        "status": (
            "SAT"
            if status in (cp_model.OPTIMAL, cp_model.FEASIBLE)
            else "UNSAT"
            if status == cp_model.INFEASIBLE
            else status_name
        ),
        "solver_status": status_name,
        "solver_level_exact": status == cp_model.INFEASIBLE,
        "seconds": round(elapsed, 3),
        "time_limit_seconds": seconds,
        "workers": workers,
        "seed": seed,
        "carrier": "C16(1,7,8) ordered-pair cycle",
        "carrier_orientation_fixed": True,
    }

    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        out = extract_full(solver, tm)
        check = verify(out)
        if not check["is_pisa"]:
            raise RuntimeError("solver candidate failed independent verifier")
        record["verified"] = True
        record["witness"] = check
    return record


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--box", choices=sorted(BOXES))
    parser.add_argument("--list-boxes", action="store_true")
    parser.add_argument("--gate-only", action="store_true")
    parser.add_argument("--seconds", type=int, default=900)
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
    if args.list_boxes:
        print("\n".join(sorted(BOXES)))
        return

    gate = verify_sparse_carrier(carrier_out())
    if not gate["valid"]:
        raise RuntimeError(f"carrier gate failed: {gate}")
    print(
        "CARRIER_GATE_PASS",
        "profile=2^8_3^8",
        "margins=0^8_-1^8",
        "boxes=11",
        flush=True,
    )
    if args.gate_only:
        return
    if not args.box:
        raise SystemExit("--box is required unless --gate-only/--list-boxes is used")

    record = solve_box(args.box, args.seconds, args.workers, args.seed)
    print(
        f"BOX_RESULT box={args.box} status={record['status']} "
        f"seconds={record['seconds']}",
        flush=True,
    )
    if record["status"] == "SAT":
        print("K16_PISA_WITNESS_FOUND_AND_VERIFIED", flush=True)
        print(
            " ".join(
                f"{u}>{v}" for u, v in record["witness"]["arcs"]
            ),
            flush=True,
        )
    elif record["status"] == "UNSAT":
        print("THIS_EXACT_CARRIER_COMPLETION_BOX_IS_UNSAT", flush=True)
    else:
        print("NO_CONCLUSION_FOR_THIS_BOX", flush=True)

    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(record, indent=2), encoding="utf-8")


if __name__ == "__main__":
    main()
