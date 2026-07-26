#!/usr/bin/env python3
"""K16 Pisa v7: exact local-median-order campaign.

This campaign uses a theorem of Havet and Thomasse:

* every tournament has a local median order;
* the feed (last) vertex of every local median order has a large second
  out-neighbourhood.

In a Pisa tournament every margin is nonpositive, so the feed vertex has
margin exactly zero.  We may therefore relabel a local median order as

    1, 2, ..., 15, 0

and pin vertex 0 to the selected zero type without loss of generality.

The feedback property adds two inequalities for every interval.  It also
makes the displayed order a directed Hamiltonian path.  Strong components
of a tournament are totally ordered, and a directed Hamiltonian path visits
them in that order.  Hence the tournament is strong exactly when every
proper prefix has at least one reverse arc entering it from the suffix.  This
replaces the score-permutation strongness encoding by only 15 prefix cuts.

The boxes below are the exact still-open parent layers after the completed
v6 closures of d7/b1 total-blocker layers 14 and 15.  They overlap the finer
v6 orbit boxes deliberately: this is an independent exact algorithm.
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
from k16_pisa_solver import (  # noqa: E402
    EXCLUDED_PROFILES,
    TerminalTournamentModel,
    arc,
    exact_and,
    extract_full,
    fixed_edges_from_out,
    near_regular_even,
    relabel,
    verify,
)

N = 16
MODEL_VERSION = "k16-pisa-v7.1-lmo-v6-unknown-only-20260727"
FIXED_LMO = tuple(range(1, N)) + (0,)
CUBE_EDGES = ((0, 1), (0, 2), (0, 3))
CUBE_COUNT = 1 << len(CUBE_EDGES)
GATE12 = [
    0x1C6, 0x9C4, 0x618, 0xC33, 0xC23, 0x9C7,
    0x69C, 0x71C, 0x65C, 0xC3B, 0x823, 0x1C5,
]

# Exact v6 closures obtained in run 30203156507.  The v7.1 formulation
# translates these orbit labels into invariant conditions around the LMO feed
# vertex, so none of the 21 v6-UNSAT boxes is searched again.  The five whole
# layers B14/B15 are absent from BOXES; the 16 entries below are subboxes
# inside the six remaining parent layers.
D7_CLOSED_BLOCKER_DEGREES = {
    16: {11, 12},
    17: {11, 12, 13},
    18: {12, 13},
    19: {13, 14},
}
D6_CLOSED_MIN_DEGREE_WINS = {
    (9, 2),
    (10, 2),
    (11, 2),
    (12, 1),
    (12, 2),
    (13, 1),
    (13, 2),
}


def box_specs() -> dict[str, dict]:
    specs = {}
    for total_b in (16, 17, 18, 19):
        specs[f"lmo_d7_b1_B{total_b}"] = {
            "degree": 7,
            "blockers": 1,
            "total_b": total_b,
        }
    specs["lmo_d7_b1_B20plus"] = {
        "degree": 7,
        "blockers": 1,
        "total_b": "20+",
    }
    specs["lmo_d6_b3_B20plus"] = {
        "degree": 6,
        "blockers": 3,
        "total_b": "20+",
    }
    return specs


BOXES = box_specs()


def matrix_json() -> str:
    return json.dumps(
        {
            "include": [
                {"box": box, "cube": cube}
                for box in sorted(BOXES)
                for cube in range(CUBE_COUNT)
            ]
        },
        separators=(",", ":"),
    )


def median_order(out: list[int]) -> list[int]:
    """Return an exact median order by subset dynamic programming."""
    n = len(out)
    size = 1 << n
    score = [-1] * size
    last = [-1] * size
    score[0] = 0

    for mask in range(1, size):
        bits = mask
        while bits:
            bit = bits & -bits
            v = bit.bit_length() - 1
            previous = mask ^ bit
            gain = 0
            previous_bits = previous
            while previous_bits:
                u_bit = previous_bits & -previous_bits
                u = u_bit.bit_length() - 1
                gain += arc(out, u, v)
                previous_bits ^= u_bit
            candidate = score[previous] + gain
            if candidate > score[mask]:
                score[mask] = candidate
                last[mask] = v
            bits ^= bit

    order_reversed = []
    mask = size - 1
    while mask:
        v = last[mask]
        if v < 0:
            raise RuntimeError("median-order reconstruction failed")
        order_reversed.append(v)
        mask ^= 1 << v
    return list(reversed(order_reversed))


def feedback_holds(out: list[int], order: list[int]) -> bool:
    n = len(order)
    for i in range(n):
        for j in range(i + 1, n):
            span = j - i
            first_out = sum(arc(out, order[i], order[k]) for k in range(i + 1, j + 1))
            last_in = sum(arc(out, order[k], order[j]) for k in range(i, j))
            if 2 * first_out < span or 2 * last_in < span:
                return False
    return True


def canonical_median_gate(out: list[int]) -> tuple[list[int], int, int]:
    order = median_order(out)
    if not feedback_holds(out, order):
        raise RuntimeError("dynamic-programming median order lacks feedback property")

    # New labels are: feed -> 0, then the preceding median-order vertices
    # -> 1..n-1.  Thus the fixed local median order is 1,2,...,n-1,0.
    canon = relabel(out, [order[-1], *order[:-1]])
    fixed_order = list(range(1, len(out))) + [0]
    if not feedback_holds(canon, fixed_order):
        raise RuntimeError("median-order relabelling failed")
    check = verify(canon)
    if not check["is_pisa"] or check["margins"][0] != 0:
        raise RuntimeError("feed vertex did not become a zero-margin point")
    return canon, check["outdegrees"][0], check["blockers"][0]


def add_local_median_constraints(
    tm: TerminalTournamentModel,
    order: tuple[int, ...] | list[int],
) -> None:
    """Add the feedback property and exact prefix-cut strongness."""
    m = tm.model
    n = len(order)

    # Feedback property: the first vertex of every interval has at least
    # half of the interval arcs pointing out, and the last has at least half
    # pointing in.
    for i in range(n):
        for j in range(i + 1, n):
            span = j - i
            m.Add(
                2 * sum(tm.A(order[i], order[k]) for k in range(i + 1, j + 1))
                >= span
            )
            m.Add(
                2 * sum(tm.A(order[k], order[j]) for k in range(i, j))
                >= span
            )

    # The length-two feedback constraints already give the Hamiltonian path
    # order[i] -> order[i+1].  Its SCC blocks are contiguous.  A reverse arc
    # across every proper prefix is therefore equivalent to strongness.
    for cut in range(1, n):
        prefix = order[:cut]
        suffix = order[cut:]
        m.AddBoolOr([tm.A(v, u) for u in prefix for v in suffix])


def _reified_equal(model, value, target: int, name: str):
    flag = model.NewBoolVar(name)
    model.Add(value == target).OnlyEnforceIf(flag)
    model.Add(value != target).OnlyEnforceIf(flag.Not())
    return flag


def add_v6_unknown_only_cuts(
    tm: TerminalTournamentModel,
    spec: dict,
) -> int:
    """Exclude exactly the orbit subboxes proved UNSAT by completed v6.

    For d7/b1 the unique blocker's degree is label-invariant.

    For d6/b3, an anchor is any minimum-degree blocker of the feed.  The v6
    pattern 00/01/11 is exactly the number 0/1/2 of other feed blockers beaten
    by that anchor.  We forbid every (minimum degree, win count) pair whose
    complete v6 orbit box was UNSAT.  The construction is label-invariant and
    therefore compatible with the fixed local median order.
    """
    m = tm.model
    degree = int(spec["degree"])
    blockers = int(spec["blockers"])

    if (degree, blockers) == (7, 1):
        total_b = spec["total_b"]
        excluded = D7_CLOSED_BLOCKER_DEGREES.get(total_b, set())
        for x in range(1, N):
            q = tm.blocker[(0, x)]
            for closed_degree in excluded:
                m.Add(tm.degree[x] != closed_degree).OnlyEnforceIf(q)
        return len(excluded)

    if (degree, blockers) != (6, 3):
        return 0

    # q(0,x) selects the three blockers of the feed.  For each possible
    # anchor x, compute whether it has minimum blocker degree and how many of
    # the other selected blockers it beats.
    for x in range(1, N):
        qx = tm.blocker[(0, x)]
        minimum_conditions = [qx]
        anchor_wins = []

        for y in range(1, N):
            if y == x:
                continue
            qy = tm.blocker[(0, y)]

            le = m.NewBoolVar(f"v71_d_{x}_le_d_{y}")
            m.Add(tm.degree[x] <= tm.degree[y]).OnlyEnforceIf(le)
            m.Add(tm.degree[x] > tm.degree[y]).OnlyEnforceIf(le.Not())

            # min_ok iff y is not a feed blocker, or d(x) <= d(y).
            min_ok = m.NewBoolVar(f"v71_min_ok_{x}_{y}")
            m.AddBoolOr([qy.Not(), le]).OnlyEnforceIf(min_ok)
            m.Add(qy == 1).OnlyEnforceIf(min_ok.Not())
            m.Add(le == 0).OnlyEnforceIf(min_ok.Not())
            minimum_conditions.append(min_ok)

            win = m.NewBoolVar(f"v71_anchor_{x}_beats_blocker_{y}")
            exact_and(m, win, [qy, tm.A(x, y)])
            anchor_wins.append(win)

        is_minimum_blocker = m.NewBoolVar(f"v71_minimum_blocker_{x}")
        exact_and(m, is_minimum_blocker, minimum_conditions)

        wins_count = m.NewIntVar(0, 3, f"v71_anchor_blocker_wins_{x}")
        m.Add(wins_count == sum(anchor_wins))
        degree_flags = {
            d: _reified_equal(m, tm.degree[x], d, f"v71_anchor_{x}_degree_{d}")
            for d in {d for d, _ in D6_CLOSED_MIN_DEGREE_WINS}
        }
        wins_flags = {
            w: _reified_equal(m, wins_count, w, f"v71_anchor_{x}_wins_{w}")
            for w in {w for _, w in D6_CLOSED_MIN_DEGREE_WINS}
        }

        for closed_degree, closed_wins in D6_CLOSED_MIN_DEGREE_WINS:
            forbidden = m.NewBoolVar(
                f"v71_closed_anchor_{x}_d{closed_degree}_w{closed_wins}"
            )
            exact_and(
                m,
                forbidden,
                [
                    is_minimum_blocker,
                    degree_flags[closed_degree],
                    wins_flags[closed_wins],
                ],
            )
            m.Add(forbidden == 0)

    return len(D6_CLOSED_MIN_DEGREE_WINS)


def build_model(spec: dict, *, fixed=None, n: int = N) -> TerminalTournamentModel:
    total_args = {}
    if spec.get("total_b") == "20+":
        total_args["total_b_min"] = 20
    elif spec.get("total_b") is not None:
        total_args["total_b_eq"] = int(spec["total_b"])

    tm = TerminalTournamentModel(
        n,
        fixed=fixed,
        zero_partition=None,
        min_degree=2,
        excluded_profiles=EXCLUDED_PROFILES if n == N else None,
        strongness_mode="external",
        **total_args,
    )
    tm.model.Add(tm.degree[0] == int(spec["degree"]))
    tm.model.Add(tm.bcount[0] == int(spec["blockers"]))
    add_local_median_constraints(tm, tuple(range(1, n)) + (0,))
    if n == N:
        add_v6_unknown_only_cuts(tm, spec)
    return tm


def add_cube_constraints(tm: TerminalTournamentModel, cube: int) -> None:
    if not 0 <= cube < CUBE_COUNT:
        raise ValueError(f"cube must be in 0..{CUBE_COUNT - 1}")
    for bit_index, (u, v) in enumerate(CUBE_EDGES):
        value = (cube >> bit_index) & 1
        tm.model.Add(tm.A(u, v) == value)


def configure(seconds: int, workers: int, seed: int) -> cp_model.CpSolver:
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = seconds
    solver.parameters.num_search_workers = workers
    solver.parameters.random_seed = seed
    solver.parameters.randomize_search = True
    solver.parameters.stop_after_first_solution = True
    solver.parameters.cp_model_presolve = True
    solver.parameters.symmetry_level = 2
    return solver


def solve_gate(name: str, out: list[int], seconds: int, workers: int) -> dict:
    canon, degree, blockers = canonical_median_gate(out)
    check = verify(canon)
    tm = build_model(
        {
            "degree": degree,
            "blockers": blockers,
            "total_b": check["sum_blockers"],
        },
        fixed=fixed_edges_from_out(canon),
        n=len(canon),
    )
    solver = configure(seconds, workers, 20260727 + len(out))
    started = time.time()
    status = solver.Solve(tm.model)
    elapsed = time.time() - started
    if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        raise RuntimeError(
            f"{name} failed: {solver.StatusName(status)} after {elapsed:.3f}s"
        )
    extracted = verify(extract_full(solver, tm))
    if not extracted["is_pisa"]:
        raise RuntimeError(f"{name} failed independent verification")
    return {
        "gate": name,
        "status": "SAT",
        "solver_status": solver.StatusName(status),
        "seconds": round(elapsed, 3),
        "feed_zero_type": [degree, blockers],
        "sum_blockers": check["sum_blockers"],
        "feedback_intervals": len(out) * (len(out) - 1) // 2,
        "verified": True,
    }


def run_gates(seconds: int, workers: int) -> dict:
    gates = [
        solve_gate("K12_exact_median_feed", GATE12, seconds, workers),
        solve_gate(
            "K14_exact_median_feed",
            near_regular_even(14),
            seconds,
            workers,
        ),
    ]
    return {
        "model_version": MODEL_VERSION,
        "status": "PASS",
        "gates": gates,
    }


def solve_box(
    box: str,
    cube: int,
    seconds: int,
    workers: int,
    seed: int,
) -> dict:
    spec = BOXES[box]
    tm = build_model(spec)
    add_cube_constraints(tm, cube)
    solver = configure(seconds, workers, seed)
    started = time.time()
    status = solver.Solve(tm.model)
    elapsed = time.time() - started
    solver_status = solver.StatusName(status)
    logical_status = (
        "SAT"
        if status in (cp_model.OPTIMAL, cp_model.FEASIBLE)
        else "UNSAT"
        if status == cp_model.INFEASIBLE
        else solver_status
    )
    record = {
        "model_version": MODEL_VERSION,
        "algorithm": "local median order feedback plus prefix-cut strongness",
        "box": box,
        "cube": cube,
        "cube_bits": [
            (cube >> bit_index) & 1
            for bit_index in range(len(CUBE_EDGES))
        ],
        "cube_edges": [list(edge) for edge in CUBE_EDGES],
        "status": logical_status,
        "solver_status": solver_status,
        "solver_level_exact": status == cp_model.INFEASIBLE,
        "seconds": round(elapsed, 3),
        "time_limit_seconds": seconds,
        "workers": workers,
        "seed": seed,
        "feed_zero_type": [spec["degree"], spec["blockers"]],
        "total_blockers": spec["total_b"],
        "fixed_local_median_order": list(FIXED_LMO),
        "feedback_constraints": N * (N - 1),
        "strong_prefix_cuts": N - 1,
        "v6_exact_subboxes_excluded": add_v6_unknown_only_cuts_count(spec),
        "coverage": (
            "One of eight mutually exclusive labelled LMO cubes in the full "
            "parent layer. All eight cubes exactly cover that layer."
        ),
        "dependencies": {
            "v6_closed_layers": "d7/b1 total blockers 14 and 15 excluded",
            "near_regular_theorem": "profile 7^8 8^8 excluded",
            "frontier_thin_a": "profile 6^1 7^6 8^9 excluded",
            "frontier_thin_b": "profile 7^9 8^6 9^1 excluded",
        },
        "conflicts": solver.NumConflicts(),
        "branches": solver.NumBranches(),
    }
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        check = verify(extract_full(solver, tm))
        if not check["is_pisa"]:
            raise RuntimeError("solver candidate failed independent verifier")
        record["verified"] = True
        record["witness"] = check
    return record


def add_v6_unknown_only_cuts_count(spec: dict) -> int:
    if (spec["degree"], spec["blockers"]) == (7, 1):
        return len(D7_CLOSED_BLOCKER_DEGREES.get(spec["total_b"], set()))
    if (spec["degree"], spec["blockers"]) == (6, 3):
        return len(D6_CLOSED_MIN_DEGREE_WINS)
    return 0


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--box", choices=sorted(BOXES))
    parser.add_argument("--cube", type=int, choices=range(CUBE_COUNT))
    parser.add_argument("--list-boxes", action="store_true")
    parser.add_argument("--matrix", action="store_true")
    parser.add_argument("--gates-only", action="store_true")
    parser.add_argument("--seconds", type=int, default=3600)
    parser.add_argument("--gate-seconds", type=int, default=60)
    parser.add_argument(
        "--workers",
        type=int,
        default=max(1, min(4, os.cpu_count() or 4)),
    )
    parser.add_argument("--seed", type=int, default=20260727)
    parser.add_argument("--output", type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.list_boxes:
        print("\n".join(sorted(BOXES)))
        return 0
    if args.matrix:
        print(matrix_json())
        return 0
    if args.gates_only:
        record = run_gates(args.gate_seconds, args.workers)
    else:
        if not args.box:
            raise SystemExit("--box is required unless listing/matrix/gates")
        if args.cube is None:
            raise SystemExit("--cube is required for an exact box solve")
        record = solve_box(
            args.box,
            args.cube,
            args.seconds,
            args.workers,
            args.seed,
        )

    print(json.dumps(record, indent=2), flush=True)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(
            json.dumps(record, indent=2) + "\n",
            encoding="utf-8",
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
