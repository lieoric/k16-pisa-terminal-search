#!/usr/bin/env python3
"""Exact weighted-quotient search for the K16 Pisa problem.

For each integer partition of 16 into h positive parts, 10 <= h <= 15,
the program searches for a strong tournament Q and an assignment of those
weights to its vertices such that every strict-second-neighbourhood weighted
margin is non-positive.

The model fixes a directed Hamilton cycle and labels one zero weighted-margin
class as vertex 0.  This is lossless:

* every strong tournament has a directed Hamilton cycle (Camion);
* every feasible weighted quotient has at least two zero classes (the
  Havet--Thomasse theorem applied to the transitive-fibre expansion).

Weights are variables with prescribed multiplicities.  Therefore fixing the
cycle does not silently fix an ordering of unequal fibre sizes.
"""

from __future__ import annotations

import argparse
import itertools
import json
import random
import sys
import time
from collections import Counter
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path

from ortools.sat.python import cp_model

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from pisa_verify import verify


MODEL_VERSION = "k16-weighted-quotient-ladder-v1-cycle-zero2-20260727"
TARGET_ORDER = 16
EXPECTED_COUNTS = {10: 11, 11: 7, 12: 5, 13: 3, 14: 2, 15: 1}


def integer_partitions(
    total: int,
    length: int,
    maximum: int | None = None,
):
    """Yield non-increasing positive integer partitions."""
    if length == 0:
        if total == 0:
            yield ()
        return
    if total < length:
        return
    if maximum is None:
        maximum = total
    upper = min(maximum, total - length + 1)
    for first in range(upper, 0, -1):
        for rest in integer_partitions(total - first, length - 1, first):
            yield (first, *rest)


def pattern_table() -> list[dict]:
    records = []
    for h in range(15, 9, -1):
        patterns = list(integer_partitions(TARGET_ORDER, h))
        if len(patterns) != EXPECTED_COUNTS[h]:
            raise AssertionError((h, len(patterns), EXPECTED_COUNTS[h]))
        for index, weights in enumerate(patterns):
            records.append(
                {
                    "box": f"h{h}_p{index:02d}",
                    "h": h,
                    "pattern_index": index,
                    "weights": list(weights),
                }
            )
    if len(records) != 29:
        raise AssertionError(len(records))
    return records


def find_pattern(box: str) -> dict:
    for record in pattern_table():
        if record["box"] == box:
            return record
    raise ValueError(f"unknown box {box!r}")


def strict_second_mask(out: list[int], vertex: int) -> int:
    second = 0
    bits = out[vertex]
    while bits:
        bit = bits & -bits
        intermediate = bit.bit_length() - 1
        second |= out[intermediate]
        bits ^= bit
    return second & ~out[vertex] & ~(1 << vertex)


def weighted_margins(out: list[int], weights: list[int]) -> list[int]:
    margins = []
    for vertex in range(len(out)):
        second = strict_second_mask(out, vertex)
        out_weight = sum(
            weights[x]
            for x in range(len(out))
            if (out[vertex] >> x) & 1
        )
        second_weight = sum(
            weights[x]
            for x in range(len(out))
            if (second >> x) & 1
        )
        margins.append(second_weight - out_weight)
    return margins


def is_strong(out: list[int]) -> bool:
    n = len(out)
    full = (1 << n) - 1

    def closure(reverse: bool) -> int:
        graph = out
        if reverse:
            graph = [0] * n
            for u in range(n):
                for v in range(n):
                    if (out[u] >> v) & 1:
                        graph[v] |= 1 << u
        seen = frontier = 1
        while frontier:
            nxt = 0
            bits = frontier
            while bits:
                bit = bits & -bits
                u = bit.bit_length() - 1
                nxt |= graph[u]
                bits ^= bit
            nxt &= full ^ seen
            seen |= nxt
            frontier = nxt
        return seen

    return closure(False) == full and closure(True) == full


def expand_transitive_fibres(
    quotient: list[int],
    weights: list[int],
) -> list[int]:
    offsets = []
    total = 0
    for weight in weights:
        offsets.append(total)
        total += weight
    expanded = [0] * total
    for p, weight in enumerate(weights):
        start = offsets[p]
        # Transitive fibre: earlier local vertices beat later local vertices.
        for i in range(weight):
            for j in range(i + 1, weight):
                expanded[start + i] |= 1 << (start + j)

    for p in range(len(quotient)):
        for q in range(len(quotient)):
            if p == q or not ((quotient[p] >> q) & 1):
                continue
            for i in range(weights[p]):
                for j in range(weights[q]):
                    expanded[offsets[p] + i] |= 1 << (offsets[q] + j)
    return expanded


@dataclass
class WeightedQuotientModel:
    h: int
    weight_pattern: tuple[int, ...]
    model: cp_model.CpModel
    arc: dict[tuple[int, int], cp_model.IntVar]
    blocker: dict[tuple[int, int], cp_model.IntVar]
    weight: list[cp_model.IntVar]
    zero: list[cp_model.IntVar]
    score: list[cp_model.IntVar]


def build_model(weight_pattern: tuple[int, ...]) -> WeightedQuotientModel:
    h = len(weight_pattern)
    total_weight = sum(weight_pattern)
    if not 3 <= h <= TARGET_ORDER:
        raise ValueError(h)
    if total_weight < h or min(weight_pattern) <= 0:
        raise ValueError(weight_pattern)

    model = cp_model.CpModel()

    # Use explicit ordered arc variables.  This keeps every multiplication
    # below on a positive BoolVar rather than on a negated literal.
    arc = {
        (u, v): model.NewBoolVar(f"a_{u}_{v}")
        for u in range(h)
        for v in range(h)
        if u != v
    }
    for u in range(h):
        for v in range(u + 1, h):
            model.Add(arc[(u, v)] + arc[(v, u)] == 1)

    # Strong tournament <=> it has a directed Hamilton cycle.  Any chosen
    # zero class can be the first label on that cycle.
    for u in range(h - 1):
        model.Add(arc[(u, u + 1)] == 1)
    model.Add(arc[(h - 1, 0)] == 1)

    values = sorted(set(weight_pattern))
    multiplicities = Counter(weight_pattern)
    domain = cp_model.Domain.FromValues(values)
    weight = [
        model.NewIntVarFromDomain(domain, f"weight_{v}")
        for v in range(h)
    ]
    is_weight: dict[tuple[int, int], cp_model.IntVar] = {}
    for vertex in range(h):
        flags = []
        for value in values:
            flag = model.NewBoolVar(f"weight_{vertex}_is_{value}")
            is_weight[(vertex, value)] = flag
            model.Add(weight[vertex] == value).OnlyEnforceIf(flag)
            model.Add(weight[vertex] != value).OnlyEnforceIf(flag.Not())
            flags.append(flag)
        model.AddExactlyOne(flags)
    for value in values:
        model.Add(
            sum(is_weight[(vertex, value)] for vertex in range(h))
            == multiplicities[value]
        )

    # p[v,u,x] iff v -> u -> x.
    path: dict[tuple[int, int, int], cp_model.IntVar] = {}
    for v in range(h):
        for x in range(h):
            if x == v:
                continue
            for u in range(h):
                if u == v or u == x:
                    continue
                p = model.NewBoolVar(f"path_{v}_{u}_{x}")
                path[(v, u, x)] = p
                model.Add(p <= arc[(v, u)])
                model.Add(p <= arc[(u, x)])
                model.Add(p >= arc[(v, u)] + arc[(u, x)] - 1)

    # q[v,x] iff x is an in-neighbour of v that v cannot reach in two
    # steps.  These are exactly the weighted blocker terms.
    blocker: dict[tuple[int, int], cp_model.IntVar] = {}
    for v in range(h):
        for x in range(h):
            if x == v:
                continue
            q = model.NewBoolVar(f"blocker_{v}_{x}")
            blocker[(v, x)] = q
            paths = [
                path[(v, u, x)]
                for u in range(h)
                if u != v and u != x
            ]
            model.Add(q <= arc[(x, v)])
            for p in paths:
                model.Add(q + p <= 1)
            model.Add(q >= arc[(x, v)] - sum(paths))

    maximum_weight = max(weight_pattern)
    out_weight = []
    blocker_weight = []
    score = []
    zero = []
    for v in range(h):
        outgoing_products = []
        blocker_products = []
        for x in range(h):
            if x == v:
                continue
            out_product = model.NewIntVar(
                0,
                maximum_weight,
                f"weighted_arc_{v}_{x}",
            )
            model.AddMultiplicationEquality(
                out_product,
                [weight[x], arc[(v, x)]],
            )
            outgoing_products.append(out_product)

            blocker_product = model.NewIntVar(
                0,
                maximum_weight,
                f"weighted_blocker_{v}_{x}",
            )
            model.AddMultiplicationEquality(
                blocker_product,
                [weight[x], blocker[(v, x)]],
            )
            blocker_products.append(blocker_product)

        outgoing = model.NewIntVar(0, total_weight, f"out_weight_{v}")
        blocked = model.NewIntVar(0, total_weight, f"block_weight_{v}")
        model.Add(outgoing == sum(outgoing_products))
        model.Add(blocked == sum(blocker_products))
        out_weight.append(outgoing)
        blocker_weight.append(blocked)

        # score = t(v) + 2*w(N1+(v)) + w(blockers(v)).
        # Weighted margin <= 0 iff score >= total weight, and equality means zero
        # weighted margin.
        vertex_score = model.NewIntVar(
            0,
            3 * total_weight,
            f"score_{v}",
        )
        model.Add(
            vertex_score == weight[v] + 2 * outgoing + blocked
        )
        model.Add(vertex_score >= total_weight)
        score.append(vertex_score)

        z = model.NewBoolVar(f"zero_weighted_margin_{v}")
        model.Add(vertex_score == total_weight).OnlyEnforceIf(z)
        model.Add(vertex_score >= total_weight + 1).OnlyEnforceIf(z.Not())
        zero.append(z)

    # WLOG choose a zero class as the first vertex of the fixed cycle.
    model.Add(zero[0] == 1)

    # Safe Havet--Thomasse cut.  In the transitive-fibre expansion there
    # are no globally dominated vertices, hence there are two Seymour
    # vertices.  Only the sink of a transitive fibre can have local
    # margin zero, so they belong to two distinct zero weighted classes.
    model.Add(sum(zero) >= 2)

    return WeightedQuotientModel(
        h=h,
        weight_pattern=weight_pattern,
        model=model,
        arc=arc,
        blocker=blocker,
        weight=weight,
        zero=zero,
        score=score,
    )


def configure_solver(
    seconds: int,
    workers: int,
    seed: int,
    log_progress: bool,
) -> cp_model.CpSolver:
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = seconds
    solver.parameters.num_search_workers = max(1, workers)
    solver.parameters.random_seed = seed
    solver.parameters.randomize_search = True
    solver.parameters.cp_model_presolve = True
    solver.parameters.symmetry_level = 2
    solver.parameters.stop_after_first_solution = True
    solver.parameters.log_search_progress = log_progress
    return solver


def extract_solution(
    solver: cp_model.CpSolver,
    built: WeightedQuotientModel,
) -> dict:
    quotient = [0] * built.h
    for u in range(built.h):
        for v in range(built.h):
            if u != v and solver.Value(built.arc[(u, v)]):
                quotient[u] |= 1 << v
    weights = [solver.Value(variable) for variable in built.weight]
    weighted = weighted_margins(quotient, weights)
    zero_classes = [i for i, value in enumerate(weighted) if value == 0]
    expanded = expand_transitive_fibres(quotient, weights)
    check = verify(expanded)

    if sorted(weights, reverse=True) != list(built.weight_pattern):
        raise RuntimeError("solver changed the prescribed weight multiset")
    if not is_strong(quotient):
        raise RuntimeError("quotient failed independent strong check")
    if max(weighted) != 0 or len(zero_classes) < 2:
        raise RuntimeError("weighted quotient failed independent margin check")
    if not check["is_pisa"]:
        raise RuntimeError("expanded K16 witness failed independent verifier")

    return {
        "quotient_out_masks": quotient,
        "quotient_arcs": [
            [u, v]
            for u in range(built.h)
            for v in range(built.h)
            if (quotient[u] >> v) & 1
        ],
        "weights_by_vertex": weights,
        "weighted_margins": weighted,
        "zero_weighted_classes": zero_classes,
        "expanded_k16_out_masks": expanded,
        "expanded_k16_verification": check,
    }


def solve_pattern(
    pattern: dict,
    *,
    seconds: int,
    workers: int,
    seed: int,
    log_progress: bool,
) -> dict:
    started = time.monotonic()
    built = build_model(tuple(pattern["weights"]))
    solver = configure_solver(seconds, workers, seed, log_progress)
    status = solver.Solve(built.model)
    elapsed = time.monotonic() - started

    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        logical_status = "SAT"
    elif status == cp_model.INFEASIBLE:
        logical_status = "UNSAT"
    elif status == cp_model.MODEL_INVALID:
        logical_status = "ERROR"
    else:
        logical_status = "UNKNOWN"

    result = {
        "schema": "k16-weighted-quotient-pattern-result-v1",
        "model_version": MODEL_VERSION,
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "box": pattern["box"],
        "h": pattern["h"],
        "pattern_index": pattern["pattern_index"],
        "weight_multiset": pattern["weights"],
        "total_weight": sum(pattern["weights"]),
        "status": logical_status,
        "solver_status": solver.StatusName(status),
        "solver_level_exact": logical_status == "UNSAT",
        "seconds_budget": seconds,
        "wall_seconds": round(elapsed, 3),
        "workers": workers,
        "seed": seed,
        "branches": solver.NumBranches(),
        "conflicts": solver.NumConflicts(),
        "coverage": (
            "All strong h-vertex quotient tournaments with this weight "
            "multiset, modulo lossless Hamilton-cycle/zero-class relabelling."
        ),
        "theorem_dependencies": [
            "Camion: every strong tournament has a directed Hamilton cycle.",
            (
                "Havet--Thomasse plus transitive-fibre expansion: every "
                "feasible weighted quotient has at least two zero classes."
            ),
        ],
    }
    if logical_status == "SAT":
        result["witness"] = extract_solution(solver, built)
    elif logical_status == "ERROR":
        result["error"] = "CP-SAT reported MODEL_INVALID"
    return result


def write_result(result: dict, output: Path) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_suffix(output.suffix + ".tmp")
    temporary.write_text(
        json.dumps(result, indent=2, sort_keys=True),
        encoding="utf-8",
    )
    temporary.replace(output)


def run_gates(seconds: int, workers: int) -> dict:
    if len(pattern_table()) != 29:
        raise RuntimeError("29-pattern coverage gate failed")

    # Pure identity gate on random quotients and positive weights.
    rng = random.Random(20260727)
    identity_vertices = 0
    for _ in range(100):
        h = rng.randint(3, 8)
        out = [0] * h
        for u in range(h):
            for v in range(u + 1, h):
                if rng.getrandbits(1):
                    out[u] |= 1 << v
                else:
                    out[v] |= 1 << u
        weights = [rng.randint(1, 4) for _ in range(h)]
        expanded = expand_transitive_fibres(out, weights)
        quotient_margin = weighted_margins(out, weights)
        expanded_margin = verify(expanded)["margins"]
        offset = 0
        for p, weight in enumerate(weights):
            # Sink of TT_weight has local margin zero.
            sink = offset + weight - 1
            if expanded_margin[sink] != quotient_margin[p]:
                raise RuntimeError("lexicographic margin identity failed")
            offset += weight
            identity_vertices += 1

    positive_patterns = [
        {
            "box": "gate_c3_weights_2_2_2",
            "h": 3,
            "pattern_index": 0,
            "weights": [2, 2, 2],
        },
        {
            "box": "gate_c7_weights_2x7",
            "h": 7,
            "pattern_index": 0,
            "weights": [2] * 7,
        },
    ]
    positive = [
        solve_pattern(
            pattern,
            seconds=seconds,
            workers=workers,
            seed=20260727,
            log_progress=False,
        )
        for pattern in positive_patterns
    ]
    if any(result["status"] != "SAT" for result in positive):
        raise RuntimeError(f"positive solver gate failed: {positive}")

    negative = solve_pattern(
        {
            "box": "gate_c3_unequal_weights",
            "h": 3,
            "pattern_index": 0,
            "weights": [6, 5, 5],
        },
        seconds=seconds,
        workers=workers,
        seed=20260727,
        log_progress=False,
    )
    if negative["status"] != "UNSAT":
        raise RuntimeError(f"negative solver gate failed: {negative}")

    # Exhaustive cross-check against a solver-independent enumerator on all
    # 28 weight multisets of totals 6, 7 and 8 with quotient orders 3..5.
    # This specifically audits the fixed-cycle, weight-permutation and
    # labelled-zero reductions.
    crosscheck_patterns = 0
    crosscheck_sat = 0
    for total in (6, 7, 8):
        for h in range(3, min(5, total) + 1):
            pairs = [
                (u, v)
                for u in range(h)
                for v in range(u + 1, h)
            ]
            strong_tournaments = []
            for bits in range(1 << len(pairs)):
                out = [0] * h
                for index, (u, v) in enumerate(pairs):
                    if (bits >> index) & 1:
                        out[u] |= 1 << v
                    else:
                        out[v] |= 1 << u
                if is_strong(out):
                    strong_tournaments.append(out)

            for pattern in integer_partitions(total, h):
                expected = False
                for out in strong_tournaments:
                    for assignment in set(itertools.permutations(pattern)):
                        margin = weighted_margins(out, list(assignment))
                        if max(margin) <= 0 and sum(x == 0 for x in margin) >= 2:
                            expected = True
                            break
                    if expected:
                        break
                observed = solve_pattern(
                    {
                        "box": "gate_small_exhaustive",
                        "h": h,
                        "pattern_index": 0,
                        "weights": list(pattern),
                    },
                    seconds=seconds,
                    workers=workers,
                    seed=20260727,
                    log_progress=False,
                )
                if observed["status"] == "UNKNOWN":
                    raise RuntimeError(
                        f"small exhaustive gate timed out: {(total, h, pattern)}"
                    )
                if (observed["status"] == "SAT") != expected:
                    raise RuntimeError(
                        "small exhaustive gate mismatch: "
                        f"{(total, h, pattern, expected, observed['status'])}"
                    )
                crosscheck_patterns += 1
                crosscheck_sat += int(expected)

    return {
        "schema": "k16-weighted-quotient-gates-v1",
        "model_version": MODEL_VERSION,
        "status": "PASS",
        "pattern_counts": EXPECTED_COUNTS,
        "patterns_total": 29,
        "identity_vertices_checked": identity_vertices,
        "small_exhaustive_patterns_checked": crosscheck_patterns,
        "small_exhaustive_sat_patterns": crosscheck_sat,
        "positive_gates": positive,
        "negative_gate": negative,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--box", help="Solve one h10--h15 weight pattern")
    modes.add_argument("--gates", action="store_true")
    modes.add_argument("--matrix-json", action="store_true")
    modes.add_argument("--list", action="store_true")
    parser.add_argument("--seconds", type=int, default=300)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--seed", type=int, default=20260727)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--log-progress", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.matrix_json:
        print(json.dumps({"include": pattern_table()}, separators=(",", ":")))
        return 0
    if args.list:
        print(json.dumps(pattern_table(), indent=2))
        return 0

    if args.gates:
        result = run_gates(args.seconds, args.workers)
        print(json.dumps(result, indent=2))
    else:
        pattern = find_pattern(args.box)
        print(
            f"START {pattern['box']} h={pattern['h']} "
            f"weights={pattern['weights']} budget={args.seconds}s",
            flush=True,
        )
        result = solve_pattern(
            pattern,
            seconds=args.seconds,
            workers=args.workers,
            seed=args.seed,
            log_progress=args.log_progress,
        )
        print(
            f"FINAL {result['box']} status={result['status']} "
            f"solver={result['solver_status']} "
            f"wall={result['wall_seconds']}s",
            flush=True,
        )
        print(json.dumps(result, indent=2))

    if args.output:
        write_result(result, args.output)
        print(f"SAVED {args.output}", flush=True)
    return 1 if result.get("status") == "ERROR" else 0


if __name__ == "__main__":
    raise SystemExit(main())
