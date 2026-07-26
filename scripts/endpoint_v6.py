#!/usr/bin/env python3
"""K16 Pisa v6 exact endpoint campaign.

This is an exact refinement of the 43 boxes left UNKNOWN by v5.  It replaces
the score-permutation strongness encoding with exact rooted role cuts.

The d=7,b=1 branch has a unique blocker and is refined by its degree.
The d=6,b=3 tail is additionally split by the unique three canonical patterns
between a minimum-degree anchor blocker and the other two blockers:
00, 01, and 11 (the latter two blockers are interchangeable).

SAT is independently verified. INFEASIBLE closes exactly the named box.
UNKNOWN closes nothing.
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
    extract_full,
    fixed_edges_from_out,
    relabel,
    verify,
)

N = 16
MODEL_VERSION = "k16-pisa-v6-rooted-role-anchor-orbits-20260726"
GATE12 = [
    0x1C6, 0x9C4, 0x618, 0xC33, 0xC23, 0x9C7,
    0x69C, 0x71C, 0x65C, 0xC3B, 0x823, 0x1C5,
]


def _covered_counts(check: dict) -> list[int]:
    counts = [0] * len(check["outdegrees"])
    for blocker_set in check["blocker_sets"]:
        for x in blocker_set:
            counts[x] += 1
    return counts


def canonicalize_anchor_gate(out: list[int], zero_vertex: int) -> tuple:
    """Relabel a fixed positive witness to the v6 anchor role convention."""
    check = verify(out)
    if not check["is_pisa"] or check["margins"][zero_vertex] != 0:
        raise ValueError("bad positive gate or zero vertex")
    covered = _covered_counts(check)

    def key(v: int) -> tuple:
        return (
            check["outdegrees"][v],
            check["blockers"][v],
            covered[v],
            v,
        )

    out_group = sorted(
        [v for v in range(len(out)) if arc(out, zero_vertex, v)],
        key=key,
    )
    blockers = list(check["blocker_sets"][zero_vertex])
    anchor = min(blockers, key=key)
    remaining = [v for v in blockers if v != anchor]
    blocker_zeros = sorted(
        [v for v in remaining if not arc(out, anchor, v)], key=key
    )
    blocker_ones = sorted(
        [v for v in remaining if arc(out, anchor, v)], key=key
    )
    pattern = (0,) * len(blocker_zeros) + (1,) * len(blocker_ones)
    blocker_group = [anchor] + blocker_zeros + blocker_ones
    blocker_set = set(blockers)
    other_in = [
        v
        for v in range(len(out))
        if v != zero_vertex
        and not arc(out, zero_vertex, v)
        and v not in blocker_set
    ]
    anchor_wins = sorted(
        [v for v in other_in if arc(out, anchor, v)], key=key
    )
    anchor_losses = sorted(
        [v for v in other_in if not arc(out, anchor, v)], key=key
    )
    order = (
        [zero_vertex]
        + out_group
        + blocker_group
        + anchor_wins
        + anchor_losses
    )
    canon = relabel(out, order)
    return (
        canon,
        len(out_group),
        len(blockers),
        check["outdegrees"][anchor],
        pattern,
    )


def box_specs() -> dict[str, dict]:
    specs: dict[str, dict] = {}
    d7_layers = {
        "14": range(9, 11),
        "15": range(9, 12),
        "16": range(8, 13),
        "17": range(8, 14),
        "18": range(8, 14),
        "19": range(8, 15),
        "20+": range(8, 15),
    }
    for total_b, degrees in d7_layers.items():
        for anchor_degree in degrees:
            name = f"d7_b1_B{total_b}_anchorD{anchor_degree}"
            specs[name] = {
                "degree": 7,
                "blockers": 1,
                "total_b": total_b,
                "anchor_degree": anchor_degree,
                "pattern": (),
                "parent_v5_box": (
                    f"d7_b1_B{total_b.replace('+', 'plus')}_"
                    f"minblockerD{anchor_degree}"
                ),
            }

    for anchor_degree in range(7, 14):
        for pattern in ((0, 0), (0, 1), (1, 1)):
            wins_in_other = anchor_degree - 7 - sum(pattern)
            if not 0 <= wins_in_other <= 6:
                continue
            pattern_label = "".join(map(str, pattern))
            name = (
                f"d6_b3_B20plus_anchorD{anchor_degree}_"
                f"pattern{pattern_label}"
            )
            specs[name] = {
                "degree": 6,
                "blockers": 3,
                "total_b": "20+",
                "anchor_degree": anchor_degree,
                "pattern": pattern,
                "parent_v5_box": (
                    f"d6_b3_B20plus_minblockerD{anchor_degree}"
                ),
            }
    assert len(specs) == 54
    return specs


BOXES = box_specs()


def matrix_json() -> str:
    return json.dumps(
        {"include": [{"box": box} for box in sorted(BOXES)]},
        separators=(",", ":"),
    )


def build_model(spec: dict) -> TerminalTournamentModel:
    total_args = (
        {"total_b_min": 20}
        if spec["total_b"] == "20+"
        else {"total_b_eq": int(spec["total_b"])}
    )
    return TerminalTournamentModel(
        N,
        zero_partition=(spec["degree"], spec["blockers"]),
        min_degree=2,
        excluded_profiles=EXCLUDED_PROFILES,
        strongness_mode="rooted_role_cuts",
        anchor_refinement={
            "degree": spec["anchor_degree"],
            "other_blocker_pattern": spec["pattern"],
        },
        invariant_role_sort=True,
        **total_args,
    )


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


def run_positive_gate(
    name: str,
    zero_vertex: int,
    seconds: int,
    workers: int,
) -> dict:
    canon, degree, blockers, anchor_degree, pattern = (
        canonicalize_anchor_gate(GATE12, zero_vertex)
    )
    tm = TerminalTournamentModel(
        12,
        fixed=fixed_edges_from_out(canon),
        zero_partition=(degree, blockers),
        min_degree=2,
        total_b_min=6,
        strongness_mode="rooted_role_cuts",
        anchor_refinement={
            "degree": anchor_degree,
            "other_blocker_pattern": pattern,
        },
        invariant_role_sort=True,
    )
    solver = configure(seconds, workers, 20260726 + zero_vertex)
    started = time.time()
    status = solver.Solve(tm.model)
    elapsed = time.time() - started
    if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        raise RuntimeError(
            f"{name} failed: {solver.StatusName(status)} after {elapsed:.3f}s"
        )
    check = verify(extract_full(solver, tm))
    if not check["is_pisa"]:
        raise RuntimeError(f"{name} failed independent verification")
    return {
        "gate": name,
        "status": "SAT",
        "solver_status": solver.StatusName(status),
        "seconds": round(elapsed, 3),
        "zero_type": [degree, blockers],
        "anchor_degree": anchor_degree,
        "anchor_pattern": list(pattern),
        "verified": True,
    }


def run_gates(seconds: int, workers: int) -> dict:
    # K12 has zero-margin examples in both a one-blocker and a three-blocker
    # branch, so these gates exercise both exact rooted cuts and all three
    # anchor-role refinements used by the formal matrix.
    gates = [
        run_positive_gate("K12_d5_b1_rooted_anchor", 0, seconds, workers),
        run_positive_gate("K12_d4_b3_rooted_anchor", 2, seconds, workers),
    ]
    return {
        "model_version": MODEL_VERSION,
        "status": "PASS",
        "gates": gates,
    }


def solve_box(
    box: str,
    seconds: int,
    workers: int,
    seed: int,
) -> dict:
    spec = BOXES[box]
    tm = build_model(spec)
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
        "box": box,
        "status": logical_status,
        "solver_status": solver_status,
        "solver_level_exact": status == cp_model.INFEASIBLE,
        "seconds": round(elapsed, 3),
        "time_limit_seconds": seconds,
        "workers": workers,
        "seed": seed,
        "zero_type": [spec["degree"], spec["blockers"]],
        "total_blockers": spec["total_b"],
        "anchor_degree": spec["anchor_degree"],
        "anchor_pattern": list(spec["pattern"]),
        "parent_v5_box": spec["parent_v5_box"],
        "coverage": (
            "One disjoint orbit-refined subbox of the exact 43-box v5 "
            "remaining endpoint union"
        ),
        "dependencies": {
            "v5_closed_boxes": "68 of 111 endpoint boxes exactly UNSAT",
            "near_regular_theorem": "profile 7^8 8^8 excluded",
            "frontier_thin_a": "profile 6^1 7^6 8^9 excluded",
            "frontier_thin_b": "profile 7^9 8^6 9^1 excluded",
        },
    }
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        check = verify(extract_full(solver, tm))
        if not check["is_pisa"]:
            raise RuntimeError("solver candidate failed independent verifier")
        record["verified"] = True
        record["witness"] = check
    return record


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--box", choices=sorted(BOXES))
    parser.add_argument("--list-boxes", action="store_true")
    parser.add_argument("--matrix", action="store_true")
    parser.add_argument("--gates-only", action="store_true")
    parser.add_argument("--seconds", type=int, default=900)
    parser.add_argument("--gate-seconds", type=int, default=60)
    parser.add_argument(
        "--workers",
        type=int,
        default=max(1, min(4, os.cpu_count() or 4)),
    )
    parser.add_argument("--seed", type=int, default=20260726)
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
        record = solve_box(args.box, args.seconds, args.workers, args.seed)

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
