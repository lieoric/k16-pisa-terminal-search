#!/usr/bin/env python3
"""Exact partition of the remaining global K16 Pisa endgame.

Earlier exact runs closed:

* every zero branch d=2,3,4,5;
* d=6 with total blocker count B <= 14;
* d=7 with total blocker count B <= 11.

Together with the near-regular theorem and the two Frontier profile closures,
only these two global regions remain:

    (d(0), b(0)) = (7,1), B >= 12
    (d(0), b(0)) = (6,3), B >= 15.

This script partitions them by exact B layers (plus a B>=20 tail) and by the
degree of the first blocker in the degree-sorted blocker role class.  The
boxes are disjoint and their union is exactly the remaining endgame.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import time
from pathlib import Path

N = 16
MODEL_VERSION = "k16-pisa-v5-endpoint-anchor-partition-20260726"


def box_specs() -> dict[str, dict]:
    specs: dict[str, dict] = {}
    branches = (
        {
            "branch": "d7_b1",
            "degree": 7,
            "blockers": 1,
            "exact_b": range(12, 20),
            "anchor_degrees": range(8, 15),
        },
        {
            "branch": "d6_b3",
            "degree": 6,
            "blockers": 3,
            "exact_b": range(15, 20),
            "anchor_degrees": range(7, 15),
        },
    )
    for branch in branches:
        for total_b in branch["exact_b"]:
            for anchor_degree in branch["anchor_degrees"]:
                key = (
                    f"{branch['branch']}_B{total_b}_"
                    f"minblockerD{anchor_degree}"
                )
                specs[key] = {
                    **branch,
                    "total_b_eq": total_b,
                    "total_b_min": None,
                    "total_b_label": str(total_b),
                    "anchor_degree": anchor_degree,
                }
        for anchor_degree in branch["anchor_degrees"]:
            key = (
                f"{branch['branch']}_B20plus_"
                f"minblockerD{anchor_degree}"
            )
            specs[key] = {
                **branch,
                "total_b_eq": None,
                "total_b_min": 20,
                "total_b_label": "20+",
                "anchor_degree": anchor_degree,
            }
    return specs


BOXES = box_specs()


def matrix_json() -> str:
    return json.dumps(
        {"include": [{"box": box} for box in sorted(BOXES)]},
        separators=(",", ":"),
    )


def solve_box(
    box: str,
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

    spec = BOXES[box]
    tm = TerminalTournamentModel(
        N,
        zero_partition=(spec["degree"], spec["blockers"]),
        min_degree=2,
        total_b_eq=spec["total_b_eq"],
        total_b_min=spec["total_b_min"],
        excluded_profiles=EXCLUDED_PROFILES,
    )

    # In the zero-role labelling, blockers occupy
    # d+1,...,d+b and are sorted by degree.  Therefore d+1 is the minimum
    # blocker and its degree gives a safe, exhaustive partition.
    anchor_vertex = spec["degree"] + 1
    tm.model.Add(tm.degree[anchor_vertex] == spec["anchor_degree"])

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
    record = {
        "model_version": MODEL_VERSION,
        "box": box,
        "status": logical_status,
        "solver_status": status_name,
        "solver_level_exact": status == cp_model.INFEASIBLE,
        "seconds": round(elapsed, 3),
        "time_limit_seconds": seconds,
        "workers": workers,
        "seed": seed,
        "zero_type": [spec["degree"], spec["blockers"]],
        "total_blockers": spec["total_b_label"],
        "anchor_vertex": anchor_vertex,
        "minimum_blocker_degree": spec["anchor_degree"],
        "coverage": (
            "One disjoint box in the complete remaining global K16 endgame"
        ),
        "dependencies": {
            "near_regular_theorem": "profile 7^8 8^8 excluded",
            "frontier_thin_a": "profile 6^1 7^6 8^9 excluded",
            "frontier_thin_b": "profile 7^9 8^6 9^1 excluded",
            "formal_terminal": (
                "d2-d5 closed; d6/B<=14 closed; d7/B<=11 closed"
            ),
        },
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
    parser.add_argument("--matrix", action="store_true")
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
    if args.matrix:
        print(matrix_json())
        return
    if not args.box:
        raise SystemExit("--box is required")

    record = solve_box(args.box, args.seconds, args.workers, args.seed)
    print(
        f"ENDPOINT_RESULT box={args.box} status={record['status']} "
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
        print("THIS_DISJOINT_ENDPOINT_BOX_IS_UNSAT", flush=True)
    else:
        print("NO_CONCLUSION_FOR_THIS_ENDPOINT_BOX", flush=True)

    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(record, indent=2), encoding="utf-8")


if __name__ == "__main__":
    main()
