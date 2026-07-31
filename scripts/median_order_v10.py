#!/usr/bin/env python3
"""K16 Pisa v10: invariant refinement of the 30 open v7.1 LMO cubes.

The completed v7.1 run 30208791250 closed 18 of 48 labelled local-median
order (LMO) cubes.  This campaign first compiles those exact closures into
compact cuts on the first three feed edges, then partitions the complete
residual by label-invariant blocker data:

* for a d=7, b=1 feed, the degree of its unique blocker;
* for a d=6, b=3 feed, the minimum degree among its three blockers.

The resulting 34 boxes are mutually exclusive and cover exactly the union of
the 30 v7.1 UNKNOWN cubes.  No completed v7.1 cube is searched again.
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
from k16_pisa_solver import exact_and, extract_full, verify  # noqa: E402

import median_order_v7 as v7  # noqa: E402


N = 16
MODEL_VERSION = "k16-pisa-v10-invariant-lmo-refinement-20260727"
SOURCE_RUN = 30208791250

# Exact v7.1 UNKNOWN cubes, expressed in the little-endian bit order
# [A(0,1), A(0,2), A(0,3)].
V7_OPEN_CUBES = {
    "lmo_d7_b1_B16": {1, 2, 3, 5, 6, 7},
    "lmo_d7_b1_B17": {1, 2, 3, 5, 6, 7},
    "lmo_d7_b1_B18": {1, 2, 3, 5, 6, 7},
    "lmo_d7_b1_B19": {1, 2, 3, 5, 6},
    "lmo_d7_b1_B20plus": {1, 2, 3, 5, 6},
    "lmo_d6_b3_B20plus": {0, 4},
}

# The unique blocker of a d=7 feed has degree 8..14.  Degrees already closed
# by v6 are removed here because v7.build_model also carries their exact
# label-invariant nogoods.
D7_ALLOWED_BLOCKER_DEGREES = {
    16: (8, 9, 10, 13, 14),
    17: (8, 9, 10, 14),
    18: (8, 9, 10, 11, 14),
    19: (8, 9, 10, 11, 12),
    "20+": (8, 9, 10, 11, 12, 13, 14),
}

# Every blocker of a d=6 feed beats the feed and all six of its out-neighbours.
# Strong connectivity excludes degree 15, so the minimum blocker degree is
# exactly one of 7..14.
D6_MIN_BLOCKER_DEGREES = tuple(range(7, 15))


def invariant_specs() -> dict[str, dict]:
    specs: dict[str, dict] = {}
    for total_b, degrees in D7_ALLOWED_BLOCKER_DEGREES.items():
        suffix = "20plus" if total_b == "20+" else str(total_b)
        parent = f"lmo_d7_b1_B{suffix}"
        for degree in degrees:
            name = f"inv_d7_b1_B{suffix}_blocker_d{degree}"
            specs[name] = {
                "parent": parent,
                "degree": 7,
                "blockers": 1,
                "total_b": total_b,
                "split_kind": "unique_blocker_degree",
                "split_value": degree,
            }

    parent = "lmo_d6_b3_B20plus"
    for degree in D6_MIN_BLOCKER_DEGREES:
        name = f"inv_d6_b3_B20plus_min_blocker_d{degree}"
        specs[name] = {
            "parent": parent,
            "degree": 6,
            "blockers": 3,
            "total_b": "20+",
            "split_kind": "minimum_blocker_degree",
            "split_value": degree,
        }
    return specs


BOXES = invariant_specs()


def matrix_json() -> str:
    return json.dumps(
        {
            "include": [
                {"box": box, "index": index}
                for index, box in enumerate(sorted(BOXES))
            ]
        },
        separators=(",", ":"),
    )


def _cube_bits(cube: int) -> tuple[int, int, int]:
    return tuple((cube >> bit) & 1 for bit in range(3))


def _survives_compact_cut(parent: str, cube: int) -> bool:
    a01, a02, a03 = _cube_bits(cube)
    if parent == "lmo_d6_b3_B20plus":
        return a01 == 0 and a02 == 0
    if a01 == 0 and a02 == 0:
        return False
    if parent in {"lmo_d7_b1_B19", "lmo_d7_b1_B20plus"}:
        return not (a01 == a02 == a03 == 1)
    return True


def coverage_gate() -> dict:
    if len(BOXES) != 34:
        raise RuntimeError(f"expected 34 invariant boxes, found {len(BOXES)}")

    checked = {}
    for parent, expected in V7_OPEN_CUBES.items():
        actual = {
            cube for cube in range(8)
            if _survives_compact_cut(parent, cube)
        }
        if actual != expected:
            raise RuntimeError(
                f"compact cut mismatch for {parent}: {actual} != {expected}"
            )
        checked[parent] = sorted(actual)

    for total_b, allowed in D7_ALLOWED_BLOCKER_DEGREES.items():
        closed = v7.D7_CLOSED_BLOCKER_DEGREES.get(total_b, set())
        expected = set(range(8, 15)) - set(closed)
        if set(allowed) != expected:
            raise RuntimeError(
                f"blocker-degree coverage mismatch for B={total_b}"
            )

    return {
        "gate": "v10_partition_coverage",
        "status": "PASS",
        "source_run": SOURCE_RUN,
        "boxes": len(BOXES),
        "v7_open_cubes": checked,
        "coverage": (
            "The 34 invariant boxes are disjoint and cover exactly the "
            "30 UNKNOWN cubes from v7.1 run 30208791250."
        ),
    }


def add_compact_v7_closure_cuts(tm, parent: str) -> None:
    m = tm.model
    a01, a02, a03 = tm.A(0, 1), tm.A(0, 2), tm.A(0, 3)
    if parent == "lmo_d6_b3_B20plus":
        m.Add(a01 == 0)
        m.Add(a02 == 0)
        return

    # Cubes 0 and 4 are closed: their common condition is A01=A02=0.
    m.Add(a01 + a02 >= 1)
    if parent in {"lmo_d7_b1_B19", "lmo_d7_b1_B20plus"}:
        # Cube 7 is also closed.
        m.Add(a01 + a02 + a03 <= 2)


def _reified_equal(model, variable, value: int, name: str):
    flag = model.NewBoolVar(name)
    model.Add(variable == value).OnlyEnforceIf(flag)
    model.Add(variable != value).OnlyEnforceIf(flag.Not())
    return flag


def add_invariant_split(tm, spec: dict) -> None:
    m = tm.model
    target = int(spec["split_value"])

    if spec["split_kind"] == "unique_blocker_degree":
        for x in range(1, N):
            m.Add(tm.degree[x] == target).OnlyEnforceIf(
                tm.blocker[(0, x)]
            )
        return

    if spec["split_kind"] != "minimum_blocker_degree":
        raise ValueError(f"unknown split kind {spec['split_kind']}")

    minimum_flags = []
    for x in range(1, N):
        q = tm.blocker[(0, x)]
        m.Add(tm.degree[x] >= target).OnlyEnforceIf(q)
        at_target = _reified_equal(
            m,
            tm.degree[x],
            target,
            f"v10_blocker_{x}_degree_{target}",
        )
        is_minimum = m.NewBoolVar(f"v10_minimum_blocker_{x}_d{target}")
        exact_and(m, is_minimum, [q, at_target])
        minimum_flags.append(is_minimum)
    m.Add(sum(minimum_flags) >= 1)


def build_box(box: str):
    spec = BOXES[box]
    parent_spec = {
        "degree": spec["degree"],
        "blockers": spec["blockers"],
        "total_b": spec["total_b"],
    }
    tm = v7.build_model(parent_spec)
    add_compact_v7_closure_cuts(tm, spec["parent"])
    add_invariant_split(tm, spec)
    return tm


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


def solve_box(
    box: str,
    seconds: int,
    workers: int,
    seed: int,
) -> dict:
    spec = BOXES[box]
    tm = build_box(box)
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
        "algorithm": (
            "local median order with invariant blocker-degree refinement"
        ),
        "box": box,
        "parent": spec["parent"],
        "status": logical_status,
        "solver_status": solver_status,
        "solver_level_exact": status == cp_model.INFEASIBLE,
        "seconds": round(elapsed, 3),
        "time_limit_seconds": seconds,
        "workers": workers,
        "seed": seed,
        "feed_zero_type": [spec["degree"], spec["blockers"]],
        "total_blockers": spec["total_b"],
        "split_kind": spec["split_kind"],
        "split_value": spec["split_value"],
        "source_run": SOURCE_RUN,
        "compiled_v7_open_cubes": sorted(V7_OPEN_CUBES[spec["parent"]]),
        "coverage": (
            "One mutually exclusive invariant subbox of the complete v7.1 "
            "UNKNOWN residual. All 34 v10 boxes exactly cover that residual."
        ),
        "dependencies": {
            "v7_1_exact_cubes": (
                "18 UNSAT cubes from run 30208791250 compiled as cuts"
            ),
            "v6_exact_subboxes": "label-invariant v6 closures retained",
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


def run_gates(seconds: int, workers: int) -> dict:
    old = v7.run_gates(seconds, workers)
    return {
        "model_version": MODEL_VERSION,
        "status": "PASS",
        "positive_gates": old["gates"],
        "coverage_gate": coverage_gate(),
    }


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--box", choices=sorted(BOXES))
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
        record = solve_box(
            args.box,
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
