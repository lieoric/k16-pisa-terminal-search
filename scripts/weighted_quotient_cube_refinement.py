#!/usr/bin/env python3
"""Exact cube-and-conquer refinement for the remaining K16 module boxes.

The first weighted-quotient ladder closed all h <= 10 boxes and the
single-large-fibre boxes for h=11 and h=12.  Consequently a non-trivial
module in a K16 witness can only have size 2, 3, or 4.  Those three cases
are precisely:

    h15_p00 = (2, 1^14)
    h14_p00 = (3, 1^13)
    h13_p00 = (4, 1^12)

This program partitions each of those exact root models in two stages:

1. Fix the complete assignment of the weight multiset to the labelled
   Hamilton cycle.  Distinct multiset permutations are disjoint and their
   union is the original root model.
2. If a stage-one cube is still UNKNOWN, partition it by the least index
   k > 0 whose weighted margin is zero.  The safe two-zero-class theorem
   guarantees that exactly one such k exists for every feasible assignment.

Thus every UNSAT result permanently closes a named, disjoint region.  An
UNKNOWN result never masquerades as evidence of infeasibility.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path

from ortools.sat.python import cp_model

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from weighted_quotient_ladder import (
    MODEL_VERSION as ROOT_MODEL_VERSION,
    WeightedQuotientModel,
    build_model,
    configure_solver,
    extract_solution,
    find_pattern,
)


MODEL_VERSION = "k16-weighted-quotient-cubes-v2-fixed-weights-zero-prefix-20260727"
CRITICAL_BOXES = ("h13_p00", "h14_p00", "h15_p00")


def unique_multiset_permutations(values: list[int]):
    """Yield all distinct permutations without constructing a factorial set."""
    counts = Counter(values)
    keys = sorted(counts, reverse=True)
    result = [0] * len(values)

    def visit(index: int):
        if index == len(result):
            yield tuple(result)
            return
        for value in keys:
            if counts[value] == 0:
                continue
            counts[value] -= 1
            result[index] = value
            yield from visit(index + 1)
            counts[value] += 1

    yield from visit(0)


def assignment_code(assignment: tuple[int, ...]) -> str:
    return "-".join(str(value) for value in assignment)


def assignment_cubes(boxes: tuple[str, ...] = CRITICAL_BOXES) -> list[dict]:
    records = []
    for box in boxes:
        pattern = find_pattern(box)
        for index, assignment in enumerate(
            unique_multiset_permutations(pattern["weights"])
        ):
            records.append(
                {
                    "cube_id": f"{box}_a{index:03d}",
                    "box": box,
                    "h": pattern["h"],
                    "assignment_index": index,
                    "assignment": list(assignment),
                    "assignment_csv": ",".join(map(str, assignment)),
                    "assignment_code": assignment_code(assignment),
                }
            )
    return records


def expected_assignment_counts() -> dict[str, int]:
    return {
        "h13_p00": 13,
        "h14_p00": 14,
        "h15_p00": 15,
    }


def find_assignment_cube(box: str, assignment: tuple[int, ...]) -> dict:
    for record in assignment_cubes((box,)):
        if tuple(record["assignment"]) == assignment:
            return record
    raise ValueError(f"assignment is not a permutation of {box}: {assignment}")


def add_fixed_cube_constraints(
    built: WeightedQuotientModel,
    assignment: tuple[int, ...],
    second_zero: int | None,
) -> None:
    """Fix a disjoint cube and add sound dominance propagation cuts."""
    h = built.h
    if len(assignment) != h:
        raise ValueError((len(assignment), h))
    if sorted(assignment, reverse=True) != list(built.weight_pattern):
        raise ValueError((assignment, built.weight_pattern))
    if second_zero is not None and not 1 <= second_zero < h:
        raise ValueError(second_zero)

    model = built.model
    for vertex, value in enumerate(assignment):
        model.Add(built.weight[vertex] == value)

    if second_zero is not None:
        # Canonical, exact partition: k is the least zero class after vertex 0.
        model.Add(built.zero[second_zero] == 1)
        for vertex in range(1, second_zero):
            model.Add(built.zero[vertex] == 0)

    # With weights fixed, these linear expressions propagate much more
    # strongly than the generic multiplication encoding alone.
    outgoing = [
        sum(
            assignment[x] * built.arc[(v, x)]
            for x in range(h)
            if x != v
        )
        for v in range(h)
    ]
    blocked = [
        sum(
            assignment[x] * built.blocker[(v, x)]
            for x in range(h)
            if x != v
        )
        for v in range(h)
    ]

    for v in range(h):
        for x in range(h):
            if x == v:
                continue
            q_vx = built.blocker[(v, x)]

            # x blocks v => x beats v and every out-neighbour of v.
            model.Add(
                outgoing[x] >= outgoing[v] + assignment[v]
            ).OnlyEnforceIf(q_vx)

            # B(x) union {x} is contained in B(v).
            model.Add(
                blocked[v] >= blocked[x] + assignment[x]
            ).OnlyEnforceIf(q_vx)

    # The blocker/cover relation is transitive.  This is logically redundant
    # but gives CP-SAT the short clauses that the path encoding hides.
    for v in range(h):
        for x in range(h):
            if x == v:
                continue
            for y in range(h):
                if y == v or y == x:
                    continue
                model.Add(
                    built.blocker[(v, x)] + built.blocker[(x, y)]
                    <= 1 + built.blocker[(v, y)]
                )


def logical_status(status: cp_model.CpSolverStatus) -> str:
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        return "SAT"
    if status == cp_model.INFEASIBLE:
        return "UNSAT"
    if status == cp_model.MODEL_INVALID:
        return "ERROR"
    return "UNKNOWN"


def solve_cube(
    *,
    box: str,
    assignment: tuple[int, ...],
    second_zero: int | None,
    seconds: int,
    workers: int,
    seed: int,
    log_progress: bool,
) -> dict:
    pattern = find_pattern(box)
    cube = find_assignment_cube(box, assignment)
    started = time.monotonic()
    built = build_model(tuple(pattern["weights"]))
    add_fixed_cube_constraints(built, assignment, second_zero)
    solver = configure_solver(seconds, workers, seed, log_progress)
    status = solver.Solve(built.model)
    elapsed = time.monotonic() - started
    result_status = logical_status(status)

    slice_id = cube["cube_id"]
    stage = 1
    if second_zero is not None:
        slice_id += f"_z{second_zero:02d}"
        stage = 2

    result = {
        "schema": "k16-weighted-quotient-cube-result-v2",
        "model_version": MODEL_VERSION,
        "root_model_version": ROOT_MODEL_VERSION,
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "slice_id": slice_id,
        "stage": stage,
        "parent_box": box,
        "h": pattern["h"],
        "weight_multiset": pattern["weights"],
        "assignment_index": cube["assignment_index"],
        "weights_by_vertex_fixed": list(assignment),
        "second_zero_index": second_zero,
        "status": result_status,
        "solver_status": solver.StatusName(status),
        "solver_level_exact": result_status == "UNSAT",
        "seconds_budget": seconds,
        "wall_seconds": round(elapsed, 3),
        "workers": workers,
        "seed": seed,
        "branches": solver.NumBranches(),
        "conflicts": solver.NumConflicts(),
        "coverage": (
            "Exact fixed weight assignment on the lossless labelled "
            "Hamilton-cycle/zero-0 root model."
            if second_zero is None
            else (
                "Exact fixed weight assignment with this vertex as the "
                "least-index zero weighted-margin class after vertex 0."
            )
        ),
        "partition_invariants": {
            "stage1_assignments_are_disjoint": True,
            "stage1_assignments_cover_parent": True,
            "stage2_least_second_zero_slices_are_disjoint": True,
            "stage2_slices_cover_unknown_stage1_cube": True,
        },
        "theorem_dependencies": [
            "Camion: every strong tournament has a directed Hamilton cycle.",
            (
                "Havet--Thomasse applied to the transitive-fibre expansion: "
                "every feasible weighted quotient has at least two zero classes."
            ),
        ],
    }
    if result_status == "SAT":
        result["witness"] = extract_solution(solver, built)
    elif result_status == "ERROR":
        result["error"] = built.model.Validate()
    return result


def write_json(record: dict, output: Path) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_suffix(output.suffix + ".tmp")
    temporary.write_text(
        json.dumps(record, indent=2, sort_keys=True),
        encoding="utf-8",
    )
    temporary.replace(output)


def load_results(root: Path) -> list[dict]:
    records = []
    for path in sorted(root.rglob("result.json")):
        try:
            record = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        if record.get("schema") == "k16-weighted-quotient-cube-result-v2":
            records.append(record)
    return records


def make_refinement_plan(input_dir: Path) -> dict:
    records = load_results(input_dir)
    stage1 = {
        record["slice_id"]: record
        for record in records
        if record.get("stage") == 1
    }
    matrices: dict[str, list[dict]] = {
        "h13": [],
        "h14": [],
        "h15": [],
    }
    errors = []
    missing = []
    sat = []
    for cube in assignment_cubes():
        record = stage1.get(cube["cube_id"])
        if record is None:
            missing.append(cube["cube_id"])
            continue
        status = record.get("status")
        if status == "SAT":
            sat.append(cube["cube_id"])
            continue
        if status == "ERROR":
            errors.append(cube["cube_id"])
            continue
        if status != "UNKNOWN":
            continue
        key = f"h{cube['h']}"
        for second_zero in range(1, cube["h"]):
            matrices[key].append(
                {
                    "skip": False,
                    "cube_id": cube["cube_id"],
                    "box": cube["box"],
                    "assignment_csv": cube["assignment_csv"],
                    "second_zero": second_zero,
                }
            )

    return {
        "schema": "k16-weighted-quotient-refinement-plan-v2",
        "model_version": MODEL_VERSION,
        "stage1_results_found": len(stage1),
        "missing_stage1": missing,
        "error_stage1": errors,
        "sat_stage1": sat,
        "matrix_counts": {
            key: len(value)
            for key, value in matrices.items()
        },
        "matrices": matrices,
    }


def aggregate(input_dir: Path) -> dict:
    records = load_results(input_dir)
    by_slice: dict[str, dict] = {}
    duplicates = []
    for record in records:
        slice_id = record["slice_id"]
        if slice_id in by_slice:
            duplicates.append(slice_id)
        by_slice[slice_id] = record

    parent_summaries = {}
    all_sat = []
    all_errors = []
    for box in CRITICAL_BOXES:
        assignments = assignment_cubes((box,))
        closed = []
        open_slices = []
        missing = []
        errors = []
        for cube in assignments:
            root = by_slice.get(cube["cube_id"])
            if root is None:
                missing.append(cube["cube_id"])
                continue
            status = root.get("status")
            if status == "SAT":
                all_sat.append(cube["cube_id"])
                continue
            if status == "UNSAT":
                closed.append(cube["cube_id"])
                continue
            if status == "ERROR":
                errors.append(cube["cube_id"])
                all_errors.append(cube["cube_id"])
                continue

            child_ids = [
                f"{cube['cube_id']}_z{k:02d}"
                for k in range(1, cube["h"])
            ]
            children = [by_slice.get(child_id) for child_id in child_ids]
            if any(child and child.get("status") == "SAT" for child in children):
                hit = next(
                    child["slice_id"]
                    for child in children
                    if child and child.get("status") == "SAT"
                )
                all_sat.append(hit)
            elif all(
                child is not None and child.get("status") == "UNSAT"
                for child in children
            ):
                closed.append(cube["cube_id"])
            else:
                for child_id, child in zip(child_ids, children):
                    if child is None:
                        missing.append(child_id)
                    elif child.get("status") == "ERROR":
                        errors.append(child_id)
                        all_errors.append(child_id)
                    elif child.get("status") != "UNSAT":
                        open_slices.append(child_id)

        if all_sat:
            status = "SAT"
        elif len(closed) == len(assignments):
            status = "UNSAT"
        else:
            status = "INCOMPLETE"
        parent_summaries[box] = {
            "status": status,
            "assignments_total": len(assignments),
            "assignments_closed": len(closed),
            "closed_assignment_cubes": closed,
            "open_refined_slices": sorted(set(open_slices)),
            "missing_slices": sorted(set(missing)),
            "error_slices": sorted(set(errors)),
        }

    if all_sat:
        overall = "SAT"
    elif all(
        summary["status"] == "UNSAT"
        for summary in parent_summaries.values()
    ):
        overall = "UNSAT_MODULE_SIZES_2_TO_4"
    else:
        overall = "INCOMPLETE"

    return {
        "schema": "k16-weighted-quotient-cube-summary-v2",
        "model_version": MODEL_VERSION,
        "status": overall,
        "records_returned": len(records),
        "duplicate_slices": sorted(set(duplicates)),
        "sat_slices": sorted(set(all_sat)),
        "error_slices": sorted(set(all_errors)),
        "parents": parent_summaries,
        "logical_scope": (
            "The h13_p00, h14_p00, and h15_p00 weighted quotient boxes, "
            "equivalently possible module sizes 4, 3, and 2."
        ),
    }


def run_gates(seconds: int, workers: int) -> dict:
    counts = Counter(cube["box"] for cube in assignment_cubes())
    if dict(counts) != expected_assignment_counts():
        raise RuntimeError((dict(counts), expected_assignment_counts()))

    # Positive cube gate: C3 with equal weights.  Every class is zero, hence
    # the least second zero is vertex 1.
    positive_pattern = {
        "box": "gate_equal_c3",
        "h": 3,
        "pattern_index": 0,
        "weights": [2, 2, 2],
    }
    # Build this small gate directly because it is outside the h10..h15 table.
    built = build_model((2, 2, 2))
    add_fixed_cube_constraints(built, (2, 2, 2), 1)
    solver = configure_solver(seconds, workers, 20260727, False)
    positive_status = solver.Solve(built.model)
    if positive_status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        raise RuntimeError(
            f"positive fixed-cube gate failed: {solver.StatusName(positive_status)}"
        )
    extract_solution(solver, built)

    # Unequal C3 weights cannot satisfy all three cyclic inequalities.  Check
    # every weight assignment and both least-second-zero slices.
    negative_checked = 0
    for assignment in unique_multiset_permutations([4, 1, 1]):
        for second_zero in (1, 2):
            built = build_model((4, 1, 1))
            add_fixed_cube_constraints(built, assignment, second_zero)
            solver = configure_solver(seconds, workers, 20260727, False)
            status = solver.Solve(built.model)
            if status != cp_model.INFEASIBLE:
                raise RuntimeError(
                    "negative fixed-cube gate failed: "
                    f"{assignment}, z={second_zero}, {solver.StatusName(status)}"
                )
            negative_checked += 1

    return {
        "schema": "k16-weighted-quotient-cube-gates-v2",
        "model_version": MODEL_VERSION,
        "status": "PASS",
        "critical_assignment_counts": dict(counts),
        "critical_assignments_total": sum(counts.values()),
        "positive_gate": positive_pattern,
        "negative_cubes_checked": negative_checked,
    }


def parse_csv_assignment(value: str) -> tuple[int, ...]:
    try:
        return tuple(int(part) for part in value.split(","))
    except ValueError as exc:
        raise argparse.ArgumentTypeError(str(exc)) from exc


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--stage1-matrix", action="store_true")
    modes.add_argument("--solve-cube", action="store_true")
    modes.add_argument("--refine-plan", type=Path)
    modes.add_argument("--aggregate", type=Path)
    modes.add_argument("--gates", action="store_true")
    parser.add_argument("--box")
    parser.add_argument("--assignment", type=parse_csv_assignment)
    parser.add_argument("--second-zero", type=int)
    parser.add_argument("--seconds", type=int, default=300)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--seed", type=int, default=20260727)
    parser.add_argument("--log-progress", action="store_true")
    parser.add_argument("--output", type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.stage1_matrix:
        print(json.dumps({"include": assignment_cubes()}, separators=(",", ":")))
        return 0

    if args.gates:
        result = run_gates(args.seconds, args.workers)
    elif args.refine_plan:
        result = make_refinement_plan(args.refine_plan)
    elif args.aggregate:
        result = aggregate(args.aggregate)
    else:
        if not args.box or args.assignment is None:
            raise SystemExit("--solve-cube requires --box and --assignment")
        result = solve_cube(
            box=args.box,
            assignment=args.assignment,
            second_zero=args.second_zero,
            seconds=args.seconds,
            workers=args.workers,
            seed=args.seed,
            log_progress=args.log_progress,
        )

    print(json.dumps(result, indent=2, sort_keys=True))
    if args.output:
        write_json(result, args.output)
        print(f"SAVED {args.output}", flush=True)
    return 1 if result.get("status") == "ERROR" else 0


if __name__ == "__main__":
    raise SystemExit(main())
