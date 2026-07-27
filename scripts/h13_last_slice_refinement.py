#!/usr/bin/env python3
"""Exact semantic refinement of the final open h13_p00 cube.

The completed quotient cube campaign left exactly one h13_p00 slice open:

    weights = (4, 1^12)
    vertex 0 is a zero weighted-margin class
    vertex 1 is nonzero
    vertex 2 is the least second zero class

For vertex 0 the zero-score identity is

    4 + 2*d_Q^+(0) + b_Q(0) = 16.

All other quotient weights are one, so d_Q^+(0) is an ordinary outdegree
and b_Q(0) is an ordinary blocker count.  Hence the open slice is the
disjoint union of the six semantic cubes

    d_Q^+(0) = d,  b_Q(0) = 12 - 2d,  d = 1, ..., 6.

Any degree cube that remains UNKNOWN is split once more by the free arc
0->2 and the weighted outdegree of the second zero class 2.  Its zero-score
identity is

    1 + 2*w(N1+(2)) + w(B(2)) = 16.

The fixed cycle contains 2->3.  Therefore the exact child list is

    0->2: w(N1+(2)) = 1, ..., 7
    2->0: w(N1+(2)) = 5, 6, 7.

These ten children are disjoint and complete.  Every UNSAT result therefore
permanently closes a named part of the last h13 slice.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

from ortools.sat.python import cp_model

REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = REPO_ROOT / "scripts"
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from weighted_quotient_cube_refinement import (
    add_fixed_cube_constraints,
    logical_status,
    write_json,
)
from weighted_quotient_ladder import (
    MODEL_VERSION as ROOT_MODEL_VERSION,
    build_model,
    configure_solver,
    extract_solution,
)


MODEL_VERSION = "k16-h13-last-slice-v1-degree-zero2-blockerout-20260728"
SCHEMA = "k16-h13-last-slice-result-v1"
BOX = "h13_p00"
ASSIGNMENT = (4,) + (1,) * 12
SECOND_ZERO = 2
DEGREES = tuple(range(1, 7))


def cube_id(
    d0: int,
    arc02: int | None,
    outweight2: int | None = None,
    blocker2_outweight: int | None = None,
) -> str:
    suffix = ""
    if arc02 is not None:
        suffix = f"_a02{arc02}_w2{outweight2}"
    if blocker2_outweight is not None:
        suffix += f"_bk{blocker2_outweight}"
    return f"h13_p00_a000_z02_d0{d0}{suffix}"


def stage1_rows() -> list[dict]:
    return [
        {
            "d0": d0,
            "b0": 12 - 2 * d0,
            "cube_id": cube_id(d0, None),
        }
        for d0 in DEGREES
    ]


def add_semantic_cube(
    built,
    d0: int,
    arc02: int | None,
    outweight2: int | None,
    blocker2_outweight: int | None,
) -> None:
    if d0 not in DEGREES:
        raise ValueError(f"d0 must be in {DEGREES}: {d0}")
    if arc02 not in (None, 0, 1):
        raise ValueError(f"arc02 must be 0, 1, or omitted: {arc02}")
    if (arc02 is None) != (outweight2 is None):
        raise ValueError("arc02 and outweight2 must be supplied together")
    if outweight2 is not None:
        allowed = range(1, 8) if arc02 == 1 else range(5, 8)
        if outweight2 not in allowed:
            raise ValueError(
                f"invalid arc02/outweight2 pair: {arc02}/{outweight2}"
            )
    if blocker2_outweight is not None:
        if outweight2 != 7:
            raise ValueError(
                "unique-blocker outweight split is only defined when "
                "outweight2=7 and blocker_weight2=1"
            )
        if blocker2_outweight not in range(8, 15):
            raise ValueError(blocker2_outweight)

    add_fixed_cube_constraints(built, ASSIGNMENT, SECOND_ZERO)
    model = built.model
    outdegree0 = sum(
        built.arc[(0, x)]
        for x in range(1, built.h)
    )
    blocker_count0 = sum(
        built.blocker[(0, x)]
        for x in range(1, built.h)
    )
    model.Add(outdegree0 == d0)
    model.Add(blocker_count0 == 12 - 2 * d0)
    if arc02 is not None:
        model.Add(built.arc[(0, 2)] == arc02)
        outgoing_weight2 = sum(
            ASSIGNMENT[x] * built.arc[(2, x)]
            for x in range(built.h)
            if x != 2
        )
        blocker_weight2 = sum(
            ASSIGNMENT[x] * built.blocker[(2, x)]
            for x in range(built.h)
            if x != 2
        )
        model.Add(outgoing_weight2 == outweight2)
        model.Add(blocker_weight2 == 15 - 2 * outweight2)
        if blocker2_outweight is not None:
            # blocker_weight(2)=1 means exactly one unit-weight vertex blocks
            # class 2, while the weight-four class 0 does not.  Partition by
            # the weighted outdegree of that unique blocker.
            for x in range(built.h):
                if x in (0, 2):
                    continue
                outgoing_weight_x = sum(
                    ASSIGNMENT[y] * built.arc[(x, y)]
                    for y in range(built.h)
                    if y != x
                )
                model.Add(
                    outgoing_weight_x == blocker2_outweight
                ).OnlyEnforceIf(built.blocker[(2, x)])


def solve(
    *,
    d0: int,
    arc02: int | None,
    outweight2: int | None,
    blocker2_outweight: int | None,
    seconds: int,
    workers: int,
    seed: int,
    log_progress: bool,
) -> dict:
    started = time.monotonic()
    built = build_model(ASSIGNMENT)
    add_semantic_cube(
        built,
        d0,
        arc02,
        outweight2,
        blocker2_outweight,
    )
    solver = configure_solver(seconds, workers, seed, log_progress)
    status = solver.Solve(built.model)
    elapsed = time.monotonic() - started
    result_status = logical_status(status)

    result = {
        "schema": SCHEMA,
        "model_version": MODEL_VERSION,
        "root_model_version": ROOT_MODEL_VERSION,
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "slice_id": cube_id(
            d0,
            arc02,
            outweight2,
            blocker2_outweight,
        ),
        "parent_slice": "h13_p00_a000_z02",
        "parent_box": BOX,
        "h": 13,
        "weights_by_vertex_fixed": list(ASSIGNMENT),
        "least_second_zero_index": SECOND_ZERO,
        "zero0_outdegree": d0,
        "zero0_blocker_count": 12 - 2 * d0,
        "arc_0_2": arc02,
        "zero2_outgoing_weight": outweight2,
        "zero2_blocker_weight": (
            None if outweight2 is None else 15 - 2 * outweight2
        ),
        "unique_blocker2_outgoing_weight": blocker2_outweight,
        "stage": (
            1
            if arc02 is None
            else (2 if blocker2_outweight is None else 3)
        ),
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
            "Exact h13_p00_a000_z02 semantic cube with fixed zero-0 "
            "quotient outdegree."
            if arc02 is None
            else (
                (
                    "Exact child of the second-zero semantic cube, "
                    "partitioned by the unique blocker-2 outgoing weight."
                )
                if blocker2_outweight is not None
                else (
                    "Exact child of the fixed zero-0 quotient-outdegree cube, "
                    "partitioned by arc {0,2} and zero-2 outgoing weight."
                )
            )
        ),
        "partition_invariants": {
            "degree_values_1_through_6_are_disjoint": True,
            "degree_values_1_through_6_cover_parent": True,
            "arc02_outweight2_children_are_disjoint": True,
            "arc02_outweight2_children_cover_degree_cube": True,
            "blocker2_outweight_8_through_14_are_disjoint": True,
            "blocker2_outweight_8_through_14_cover_w2_7_child": True,
            "zero_score_identity": "4 + 2*d0 + b0 = 16",
            "zero2_score_identity": "1 + 2*outweight2 + b2 = 16",
        },
        "theorem_dependencies": [
            "Camion: every strong tournament has a directed Hamilton cycle.",
            (
                "Havet--Thomasse Theorem 2: a tournament with no dominated "
                "vertex (defined there as outdegree zero) has two Seymour "
                "vertices; applied to the strong transitive-fibre expansion."
            ),
        ],
    }
    if result_status == "SAT":
        result["witness"] = extract_solution(solver, built)
    elif result_status == "ERROR":
        result["error"] = built.model.Validate()
    return result


def load_results(root: Path) -> list[dict]:
    records = []
    for path in sorted(root.rglob("result.json")):
        try:
            record = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        if record.get("schema") == SCHEMA:
            records.append(record)
    return records


def refinement_plan(root: Path) -> dict:
    records = {
        record["slice_id"]: record
        for record in load_results(root)
        if record.get("stage") == 1
    }
    rows = []
    missing = []
    errors = []
    sat = []
    for d0 in DEGREES:
        parent_id = cube_id(d0, None)
        record = records.get(parent_id)
        if record is None:
            missing.append(parent_id)
            continue
        status = record.get("status")
        if status == "SAT":
            sat.append(parent_id)
        elif status == "ERROR":
            errors.append(parent_id)
        elif status == "UNKNOWN":
            child_pairs = (
                [(1, outweight2) for outweight2 in range(1, 8)]
                + [(0, outweight2) for outweight2 in range(5, 8)]
            )
            for arc02, outweight2 in child_pairs:
                rows.append(
                    {
                        "d0": d0,
                        "b0": 12 - 2 * d0,
                        "arc02": arc02,
                        "outweight2": outweight2,
                        "blocker_weight2": 15 - 2 * outweight2,
                        "cube_id": cube_id(d0, arc02, outweight2),
                    }
                )

    return {
        "schema": "k16-h13-last-slice-refinement-plan-v1",
        "model_version": MODEL_VERSION,
        "stage1_results_found": len(records),
        "missing_stage1": missing,
        "error_stage1": errors,
        "sat_stage1": sat,
        "matrix": rows,
        "matrix_count": len(rows),
    }


def blocker_refinement_plan(root: Path) -> dict:
    records = {
        record["slice_id"]: record
        for record in load_results(root)
        if record.get("stage") == 2
    }
    rows = []
    missing = []
    errors = []
    sat = []
    for d0 in DEGREES:
        child_pairs = (
            [(1, outweight2) for outweight2 in range(1, 8)]
            + [(0, outweight2) for outweight2 in range(5, 8)]
        )
        for arc02, outweight2 in child_pairs:
            parent_id = cube_id(d0, arc02, outweight2)
            record = records.get(parent_id)
            if record is None:
                continue
            status = record.get("status")
            if status == "SAT":
                sat.append(parent_id)
            elif status == "ERROR":
                errors.append(parent_id)
            elif status == "UNKNOWN":
                if outweight2 != 7:
                    # The workflow may discover an unexpectedly hard lower
                    # outweight child.  Keep it visible instead of claiming a
                    # false complete partition with the w2=7-specific split.
                    errors.append(
                        parent_id + ": no safe blocker-outweight split configured"
                    )
                    continue
                for blocker_outweight in range(8, 15):
                    rows.append(
                        {
                            "d0": d0,
                            "b0": 12 - 2 * d0,
                            "arc02": arc02,
                            "outweight2": outweight2,
                            "blocker_outweight": blocker_outweight,
                            "cube_id": cube_id(
                                d0,
                                arc02,
                                outweight2,
                                blocker_outweight,
                            ),
                        }
                    )

    return {
        "schema": "k16-h13-last-slice-blocker-plan-v1",
        "model_version": MODEL_VERSION,
        "stage2_results_found": len(records),
        "missing_stage2": missing,
        "error_or_unsplit_stage2": errors,
        "sat_stage2": sat,
        "matrix": rows,
        "matrix_count": len(rows),
    }


def aggregate(root: Path) -> dict:
    records = {}
    duplicates = []
    for record in load_results(root):
        slice_id = record["slice_id"]
        if slice_id in records:
            duplicates.append(slice_id)
        records[slice_id] = record

    closed = []
    open_slices = []
    missing = []
    errors = []
    sat = []
    for d0 in DEGREES:
        parent_id = cube_id(d0, None)
        parent = records.get(parent_id)
        if parent is None:
            missing.append(parent_id)
            continue
        status = parent.get("status")
        if status == "SAT":
            sat.append(parent_id)
            continue
        if status == "UNSAT":
            closed.append(parent_id)
            continue
        if status == "ERROR":
            errors.append(parent_id)
            continue

        child_pairs = (
            [(1, outweight2) for outweight2 in range(1, 8)]
            + [(0, outweight2) for outweight2 in range(5, 8)]
        )
        children = [
            records.get(cube_id(d0, arc02, outweight2))
            for arc02, outweight2 in child_pairs
        ]
        if any(
            child is not None and child.get("status") == "SAT"
            for child in children
        ):
            sat.append(
                next(
                    child["slice_id"]
                    for child in children
                    if child is not None and child.get("status") == "SAT"
                )
            )
        child_closed = []
        for (arc02, outweight2), child in zip(child_pairs, children):
            if child is None:
                child_closed.append(False)
                continue
            if child.get("status") == "UNSAT":
                child_closed.append(True)
                continue
            if child.get("status") != "UNKNOWN" or outweight2 != 7:
                child_closed.append(False)
                continue
            grandchildren = [
                records.get(
                    cube_id(
                        d0,
                        arc02,
                        outweight2,
                        blocker_outweight,
                    )
                )
                for blocker_outweight in range(8, 15)
            ]
            child_closed.append(
                all(
                    grandchild is not None
                    and grandchild.get("status") == "UNSAT"
                    for grandchild in grandchildren
                )
            )

        if all(child_closed):
            closed.append(parent_id)
        else:
            for (
                (arc02, outweight2),
                child,
                is_closed,
            ) in zip(child_pairs, children, child_closed):
                if is_closed:
                    continue
                child_id = cube_id(d0, arc02, outweight2)
                if child is None:
                    missing.append(child_id)
                elif child.get("status") == "ERROR":
                    errors.append(child_id)
                elif child.get("status") == "UNKNOWN" and outweight2 == 7:
                    for blocker_outweight in range(8, 15):
                        grandchild_id = cube_id(
                            d0,
                            arc02,
                            outweight2,
                            blocker_outweight,
                        )
                        grandchild = records.get(grandchild_id)
                        if grandchild is None:
                            missing.append(grandchild_id)
                        elif grandchild.get("status") == "ERROR":
                            errors.append(grandchild_id)
                        elif grandchild.get("status") != "UNSAT":
                            open_slices.append(grandchild_id)
                elif child.get("status") != "UNSAT":
                    open_slices.append(child_id)

    if sat:
        status = "SAT"
    elif len(closed) == len(DEGREES):
        status = "UNSAT_H13_LAST_SLICE"
    else:
        status = "INCOMPLETE"

    return {
        "schema": "k16-h13-last-slice-summary-v1",
        "model_version": MODEL_VERSION,
        "status": status,
        "records_returned": len(records),
        "degree_cubes_total": len(DEGREES),
        "degree_cubes_closed": len(closed),
        "closed_degree_cubes": closed,
        "open_refined_slices": sorted(set(open_slices)),
        "missing_slices": sorted(set(missing)),
        "error_slices": sorted(set(errors)),
        "sat_slices": sorted(set(sat)),
        "duplicate_slices": sorted(set(duplicates)),
        "logical_scope": (
            "Exactly the final open h13_p00_a000_z02 slice left by "
            "run 30250854456."
        ),
    }


def gates(seconds: int, workers: int) -> dict:
    rows = stage1_rows()
    if [row["d0"] for row in rows] != list(DEGREES):
        raise RuntimeError("degree partition is incomplete")
    if [row["b0"] for row in rows] != [10, 8, 6, 4, 2, 0]:
        raise RuntimeError("zero-score identity generated wrong blocker counts")

    validations = []
    for d0 in DEGREES:
        built = build_model(ASSIGNMENT)
        add_semantic_cube(built, d0, None, None, None)
        validation = built.model.Validate()
        if validation:
            raise RuntimeError(f"d0={d0} model invalid: {validation}")
        validations.append({"d0": d0, "b0": 12 - 2 * d0})

    # The inherited fixed-cube encoder has independent positive/negative
    # gates in the parent campaign.  Here we additionally make sure all ten
    # second-zero semantic children are valid and executable.
    child_statuses = []
    child_pairs = (
        [(1, outweight2) for outweight2 in range(1, 8)]
        + [(0, outweight2) for outweight2 in range(5, 8)]
    )
    for arc02, outweight2 in child_pairs:
        built = build_model(ASSIGNMENT)
        add_semantic_cube(built, 6, arc02, outweight2, None)
        solver = configure_solver(seconds, workers, 20260728, False)
        status = solver.Solve(built.model)
        if status == cp_model.MODEL_INVALID:
            raise RuntimeError(
                "semantic child gate invalid: "
                f"arc02={arc02}, outweight2={outweight2}: "
                f"{built.model.Validate()}"
            )
        child_statuses.append(
            {
                "arc02": arc02,
                "outweight2": outweight2,
                "blocker_weight2": 15 - 2 * outweight2,
                "solver_status": solver.StatusName(status),
            }
        )

    return {
        "schema": "k16-h13-last-slice-gates-v1",
        "model_version": MODEL_VERSION,
        "status": "PASS",
        "degree_partition": validations,
        "arc02_child_smoke": child_statuses,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--stage1-matrix", action="store_true")
    modes.add_argument("--solve", action="store_true")
    modes.add_argument("--refine-plan", type=Path)
    modes.add_argument("--blocker-plan", type=Path)
    modes.add_argument("--aggregate", type=Path)
    modes.add_argument("--gates", action="store_true")
    parser.add_argument("--d0", type=int)
    parser.add_argument("--arc02", type=int, choices=(0, 1))
    parser.add_argument("--outweight2", type=int)
    parser.add_argument("--blocker2-outweight", type=int)
    parser.add_argument("--seconds", type=int, default=300)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--seed", type=int, default=20260728)
    parser.add_argument("--log-progress", action="store_true")
    parser.add_argument("--output", type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.stage1_matrix:
        print(json.dumps({"include": stage1_rows()}, separators=(",", ":")))
        return 0

    if args.gates:
        result = gates(args.seconds, args.workers)
    elif args.refine_plan:
        result = refinement_plan(args.refine_plan)
    elif args.blocker_plan:
        result = blocker_refinement_plan(args.blocker_plan)
    elif args.aggregate:
        result = aggregate(args.aggregate)
    else:
        if args.d0 is None:
            raise SystemExit("--solve requires --d0")
        result = solve(
            d0=args.d0,
            arc02=args.arc02,
            outweight2=args.outweight2,
            blocker2_outweight=args.blocker2_outweight,
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
