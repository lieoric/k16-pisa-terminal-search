#!/usr/bin/env python3
"""Exact colour-symmetric search for h15_p00 = (2, 1^14).

The unique weight-two quotient class is labelled 0 without loss of
generality.  Vertices 1..14 remain interchangeable, giving the colour
symmetry S_1 x S_14 to SAT Modulo Symmetries:

    --vertices 15 --directed --initial-partition 1 14

Every feasible endpoint has heavy outdegree 1..13.  The heavy class can be a
zero weighted-margin class only at degrees 6 and 7, so those two degrees are
split once more by the exact zero flag.  The resulting fifteen slices are
pairwise disjoint and exhaustive.
"""

from __future__ import annotations

import argparse
import json
import random
import subprocess
import sys
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import CNF
from pysat.solvers import Solver

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from pisa_verify import verify
from h14_module3_sms import (
    SMS_COMMIT,
    NamedPool,
    add_cardinality,
    arcs_to_masks,
    classify,
    expand_transitive_fibres,
    iff_and,
    is_strong,
    parse_sms_arcs,
    random_tournament,
    strict_second_mask,
    weighted_copies,
    weighted_margins,
)

MODEL_VERSION = "k16-h15-module2-sms-v1-colour-s14-endpoint-20260728"
H = 15
WEIGHTS = (2,) + (1,) * 14
TOTAL_WEIGHT = 16
INTERNAL_BLOCKER_TOTAL = 1  # C(2, 2) in the transitive heavy fibre.


def formal_slices() -> list[dict[str, object]]:
    slices: list[dict[str, object]] = []
    for degree in range(1, 14):
        zero_modes = (False, True) if degree in (6, 7) else (False,)
        for heavy_zero in zero_modes:
            suffix = "z1" if heavy_zero else "z0"
            slices.append({
                "degree": degree,
                "heavy_zero": int(heavy_zero),
                "slice_id": (
                    f"h15-p00-heavy-degree-{degree:02d}-{suffix}"
                ),
            })
    if len(slices) != 15:
        raise AssertionError("the h15 partition must contain 15 slices")
    return slices


@dataclass
class Encoding:
    cnf: CNF
    pool: NamedPool
    blocker: dict[tuple[int, int], int]
    zero: list[int]
    heavy_outdegree: int | None
    heavy_zero: bool | None

    def metadata(self) -> dict:
        return {
            "model_version": MODEL_VERSION,
            "sms_commit": SMS_COMMIT,
            "h": H,
            "weights": list(WEIGHTS),
            "heavy_vertex": 0,
            "heavy_outdegree": self.heavy_outdegree,
            "heavy_zero": self.heavy_zero,
            "variables": max(self.cnf.nv, self.pool.top),
            "clauses": len(self.cnf.clauses),
            "arc_variables": H * (H - 1),
            "sms_initial_partition": [1, 14],
            "coverage": (
                "Heavy degrees 1..13 cover every strong h15 quotient. "
                "Endpoint zero-degree bounds force the heavy zero flag false "
                "outside degrees 6 and 7; those two degrees are split by its "
                "exact truth value. The resulting 15 slices are disjoint and "
                "exhaustive."
            ),
            "cuts": [
                "weighted margin <= 0 at every quotient class",
                "zero flags iff weighted margin = 0",
                "at least two zero classes (Havet--Thomasse)",
                "exact strong connectivity by directed cut clauses",
                "expanded minimum outdegree >= 2",
                "every remaining K16 zero degree is 6 or 7",
                "expanded total blocker count >= 16",
                "a degree-6 zero forces expanded total blockers >= 20",
            ],
        }


def build_cnf(
    *,
    weights: tuple[int, ...] = WEIGHTS,
    heavy_outdegree: int | None = None,
    heavy_zero: bool | None = None,
    endpoint_cuts: bool = True,
    minimum_zero_classes: int = 2,
) -> Encoding:
    h = len(weights)
    total = sum(weights)
    if h < 3 or min(weights) <= 0:
        raise ValueError(weights)
    if endpoint_cuts and (h != H or weights != WEIGHTS):
        raise ValueError("K16 endpoint cuts apply only to (2,1^14)")
    if heavy_outdegree is not None and not 0 <= heavy_outdegree < h:
        raise ValueError(heavy_outdegree)
    if heavy_zero is not None and heavy_outdegree is None:
        raise ValueError("heavy_zero requires a fixed heavy_outdegree")

    named = NamedPool(h)
    cnf = CNF()
    arc = named.arcs

    for u in range(h):
        for v in range(u + 1, h):
            cnf.append([arc[(u, v)], arc[(v, u)]])
            cnf.append([-arc[(u, v)], -arc[(v, u)]])

    path_cycles = {
        (v, x): []
        for v in range(h)
        for x in range(h)
        if v != x
    }
    for a in range(h):
        for b in range(a + 1, h):
            for c in range(b + 1, h):
                forward = named.new(f"cycle_{a}_{b}_{c}_forward")
                reverse = named.new(f"cycle_{a}_{b}_{c}_reverse")
                iff_and(
                    cnf,
                    forward,
                    [arc[(a, b)], arc[(b, c)], arc[(c, a)]],
                )
                iff_and(
                    cnf,
                    reverse,
                    [arc[(a, c)], arc[(c, b)], arc[(b, a)]],
                )
                for pair in ((a, c), (b, a), (c, b)):
                    path_cycles[pair].append(forward)
                for pair in ((a, b), (c, a), (b, c)):
                    path_cycles[pair].append(reverse)

    blocker: dict[tuple[int, int], int] = {}
    for v in range(h):
        for x in range(h):
            if v == x:
                continue
            q = named.new(f"blocker_{v}_{x}")
            blocker[(v, x)] = q
            cycles = path_cycles[(v, x)]
            cnf.append([-q, arc[(x, v)]])
            for cycle in cycles:
                cnf.append([-q, -cycle])
            cnf.append([q, -arc[(x, v)]] + cycles)

    zero: list[int] = []
    degree_six_zero: list[int] = []

    for v in range(h):
        outgoing_terms = [
            (arc[(v, x)], weights[x])
            for x in range(h)
            if x != v
        ]
        blocked_terms = [
            (blocker[(v, x)], weights[x])
            for x in range(h)
            if x != v
        ]
        outgoing = weighted_copies(
            cnf, named, outgoing_terms, f"outweight_{v}"
        )

        # The sink of a transitive fibre has exactly the external weighted
        # outdegree.  The proved K16 minimum-degree bound therefore applies.
        add_cardinality(
            cnf, named, outgoing, bound=2, kind="atleast"
        )

        score = weighted_copies(
            cnf,
            named,
            outgoing_terms + outgoing_terms + blocked_terms,
            f"score_{v}",
        )
        target = total - weights[v]
        add_cardinality(
            cnf, named, score, bound=target, kind="atleast"
        )

        z = named.new(f"zero_weighted_margin_{v}")
        zero.append(z)
        # score >= target unconditionally; hence z iff score == target.
        add_cardinality(
            cnf,
            named,
            score,
            bound=target,
            kind="atmost",
            guard_lit=z,
        )
        add_cardinality(
            cnf,
            named,
            score,
            bound=target + 1,
            kind="atleast",
            guard_lit=-z,
        )

        if endpoint_cuts:
            add_cardinality(
                cnf,
                named,
                outgoing,
                bound=6,
                kind="atleast",
                guard_lit=z,
            )
            add_cardinality(
                cnf,
                named,
                outgoing,
                bound=7,
                kind="atmost",
                guard_lit=z,
            )

            d6z = named.new(f"degree_six_zero_{v}")
            degree_six_zero.append(d6z)
            cnf.append([-d6z, z])
            add_cardinality(
                cnf,
                named,
                outgoing,
                bound=6,
                kind="atmost",
                guard_lit=d6z,
            )
            gt6 = CardEnc.atleast(
                lits=outgoing,
                bound=7,
                vpool=named.pool,
                encoding=EncType.seqcounter,
            )
            # z and not d6z imply outweight >= 7.
            cnf.extend([[d6z, -z] + clause for clause in gt6.clauses])

    add_cardinality(
        cnf,
        named,
        zero,
        bound=minimum_zero_classes,
        kind="atleast",
    )

    if heavy_outdegree is not None:
        heavy_outgoing = [arc[(0, x)] for x in range(1, h)]
        add_cardinality(
            cnf,
            named,
            heavy_outgoing,
            bound=heavy_outdegree,
            kind="atleast",
        )
        add_cardinality(
            cnf,
            named,
            heavy_outgoing,
            bound=heavy_outdegree,
            kind="atmost",
        )
    if heavy_zero is not None:
        cnf.append([zero[0] if heavy_zero else -zero[0]])

    if endpoint_cuts:
        external_blocker_terms = [
            (blocker[(v, x)], weights[v] * weights[x])
            for v in range(h)
            for x in range(h)
            if v != x
        ]
        external_blockers = weighted_copies(
            cnf,
            named,
            external_blocker_terms,
            "expanded_external_blockers",
        )
        add_cardinality(
            cnf,
            named,
            external_blockers,
            bound=16 - INTERNAL_BLOCKER_TOTAL,
            kind="atleast",
        )
        for d6z in degree_six_zero:
            add_cardinality(
                cnf,
                named,
                external_blockers,
                bound=20 - INTERNAL_BLOCKER_TOTAL,
                kind="atleast",
                guard_lit=d6z,
            )

    # Exact strong connectivity.  Each nonempty proper cut containing vertex
    # 0 on its complement is represented exactly once.
    others = list(range(1, h))
    for mask in range(1, 1 << (h - 1)):
        inside = {
            others[index]
            for index in range(h - 1)
            if (mask >> index) & 1
        }
        outside = [v for v in range(h) if v not in inside]
        cnf.append([
            arc[(u, v)]
            for u in outside
            for v in inside
        ])
        cnf.append([
            arc[(v, u)]
            for v in inside
            for u in outside
        ])

    cnf.nv = max(cnf.nv, named.top)
    return Encoding(
        cnf=cnf,
        pool=named,
        blocker=blocker,
        zero=zero,
        heavy_outdegree=heavy_outdegree,
        heavy_zero=heavy_zero,
    )


def verify_weighted_quotient(
    quotient: list[int],
    weights: tuple[int, ...],
) -> dict:
    margins = weighted_margins(quotient, list(weights))
    expanded = expand_transitive_fibres(quotient, list(weights))
    expanded_check = verify(expanded)
    return {
        "quotient_strong": is_strong(quotient),
        "weighted_margins": margins,
        "weighted_feasible": max(margins) == 0,
        "expanded_k16": expanded_check,
        "valid": (
            is_strong(quotient)
            and max(margins) == 0
            and bool(expanded_check["is_pisa"])
        ),
    }


def mathematical_acceptance(
    quotient: list[int],
    weights: tuple[int, ...],
    *,
    endpoint_cuts: bool,
) -> bool:
    margins = weighted_margins(quotient, list(weights))
    outweights = [
        sum(
            weights[x]
            for x in range(len(weights))
            if (quotient[v] >> x) & 1
        )
        for v in range(len(weights))
    ]
    zeros = [v for v, margin in enumerate(margins) if margin == 0]
    valid = (
        is_strong(quotient)
        and max(margins) <= 0
        and len(zeros) >= 2
        and min(outweights) >= 2
    )
    if not endpoint_cuts:
        return valid

    external_blockers = 0
    for v in range(len(weights)):
        second = strict_second_mask(quotient, v)
        for x in range(len(weights)):
            if x == v:
                continue
            if (quotient[v] >> x) & 1:
                continue
            if (second >> x) & 1:
                continue
            external_blockers += weights[v] * weights[x]
    total_blockers = external_blockers + INTERNAL_BLOCKER_TOTAL
    valid = (
        valid
        and all(6 <= outweights[v] <= 7 for v in zeros)
        and total_blockers >= 16
    )
    if any(outweights[v] == 6 for v in zeros):
        valid = valid and total_blockers >= 20
    return valid


def fixed_arc_equivalence_gate(
    weights: tuple[int, ...],
    *,
    endpoint_cuts: bool,
    samples: int,
    seed: int,
) -> dict:
    built = build_cnf(
        weights=weights,
        endpoint_cuts=endpoint_cuts,
        minimum_zero_classes=2,
    )
    rng = random.Random(seed)
    accepted = 0
    with Solver(
        name="cadical195",
        bootstrap_with=built.cnf.clauses,
    ) as solver:
        for index in range(samples):
            quotient = random_tournament(len(weights), rng)
            assumptions = [
                variable
                if (quotient[u] >> v) & 1
                else -variable
                for (u, v), variable in built.pool.arcs.items()
            ]
            encoded = solver.solve(assumptions=assumptions)
            expected = mathematical_acceptance(
                quotient,
                weights,
                endpoint_cuts=endpoint_cuts,
            )
            if encoded != expected:
                raise RuntimeError(
                    "fixed-arc equivalence mismatch: "
                    f"sample={index} encoded={encoded} expected={expected}"
                )
            accepted += int(encoded)
    return {
        "gate": "fixed_arc_equivalence",
        "weights": list(weights),
        "endpoint_cuts": endpoint_cuts,
        "samples": samples,
        "accepted": accepted,
        "status": "PASS",
    }


def run_gates() -> dict:
    records = []
    gates = (
        ("positive_c3_equal", (2, 2, 2), "SAT"),
        ("negative_c3_unequal", (3, 1, 1), "UNSAT"),
        ("positive_c7_equal", (2,) * 7, "SAT"),
    )
    for name, weights, expected in gates:
        built = build_cnf(
            weights=weights,
            endpoint_cuts=False,
            minimum_zero_classes=2,
        )
        with Solver(
            name="cadical195",
            bootstrap_with=built.cnf.clauses,
        ) as solver:
            sat = solver.solve()
            status = "SAT" if sat else "UNSAT"
            if status != expected:
                raise RuntimeError(
                    f"{name}: expected {expected}, got {status}"
                )
            record = {
                "gate": name,
                "weights": list(weights),
                "status": status,
                "expected": expected,
            }
            if sat:
                model = {lit for lit in solver.get_model() if lit > 0}
                arcs = [
                    [u, v]
                    for (u, v), var in built.pool.arcs.items()
                    if var in model
                ]
                check = verify_weighted_quotient(
                    arcs_to_masks(arcs, len(weights)),
                    weights,
                )
                if not check["valid"]:
                    raise RuntimeError(f"{name}: witness failed {check}")
                record["verified"] = True
            records.append(record)

    records.append(
        fixed_arc_equivalence_gate(
            (2, 2, 2, 2, 2),
            endpoint_cuts=False,
            samples=128,
            seed=20260728,
        )
    )
    records.append(
        fixed_arc_equivalence_gate(
            WEIGHTS,
            endpoint_cuts=True,
            samples=32,
            seed=271828,
        )
    )

    slice_meta = []
    for item in formal_slices():
        built = build_cnf(
            heavy_outdegree=int(item["degree"]),
            heavy_zero=bool(item["heavy_zero"]),
        )
        slice_meta.append(built.metadata())

    expected = {
        (degree, zero)
        for degree in range(1, 14)
        for zero in (
            (False, True) if degree in (6, 7) else (False,)
        )
    }
    observed = {
        (int(item["degree"]), bool(item["heavy_zero"]))
        for item in formal_slices()
    }
    if observed != expected:
        raise AssertionError("h15 partition is incomplete")

    return {
        "model_version": MODEL_VERSION,
        "status": "PASS",
        "gates": records,
        "formal_slices": slice_meta,
    }


def solve_sms(
    *,
    binary: Path,
    degree: int,
    heavy_zero: bool,
    seconds: int,
    cnf_path: Path,
    result_path: Path,
    log_path: Path,
) -> dict:
    built = build_cnf(
        heavy_outdegree=degree,
        heavy_zero=heavy_zero,
    )
    cnf_path.parent.mkdir(parents=True, exist_ok=True)
    result_path.parent.mkdir(parents=True, exist_ok=True)
    log_path.parent.mkdir(parents=True, exist_ok=True)
    built.cnf.to_file(cnf_path)
    cnf_path.with_suffix(".meta.json").write_text(
        json.dumps(built.metadata(), indent=2) + "\n",
        encoding="utf-8",
    )

    command = [
        str(binary),
        "--vertices",
        str(H),
        "--directed",
        "--dimacs",
        str(cnf_path),
        "--initial-partition",
        "1",
        "14",
        "--timeout",
        str(seconds),
    ]
    started = time.monotonic()
    timed_out = False
    try:
        completed = subprocess.run(
            command,
            capture_output=True,
            text=True,
            timeout=seconds + 30,
            check=False,
        )
        returncode = completed.returncode
        output = completed.stdout + completed.stderr
    except subprocess.TimeoutExpired as exc:
        timed_out = True
        returncode = 0
        stdout = (
            exc.stdout.decode()
            if isinstance(exc.stdout, bytes)
            else (exc.stdout or "")
        )
        stderr = (
            exc.stderr.decode()
            if isinstance(exc.stderr, bytes)
            else (exc.stderr or "")
        )
        output = stdout + stderr + "\nWRAPPER TIMEOUT\n"
    elapsed = time.monotonic() - started
    status = classify(returncode, output, timed_out)
    suffix = "z1" if heavy_zero else "z0"
    record: dict[str, object] = {
        "schema": "k16-h15-module2-sms-result-v1",
        "model_version": MODEL_VERSION,
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "slice_id": f"h15_p00_heavy_outdegree_{degree:02d}_{suffix}",
        "h": H,
        "weights": list(WEIGHTS),
        "heavy_outdegree": degree,
        "heavy_zero": heavy_zero,
        "status": status,
        "seconds": round(elapsed, 3),
        "solver_exit_code": returncode,
        "timed_out": timed_out,
        "command": command,
        "solver_level_exact": status == "UNSAT",
        "coverage": (
            "One of fifteen disjoint heavy-degree/zero-status slices. "
            "All fifteen UNSAT results close h15_p00 exactly."
        ),
    }
    if status == "SAT":
        arcs = parse_sms_arcs(output, H)
        if arcs is None:
            record["verified"] = False
            record["verification_error"] = "no parseable SMS tournament"
        else:
            quotient = arcs_to_masks(arcs, H)
            check = verify_weighted_quotient(quotient, WEIGHTS)
            record["verified"] = bool(check["valid"])
            record["quotient_arcs"] = arcs
            record["verification"] = check
            if not check["valid"]:
                record["verification_error"] = (
                    "SMS model failed independent weighted/K16 verification"
                )
    log_path.write_text(output, encoding="utf-8")
    result_path.write_text(
        json.dumps(record, indent=2) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(record, indent=2), flush=True)
    if status == "SAT" and not record.get("verified", False):
        raise RuntimeError(str(record["verification_error"]))
    return record


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--gates", action="store_true")
    parser.add_argument("--matrix-json", action="store_true")
    parser.add_argument("--build", action="store_true")
    parser.add_argument("--solve", action="store_true")
    parser.add_argument("--degree", type=int)
    parser.add_argument("--heavy-zero", choices=("0", "1"))
    parser.add_argument("--binary", type=Path)
    parser.add_argument("--seconds", type=int, default=19_200)
    parser.add_argument("--cnf", type=Path)
    parser.add_argument("--result", type=Path)
    parser.add_argument("--log", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    if args.matrix_json:
        print(json.dumps(
            {"include": formal_slices()},
            separators=(",", ":"),
        ))
        return
    if args.gates:
        record = run_gates()
        if args.output:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(
                json.dumps(record, indent=2) + "\n",
                encoding="utf-8",
            )
        print(json.dumps(record, indent=2))
        return
    if args.build:
        if (
            args.degree is None
            or args.heavy_zero is None
            or args.cnf is None
        ):
            parser.error(
                "--build requires --degree --heavy-zero and --cnf"
            )
        built = build_cnf(
            heavy_outdegree=args.degree,
            heavy_zero=args.heavy_zero == "1",
        )
        args.cnf.parent.mkdir(parents=True, exist_ok=True)
        built.cnf.to_file(args.cnf)
        metadata = built.metadata()
        if args.output:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(
                json.dumps(metadata, indent=2) + "\n",
                encoding="utf-8",
            )
        print(json.dumps(metadata, indent=2))
        return
    if args.solve:
        required = (
            args.degree,
            args.heavy_zero,
            args.binary,
            args.cnf,
            args.result,
            args.log,
        )
        if any(value is None for value in required):
            parser.error(
                "--solve requires --degree --heavy-zero --binary --cnf "
                "--result --log"
            )
        if not 1 <= args.degree <= 13:
            parser.error("--degree must be 1..13")
        if args.degree not in (6, 7) and args.heavy_zero != "0":
            parser.error("heavy zero is possible only at degrees 6 and 7")
        solve_sms(
            binary=args.binary,
            degree=args.degree,
            heavy_zero=args.heavy_zero == "1",
            seconds=args.seconds,
            cnf_path=args.cnf,
            result_path=args.result,
            log_path=args.log,
        )
        return
    parser.error("choose --gates, --matrix-json, --build, or --solve")


if __name__ == "__main__":
    main()
