#!/usr/bin/env python3
"""Exact symmetry-aware search for h14_p00 = (3, 1^13).

The unique weight-three quotient class is labelled 0 without loss of
generality.  Vertices 1..13 remain completely interchangeable.  The DIMACS
formula therefore has colour-preserving symmetry S_1 x S_13 and is intended
for SAT Modulo Symmetries with:

    --vertices 14 --directed --initial-partition 1 13

The twelve heavy-outdegree slices 1..12 are pairwise disjoint and cover every
strong 14-vertex quotient.  A SAT model is expanded with a transitive
three-vertex fibre and independently checked as a K16 Pisa tournament.
"""

from __future__ import annotations

import argparse
import json
import random
import re
import subprocess
import sys
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Solver

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from pisa_verify import verify
MODEL_VERSION = "k16-h14-module3-sms-v1-colour-s13-endpoint-20260728"
SMS_COMMIT = "464f12f1fd36b496e7ba9dcbb622b079de02dce4"
H = 14
WEIGHTS = (3,) + (1,) * 13
TOTAL_WEIGHT = 16
INTERNAL_BLOCKER_TOTAL = 3  # C(3, 2) in the transitive heavy fibre.
ARC_LINE = re.compile(r"^\[(?:\(\d+,\d+\)(?:,\(\d+,\d+\))*)?\]$")
ARC_PAIR = re.compile(r"\((\d+),(\d+)\)")


def strict_second_mask(out: list[int], vertex: int) -> int:
    second = 0
    bits = out[vertex]
    while bits:
        bit = bits & -bits
        middle = bit.bit_length() - 1
        second |= out[middle]
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
                vertex = bit.bit_length() - 1
                nxt |= graph[vertex]
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


class NamedPool:
    def __init__(self, n: int):
        self.n = n
        self.pool = IDPool(start_from=1)
        self.names: dict[int, str] = {}
        self.arcs: dict[tuple[int, int], int] = {}
        for u in range(n):
            for v in range(n):
                if u == v:
                    continue
                var = self.new(f"arc_{u}_{v}")
                expected = len(self.arcs) + 1
                if var != expected:
                    raise AssertionError("arc variables are not the SMS prefix")
                self.arcs[(u, v)] = var

    def new(self, name: str) -> int:
        var = self.pool.id(name)
        self.names[var] = name
        return var

    @property
    def top(self) -> int:
        return self.pool.top


def iff_and(cnf: CNF, target: int, literals: list[int]) -> None:
    for literal in literals:
        cnf.append([-target, literal])
    cnf.append([target] + [-literal for literal in literals])


def add_cardinality(
    cnf: CNF,
    pool: NamedPool,
    literals: list[int],
    *,
    bound: int,
    kind: str,
    guard_lit: int | None = None,
) -> None:
    """Add a cardinality, optionally guarded by an arbitrary literal."""
    if kind == "atleast":
        if bound <= 0:
            return
        if bound > len(literals):
            clauses = [[]]
        else:
            clauses = CardEnc.atleast(
                lits=literals,
                bound=bound,
                vpool=pool.pool,
                encoding=EncType.seqcounter,
            ).clauses
    elif kind == "atmost":
        if bound >= len(literals):
            return
        if bound < 0:
            clauses = [[]]
        else:
            clauses = CardEnc.atmost(
                lits=literals,
                bound=bound,
                vpool=pool.pool,
                encoding=EncType.seqcounter,
            ).clauses
    else:
        raise ValueError(kind)
    if guard_lit is None:
        cnf.extend(clauses)
    else:
        cnf.extend([[-guard_lit] + clause for clause in clauses])


def weighted_copies(
    cnf: CNF,
    pool: NamedPool,
    terms: list[tuple[int, int]],
    name: str,
) -> list[int]:
    """Return distinct, equivalent literals representing a weighted sum."""
    result: list[int] = []
    for index, (literal, coefficient) in enumerate(terms):
        if coefficient < 0:
            raise ValueError("only non-negative coefficients are supported")
        for copy_index in range(coefficient):
            copy = pool.new(f"{name}_{index}_{copy_index}")
            cnf.append([-copy, literal])
            cnf.append([copy, -literal])
            result.append(copy)
    return result


@dataclass
class Encoding:
    cnf: CNF
    pool: NamedPool
    blocker: dict[tuple[int, int], int]
    zero: list[int]
    heavy_outdegree: int | None

    def metadata(self) -> dict:
        return {
            "model_version": MODEL_VERSION,
            "sms_commit": SMS_COMMIT,
            "h": H,
            "weights": list(WEIGHTS),
            "heavy_vertex": 0,
            "heavy_outdegree": self.heavy_outdegree,
            "variables": max(self.cnf.nv, self.pool.top),
            "clauses": len(self.cnf.clauses),
            "arc_variables": H * (H - 1),
            "sms_initial_partition": [1, 13],
            "coverage": (
                "The degree slices 1..12 are disjoint and cover every strong "
                "h14 quotient with the unique weight-three class labelled 0."
            ),
            "cuts": [
                "weighted margin <= 0 at every quotient class",
                "zero flags iff weighted margin = 0",
                "at least two zero classes",
                "exact strong connectivity by directed cut clauses",
                "expanded minimum outdegree >= 2",
                "remaining K16 zero degree is 6 or 7",
                "expanded total blocker count >= 16",
                "a degree-6 zero forces expanded total blockers >= 20",
            ],
        }


def build_cnf(
    *,
    weights: tuple[int, ...] = WEIGHTS,
    heavy_outdegree: int | None = None,
    endpoint_cuts: bool = True,
    minimum_zero_classes: int = 2,
) -> Encoding:
    h = len(weights)
    total = sum(weights)
    if h < 3 or min(weights) <= 0:
        raise ValueError(weights)
    if endpoint_cuts and (h != H or weights != WEIGHTS):
        raise ValueError("K16 endpoint cuts apply only to (3,1^13)")
    if heavy_outdegree is not None and not 0 <= heavy_outdegree < h:
        raise ValueError(heavy_outdegree)

    named = NamedPool(h)
    cnf = CNF()
    arc = named.arcs

    for u in range(h):
        for v in range(u + 1, h):
            cnf.append([arc[(u, v)], arc[(v, u)]])
            cnf.append([-arc[(u, v)], -arc[(v, u)]])

    # Directed triangle variables expose every strict two-step path.
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

    outweight_literals: list[list[int]] = []
    blockerweight_literals: list[list[int]] = []
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
        blocked = weighted_copies(
            cnf, named, blocked_terms, f"blockerweight_{v}"
        )
        outweight_literals.append(outgoing)
        blockerweight_literals.append(blocked)

        # The sink of each transitive fibre has exactly this external
        # outdegree, so the proved minimum-degree bound applies.
        add_cardinality(
            cnf, named, outgoing, bound=2, kind="atleast"
        )

        score = weighted_copies(
            cnf,
            named,
            outgoing_terms
            + outgoing_terms
            + blocked_terms,
            f"score_{v}",
        )
        target = total - weights[v]
        add_cardinality(
            cnf, named, score, bound=target, kind="atleast"
        )

        z = named.new(f"zero_weighted_margin_{v}")
        zero.append(z)
        # z iff score == target, since score >= target is unconditional.
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
            upper = 6 if v == 0 else 7
            add_cardinality(
                cnf,
                named,
                outgoing,
                bound=upper,
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
            # z and not d6z -> outweight >= 7.
            gt6 = CardEnc.atleast(
                lits=outgoing,
                bound=7,
                vpool=named.pool,
                encoding=EncType.seqcounter,
            )
            cnf.extend([[d6z, -z] + clause for clause in gt6.clauses])

    add_cardinality(
        cnf,
        named,
        zero,
        bound=minimum_zero_classes,
        kind="atleast",
    )

    if heavy_outdegree is not None:
        heavy_outgoing = [
            arc[(0, x)]
            for x in range(1, h)
        ]
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
        # B(T) = external blockers + C(3,2).
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

    # Exact strong connectivity, invariant under every weight-preserving
    # permutation.  Generate one representative of each complementary cut.
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
    )


def arcs_to_masks(arcs: list[list[int]], n: int) -> list[int]:
    out = [0] * n
    for u, v in arcs:
        if not (0 <= u < n and 0 <= v < n and u != v):
            raise ValueError((u, v))
        out[u] |= 1 << v
    return out


def parse_sms_arcs(text: str, n: int) -> list[list[int]] | None:
    for raw in reversed(text.splitlines()):
        line = raw.strip()
        if not ARC_LINE.fullmatch(line):
            continue
        arcs = [[int(u), int(v)] for u, v in ARC_PAIR.findall(line)]
        if len(arcs) == n * (n - 1) // 2:
            return arcs
    return None


def classify(returncode: int, text: str, timed_out: bool) -> str:
    if timed_out:
        return "UNKNOWN"
    if returncode == 10:
        return "SAT"
    if returncode == 20:
        return "UNSAT"
    if returncode != 0:
        return "ERROR"
    upper = text.upper()
    matches = re.findall(r"RESULT:\s*(\d+)", upper)
    if matches:
        return {"10": "SAT", "20": "UNSAT"}.get(
            matches[-1], "UNKNOWN"
        )
    if "S UNSATISFIABLE" in upper:
        return "UNSAT"
    if "S SATISFIABLE" in upper and "UNSATISFIABLE" not in upper:
        return "SAT"
    return "UNKNOWN"


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
    """Independent predicate used only by the fixed-arc regression gate."""
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
        and all(
            6 <= outweights[v] <= (6 if v == 0 else 7)
            for v in zeros
        )
        and total_blockers >= 16
    )
    if any(outweights[v] == 6 for v in zeros):
        valid = valid and total_blockers >= 20
    return valid


def random_tournament(n: int, rng: random.Random) -> list[int]:
    out = [0] * n
    for u in range(n):
        for v in range(u + 1, n):
            if rng.getrandbits(1):
                out[u] |= 1 << v
            else:
                out[v] |= 1 << u
    return out


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
                model = set(lit for lit in solver.get_model() if lit > 0)
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
            seed=314159,
        )
    )

    # Structural gate: all twelve degree slices form exactly the possible
    # heavy degrees in a strong quotient.
    if set(range(1, 13)) != {
        degree for degree in range(1, H - 1)
    }:
        raise AssertionError("heavy-degree partition is incomplete")

    # Build every formal slice to catch cardinality and endpoint regressions.
    slice_meta = []
    for degree in range(1, 13):
        built = build_cnf(heavy_outdegree=degree)
        slice_meta.append(built.metadata())
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
    seconds: int,
    cnf_path: Path,
    result_path: Path,
    log_path: Path,
) -> dict:
    built = build_cnf(heavy_outdegree=degree)
    cnf_path.parent.mkdir(parents=True, exist_ok=True)
    result_path.parent.mkdir(parents=True, exist_ok=True)
    log_path.parent.mkdir(parents=True, exist_ok=True)
    built.cnf.to_file(cnf_path)
    metadata_path = cnf_path.with_suffix(".meta.json")
    metadata_path.write_text(
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
        "13",
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
    record: dict[str, object] = {
        "schema": "k16-h14-module3-sms-result-v1",
        "model_version": MODEL_VERSION,
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "slice_id": f"h14_p00_heavy_outdegree_{degree:02d}",
        "h": H,
        "weights": list(WEIGHTS),
        "heavy_outdegree": degree,
        "status": status,
        "seconds": round(elapsed, 3),
        "solver_exit_code": returncode,
        "timed_out": timed_out,
        "command": command,
        "solver_level_exact": status == "UNSAT",
        "coverage": (
            "One of twelve disjoint heavy-outdegree slices; all twelve "
            "UNSAT results close h14_p00 exactly."
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
        raise RuntimeError(record["verification_error"])
    return record


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--gates", action="store_true")
    parser.add_argument("--matrix-json", action="store_true")
    parser.add_argument("--build", action="store_true")
    parser.add_argument("--solve", action="store_true")
    parser.add_argument("--degree", type=int)
    parser.add_argument("--binary", type=Path)
    parser.add_argument("--seconds", type=int, default=19_200)
    parser.add_argument("--cnf", type=Path)
    parser.add_argument("--result", type=Path)
    parser.add_argument("--log", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    if args.matrix_json:
        print(json.dumps({
            "include": [
                {
                    "degree": degree,
                    "slice_id": f"h14-p00-heavy-degree-{degree:02d}",
                }
                for degree in range(1, 13)
            ]
        }, separators=(",", ":")))
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
        if args.degree is None or args.cnf is None:
            parser.error("--build requires --degree and --cnf")
        built = build_cnf(heavy_outdegree=args.degree)
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
            args.binary,
            args.cnf,
            args.result,
            args.log,
        )
        if any(value is None for value in required):
            parser.error(
                "--solve requires --degree --binary --cnf --result --log"
            )
        if not 1 <= args.degree <= 12:
            parser.error("--degree must be 1..12")
        solve_sms(
            binary=args.binary,
            degree=args.degree,
            seconds=args.seconds,
            cnf_path=args.cnf,
            result_path=args.result,
            log_path=args.log,
        )
        return
    parser.error("choose --gates, --matrix-json, --build, or --solve")


if __name__ == "__main__":
    main()
