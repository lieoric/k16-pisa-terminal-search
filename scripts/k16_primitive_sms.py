#!/usr/bin/env python3
"""Exact symmetry-aware search for the primitive K16 Pisa endgame.

All decomposable K16 candidates are handled by the completed h<16 weighted
quotient ledger.  This model searches the remaining primitive case and keeps
all graph constraints invariant under a declared vertex-colour partition.

Three lossless labelling lanes are benchmarked:

* full_s16: require the full T16 to be primitive, with one colour class;
* core15: additionally require T[0..14] primitive (Schmerl--Trotter);
* even_chain: additionally require the nested primitive chain
  T6 < T8 < T10 < T12 < T14 < T16 (repeated n+2 -> n theorem).

Every lane still encodes full T16 primitivity.  The extra cores are redundant
theorem cuts that trade some symmetry for substantially stronger propagation.
"""

from __future__ import annotations

import argparse
import itertools
import json
import subprocess
import sys
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path

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
    parse_sms_arcs,
    weighted_copies,
)


N = 16
MODEL_VERSION = "k16-pisa-v16-primitive-sms-st-chain-20260728"
INDEPENDENT_VERIFIER = REPO_ROOT / "scripts" / "verify_primitive_witness.py"


@dataclass(frozen=True)
class Lane:
    lane_id: str
    partition: tuple[int, ...]
    proper_cores: tuple[tuple[int, ...], ...]
    description: str

    @property
    def all_cores(self) -> tuple[tuple[int, ...], ...]:
        return (tuple(range(N)),) + self.proper_cores


LANES: dict[str, Lane] = {
    "full_s16": Lane(
        lane_id="full_s16",
        partition=(16,),
        proper_cores=(),
        description=(
            "Full S16 symmetry; only the complete T16 is constrained "
            "primitive."
        ),
    ),
    "core15": Lane(
        lane_id="core15",
        partition=(15, 1),
        proper_cores=(tuple(range(15)),),
        description=(
            "A distinguished extension vertex; T[0..14] and T16 are "
            "primitive. This is lossless because no even-order critically "
            "indecomposable tournament exists."
        ),
    ),
    "even_chain": Lane(
        lane_id="even_chain",
        partition=(6, 2, 2, 2, 2, 2),
        proper_cores=tuple(
            tuple(range(size))
            for size in (6, 8, 10, 12, 14)
        ),
        description=(
            "Nested primitive T6,T8,T10,T12,T14,T16 chain from repeated "
            "Schmerl--Trotter n+2 -> n."
        ),
    ),
}


BOXES = (
    "a0_z2", "a0_z3", "a0_z4p",
    "a1_z2", "a1_z3", "a1_z4p",
    "a2p_z2", "a2p_z3", "a2p_z4p",
)

BENCHMARK_BOXES = ("a0_z2", "a1_z2", "a2p_z4p")


@dataclass
class Encoding:
    n: int
    lane: Lane
    box: str | None
    cnf: CNF
    pool: NamedPool
    blocker: dict[tuple[int, int], int]
    zero: list[int]
    degree_six_zero: list[int]
    primitive_cores: tuple[tuple[int, ...], ...]
    module_clause_count: int
    module_literal_count: int
    separator_count: int

    def metadata(self) -> dict:
        return {
            "model_version": MODEL_VERSION,
            "sms_commit": SMS_COMMIT,
            "n": self.n,
            "lane": self.lane.lane_id,
            "lane_description": self.lane.description,
            "sms_initial_partition": list(self.lane.partition),
            "box": self.box,
            "variables": max(self.cnf.nv, self.pool.top),
            "clauses": len(self.cnf.clauses),
            "arc_variables": self.n * (self.n - 1),
            "separator_variables": self.separator_count,
            "module_clauses": self.module_clause_count,
            "module_literal_occurrences": self.module_literal_count,
            "primitive_cores": [
                list(core) for core in self.primitive_cores
            ],
            "cuts": [
                "exact tournament orientation",
                "margin <= 0 at every vertex",
                "zero flags iff margin = 0",
                "at least two zero-margin vertices",
                "minimum outdegree >= 2",
                "zero-margin vertex outdegree <= 7",
                "at least one vertex has outdegree >= 8",
                "exact strong connectivity by directed cut clauses",
                "full T16 primitivity",
                "lane-specific Schmerl--Trotter primitive cores",
            ],
            "coverage": (
                "The nine a/z boxes are disjoint and exhaustive: "
                "a counts degree-six zero vertices in {0,1,>=2}; "
                "z counts all zero vertices in {2,3,>=4}. No total-blocker "
                "lower-bound closure is assumed."
            ),
        }


def parse_box(box: str) -> tuple[str, str]:
    if box not in BOXES:
        raise ValueError(box)
    return tuple(box.split("_", maxsplit=1))  # type: ignore[return-value]


def add_exact_count(
    cnf: CNF,
    pool: NamedPool,
    literals: list[int],
    value: int,
) -> None:
    add_cardinality(
        cnf, pool, literals, bound=value, kind="atleast"
    )
    add_cardinality(
        cnf, pool, literals, bound=value, kind="atmost"
    )


def reify_atleast(
    cnf: CNF,
    pool: NamedPool,
    literals: list[int],
    bound: int,
    name: str,
) -> int:
    flag = pool.new(name)
    add_cardinality(
        cnf,
        pool,
        literals,
        bound=bound,
        kind="atleast",
        guard_lit=flag,
    )
    add_cardinality(
        cnf,
        pool,
        literals,
        bound=bound - 1,
        kind="atmost",
        guard_lit=-flag,
    )
    return flag


def add_xor(
    cnf: CNF,
    target: int,
    left: int,
    right: int,
) -> None:
    """target iff left XOR right."""
    cnf.append([-target, left, right])
    cnf.append([-target, -left, -right])
    cnf.append([target, -left, right])
    cnf.append([target, left, -right])


def add_primitive_core(
    cnf: CNF,
    pool: NamedPool,
    vertices: tuple[int, ...],
    separators: dict[tuple[int, int, int], int],
) -> tuple[int, int]:
    """Forbid every non-trivial module of the induced tournament."""
    clause_count = 0
    literal_count = 0
    for size in range(2, len(vertices)):
        for module_tuple in itertools.combinations(vertices, size):
            module = set(module_tuple)
            clause: list[int] = []
            for x in vertices:
                if x in module:
                    continue
                for u, v in itertools.combinations(module_tuple, 2):
                    key = (x, min(u, v), max(u, v))
                    sep = separators.get(key)
                    if sep is None:
                        sep = pool.new(
                            f"separates_{x}_{key[1]}_{key[2]}"
                        )
                        separators[key] = sep
                        add_xor(
                            cnf,
                            sep,
                            pool.arcs[(x, key[1])],
                            pool.arcs[(x, key[2])],
                        )
                    clause.append(sep)
            if not clause:
                raise AssertionError(
                    f"empty primitive clause for {module_tuple}"
                )
            cnf.append(clause)
            clause_count += 1
            literal_count += len(clause)
    return clause_count, literal_count


def build_cnf(
    *,
    n: int = N,
    lane: Lane | None = None,
    box: str | None = None,
    primitive_cores: tuple[tuple[int, ...], ...] | None = None,
) -> Encoding:
    if n < 3:
        raise ValueError(n)
    if lane is None:
        lane = Lane(
            lane_id=f"gate_n{n}",
            partition=(n,),
            proper_cores=(),
            description="small correctness gate",
        )
    if sum(lane.partition) != n:
        raise ValueError((lane.partition, n))
    if box is not None and n != N:
        raise ValueError("a/z boxes are defined only for K16")

    cores = (
        primitive_cores
        if primitive_cores is not None
        else lane.all_cores
    )
    for core in cores:
        if len(core) < 3 or len(set(core)) != len(core):
            raise ValueError(f"bad primitive core {core}")
        if any(not 0 <= v < n for v in core):
            raise ValueError(f"core outside tournament {core}")

    named = NamedPool(n)
    cnf = CNF()
    arc = named.arcs

    for u in range(n):
        for v in range(u + 1, n):
            cnf.append([arc[(u, v)], arc[(v, u)]])
            cnf.append([-arc[(u, v)], -arc[(v, u)]])

    path_cycles = {
        (v, x): []
        for v in range(n)
        for x in range(n)
        if v != x
    }
    for a in range(n):
        for b in range(a + 1, n):
            for c in range(b + 1, n):
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
    for v in range(n):
        for x in range(n):
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
    high_degree_flags: list[int] = []
    zero_degree_ceiling = (n - 1) // 2
    guaranteed_high_degree = n // 2

    for v in range(n):
        outgoing = [arc[(v, u)] for u in range(n) if u != v]
        blocked = [blocker[(v, x)] for x in range(n) if x != v]

        add_cardinality(
            cnf, named, outgoing, bound=2, kind="atleast"
        )

        score = weighted_copies(
            cnf,
            named,
            [(literal, 2) for literal in outgoing]
            + [(literal, 1) for literal in blocked],
            f"margin_score_{v}",
        )
        add_cardinality(
            cnf,
            named,
            score,
            bound=n - 1,
            kind="atleast",
        )

        z = named.new(f"zero_margin_{v}")
        zero.append(z)
        add_cardinality(
            cnf,
            named,
            score,
            bound=n - 1,
            kind="atmost",
            guard_lit=z,
        )
        add_cardinality(
            cnf,
            named,
            score,
            bound=n,
            kind="atleast",
            guard_lit=-z,
        )
        add_cardinality(
            cnf,
            named,
            outgoing,
            bound=zero_degree_ceiling,
            kind="atmost",
            guard_lit=z,
        )

        ge6 = reify_atleast(
            cnf, named, outgoing, 6, f"degree_ge_6_{v}"
        )
        ge7 = reify_atleast(
            cnf, named, outgoing, 7, f"degree_ge_7_{v}"
        )
        eq6 = named.new(f"degree_eq_6_{v}")
        iff_and(cnf, eq6, [ge6, -ge7])
        d6z = named.new(f"degree_six_zero_{v}")
        iff_and(cnf, d6z, [z, eq6])
        degree_six_zero.append(d6z)

        high_degree_flags.append(
            reify_atleast(
                cnf,
                named,
                outgoing,
                guaranteed_high_degree,
                f"degree_ge_{guaranteed_high_degree}_{v}",
            )
        )

    add_cardinality(
        cnf, named, zero, bound=2, kind="atleast"
    )
    cnf.append(high_degree_flags)

    if box is not None:
        a_label, z_label = parse_box(box)
        if a_label == "a0":
            add_exact_count(cnf, named, degree_six_zero, 0)
        elif a_label == "a1":
            add_exact_count(cnf, named, degree_six_zero, 1)
        elif a_label == "a2p":
            add_cardinality(
                cnf,
                named,
                degree_six_zero,
                bound=2,
                kind="atleast",
            )
        else:
            raise AssertionError(a_label)

        if z_label == "z2":
            add_exact_count(cnf, named, zero, 2)
        elif z_label == "z3":
            add_exact_count(cnf, named, zero, 3)
        elif z_label == "z4p":
            add_cardinality(
                cnf, named, zero, bound=4, kind="atleast"
            )
        else:
            raise AssertionError(z_label)

    # Exact strong connectivity without choosing a root in the property.
    # Complementary cuts are represented once by placing vertex 0 outside.
    others = list(range(1, n))
    for mask in range(1, 1 << (n - 1)):
        inside = {
            others[index]
            for index in range(n - 1)
            if (mask >> index) & 1
        }
        outside = [v for v in range(n) if v not in inside]
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

    separators: dict[tuple[int, int, int], int] = {}
    module_clause_count = 0
    module_literal_count = 0
    seen_cores: set[tuple[int, ...]] = set()
    encoded_cores: list[tuple[int, ...]] = []
    for core in cores:
        if core in seen_cores:
            continue
        seen_cores.add(core)
        encoded_cores.append(core)
        clauses, literals = add_primitive_core(
            cnf, named, core, separators
        )
        module_clause_count += clauses
        module_literal_count += literals

    cnf.nv = max(cnf.nv, named.top)
    return Encoding(
        n=n,
        lane=lane,
        box=box,
        cnf=cnf,
        pool=named,
        blocker=blocker,
        zero=zero,
        degree_six_zero=degree_six_zero,
        primitive_cores=tuple(encoded_cores),
        module_clause_count=module_clause_count,
        module_literal_count=module_literal_count,
        separator_count=len(separators),
    )


def fixed_arcs(out: list[int], encoding: Encoding) -> list[int]:
    return [
        variable
        if (out[u] >> v) & 1
        else -variable
        for (u, v), variable in encoding.pool.arcs.items()
    ]


def independent_module(
    out: list[int],
    vertices: tuple[int, ...],
) -> tuple[int, ...] | None:
    for size in range(2, len(vertices)):
        for candidate in itertools.combinations(vertices, size):
            candidate_set = set(candidate)
            first = candidate[0]
            module = True
            for x in vertices:
                if x in candidate_set:
                    continue
                direction = (out[x] >> first) & 1
                if any(
                    ((out[x] >> u) & 1) != direction
                    for u in candidate[1:]
                ):
                    module = False
                    break
            if module:
                return candidate
    return None


def mathematical_acceptance(
    out: list[int],
    cores: tuple[tuple[int, ...], ...],
) -> bool:
    check = verify(out)
    if not check.get("valid") or not check.get("is_pisa"):
        return False
    zeros = [
        v for v, margin in enumerate(check["margins"])
        if margin == 0
    ]
    if len(zeros) < 2 or min(check["outdegrees"]) < 2:
        return False
    if any(
        check["outdegrees"][v] > (len(out) - 1) // 2
        for v in zeros
    ):
        return False
    if max(check["outdegrees"]) < len(out) // 2:
        return False
    return all(
        independent_module(out, core) is None
        for core in cores
    )


def cyclic_tournament(n: int) -> list[int]:
    if n % 2 == 0:
        raise ValueError("cyclic regular tournament needs odd order")
    out = [0] * n
    for u in range(n):
        for distance in range(1, (n + 1) // 2):
            out[u] |= 1 << ((u + distance) % n)
    return out


def exhaustive_fixed_arc_equivalence_gate(n: int) -> dict:
    core = tuple(range(n))
    built = build_cnf(
        n=n,
        primitive_cores=(core,),
    )
    pairs = list(itertools.combinations(range(n), 2))
    accepted = 0
    with Solver(
        name="cadical195",
        bootstrap_with=built.cnf.clauses,
    ) as solver:
        for mask in range(1 << len(pairs)):
            out = [0] * n
            for index, (u, v) in enumerate(pairs):
                if (mask >> index) & 1:
                    out[u] |= 1 << v
                else:
                    out[v] |= 1 << u
            encoded = solver.solve(
                assumptions=fixed_arcs(out, built)
            )
            expected = mathematical_acceptance(out, (core,))
            if encoded != expected:
                raise RuntimeError(
                    "primitive fixed-arc mismatch: "
                    f"n={n} mask={mask} "
                    f"encoded={encoded} expected={expected}"
                )
            accepted += int(encoded)
    return {
        "gate": "primitive_exhaustive_fixed_arc_equivalence",
        "n": n,
        "tournaments": 1 << len(pairs),
        "accepted": accepted,
        "status": "PASS",
    }


def run_gates() -> dict:
    records: list[dict] = []

    positive = cyclic_tournament(5)
    prime5 = build_cnf(
        n=5,
        primitive_cores=(tuple(range(5)),),
    )
    with Solver(
        name="cadical195",
        bootstrap_with=prime5.cnf.clauses,
    ) as solver:
        if not solver.solve(assumptions=fixed_arcs(positive, prime5)):
            raise RuntimeError("primitive T5 positive gate failed")
    records.append({
        "gate": "primitive_t5_positive",
        "status": "PASS",
    })

    quotient = cyclic_tournament(3)
    decomposable6 = expand_transitive_fibres(
        quotient, [2, 2, 2]
    )
    base6 = build_cnf(n=6, primitive_cores=())
    prime6 = build_cnf(
        n=6,
        primitive_cores=(tuple(range(6)),),
    )
    with Solver(
        name="cadical195",
        bootstrap_with=base6.cnf.clauses,
    ) as solver:
        if not solver.solve(
            assumptions=fixed_arcs(decomposable6, base6)
        ):
            raise RuntimeError("decomposable K6 base gate failed")
    with Solver(
        name="cadical195",
        bootstrap_with=prime6.cnf.clauses,
    ) as solver:
        if solver.solve(
            assumptions=fixed_arcs(decomposable6, prime6)
        ):
            raise RuntimeError("decomposable K6 survived prime clauses")
    records.append({
        "gate": "decomposable_k6_rejected_only_by_prime_cut",
        "status": "PASS",
    })

    records.append(exhaustive_fixed_arc_equivalence_gate(5))
    records.append(exhaustive_fixed_arc_equivalence_gate(6))

    expected_boxes = {
        f"{a}_{z}"
        for a in ("a0", "a1", "a2p")
        for z in ("z2", "z3", "z4p")
    }
    if set(BOXES) != expected_boxes:
        raise RuntimeError("the nine parent boxes are not exhaustive")
    for lane in LANES.values():
        if sum(lane.partition) != N:
            raise RuntimeError(f"bad SMS partition {lane}")
        if tuple(range(N)) not in lane.all_cores:
            raise RuntimeError(f"lane omits full primitivity {lane}")
    records.append({
        "gate": "nine_box_and_lane_coverage",
        "status": "PASS",
        "boxes": list(BOXES),
        "lanes": list(LANES),
    })

    # Exercise the separate process and its module detector.
    gate_dir = REPO_ROOT / "worktest" / "v16-independent-gate"
    gate_dir.mkdir(parents=True, exist_ok=True)
    payload_path = gate_dir / "t5.json"
    audit_path = gate_dir / "t5-audit.json"
    payload_path.write_text(
        json.dumps({
            "n": 5,
            "arcs": [
                [u, v]
                for u in range(5)
                for v in range(5)
                if (positive[u] >> v) & 1
            ],
        }),
        encoding="utf-8",
    )
    completed = subprocess.run(
        [
            sys.executable,
            str(INDEPENDENT_VERIFIER),
            "--input",
            str(payload_path),
            "--output",
            str(audit_path),
            "--core",
            "0,1,2,3,4",
        ],
        capture_output=True,
        text=True,
        check=False,
    )
    if completed.returncode != 0:
        raise RuntimeError(
            "standalone verifier positive gate failed\n"
            + completed.stdout
            + completed.stderr
        )
    records.append({
        "gate": "standalone_zero_shared_code_audit",
        "status": "PASS",
    })

    return {
        "model_version": MODEL_VERSION,
        "status": "PASS",
        "records": records,
    }


def sms_command(
    binary: Path,
    *,
    n: int,
    cnf_path: Path,
    partition: tuple[int, ...],
    seconds: int,
) -> list[str]:
    command = [
        str(binary),
        "--vertices",
        str(n),
        "--directed",
        "--dimacs",
        str(cnf_path),
    ]
    if len(partition) > 1:
        command.extend(
            ["--initial-partition"]
            + [str(value) for value in partition]
        )
    command.extend(["--timeout", str(seconds)])
    return command


def run_sms_process(
    command: list[str],
    *,
    wrapper_seconds: int,
) -> tuple[int, str, bool, float]:
    started = time.monotonic()
    timed_out = False
    try:
        completed = subprocess.run(
            command,
            capture_output=True,
            text=True,
            timeout=wrapper_seconds,
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
    return returncode, output, timed_out, time.monotonic() - started


def run_sms_gates(binary: Path, output_path: Path | None) -> dict:
    gate_lane = Lane(
        lane_id="sms_partition_gate",
        partition=(5, 2),
        proper_cores=(tuple(range(5)),),
        description="small directed/colour-partition SMS gate",
    )
    built = build_cnf(
        n=7,
        lane=gate_lane,
        primitive_cores=(
            tuple(range(7)),
            tuple(range(5)),
        ),
    )
    gate_dir = REPO_ROOT / "worktest" / "v16-sms-gate"
    gate_dir.mkdir(parents=True, exist_ok=True)
    cnf_path = gate_dir / "partition-gate.cnf"
    built.cnf.to_file(cnf_path)
    command = sms_command(
        binary,
        n=7,
        cnf_path=cnf_path,
        partition=gate_lane.partition,
        seconds=60,
    )
    returncode, text, timed_out, elapsed = run_sms_process(
        command,
        wrapper_seconds=90,
    )
    status = classify(returncode, text, timed_out)
    if status != "SAT":
        raise RuntimeError(
            f"SMS directed/partition gate returned {status}\n{text}"
        )
    arcs = parse_sms_arcs(text, 7)
    if arcs is None:
        raise RuntimeError("SMS gate emitted no parseable tournament")
    out = arcs_to_masks(arcs, 7)
    if not mathematical_acceptance(
        out,
        (tuple(range(7)), tuple(range(5))),
    ):
        raise RuntimeError("SMS partition gate witness failed")
    record = {
        "model_version": MODEL_VERSION,
        "gate": "sms_directed_initial_partition_5_2",
        "status": "PASS",
        "seconds": round(elapsed, 3),
        "command": command,
        "sms_commit": SMS_COMMIT,
    }
    if output_path:
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(
            json.dumps(record, indent=2) + "\n",
            encoding="utf-8",
        )
    print(json.dumps(record, indent=2))
    return record


def independent_audit(
    arcs: list[list[int]],
    *,
    lane: Lane,
    box: str,
    directory: Path,
) -> dict:
    directory.mkdir(parents=True, exist_ok=True)
    candidate = directory / "candidate-arcs.json"
    audit_path = directory / "independent-audit.json"
    candidate.write_text(
        json.dumps({"n": N, "arcs": arcs}, indent=2) + "\n",
        encoding="utf-8",
    )
    command = [
        sys.executable,
        str(INDEPENDENT_VERIFIER),
        "--input",
        str(candidate),
        "--output",
        str(audit_path),
        "--box",
        box,
    ]
    for core in lane.proper_cores:
        command.extend(
            ["--core", ",".join(str(v) for v in core)]
        )
    completed = subprocess.run(
        command,
        capture_output=True,
        text=True,
        check=False,
    )
    if not audit_path.exists():
        return {
            "valid": False,
            "error": "standalone verifier produced no audit",
            "stdout": completed.stdout,
            "stderr": completed.stderr,
        }
    record = json.loads(audit_path.read_text(encoding="utf-8"))
    record["process_exit_code"] = completed.returncode
    return record


def solve_sms(
    *,
    binary: Path,
    lane_id: str,
    box: str,
    seconds: int,
    cnf_path: Path,
    result_path: Path,
    log_path: Path,
) -> dict:
    lane = LANES[lane_id]
    built = build_cnf(lane=lane, box=box)
    cnf_path.parent.mkdir(parents=True, exist_ok=True)
    result_path.parent.mkdir(parents=True, exist_ok=True)
    log_path.parent.mkdir(parents=True, exist_ok=True)
    built.cnf.to_file(cnf_path)
    cnf_path.with_suffix(".meta.json").write_text(
        json.dumps(built.metadata(), indent=2) + "\n",
        encoding="utf-8",
    )
    command = sms_command(
        binary,
        n=N,
        cnf_path=cnf_path,
        partition=lane.partition,
        seconds=seconds,
    )
    returncode, output, timed_out, elapsed = run_sms_process(
        command,
        wrapper_seconds=seconds + 60,
    )
    status = classify(returncode, output, timed_out)
    record: dict[str, object] = {
        "schema": "k16-primitive-sms-result-v1",
        "model_version": MODEL_VERSION,
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "slice_id": f"{lane_id}-{box}",
        "lane": lane_id,
        "sms_initial_partition": list(lane.partition),
        "primitive_cores": [
            list(core) for core in lane.all_cores
        ],
        "box": box,
        "status": status,
        "seconds": round(elapsed, 3),
        "time_limit_seconds": seconds,
        "solver_exit_code": returncode,
        "timed_out": timed_out,
        "command": command,
        "solver_level_exact": status == "UNSAT",
        "cnf": built.metadata(),
        "coverage": (
            "One of nine disjoint a/z parent boxes in one lossless "
            "primitive-labelling lane. UNKNOWN remains open."
        ),
    }
    if status == "SAT":
        arcs = parse_sms_arcs(output, N)
        if arcs is None:
            record["verified"] = False
            record["verification_error"] = "no parseable SMS tournament"
        else:
            audit = independent_audit(
                arcs,
                lane=lane,
                box=box,
                directory=result_path.parent / f"{lane_id}-{box}-audit",
            )
            record["candidate_arcs"] = arcs
            record["independent_audit"] = audit
            record["verified"] = bool(audit.get("valid"))
            if not record["verified"]:
                record["verification_error"] = (
                    "candidate failed zero-shared-code Pisa/primitivity audit"
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


def matrix_json(kind: str, lane: str | None) -> str:
    if kind == "benchmark":
        include = [
            {
                "lane": lane_id,
                "box": box,
                "slice_id": f"{lane_id}-{box}",
            }
            for lane_id in LANES
            for box in BENCHMARK_BOXES
        ]
    elif kind == "formal":
        if lane not in LANES:
            raise ValueError("formal matrix requires a valid lane")
        include = [
            {
                "lane": lane,
                "box": box,
                "slice_id": f"{lane}-{box}",
            }
            for box in BOXES
        ]
    else:
        raise ValueError(kind)
    return json.dumps({"include": include}, separators=(",", ":"))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--gates", action="store_true")
    parser.add_argument("--sms-gates", action="store_true")
    parser.add_argument(
        "--matrix",
        choices=("benchmark", "formal"),
    )
    parser.add_argument("--lane", choices=tuple(LANES))
    parser.add_argument("--box", choices=BOXES)
    parser.add_argument("--binary", type=Path)
    parser.add_argument("--seconds", type=int, default=300)
    parser.add_argument("--cnf", type=Path)
    parser.add_argument("--result", type=Path)
    parser.add_argument("--log", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--solve", action="store_true")
    args = parser.parse_args()

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
    if args.sms_gates:
        if args.binary is None:
            parser.error("--sms-gates requires --binary")
        run_sms_gates(args.binary, args.output)
        return
    if args.matrix:
        print(matrix_json(args.matrix, args.lane))
        return
    if args.solve:
        required = (
            args.lane,
            args.box,
            args.binary,
            args.cnf,
            args.result,
            args.log,
        )
        if any(value is None for value in required):
            parser.error(
                "--solve requires --lane --box --binary --cnf "
                "--result --log"
            )
        solve_sms(
            binary=args.binary,
            lane_id=args.lane,
            box=args.box,
            seconds=args.seconds,
            cnf_path=args.cnf,
            result_path=args.result,
            log_path=args.log,
        )
        return
    parser.error("choose --gates, --sms-gates, --matrix, or --solve")


if __name__ == "__main__":
    main()
