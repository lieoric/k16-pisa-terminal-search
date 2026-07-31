#!/usr/bin/env python3
"""Symmetry-safe exact SAT/PB encodings for Pisa tournaments.

Unlike the earlier terminal models, this formula does not distinguish a
particular zero-margin vertex or a labelled median order.  The complete
formula is invariant under all vertex permutations, so a directed
SAT-Modulo-Symmetries solver may safely retain only one representative of
each tournament isomorphism class.

The first n(n-1) variables are the ordered arc variables in the row-major
layout required by SMS.  All other variables are auxiliary.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from dataclasses import dataclass
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Solver

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from pisa_verify import verify


BASE_MODEL_VERSION = "k16-pisa-v11-symmetry-safe-sat-pb-20260727"
HYBRID_MODEL_VERSION = "k16-pisa-v12-symmetry-endpoint-hybrid-20260727"


def model_version(endpoint_closures: bool) -> str:
    return HYBRID_MODEL_VERSION if endpoint_closures else BASE_MODEL_VERSION


class NamedPool:
    def __init__(self, n: int):
        self.n = n
        self.pool = IDPool(start_from=1)
        self.names: dict[int, str] = {}
        self.arcs: dict[tuple[int, int], int] = {}

        # SMS requires directed edges to be variables 1..n(n-1), row-major
        # over the adjacency matrix with the diagonal omitted.
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
    for lit in literals:
        cnf.append([-target, lit])
    cnf.append([target] + [-lit for lit in literals])


def add_cardinality(
    cnf: CNF,
    pool: NamedPool,
    literals: list[int],
    *,
    bound: int,
    kind: str,
    guard: int | None = None,
) -> None:
    if kind == "atleast":
        encoded = CardEnc.atleast(
            lits=literals,
            bound=bound,
            vpool=pool.pool,
            encoding=EncType.seqcounter,
        )
    elif kind == "atmost":
        encoded = CardEnc.atmost(
            lits=literals,
            bound=bound,
            vpool=pool.pool,
            encoding=EncType.seqcounter,
        )
    else:
        raise ValueError(f"unknown cardinality kind {kind}")

    if guard is None:
        cnf.extend(encoded.clauses)
    else:
        # guard -> encoded constraint
        cnf.extend([[-guard] + clause for clause in encoded.clauses])


@dataclass
class CNFEncoding:
    n: int
    min_total_blockers: int
    endpoint_closures: bool
    cnf: CNF
    pool: NamedPool
    cycle: dict[tuple[int, int, int, int], int]
    blocker: dict[tuple[int, int], int]
    zero: list[int]

    def metadata(self) -> dict:
        return {
            "model_version": model_version(self.endpoint_closures),
            "format": "DIMACS CNF",
            "n": self.n,
            "variables": max(self.cnf.nv, self.pool.top),
            "clauses": len(self.cnf.clauses),
            "arc_variables": self.n * (self.n - 1),
            "min_total_blockers": self.min_total_blockers,
            "endpoint_closures": self.endpoint_closures,
            "symmetry": (
                "The formula is invariant under every permutation of the "
                "n tournament vertices; no feed vertex is labelled."
            ),
            "sms_edge_layout": "directed row-major, diagonal omitted",
        }


def build_cnf(
    n: int,
    min_total_blockers: int = 0,
    endpoint_closures: bool = False,
) -> CNFEncoding:
    if n < 3:
        raise ValueError("n must be at least 3")
    if not 0 <= min_total_blockers <= n * (n - 1):
        raise ValueError("bad blocker lower bound")
    if endpoint_closures and n != 16:
        raise ValueError("endpoint closures are certified only for n=16")

    named = NamedPool(n)
    cnf = CNF()
    arc = named.arcs

    # Exactly one direction on every unordered pair.
    for u in range(n):
        for v in range(u + 1, n):
            cnf.append([arc[(u, v)], arc[(v, u)]])
            cnf.append([-arc[(u, v)], -arc[(v, u)]])

    # The two possible directed 3-cycles on every vertex triple.
    cycle: dict[tuple[int, int, int, int], int] = {}
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
                cycle[(a, b, c, 0)] = forward
                cycle[(a, b, c, 1)] = reverse
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
                path_cycles[(a, c)].append(forward)
                path_cycles[(b, a)].append(forward)
                path_cycles[(c, b)].append(forward)
                path_cycles[(a, b)].append(reverse)
                path_cycles[(c, a)].append(reverse)
                path_cycles[(b, c)].append(reverse)

    # q[v,x] iff x->v and no directed triangle gives v a two-step path to x.
    blocker: dict[tuple[int, int], int] = {}
    for v in range(n):
        for x in range(n):
            if v == x:
                continue
            q = named.new(f"blocker_{v}_{x}")
            blocker[(v, x)] = q
            cycles = path_cycles[(v, x)]
            cnf.append([-q, arc[(x, v)]])
            for cyc in cycles:
                cnf.append([-q, -cyc])
            cnf.append([q, -arc[(x, v)]] + cycles)

    zero = []
    for v in range(n):
        outgoing = [arc[(v, u)] for u in range(n) if u != v]
        blocked = [blocker[(v, x)] for x in range(n) if x != v]

        # Minimum out-degree theorem used by all terminal campaigns.
        add_cardinality(
            cnf,
            named,
            outgoing,
            bound=2,
            kind="atleast",
        )

        # Count each outgoing arc twice without passing duplicate literals to
        # a cardinality encoder.
        degree_copies = []
        for u, edge in zip(
            [u for u in range(n) if u != v],
            outgoing,
        ):
            copy = named.new(f"degree_copy_{v}_{u}")
            cnf.append([-copy, edge])
            cnf.append([copy, -edge])
            degree_copies.append(copy)
        weighted_margin_terms = blocked + outgoing + degree_copies

        # b(v) + 2d+(v) >= n-1 is exactly margin(v) <= 0.
        add_cardinality(
            cnf,
            named,
            weighted_margin_terms,
            bound=n - 1,
            kind="atleast",
        )

        # z_v implies the reverse inequality.  Together with the preceding
        # lower bound, z_v means margin(v)=0.
        z = named.new(f"zero_margin_{v}")
        zero.append(z)
        add_cardinality(
            cnf,
            named,
            weighted_margin_terms,
            bound=n - 1,
            kind="atmost",
            guard=z,
        )
    cnf.append(zero)

    if min_total_blockers:
        add_cardinality(
            cnf,
            named,
            list(blocker.values()),
            bound=min_total_blockers,
            kind="atleast",
        )

    # Exact v5/v6 closure, expressed without choosing a labelled feed
    # vertex.  After the already certified endpoint layers are removed,
    # every remaining K16 witness has a zero-margin endpoint of one of:
    #
    #   d+(v)=7, b(v)=1 and total blockers B>=16; or
    #   d+(v)=6, b(v)=3 and total blockers B>=20.
    #
    # The zero-margin equation already forces b=15-2d, so only the degree
    # needs to be reified here.  The existential choice is symmetric over
    # all 16 vertices and is therefore safe for SMS canonical partitioning.
    if endpoint_closures:
        all_blockers = list(blocker.values())
        if min_total_blockers < 16:
            add_cardinality(
                cnf,
                named,
                all_blockers,
                bound=16,
                kind="atleast",
            )

        branch_d7 = named.new("endpoint_branch_degree_7")
        branch_d6 = named.new("endpoint_branch_degree_6")
        cnf.append([branch_d7, branch_d6])
        cnf.append([-branch_d7, -branch_d6])

        selectors_d7 = []
        selectors_d6 = []
        for v in range(n):
            outgoing = [arc[(v, u)] for u in range(n) if u != v]
            select_d7 = named.new(f"endpoint_degree_7_vertex_{v}")
            select_d6 = named.new(f"endpoint_degree_6_vertex_{v}")
            selectors_d7.append(select_d7)
            selectors_d6.append(select_d6)

            cnf.append([-select_d7, branch_d7])
            cnf.append([-select_d6, branch_d6])
            cnf.append([-select_d7, zero[v]])
            cnf.append([-select_d6, zero[v]])
            for selector, degree in (
                (select_d7, 7),
                (select_d6, 6),
            ):
                add_cardinality(
                    cnf,
                    named,
                    outgoing,
                    bound=degree,
                    kind="atleast",
                    guard=selector,
                )
                add_cardinality(
                    cnf,
                    named,
                    outgoing,
                    bound=degree,
                    kind="atmost",
                    guard=selector,
                )

        cnf.append([-branch_d7] + selectors_d7)
        cnf.append([-branch_d6] + selectors_d6)
        selectors = selectors_d7 + selectors_d6
        cnf.append(selectors)
        add_cardinality(
            cnf,
            named,
            selectors,
            bound=1,
            kind="atmost",
        )

        # Only the degree-6 residual needs the stronger B>=20 closure.
        add_cardinality(
            cnf,
            named,
            all_blockers,
            bound=20,
            kind="atleast",
            guard=branch_d6,
        )

    # Exact strong connectivity with no distinguished root.  Every proper
    # cut must contain an arc in each direction.  Complementary cuts are
    # generated only once by requiring vertex 0 to stay outside S.
    other_vertices = list(range(1, n))
    for mask in range(1, 1 << (n - 1)):
        inside = {
            other_vertices[index]
            for index in range(n - 1)
            if (mask >> index) & 1
        }
        outside = [v for v in range(n) if v not in inside]
        incoming = [
            arc[(u, v)]
            for u in outside
            for v in inside
        ]
        outgoing = [
            arc[(v, u)]
            for v in inside
            for u in outside
        ]
        cnf.append(incoming)
        cnf.append(outgoing)

    cnf.nv = max(cnf.nv, named.top)
    return CNFEncoding(
        n=n,
        min_total_blockers=min_total_blockers,
        endpoint_closures=endpoint_closures,
        cnf=cnf,
        pool=named,
        cycle=cycle,
        blocker=blocker,
        zero=zero,
    )


class OPBBuilder:
    def __init__(self):
        self.next_var = 1
        self.names: dict[int, str] = {}
        self.constraints: list[str] = []

    def new(self, name: str) -> int:
        var = self.next_var
        self.next_var += 1
        self.names[var] = name
        return var

    @property
    def variables(self) -> int:
        return self.next_var - 1

    @staticmethod
    def expression(terms: list[tuple[int, int]]) -> str:
        return " ".join(
            f"{coefficient:+d} x{variable}"
            for coefficient, variable in terms
            if coefficient
        )

    def add(
        self,
        terms: list[tuple[int, int]],
        relation: str,
        rhs: int,
    ) -> None:
        # RoundingSat's documented OPB reader accepts >= and =, not <=.
        if relation == "<=":
            terms = [(-coefficient, variable) for coefficient, variable in terms]
            rhs = -rhs
            relation = ">="
        if relation not in {">=", "="}:
            raise ValueError(f"unsupported OPB relation: {relation}")
        self.constraints.append(
            f"{self.expression(terms)} {relation} {rhs} ;"
        )

    def write(self, path: Path, comments: list[str]) -> None:
        lines = [
            f"* {comment}" for comment in comments
        ]
        lines.append(
            f"* #variable= {self.variables} "
            f"#constraint= {len(self.constraints)}"
        )
        lines.extend(self.constraints)
        path.write_text("\n".join(lines) + "\n", encoding="utf-8")


@dataclass
class OPBEncoding:
    n: int
    min_total_blockers: int
    endpoint_closures: bool
    builder: OPBBuilder
    arcs: dict[tuple[int, int], int]
    blocker: dict[tuple[int, int], int]
    zero: list[int]

    def metadata(self) -> dict:
        return {
            "model_version": model_version(self.endpoint_closures),
            "format": "OPB",
            "n": self.n,
            "variables": self.builder.variables,
            "constraints": len(self.builder.constraints),
            "arc_variables": self.n * (self.n - 1),
            "min_total_blockers": self.min_total_blockers,
            "endpoint_closures": self.endpoint_closures,
        }


def build_opb(
    n: int,
    min_total_blockers: int = 0,
    endpoint_closures: bool = False,
) -> OPBEncoding:
    if n < 3:
        raise ValueError("n must be at least 3")
    if not 0 <= min_total_blockers <= n * (n - 1):
        raise ValueError("bad blocker lower bound")
    if endpoint_closures and n != 16:
        raise ValueError("endpoint closures are certified only for n=16")

    opb = OPBBuilder()
    arc: dict[tuple[int, int], int] = {}
    for u in range(n):
        for v in range(n):
            if u != v:
                arc[(u, v)] = opb.new(f"arc_{u}_{v}")

    for u in range(n):
        for v in range(u + 1, n):
            opb.add(
                [(1, arc[(u, v)]), (1, arc[(v, u)])],
                "=",
                1,
            )

    path_cycles = {
        (v, x): []
        for v in range(n)
        for x in range(n)
        if v != x
    }
    for a in range(n):
        for b in range(a + 1, n):
            for c in range(b + 1, n):
                specs = (
                    (
                        opb.new(f"cycle_{a}_{b}_{c}_forward"),
                        [arc[(a, b)], arc[(b, c)], arc[(c, a)]],
                        ((a, c), (b, a), (c, b)),
                    ),
                    (
                        opb.new(f"cycle_{a}_{b}_{c}_reverse"),
                        [arc[(a, c)], arc[(c, b)], arc[(b, a)]],
                        ((a, b), (c, a), (b, c)),
                    ),
                )
                for cyc, edges, pairs in specs:
                    for edge in edges:
                        opb.add([(1, edge), (-1, cyc)], ">=", 0)
                    opb.add(
                        [(1, cyc)] + [(-1, edge) for edge in edges],
                        ">=",
                        -2,
                    )
                    for pair in pairs:
                        path_cycles[pair].append(cyc)

    blocker: dict[tuple[int, int], int] = {}
    for v in range(n):
        for x in range(n):
            if v == x:
                continue
            q = opb.new(f"blocker_{v}_{x}")
            blocker[(v, x)] = q
            cycles = path_cycles[(v, x)]
            opb.add([(1, arc[(x, v)]), (-1, q)], ">=", 0)
            for cyc in cycles:
                opb.add([(1, q), (1, cyc)], "<=", 1)
            opb.add(
                [(1, q), (-1, arc[(x, v)])]
                + [(1, cyc) for cyc in cycles],
                ">=",
                0,
            )

    zero = []
    maximum_excess = 2 * (n - 1)
    for v in range(n):
        outgoing = [arc[(v, u)] for u in range(n) if u != v]
        blocked = [blocker[(v, x)] for x in range(n) if x != v]
        opb.add([(1, edge) for edge in outgoing], ">=", 2)
        weighted = (
            [(1, q) for q in blocked]
            + [(2, edge) for edge in outgoing]
        )
        opb.add(weighted, ">=", n - 1)
        z = opb.new(f"zero_margin_{v}")
        zero.append(z)
        opb.add(
            weighted + [(maximum_excess, z)],
            "<=",
            (n - 1) + maximum_excess,
        )
    opb.add([(1, z) for z in zero], ">=", 1)

    if min_total_blockers:
        opb.add(
            [(1, q) for q in blocker.values()],
            ">=",
            min_total_blockers,
        )

    if endpoint_closures:
        all_blockers = [(1, q) for q in blocker.values()]
        if min_total_blockers < 16:
            opb.add(all_blockers, ">=", 16)

        branch_d7 = opb.new("endpoint_branch_degree_7")
        branch_d6 = opb.new("endpoint_branch_degree_6")
        opb.add([(1, branch_d7), (1, branch_d6)], "=", 1)

        selectors_d7 = []
        selectors_d6 = []
        all_selectors = []
        for v in range(n):
            outgoing = [arc[(v, u)] for u in range(n) if u != v]
            select_d7 = opb.new(f"endpoint_degree_7_vertex_{v}")
            select_d6 = opb.new(f"endpoint_degree_6_vertex_{v}")
            selectors_d7.append(select_d7)
            selectors_d6.append(select_d6)
            all_selectors.extend((select_d7, select_d6))

            for selector, branch, degree in (
                (select_d7, branch_d7, 7),
                (select_d6, branch_d6, 6),
            ):
                opb.add([(1, branch), (-1, selector)], ">=", 0)
                opb.add([(1, zero[v]), (-1, selector)], ">=", 0)
                opb.add(
                    [(1, edge) for edge in outgoing]
                    + [(-degree, selector)],
                    ">=",
                    0,
                )
                opb.add(
                    [(1, edge) for edge in outgoing]
                    + [((n - 1) - degree, selector)],
                    "<=",
                    n - 1,
                )

        opb.add(
            [(1, selector) for selector in selectors_d7]
            + [(-1, branch_d7)],
            ">=",
            0,
        )
        opb.add(
            [(1, selector) for selector in selectors_d6]
            + [(-1, branch_d6)],
            ">=",
            0,
        )
        opb.add([(1, selector) for selector in all_selectors], "=", 1)
        opb.add(all_blockers + [(-20, branch_d6)], ">=", 0)

    other_vertices = list(range(1, n))
    for mask in range(1, 1 << (n - 1)):
        inside = {
            other_vertices[index]
            for index in range(n - 1)
            if (mask >> index) & 1
        }
        outside = [v for v in range(n) if v not in inside]
        opb.add(
            [(1, arc[(u, v)]) for u in outside for v in inside],
            ">=",
            1,
        )
        opb.add(
            [(1, arc[(v, u)]) for v in inside for u in outside],
            ">=",
            1,
        )

    return OPBEncoding(
        n=n,
        min_total_blockers=min_total_blockers,
        endpoint_closures=endpoint_closures,
        builder=opb,
        arcs=arc,
        blocker=blocker,
        zero=zero,
    )


def arcs_from_model(
    model: list[int],
    arcs: dict[tuple[int, int], int],
    n: int,
) -> list[int]:
    positive = {lit for lit in model if lit > 0}
    out = [0] * n
    for (u, v), variable in arcs.items():
        if variable in positive:
            out[u] |= 1 << v
    return out


def solve_cnf(
    encoding: CNFEncoding,
    solver_name: str,
) -> dict:
    started = time.perf_counter()
    with Solver(
        name=solver_name,
        bootstrap_with=encoding.cnf.clauses,
    ) as solver:
        sat = solver.solve()
        elapsed = time.perf_counter() - started
        record = {
            "model_version": model_version(encoding.endpoint_closures),
            "n": encoding.n,
            "solver": solver_name,
            "status": "SAT" if sat else "UNSAT",
            "seconds": round(elapsed, 3),
            "variables": encoding.cnf.nv,
            "clauses": len(encoding.cnf.clauses),
            "min_total_blockers": encoding.min_total_blockers,
            "endpoint_closures": encoding.endpoint_closures,
        }
        if sat:
            model = solver.get_model()
            out = arcs_from_model(
                model,
                encoding.pool.arcs,
                encoding.n,
            )
            check = verify(out)
            if not check["is_pisa"]:
                raise RuntimeError(
                    "SAT model failed the independent tournament verifier"
                )
            record["verified"] = True
            record["witness"] = check
        return record


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=16)
    parser.add_argument("--min-total-blockers", type=int)
    parser.add_argument(
        "--endpoint-closures",
        action="store_true",
        help=(
            "apply the exact n=16 v5/v6 endpoint residual closure "
            "(zero d=7 with B>=16, or zero d=6 with B>=20)"
        ),
    )
    parser.add_argument("--cnf", type=Path)
    parser.add_argument("--opb", type=Path)
    parser.add_argument("--metadata", type=Path)
    parser.add_argument("--solve", action="store_true")
    parser.add_argument("--solver", default="cadical195")
    parser.add_argument("--result", type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    minimum = (
        args.min_total_blockers
        if args.min_total_blockers is not None
        else 10 if args.n == 16 else 0
    )

    cnf_encoding = None
    metadata = {
        "model_version": model_version(args.endpoint_closures),
        "n": args.n,
        "min_total_blockers": minimum,
        "endpoint_closures": args.endpoint_closures,
    }
    if args.cnf or args.solve:
        cnf_encoding = build_cnf(
            args.n,
            minimum,
            endpoint_closures=args.endpoint_closures,
        )
        metadata["cnf"] = cnf_encoding.metadata()
        if args.cnf:
            args.cnf.parent.mkdir(parents=True, exist_ok=True)
            cnf_encoding.cnf.to_file(args.cnf)

    if args.opb:
        opb_encoding = build_opb(
            args.n,
            minimum,
            endpoint_closures=args.endpoint_closures,
        )
        metadata["opb"] = opb_encoding.metadata()
        args.opb.parent.mkdir(parents=True, exist_ok=True)
        opb_encoding.builder.write(
            args.opb,
            [
                model_version(args.endpoint_closures),
                f"Pisa tournament n={args.n}",
                f"minimum total blockers={minimum}",
                f"endpoint closures={args.endpoint_closures}",
            ],
        )

    if args.metadata:
        args.metadata.parent.mkdir(parents=True, exist_ok=True)
        args.metadata.write_text(
            json.dumps(metadata, indent=2) + "\n",
            encoding="utf-8",
        )

    if args.solve:
        if cnf_encoding is None:
            raise AssertionError("CNF encoding was not built")
        result = solve_cnf(cnf_encoding, args.solver)
        print(json.dumps(result, indent=2), flush=True)
        if args.result:
            args.result.parent.mkdir(parents=True, exist_ok=True)
            args.result.write_text(
                json.dumps(result, indent=2) + "\n",
                encoding="utf-8",
            )
    elif not (args.cnf or args.opb or args.metadata):
        raise SystemExit("request --cnf, --opb, --metadata, or --solve")
    else:
        print(json.dumps(metadata, indent=2), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
