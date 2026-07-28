#!/usr/bin/env python3
"""Lossless theorem cuts for the primitive K16 Pisa search.

This module deliberately augments the historical v16/v17 base encoding
without changing its existing variable numbers.  In particular, all arc
variables remain the first ``n * (n - 1)`` variables, so every signed cube
emitted by v17/v18 remains valid.

Only proved implications are added:

* a strong tournament has at least three kings (Havet--Thomasse);
* ``b(v) = 0`` is equivalent to ``v`` being a king;
* blocker/cover is transitive;
* in a primitive tournament, a blocker has outdegree at least two larger;
* along a blocker edge, blocker count decreases strictly.

The last two facts follow from
``N+(v) union {v} subseteq N+(x)`` whenever ``x`` blocks ``v``.  Equality
in the degree bound would make ``{v, x}`` a non-trivial module.
"""

from __future__ import annotations

from dataclasses import dataclass

from k16_primitive_sms import (
    Encoding,
    Lane,
    add_cardinality,
    build_cnf,
    reify_atleast,
)


MODEL_VERSION = "k16-pisa-v21-king-cover-unary-cuts-20260728"


@dataclass
class TheoremEncoding:
    base: Encoding
    base_clause_count: int
    base_variable_count: int
    theorem_clause_count: int
    theorem_variable_count: int
    king_literals: list[int]
    degree_atleast: dict[tuple[int, int], int]
    blocker_atleast: dict[tuple[int, int], int]

    @property
    def cnf(self):
        return self.base.cnf

    @property
    def pool(self):
        return self.base.pool

    def metadata(self) -> dict:
        record = self.base.metadata()
        record.update(
            {
                "model_version": MODEL_VERSION,
                "historical_base_model_version": record["model_version"],
                "base_variables": self.base_variable_count,
                "base_clauses": self.base_clause_count,
                "theorem_variables": self.theorem_variable_count,
                "theorem_clauses": self.theorem_clause_count,
                "variables": max(self.cnf.nv, self.pool.top),
                "clauses": len(self.cnf.clauses),
                "theorem_cuts": [
                    "at least three kings in a strong tournament",
                    "king iff blocker count is zero",
                    "blocker relation is transitive",
                    "primitive blocker outdegree gap is at least two",
                    "blocker count strictly decreases along blocker edges",
                    "a degree-seven zero vertex's unique blocker is a king",
                ],
                "excluded_unproved_cuts": [
                    "no empirical zero-class lower bound beyond two",
                    "no total-blocker lower bound beyond proved identities",
                    "no heuristic H-T weighted extension",
                ],
            }
        )
        return record


def _existing(pool, name: str) -> int:
    for variable, variable_name in pool.names.items():
        if variable_name == name:
            return variable
    raise RuntimeError(f"historical base variable is missing: {name}")


def build_theorem_cnf(
    *,
    n: int,
    lane: Lane,
    box: str | None,
    primitive_cores: tuple[tuple[int, ...], ...] | None = None,
) -> TheoremEncoding:
    """Build the historical base and append only lossless theorem cuts."""

    base = build_cnf(
        n=n,
        lane=lane,
        box=box,
        primitive_cores=primitive_cores,
    )
    cnf = base.cnf
    pool = base.pool
    base_clause_count = len(cnf.clauses)
    base_variable_count = max(cnf.nv, pool.top)
    full_core = tuple(range(n))
    if full_core not in base.primitive_cores:
        raise ValueError("the theorem campaign requires full primitivity")

    outgoing = {
        v: [pool.arcs[(v, u)] for u in range(n) if u != v]
        for v in range(n)
    }
    blocked = {
        v: [base.blocker[(v, x)] for x in range(n) if x != v]
        for v in range(n)
    }

    # Reuse thresholds already present in the historical model, then create
    # the missing unary degree thresholds.  A single threshold family lets
    # all 240 blocker edges share the same counting machinery.
    degree_atleast: dict[tuple[int, int], int] = {}
    for v in range(n):
        for threshold in range(3, n):
            if threshold in {6, 7, n // 2}:
                literal = _existing(
                    pool, f"degree_ge_{threshold}_{v}"
                )
            else:
                literal = reify_atleast(
                    cnf,
                    pool,
                    outgoing[v],
                    threshold,
                    f"v21_degree_ge_{threshold}_{v}",
                )
            degree_atleast[(v, threshold)] = literal

    blocker_atleast: dict[tuple[int, int], int] = {}
    for v in range(n):
        for threshold in range(1, n):
            blocker_atleast[(v, threshold)] = reify_atleast(
                cnf,
                pool,
                blocked[v],
                threshold,
                f"v21_blocker_ge_{threshold}_{v}",
            )

    # b(v)=0 iff v is a king.  Strong tournaments have no dominating
    # vertex, hence Havet--Thomasse gives at least three kings.
    king_literals = [
        -blocker_atleast[(v, 1)]
        for v in range(n)
    ]
    add_cardinality(
        cnf,
        pool,
        king_literals,
        bound=3,
        kind="atleast",
    )

    # Cover/blocker transitivity and the two strict monotonicities.
    for v in range(n):
        for x in range(n):
            if x == v:
                continue
            q_vx = base.blocker[(v, x)]

            # Minimum outdegree is already two, so the gap theorem starts
            # with d(x)>=4 even without a threshold premise for v.
            cnf.append([
                -q_vx,
                degree_atleast[(x, 4)],
            ])
            for threshold in range(3, n - 2):
                cnf.append([
                    -q_vx,
                    -degree_atleast[(v, threshold)],
                    degree_atleast[(x, threshold + 2)],
                ])
            # d(v)>=n-2 cannot have a blocker in a primitive tournament.
            cnf.append([
                -q_vx,
                -degree_atleast[(v, n - 2)],
            ])

            # x itself is one blocker of v, and every blocker of x also
            # blocks v.  The unary implications expose b(v)>=b(x)+1.
            for threshold in range(1, n - 1):
                cnf.append([
                    -q_vx,
                    -blocker_atleast[(x, threshold)],
                    blocker_atleast[(v, threshold + 1)],
                ])
            cnf.append([
                -q_vx,
                -blocker_atleast[(x, n - 1)],
            ])

            for y in range(n):
                if y in {v, x}:
                    continue
                cnf.append([
                    -q_vx,
                    -base.blocker[(x, y)],
                    base.blocker[(v, y)],
                ])

                if n == 16:
                    # A K16 zero vertex of degree seven has exactly one
                    # blocker.  Its blocker therefore has no blocker of its
                    # own.
                    cnf.append([
                        -base.zero[v],
                        -degree_atleast[(v, 7)],
                        -q_vx,
                        -base.blocker[(x, y)],
                    ])

    cnf.nv = max(cnf.nv, pool.top)
    return TheoremEncoding(
        base=base,
        base_clause_count=base_clause_count,
        base_variable_count=base_variable_count,
        theorem_clause_count=len(cnf.clauses) - base_clause_count,
        theorem_variable_count=max(cnf.nv, pool.top) - base_variable_count,
        king_literals=king_literals,
        degree_atleast=degree_atleast,
        blocker_atleast=blocker_atleast,
    )
