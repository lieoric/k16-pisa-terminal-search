# Exact h14 module-3 campaign

Target:

```text
h14_p00 = (3, 1^13)
```

This is the last quotient box corresponding to a module of size three in a
possible K16 Pisa tournament.

## Why the former run was retired

The cancelled fixed-Hamilton-cycle campaign returned 179 stage-two result
files.  Every result was `UNKNOWN`; none was `UNSAT`.  Those jobs consumed
about 89.5 solver-hours and averaged about nine million CP-SAT branches.
Increasing the same timeout would repeat the principal symmetry and
propagation problems rather than create cumulative coverage.

## New exact partition

The weight-three class is unique, so it is labelled vertex 0 without loss of
generality.  The other thirteen classes all have weight one and remain
interchangeable.

Every strong quotient gives vertex 0 an ordinary outdegree in `1..12`.
Consequently the twelve constraints

```text
outdegree_Q(0) = 1, 2, ..., 12
```

are disjoint and cover the full target.  No `UNKNOWN` slice is counted as an
exclusion.

## Symmetry algorithm

The formula is a directed-graph CNF whose first `14*13=182` variables are the
ordered arc variables required by SAT Modulo Symmetries (SMS).  SMS is run
with:

```text
--initial-partition 1 13
```

Thus the unique heavy class is fixed while the full `S_13` relabelling group
of the unit classes is handled dynamically.  The remaining auxiliary
variables express blockers, weighted margins, zero classes, endpoint cuts,
and strong connectivity.

This design follows the SMS approach of checking partial graphs for
canonical minimality during CDCL search:

- Markus Kirchweger and Stefan Szeider, *SAT Modulo Symmetries for Graph
  Generation*, CP 2021, DOI 10.4230/LIPIcs.CP.2021.34.

If any long slice remains `UNKNOWN`, its next refinement will retain SMS
inside every child.  This follows the warning from *Smart Cubing for Graph
Search* (arXiv:2501.17201) that propagator-based solvers lose much of their
benefit when cubes are solved without the propagator and its learned
constraints.

## Exact constraints

For quotient weights `t=(3,1^13)` and total weight 16:

```text
weighted_margin(v)
  = 16 - t[v] - 2*outweight(v) - blockerweight(v).
```

The CNF enforces:

- weighted margin at most zero at every class;
- zero flags if and only if the weighted margin is zero;
- at least two zero classes;
- exact strong connectivity using all directed cut clauses;
- expanded minimum outdegree at least two;
- every residual K16 zero vertex has degree six or seven;
- expanded total blocker count at least 16;
- a degree-six zero forces expanded total blocker count at least 20.

The transitive weight-three fibre contributes exactly
`binom(3,2)=3` internal blockers to the expanded total.

## Gates and certification

Before the long matrix starts, the workflow requires:

- an equal-weight `C3` SAT witness;
- an unequal-weight `C3` UNSAT result;
- an equal-weight `C7` SAT witness expanded to a verified K14 Pisa
  tournament;
- deterministic fixed-arc equivalence tests comparing the CNF with an
  independent mathematical predicate;
- successful construction of all twelve formal h14 slices.

A SAT quotient is expanded to sixteen vertices with a transitive
three-vertex fibre and independently verified.  An UNSAT status closes only
its named heavy-outdegree slice.  All twelve UNSAT statuses are required for
the conclusion `UNSAT_H14_P00`.

Each slice receives 19,200 seconds (5 h 20 min) of uninterrupted SMS search,
inside a 350-minute GitHub Actions job.
