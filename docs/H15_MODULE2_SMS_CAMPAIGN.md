# Exact h15 module-2 campaign

## Target

This campaign decides the last decomposable weighted quotient target

```text
h15_p00 = (2, 1^14).
```

The unique weight-two class is labelled vertex 0.  The other fourteen
vertices remain interchangeable, so the exact SAT Modulo Symmetries run uses

```text
--vertices 15 --directed --initial-partition 1 14
```

and preserves the full colour symmetry `S_1 x S_14`.

## Exact partition

Strong connectivity forces the heavy vertex's ordinary outdegree into
`1..13`.  In this target its weighted outdegree equals its ordinary
outdegree.  Every zero weighted-margin class in a remaining K16 endpoint has
expanded degree 6 or 7.  Therefore the heavy class can be zero only in the
two central degree slices.

The search uses fifteen disjoint slices:

- degrees 1--5 with the heavy zero flag false;
- degree 6 with the heavy zero flag false or true;
- degree 7 with the heavy zero flag false or true;
- degrees 8--13 with the heavy zero flag false.

These slices are exhaustive.  `UNSAT` is recorded only when SMS proves an
individual slice infeasible.  `UNKNOWN` is never treated as exclusion.

## Why SMS

The target has a single distinguished colour class and a fourteen-vertex
interchangeable colour class.  SMS checks canonical minimality during CDCL
search and can remove isomorphic partial tournaments without materializing
the full static symmetry-breaking system.

The solver is pinned to commit
`464f12f1fd36b496e7ba9dcbb622b079de02dce4`.

## Safety gates

Before any long solve, the workflow runs:

1. equal-weight directed C3 positive gate;
2. unequal-weight directed C3 negative gate;
3. equal-weight directed C7 positive gate;
4. 128 fixed-arc base-encoding equivalence checks;
5. 32 fixed-arc h15 endpoint-cut equivalence checks;
6. construction of all fifteen formal slices.

Any SAT result is expanded with a transitive two-vertex fibre and checked by
the independent K16 verifier before it is accepted.

## Logical consequence

If all fifteen slices are `UNSAT`, then no K16 Pisa tournament has a
nontrivial module of size two.  Combined with the completed h3--h14 weighted
quotient ladder, this closes every decomposable K16 Pisa tournament.  Any
remaining witness would have to be primitive.
