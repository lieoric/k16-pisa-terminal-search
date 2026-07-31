# V24-D: the last V24-C leaf, split eight ways

V24-D resumes only the sole terminal `UNKNOWN` left by completed V24-C run
`30587970184`.

## Audited baseline

- exact original partition leaves: `675 / 676`
- open original partition leaves: `1`
- roots exactly excluded: `6 / 7`
- sole open box: `a0_z4p`
- sole open V23 source leaf: `a0_z4p-c000081`
- sole open V24-B child: `b0184`
- sole open V24-C child: `c0138`
- verified SAT witnesses: `0`

The planner checks the V24-C final ledger, source manifest, solver hashes,
theorem-CNF hash, signed cube hash, exact inherited counts, and the final
status of `c0138`. No previously closed leaf is submitted again.

## Complete eight-way refinement

The inherited cube is replaced by a complete three-level adaptive MOMS tree.
Both signs of each decision are retained. This yields at most eight mutually
exclusive children whose union is exactly the inherited cube. Unit-conflicting
children, if any, are closed locally; all surviving children run independently.

The pinned V24-C endpoint produces eight solver children. They run in parallel
on eight standard Ubuntu runners.

## Solver and accounting semantics

Each child first receives CaDiCaL for up to 3600 seconds. Only CaDiCaL
`UNKNOWN` children advance to an independent Kissat run for up to another
3600 seconds.

The final original partition leaf closes only when every terminal in the
complete eight-way refinement is exactly `UNSAT`. If that happens, the global
ledger advances from `675 / 676` to `676 / 676`, and all seven root boxes are
exactly excluded.

`UNKNOWN` never counts as exclusion. A `SAT` candidate must pass the independent
tournament/Pisa audit before it is recorded as a witness. All result JSON and
raw solver logs are uploaded as retained workflow artifacts.

## Local gates

- the inherited endpoint and all hashes were validated;
- the complete three-level tree passed its coverage audit;
- an all-`UNSAT` mock advanced the ledger to `676 / 676` and seven exact roots;
- an all-`UNKNOWN` mock preserved `675 / 676`, six exact roots, and eight open
  terminal children.

These mock tests validate coverage and bookkeeping, not the mathematical
outcome of the live solvers.
