# V24-C: the last 23 V24-B children

V24-C resumes only the terminal `UNKNOWN` frontier from completed V24-B run
`30490334948`.

## Baseline

- exact original partition leaves: `656 / 676`
- open V23 source leaves: `20`
- open V24-B child leaves: `23`
- roots already excluded: `a1_z2`, `a2p_z2`, `a2p_z3`
- verified SAT witnesses: `0`

The planner verifies the V24-B ledger, its source manifest, solver hashes,
theorem-CNF hashes, signed child cubes, and the final solver status of every
one of the 23 inherited children.

## Complete refinement

Each inherited child is replaced by a complete three-level adaptive MOMS
tree. Both signs of every decision are retained. On the pinned inputs:

- source V24-B children: `23`
- source V23 leaves represented: `20`
- unit-closed terminals: `2`
- queued solver children: `178`
- group 1 (`a0_z2`, `a1_z4p`): `16`
- group 2 (`a0_z3`): `58`
- group 3 (`a0_z4p`): `104`

The groups receive `2 + 7 + 11` standard Ubuntu runners. This biases the
runner budget toward the largest and hardest `a0_z4p` frontier.

## Solver and accounting semantics

Every surviving child receives CaDiCaL for up to 3600 seconds. Only CaDiCaL
`UNKNOWN` children advance to Kissat for another 3600 seconds.

A V24-B child closes only when every terminal in its complete refinement is
exactly `UNSAT`. A V23 source leaf closes only when all of its formerly open
V24-B children close. The global count advances from 656 only by newly closed
V23 source leaves.

`UNKNOWN` never counts as exclusion. A `SAT` candidate must pass the
independent tournament/Pisa audit before it is recorded as a witness.

## Local gates

- all 23 coverage trees passed;
- an all-`UNSAT` mock closed 23/23 V24-B children, 20/20 V23 leaves, and
  676/676 global partition leaves;
- an all-`UNKNOWN` mock preserved the exact 656/676 baseline and all three
  previously excluded roots.

The mock tests validate accounting and coverage, not the mathematical solver
outcome.
