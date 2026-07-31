# V22 two-front primitive K16 campaign

V22 separates two incomparable pieces of the remaining primitive search.

## Front A: refine the 35 signed V21 UNKNOWN leaves

The final V21 ledger contains 104 permanent closures and 35 logical
`UNKNOWN` leaves inside `a1_z3` and `a2p_z4p`.  No closed leaf is submitted
again.

Every open parent is replaced by an exact adaptive binary decision tree over
directed-arc variables.  MOMS is evaluated after unit propagation at each
internal node, but both signs of the chosen variable are retained:

| Parent depth | Extra decisions | Maximum children |
|---:|---:|---:|
| `<= 6` | 3 | 8 |
| `7` | 2 | 4 |
| `>= 8` | 1 | 2 |

For the V21 ledger this gives exactly 102 surviving child tasks before any
new unit contradiction.  Each child receives 60 minutes of CaDiCaL.  Only
CaDiCaL `UNKNOWN` children receive the 90-minute SMS fallback.

The final ledger reports both child-level closures and parent-level closure.
A V21 parent closes only when every terminal child is exact `UNSAT`.

## Front B: map the seven unopened semantic roots

The complete primitive search has nine disjoint root boxes.  V17--V21
deepened only `a1_z3` and `a2p_z4p`.  The atlas targets:

- `a0_z2`, `a0_z3`, `a0_z4p`;
- `a1_z2`, `a1_z4p`;
- `a2p_z2`, `a2p_z3`.

For each root, SMS first learns symmetry clauses from the audited,
theorem-strengthened CNF.  The propagation-balanced directed-arc lookahead
cuber then emits a complete partition.  A separate coverage query must prove
that blocking all emitted cubes is `UNSAT`.

The first atlas pass selects 24 stratified leaves per complete partition,
at most 168 jobs.  Each selected leaf receives 30 minutes of CaDiCaL and,
only on `UNKNOWN`, 60 minutes of SMS.  Unselected leaves are explicitly
retained as open.  A sampled closure is never promoted to a whole-root
conclusion.

## Soundness and resume rules

- The historical primitive encoding, full primitivity clauses, two-zero
  theorem, and V21 lossless theorem cuts are retained.
- No empirical blocker bound, weighted H--T extension, or speculative
  zero-class cut is used.
- `SAT` is accepted only after the independent primitive K16 verifier.
- `UNSAT` closes only the signed leaf that was solved.
- `UNKNOWN`, timeout, a green Actions job, and an unselected partition leaf
  are never exclusions.
- Both workflows publish hash-addressed resumable ledgers.

The two workflows intentionally use 8 and 12 concurrent workers,
respectively, so the current hard frontier continues shrinking while the
seven previously uncharted roots are mapped.
