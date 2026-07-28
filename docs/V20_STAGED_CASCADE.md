# V20 staged exact cascade

V19 showed that a static, SMS-enriched CNF solved with CaDiCaL closes more
complete hard leaves per CPU hour than either unsplit SMS or four-way
120-second SMS splitting.

The observed CaDiCaL completion curve was:

| ceiling | exact closures in the 24-leaf pilot |
| ---: | ---: |
| 300 seconds | 6 |
| 600 seconds | 9 |
| 720 seconds | 10 |
| 900 seconds | 10 |

V20 therefore uses 720 seconds as the primary ceiling.  A solver that proves
SAT or UNSAT earlier exits immediately; the ceiling is consumed only by an
inconclusive leaf.

## Exact staged coverage

1. Start from the 139 V18 `UNKNOWN` queue leaves.
2. Remove the 13 leaves closed exactly by the complete V19 ledger.
3. Run CaDiCaL 3.0.1 for at most 720 seconds on each remaining leaf.
4. Create the SMS matrix from CaDiCaL `UNKNOWN` records only.
5. Run SMS for at most 900 seconds on those leaves.
6. Publish the union of prior, CaDiCaL, and SMS `UNSAT` leaves.

No SAT or UNSAT leaf is submitted to the later SMS stage.  Green Actions jobs
are infrastructure results, not mathematical exclusions.  Only a signed
solver-level `UNSAT` record closes a leaf.  Every SAT candidate must pass the
standalone zero-shared-code primitive K16 Pisa verifier.

## Resume semantics

The final `v20-cascade-ledger` artifact contains `closed_queue_ids` and
`open_queue_ids`.  A later workflow dispatch may provide the completed V20
run ID as `resume_run_id`; planning then removes every prior exact closure
before constructing a new CaDiCaL matrix.

This is campaign-level continuation.  It preserves the exact combinatorial
frontier, but does not serialize CaDiCaL's in-memory learned-clause state.
