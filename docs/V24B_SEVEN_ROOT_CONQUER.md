# V24-B: exact cleanup of the seven V23 roots

V24-B resumes from the completed V23 seven-root ledger. It does not rerun any
of the 581 partition leaves that V23 already closed exactly.

## Immutable baseline

- V22 atlas run: `30392007070`
- V23 cleanup run: `30417759253`
- audited solver binaries: V24-A run `30471531642`
- total V23 partition leaves: `676`
- exact V23 closures: `581`
- V23 `UNKNOWN` leaves: `95`

The planner reconstructs the final V23 status of every leaf from the prior,
CaDiCaL, and SMS records. It then verifies every signed cube against the
original complete V22 lookahead partition and checks the CNF, cube-file,
manifest, and solver hashes.

## Complete refinement

Every one of the 95 `UNKNOWN` source leaves is replaced by a complete
two-level binary MOMS tree:

- both polarities are retained at every internal decision;
- unit propagation may close a child exactly;
- every surviving child becomes one solver job;
- each tree receives a structural coverage audit.

On the pinned inputs, this produces:

- 95 source trees;
- 4 unit-closed child branches;
- 376 solver children;
- group 1: 104 children;
- group 2: 150 children;
- group 3: 122 children.

The three groups share 20 standard Ubuntu runners (`7 + 7 + 6`).
Group-specific source artifacts avoid downloading all seven CNFs into every
job.

## Solver cascade

1. CaDiCaL receives every surviving signed child for up to 3600 seconds.
2. Exact CaDiCaL `UNSAT` results are permanently closed.
3. A verified CaDiCaL `SAT` candidate is independently audited as a
   tournament and Pisa witness.
4. Only CaDiCaL `UNKNOWN` children advance to the independently implemented
   Kissat lane for another 3600 seconds.
5. Kissat `UNKNOWN` remains open.

Every child job uploads its JSON result and raw logs. Artifact upload has a
retry path because missing result artifacts would otherwise make exact
aggregation impossible.

## Ledger semantics

The final `v24b-ledger` artifact distinguishes three outcomes:

- `V24B_VERIFIED_SAT`: at least one candidate passed the independent audit;
- `V24B_SEVEN_ROOTS_EXACTLY_CLOSED`: all 676 V23 partition leaves are now
  exact, so all seven roots are excluded;
- `V24B_CUBE_CONQUER_COMPLETE_K16_OPEN`: at least one child remains
  `UNKNOWN`.

An `UNKNOWN` result is never counted as exclusion. The ledger records the
remaining signed child cubes so a later campaign can resume only the open
frontier.

## Local validation

Before publication, the planner was run on the pinned artifacts and all 95
coverage trees passed. Two adversarial aggregate tests were also run:

- all 376 solver children mocked as `UNSAT` produced 676/676 exact closures
  and seven closed roots;
- all children mocked as `UNKNOWN` preserved the 581/676 V23 baseline and all
  376 open child cubes.

These tests validate the accounting and partition semantics; they are not
mathematical solver results.
