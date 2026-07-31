# V18 exact smart deepening

V18 continues the two complete SMS lookahead partitions produced by
[run 30330960933](https://github.com/lieoric/k16-pisa-terminal-search/actions/runs/30330960933).
It does not rebuild the roots and does not spend time on any leaf that V17.1
already proved UNSAT.

## Exact coverage

The two target roots contain 239 mutually exclusive parent leaves:

- 17 V17.1 leaves are exact SMS `UNSAT` and stay permanently closed;
- 207 leaves were not sampled by the pilot and are queued unchanged;
- 15 pilot `UNKNOWN` leaves are each replaced by the complementary pair
  `C+x` and `C-x`.

Thus V18 queues `207 + 2*15 = 237` jobs. The planner verifies all source
hashes, the original partition-coverage certificates, the prior signed
ledger, and every complementary split before emitting the matrix.

## Branch choice

For every prior `UNKNOWN` parent, V18 unit-propagates the parent decisions
through the SMS-enriched CNF. It then applies a deterministic MOMS score to
unassigned directed-arc variables occurring in the shortest relevant
residual clauses. Both polarities are queued, so the heuristic changes
search order but cannot remove a solution.

## Result semantics

- `UNSAT` permanently closes exactly that queue leaf.
- `UNKNOWN` remains open and is eligible for another split.
- `SAT` is reported only after `verify_primitive_witness.py` independently
  recomputes the tournament, strong connectivity, Pisa margins, root-box
  membership, and primitivity.
- Missing or failed jobs are recorded as infrastructure failures rather than
  mathematical exclusions.

The aggregate artifact contains parent-level coverage, not merely green/red
GitHub job status. A split parent closes only when both complementary
children are exact `UNSAT`.

## Runtime

There are 237 independent jobs, at most 20 in parallel, with a default exact
SMS budget of 300 seconds per leaf. If most hard leaves use their full
budget, the conquer phase should take roughly one hour plus runner queue and
artifact overhead.
