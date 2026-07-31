# V19 hard-frontier strategy pilot

V18 left 139 signed `UNKNOWN` queue leaves. Blindly splitting all of them
would create 278 jobs and, at the observed hard-leaf closure rate, could make
the open frontier grow rather than shrink.

V19 therefore fixes a deterministic sample of 24 leaves:

- nine ordinary and three previously split UNKNOWN leaves from `a1_z3`;
- nine ordinary and three previously split UNKNOWN leaves from `a2p_z4p`.

Every method receives exactly those same 24 roots.

## Compared methods

### `sms900`

Run the patched SMS solver on the unsplit leaf for 900 seconds.

### `deep4_sms120`

Unit-propagate the leaf through the SMS-enriched CNF, apply deterministic
MOMS branching for two levels, and obtain an exact tree with at most four
consistent children. A child already contradicted by unit propagation is
closed immediately; run every remaining child with SMS for 120 seconds. The
parent is closed only if every terminal is either propagation-inconsistent
or solver-level `UNSAT`.

### `cadical900`

Append the leaf decisions as unit clauses to the SMS-enriched CNF and run
the official pinned
[CaDiCaL 3.0.1](https://github.com/arminbiere/cadical/releases/tag/rel-3.0.1)
for 900 seconds. This tests whether a lean static CDCL engine complements
SMS's dynamic canonical search.

## Decision rule

The aggregate ledger reports:

- complete parent closures;
- CPU hours consumed;
- closures per CPU hour;
- SAT, UNSAT, UNKNOWN, and missing results separately.

The recommended method is the complete method with the highest exact parent
closures per CPU hour. Green GitHub jobs are not counted as exclusions.
UNKNOWN remains open.

Any SAT candidate, from either SMS or CaDiCaL, must pass the standalone
zero-shared-code primitive K16 Pisa verifier before it is reported.
