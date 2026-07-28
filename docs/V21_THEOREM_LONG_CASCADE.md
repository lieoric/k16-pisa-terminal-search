# V21 theorem-cut long cascade

V21 resumes the completed V20 ledger rather than reconstructing or
resubmitting its search frontier.

## Exact input

- V20 signed frontier: 139 leaves.
- Permanent V20 closures: 58.
- Logical V20 `UNKNOWN`: 81.

The planner checks that these sets are disjoint and exhaustive.  Only the 81
open identifiers can enter V21.

## New lossless cuts

The historical v17/v18 base CNF is regenerated and checked against its
recorded SHA-256 hash before any clause is merged.  This guarantees that all
historical auxiliary-variable numbers, and especially the 240 arc-variable
prefix used by the signed cubes, still have their original meanings.

V21 then appends:

1. at least three kings in a strong tournament;
2. `king(v) iff b(v)=0`;
3. transitivity of the blocker/cover relation;
4. the primitive blocker degree gap `d+(x) >= d+(v)+2`;
5. strict blocker-count descent `b(v) >= b(x)+1`;
6. the K16 specialization that the unique blocker of a degree-seven
   zero-margin vertex is a king.

No empirical zero-class cut, speculative total-blocker lower bound, or
weighted H--T extension is used.

The theorem encoding is exhaustively compared with the independent
mathematical predicate on every labelled tournament of orders 5 and 6.

## Progressive exact filter

The planner first tests every signed V20-open cube by unit propagation under
the theorem CNF.  A contradiction is a permanent closure.  Every survivor
then receives a size-aware CaDiCaL budget:

| Cube depth | CaDiCaL | SMS fallback |
|---|---:|---:|
| `<= 6` | 60 minutes | 120 minutes |
| `7` | 45 minutes | 90 minutes |
| `>= 8` | 30 minutes | 60 minutes |

CaDiCaL `UNKNOWN` leaves alone enter the longer SMS matrix.  Both solvers
stop early on SAT or UNSAT.

## Result semantics

- `SAT`: accepted only after the standalone primitive K16 Pisa verifier.
- `UNSAT`: solver-level exact closure of that signed leaf.
- `UNKNOWN`: remains open and is preserved in the final resumable ledger.

The workflow never converts timeout, process success, or a green Actions job
into a mathematical exclusion.
