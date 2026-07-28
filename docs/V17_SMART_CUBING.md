# v17 SMS-aware adaptive cube-and-conquer

The v16 full-S16 campaign gave every semantic root box one uninterrupted
five-hour SMS call.  That is useful as a baseline, but an `UNKNOWN` call
leaves no reusable closed subproblem.  v17 replaces the monolithic call with
an accumulating cube ledger.

The design follows *Smart Cubing for Graph Search: A Comparative Study*
(Kirchweger, Xia, Peitl, and Szeider, arXiv:2501.17201).  In particular, it
does **not** cube the raw labelled-graph CNF before SMS has learned any
symmetry information.

## Pilot roots

The first workflow compares two representative full-S16 roots:

- `a1_z3`;
- `a2p_z4p`.

The existing nine `(a,z)` boxes remain the disjoint and exhaustive root
partition.  No result from the cancelled v16 run is counted as an exclusion.

## Pipeline

For each pilot root:

1. SMS runs for 600 seconds.
2. The solver writes a simplified CNF containing all remaining irredundant
   clauses, derived units, and learned clauses of length at most five.
3. Two cubers operate on that enriched formula:
   - propagation-balanced SMS lookahead restricted to directed-arc variables;
   - the SMS CDCL edge-assignment cutoff.
4. Each emitted cube is a conjunction of directed-arc literals.
5. A separate coverage query blocks every emitted cube.  Only an exact
   `UNSAT` result marks that partition coverage as independently checked.
6. Sixteen stratified leaves from each complete generated partition are
   conquered with SMS still enabled for 300 seconds.

The SMS patch in `patches/sms-v17-smart-cubing.patch` changes no mathematical
constraint.  It:

- measures an edge-only lookahead cutoff in the edge-variable space rather
  than counting inactive auxiliary variables;
- prints the exact result of a cube-assumption call so SAT, UNSAT, and timeout
  cannot be confused.

## Ledger semantics

- verified `SAT`: a candidate exists and has passed the zero-shared-code Pisa
  and primitivity audit;
- `UNSAT`: only the named cube is permanently closed;
- `UNKNOWN`: the cube remains open and must be split into two children;
- a green GitHub job is an execution result, not by itself a mathematical
  exclusion.

Every leaf records the hashes of the enriched CNF, parent cube file, and its
own assumptions.  A later recursive workflow will replace an open cube `C`
by the exact binary cover

`(C and x) or (C and not x)`.

Completed siblings are never searched again.

## Running the pilot

Use the workflow **K16 v17 SMS-aware smart-cubing pilot**.  Its defaults are:

- 600 seconds root prerun;
- directed-arc cutoff 32;
- 16 stratified leaves per root and strategy;
- 300 seconds conquer time per leaf.

The final `v17-smart-cubing-pilot-ledger` artifact compares closure rates and
selects the cuber for the recursive production campaign.  The pilot never
claims the whole primitive K16 case is closed.
