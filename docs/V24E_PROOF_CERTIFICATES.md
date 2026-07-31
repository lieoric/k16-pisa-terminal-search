# V24-E: independently checked proof certificates

V24-E freezes the exact V24-D endpoint from run `30602758451` and replaces
the eight solver-return-code claims with independently checked clausal proofs.

## Frozen source

- V24-D source commit:
  `7e639de2d6b68ec903e375c8f05dfa593b89f5d2`
- V24-D final ledger: `676 / 676` partition leaves, seven exact root boxes,
  zero open leaves, and zero SAT witnesses
- V24-D child paths: `000`, `001`, `010`, `011`, `100`, `101`, `110`, `111`
- DRAT-trim source commit:
  `2e3b2dc0ecf938addbd779d42877b6ed69d9a985`

The planner rechecks the V24-D source manifest, final ledger, all eight
original result JSON files, solver return codes, signed cubes, coverage tree,
theorem CNF hash, and solver hash. It then materializes the eight exact
assumption CNFs and records their SHA-256 hashes.

## Certificate chain

Each formula runs independently on a standard Ubuntu runner:

1. the frozen CaDiCaL binary emits a binary DRAT proof;
2. the pinned `drat-trim` binary checks the DRAT proof and emits LRAT;
3. the separately compiled `lrat-check` binary checks the LRAT proof;
4. the CNF, binaries, raw proofs, compressed proofs, logs, and result record
   are bound by SHA-256 in the final certificate ledger.

Both DRAT and LRAT proofs are compressed with Zstandard after successful
checking. Each leaf has a 355-minute job limit. The historically fastest leaf,
`d05`, runs first as a real-formula size and format pilot; after it succeeds,
the other seven leaves run in parallel.

The official CaDiCaL command line accepts `cadical input.cnf proof` and writes
a DRAT proof. DRAT-trim accepts a DIMACS formula and DRAT proof and validates
that the proof establishes unsatisfiability.

## Claim boundary

Successful V24-E completion independently certifies the eight children that
close the final V24-D partition leaf. It does **not** retroactively create
proof certificates for the 675 leaves closed by earlier campaigns.

Thus the outputs support two distinct statements:

- the complete computation has a solver-level audited ledger of `676 / 676`;
- the final formerly open leaf has a double-checked DRAT/LRAT certificate
  bundle.

A wholly certificate-backed publication artifact still requires regenerating
and checking certificates for the 675 earlier closures, or producing an
equivalent monolithic proof.
