# V24-F: complete publication certificate forest

V24-F upgrades the final solver-level `676 / 676` accounting into a
certificate-backed computation.

## Why there are 1124 certificates

The 676 original V23 partition leaves are not all terminal formulas in the
final computation:

- V23 closed 581 original leaves directly and left 95 `UNKNOWN`;
- V24-B replaced those 95 leaves by complete binary trees, producing 353
  exact solver terminals, three unit-closed terminals, and 23 open children;
- V24-C replaced the 23 open children, producing 177 exact solver terminals,
  two unit-closed terminals, and one open child;
- V24-D replaced that final child by eight exact solver terminals.

Consequently the complete terminal proof forest contains

```text
581 + 353 + 3 + 177 + 2 + 8 = 1124
```

UNSAT formulas.  Certifying only 675 historical source leaves would be
incorrect: an old `UNKNOWN` source leaf is excluded only by the complete
certified subtree that replaced it.

## Independent coverage reconstruction

The planner downloads immutable artifacts from these completed runs:

- V23: `30417759253`
- V24-B: `30490334948`
- V24-C: `30587970184`
- V24-D: `30602758451`

It checks the frozen source commits, ledger hashes, CNF hashes, task/result
cube hashes, exact historical solver statuses, all binary-tree polarities,
reachability of every refinement node, and exact replacement of every
historical `UNKNOWN`.

Every unit-propagation terminal is re-solved and receives the same proof
pipeline as the harder solver terminals.

## Certificate pipeline

For each terminal formula:

1. reconstruct the assumption CNF from the frozen theorem CNF and signed
   terminal cube;
2. require the precomputed formula SHA-256;
3. run the frozen CaDiCaL binary and emit binary DRAT;
4. validate DRAT with pinned `drat-trim` and derive LRAT;
5. validate LRAT with the separately compiled `lrat-check`;
6. compress both proofs and record raw and compressed SHA-256 hashes;
7. retain the checked LRAT payload as the durable publication certificate.

The DRAT proof is an intermediate witness used by `drat-trim`; its hashes,
sizes, command line, and successful checker receipt remain in the ledger.
The independently checked LRAT proof is split below GitHub's per-release-asset
limit and uploaded to a wave-specific GitHub Release.  Every release also
contains the frozen source/manifest bundle and one JSON receipt per terminal.
Actions artifacts retain only lightweight receipts and ledgers, avoiding both
a multi-gigabyte aggregation download and the much smaller Actions artifact
storage quota.

## Six balanced formal waves

The 1124 tasks are deterministically balanced into six waves using historical
solver time.  Each wave contains at most 188 jobs and has approximately the
same historical CPU total.  A pilot mode first tests eight representative
formulas from all refinement levels.

Run the pilot once, then dispatch formal waves `1` through `6`.  The six wave
ledgers share one deterministic `forest_sha256`.  A final ledger may claim
complete certificate coverage only when all six waves are present and their
1124 task identifiers are disjoint and exhaustive.  Each formal wave ledger
records its immutable workflow run ID and durable release tag.  The wave is
published only after the aggregator confirms that every receipt has its
declared LRAT parts and result JSON in that release.

## Claim boundary

Successful V24-F completion certifies every terminal UNSAT formula and the
stored binary refinement forest over all 676 original leaves.  The DRAT/LRAT
checkers certify the CNFs they receive; they do not by themselves prove that
the root CNF is a faithful encoding of primitive Pisa tournaments, nor that
the seven mathematical root boxes are exhaustive.  Those are separate
human-readable model and partition audits in the paper.
