# K16 Pisa tournament terminal search

This repository runs the K16 Pisa v4.1 CP-SAT terminal campaign as 18 independent
GitHub Actions jobs. Each job handles one zero-margin branch and one total-blocker
layer, writes a machine-readable JSON result, keeps the complete console log, and
uploads both as a workflow artifact.

## Logical scope

The terminal campaign depends on three previously established exclusions:

1. the proved near-regular twin-pair theorem excludes degree profile `7^8 8^8`;
2. the v3 Frontier THIN-A solver closure excludes `6^1 7^6 8^9`;
3. the v3 Frontier THIN-B solver closure excludes `7^9 8^6 9^1`.

The remaining space has total blocker count at least 10. A chosen zero-margin
vertex must have one of

```text
(d,b) = (7,1), (6,3), (5,5), (4,7), (3,9), (2,11).
```

Each branch is split into `sum(b)=10`, `sum(b)=11`, and `sum(b)>=12`, producing
18 boxes.

`SAT` is unconditional once the independent bit-mask verifier accepts the
witness. `UNSAT` closes exactly one named box. `UNKNOWN` closes nothing. A global
K16 nonexistence conclusion additionally requires all 18 boxes to be `UNSAT` and
the three dependencies above.

## Workflows

- **K16 Pisa smoke** runs three positive regression gates, then gives every box
  five seconds. It validates the Python environment, model construction, matrix
  wiring, JSON generation, logging, and artifact upload. `UNKNOWN` is expected
  and does not fail smoke jobs.
- **K16 Pisa formal 18-box matrix** runs all 18 boxes concurrently on
  `ubuntu-latest`. Exact layers receive 900 seconds by default. Residual layers
  receive two 1800-second seeds. A formal `UNKNOWN` is shown clearly and marks
  that matrix job incomplete while still uploading its evidence.

The three positive gates are:

- a fixed K12 Pisa witness through score sorting and zero-role pinning;
- a fixed near-regular K14 witness through the same score machinery;
- the positive quotient expansion `K7 -> K14`.

## Local use

```bash
python -m pip install -r requirements.txt
python k16_pisa_solver.py --gates-only --smoke
python k16_pisa_solver.py --box d7_b1_eq10 --smoke
python k16_pisa_solver.py --box d7_b1_eq10
```

List the valid box names with:

```bash
python k16_pisa_solver.py --help
```

No credentials or repository secrets are required by the workflows.

## Heuristic SAT witness campaign

The proof-oriented CP-SAT workflows above remain unchanged. The v7 witness
campaign searches only for one valid K16 Pisa orientation in the two unresolved
zero-margin branches `(d,b)=(7,1)` and `(6,3)`.

This campaign is deliberately one-sided:

- `WITNESS` means the candidate passed an independent bit-mask verifier and is
  an unconditional SAT certificate;
- `NO_WITNESS` means only that one timed heuristic partition did not find a
  witness; it is a successful job, not an UNSAT claim;
- each generated tournament contains the fixed directed Hamiltonian cycle
  `0->1->...->15->0`, which is a lossless relabelling for any strong witness;
- the 13 unfixed edges incident with zero encode its remaining out-neighbours;
  their colexicographic combination rank modulo 32 defines a structural bucket;
- shards `0..31` are the 32 disjoint `(7,1)` buckets and shards `32..63` are
  the 32 disjoint `(6,3)` buckets;
- zero-incident edges are immutable during a run, so candidates cannot cross
  buckets. The 64 logical solution spaces are mutually exclusive.

### GitHub Actions CPU search

`K16 Pisa v7 blocker-repair smoke` builds the native C++ searcher, proves that
the 32 buckets cover each branch without overlap, and samples eight partitions
from both branches. After it passes, manually dispatch
`K16 Pisa v7 CPU 64 blocker-repair partitions`. The full workflow runs 64 jobs with
`max-parallel: 20`:

```text
shard  0..31  d7_b1, bucket = shard
shard 32..63  d6_b3, bucket = shard - 32
```

Each four-thread job uses dynamic violated-vertex weights, targeted degree and
blocker-completion moves, a 32-state diversity pool, and exact radius-six local
repair when it reaches the one-offender margin-one plateau. Every job uploads
its JSON result, blocker-defect diagnostics, repair counts, an independent
partition/witness verification record, and the full log. The aggregate job
uploads a campaign summary. No secret is required.

### Kaggle GPU search

Import `kaggle/k16_pisa_gpu_hunter.ipynb` into Kaggle and select:

```text
Accelerator: GPU T4 x2
Internet: ON
```

GPU 0 searches the 32 `(7,1)` partitions while GPU 1 concurrently searches the
32 `(6,3)` partitions. The PyTorch/CUDA hunter evaluates thousands of
tournaments in parallel, writes one JSON per partition, and updates separate
checkpoints under `/kaggle/working/k16_gpu_results_v7`. Download that directory
before a Kaggle session expires. The notebook currently checks out branch
`agent/witness-hunter`; change `REF` to `main` after the pull request is merged.

## C16(1,7,8) carrier-completion campaign

The workflow `C16(1,7,8) carrier completion 11-box matrix` tests a separate
structure-led construction.  The sparse carrier is the ordered-pair blow-up of
a directed 8-cycle:

- pair `i` dominates pair `i-1` modulo 8;
- inside each pair, the high vertex dominates the low vertex;
- its underlying graph is exactly `C16(1,7,8)`;
- its degree profile is `2^8 3^8` and its margin profile is `0^8 (-1)^8`.

Module rotation leaves the carrier orientation fixed.  Therefore a zero-margin
vertex in any tournament completion can be moved to one of only two orbit
representatives.  The exact matrix covers:

```text
low orbit:  d = 2,3,4,5,6,7
high orbit: d =   3,4,5,6,7
```

These eleven boxes cover every completion of this fixed canonical carrier
orientation. `SAT` is an independently checked, unconditional K16 Pisa
witness. `UNSAT` closes the named completion box; all eleven `UNSAT` results
close this carrier-completion construction but do not prove that arbitrary K16
tournaments are impossible.

## v5 exact endgame project

The v5 workflow incorporates every exact closure obtained so far instead of
spending more time in already-dead layers.

The closed global regions are:

- every zero branch `(d,b)=(2,11),(3,9),(4,7),(5,5)`;
- `(d,b)=(6,3)` with total blocker count `B <= 14`;
- `(d,b)=(7,1)` with total blocker count `B <= 11`;
- the degree profiles `7^8 8^8`, `6^1 7^6 8^9`, and `7^9 8^6 9^1`.

Consequently the complete unresolved endpoint is exactly

```text
(d,b)=(7,1), B>=12
or
(d,b)=(6,3), B>=15.
```

`K16 Pisa v5 exact elite repair and global endpoint partition` attacks this
endpoint in two stages:

1. Recover all 64 best states from completed run `30190571931` and solve the
   complete radius-4 Hamming ball around every state with CP-SAT. This replaces
   the earlier partial repair kernel by an exact neighbourhood.
2. If no witness is found, partition the entire remaining global endpoint into
   111 disjoint boxes by total blocker count and the minimum degree among the
   selected zero point's blockers.

The second stage is exhaustive relative to the listed theorem and solver
closures. A SAT result is an unconditional independently verified K16 Pisa
witness. An UNSAT result closes exactly one named box; only all 111 UNSAT
results close the remaining global endpoint.
