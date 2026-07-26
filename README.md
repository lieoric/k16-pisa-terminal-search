# K16 Pisa tournament terminal search

## Current two-platform campaign (v6/v8)

The two platforms deliberately do different work:

- **GitHub Actions v6** is the exact proof track. It refines precisely the
  43 v5 endpoint boxes that remained `UNKNOWN` into 54 disjoint
  anchor-orbit boxes (36 in the `(d,b)=(7,1)` branch and 18 in the
  `(6,3)` branch). Every job uploads `result.json` and `run.log`.
  `INFEASIBLE` closes only the named box; `UNKNOWN` closes nothing.
- **Kaggle GPU v8** is witness-only. Its 54 targets are structurally
  different endpoint strata, and its main move is a pure directed
  3-cycle reversal, which explores a fixed score sequence without first
  destroying it. A hit is independently verified; a miss is never reported
  as an UNSAT result.

Run the short GitHub workflow `K16 Pisa v6 rooted-role smoke` before
dispatching `K16 Pisa v6 exact remaining endpoint matrix`.

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

## v9 Kaggle elite-repair evidence (revised)

Kaggle version
[`338131697`](https://www.kaggle.com/code/chamine/k16-pisa-v9-elite-exact-repair?scriptVersionId=338131697)
loaded all 54 one-offender near-witnesses from the v8 GPU campaign.  Its
positive K14 gate returned a verified `SAT`.  The run was later cancelled
during the outermost shell wave, so it is **partial evidence**, not a global
K16 decision.

The exact completed closures are:

- all 54 labelled Hamming shells at distance `1..2` from their canonical
  elite centre are `UNSAT`;
- all 54 labelled Hamming shells at distance `3..4` are `UNSAT`;
- all 54 complete labelled score-vector fibres are `UNSAT`;
- the distance `5..6` shells are `UNSAT` only for source shards
  `0, 7, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 23`.

For distance `5..6`, shards `1, 2, 3, 4, 5, 6, 8, 9, 12` timed out and remain
`UNKNOWN`; shards `21, 22, 24..53` were not reached before cancellation.
Those 41 shells remain open.

These are labelled neighbourhood statements after the zero-role
canonicalisation used by `scripts/v8_elite_exact_repair.py`.  They do not
close an entire endpoint branch, an isomorphism-orbit Hamming ball, or K16
itself.  A machine-readable transcription of the completed log is stored in
`evidence/v9-kaggle-338131697.json`.

## v7.1 local-median-order exact campaign

The v7.1 campaign is an independent exact formulation based on Havet and
Thomasse's local median orders.  We may relabel a local median order as

```text
1, 2, ..., 15, 0
```

because its feed vertex has a large second neighbourhood and therefore has
margin zero in every Pisa tournament.  The model adds the feedback property
on every interval.  These constraints also give a directed Hamiltonian path,
so exact strong connectivity needs only one reverse arc across each of the
15 proper prefix cuts; the score-permutation and rooted-role encodings are
not used.

The completed v6 run closed 21 of its 54 orbit boxes. Five of those closures
remove the whole `B=14,15` layers; the remaining 16 are translated into
label-invariant blocker-degree and blocker-pattern nogoods. Consequently v7.1
searches only the union represented by the 33 v6 `UNKNOWN` artifacts.

The smoke workflow validates fixed K12 and K14 Pisa witnesses under this
encoding, then samples the resumable cube machinery. The formal workflow
splits every remaining parent layer by the three feed edges `(0,1)`, `(0,2)`,
and `(0,3)`. The resulting eight mutually exclusive cubes cover each parent
layer exactly, giving 48 jobs in total:

```text
(d,b)=(7,1), B=16,17,18,19,>=20
(d,b)=(6,3), B>=20
```

Each `UNSAT` cube is permanently closed and never needs to run again.
An `UNKNOWN` cube can be split further by additional fixed edges without
restarting the completed cubes. All eight `UNSAT` results close the named
parent layer. `SAT` is accepted only after the independent bit-mask verifier
confirms the K16 witness.

Primary reference:
[Havet and Thomasse, Median Orders of Tournaments](https://www.math.ru.nl/OpenGraphProblems/TimV/%5BHavet%20and%20Thomass%C3%A9%5D%20Median%20Orders%20of%20Tournaments.pdf).

## v10 invariant refinement

Run `30208791250` completed all 48 v7.1 cubes: 18 were `UNSAT` and 30
remained `UNKNOWN`.  v10 compiles the 18 exact closures into compact cuts,
then repartitions the complete residual by blocker invariants rather than by
more arbitrary labelled edges.

For a `(d,b)=(7,1)` feed, v10 fixes the degree of the unique blocker.  After
the completed v6 blocker-degree closures, the five total-blocker layers
produce 26 mutually exclusive boxes.  For `(d,b)=(6,3), B>=20`, v10 fixes
the minimum degree among the three blockers, giving another eight boxes.
The resulting 34 boxes are disjoint and exactly cover the 30 open v7.1
cubes.  The coverage gate checks this identity before any solver job starts.

The smoke workflow samples all 34 models for five seconds.  The formal
workflow gives each invariant box a continuous one-hour budget and stores
the complete JSON/log artifact.  An `UNKNOWN` box is not rerun unchanged:
the next refinement will split only that box by a second invariant.

## v12 hybrid symmetry/endpoint benchmark

The v11 SMS benchmark deliberately used only permutation-invariant base
constraints.  At cutoff 32 it produced 835 complete canonical cubes, but 15
of 16 sampled cubes remained `UNKNOWN` after 120 seconds.  v12 keeps the same
unlabelled SMS search and adds the exact global endpoint closure already
certified by the v5/v6 campaigns:

```text
some zero-margin vertex has d=7 and B>=16,
or
some zero-margin vertex has d=6 and B>=20.
```

The selected endpoint is existentially quantified over all 16 vertices.  No
vertex number, local median order, or template is fixed, so the projected
formula remains invariant under every vertex permutation and SMS canonical
partitioning remains sound.  Previously closed profiles and low-blocker
layers are thereby removed before cubing instead of being rediscovered by
each residual solver.

Run the short CPU benchmark with:

```bash
python scripts/kaggle_v12_hybrid_benchmark.py
```

It performs closure-free K8/K14/K15 correctness gates, builds the baseline and
hybrid K16 formulas, obtains complete SMS partitions at cutoffs
`32,40,48,56,64`, and solves eight stratified cubes from every complete
partition for 30 seconds each.  `SAT` is accepted only after the standalone
bit-mask verifier succeeds; timeout is recorded as `UNKNOWN`.  Results are
written to `/kaggle/working/k16-v12-results/v12-hybrid-summary.json`.

Kaggle version
[`338154164`](https://www.kaggle.com/code/chamine/k16-pisa-v12-hybrid-sms-endpoint?scriptVersionId=338154164)
completed in about 9.2 minutes.  All four gates passed.  The complete
partitions contained 476, 1023, 4194, 9634, and 9788 cubes respectively.  In
particular the endpoint closures reduced the cutoff-32 partition from the v11
count of 835 cubes to 476.  Cutoff 64 performed best in the short sample:
two of eight cubes were `UNSAT` in 0.654 and 3.968 seconds, while six timed
out after 30 seconds.  This selects cutoff 64 for adaptive refinement, but it
is not a K16 decision; every sampled `UNKNOWN` region remains open.  The
machine-readable transcription is
`evidence/v12-kaggle-338154164.json`.

## v13 adaptive refinement

v13 continues only the six cutoff-64 sample parents that v12 left
`UNKNOWN`: cube lines `1,1399,2797,4195,5594,6992`.  It does not rerun cube
lines `8390` and `9788`, which v12 already proved `UNSAT`.

For each open parent, `scripts/adaptive_split_v13.py` selects still-unassigned
unordered tournament edges and enumerates every orientation pattern on those
edges.  The children are therefore disjoint and exhaustive inside their
parent; they are not repeated random seeds for the same formula.  A parent is
closed only if every child is proved `UNSAT`.  `SAT` is accepted only after
the independent bit-mask verifier succeeds, and every timeout remains
`UNKNOWN`.

The GitHub pilot uses depth four, hence 16 children for each of six parents
(96 children total), with one matrix job per parent.  The Kaggle CPU pilot
uses depth six, hence 64 children per parent (384 total):

```bash
python scripts/kaggle_v13_adaptive_pilot.py
```

Both routes rebuild and validate the same complete 9,788-cube SMS partition
before refinement, and preserve JSON/log artifacts for every result.
