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
