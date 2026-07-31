# V24-A: exact refinement of the V22 open frontier

V24-A is independent of the still-running V23 seven-root cleanup.  Its only
mathematical input is the immutable final ledger and signed CNFs from V22 run
`30392007056`.

## Exact scope

V22 left 19 logical `UNKNOWN` child leaves belonging to 16 of the original
139 parent regions.  V24-A refines exactly these 19 leaves.  It does not
resubmit any of the 123 parent regions already closed by V22.

Each open leaf is replaced by a complete three-level adaptive MOMS tree:

```text
one V22 UNKNOWN leaf
        |
        +-- three complementary directed-arc decisions
        |
        +-- at most eight V24-A children
```

Both signs of every selected variable are retained.  A unit-inconsistent
terminal is an exact closure.  Every other terminal is queued.  The planner
audits reachability of every node, both children of every branch, and the
root hash before uploading the plan.

## Solver portfolio

1. Every surviving child receives up to 60 minutes of CaDiCaL.
2. Only CaDiCaL `UNKNOWN` children receive up to 60 minutes of Kissat.
3. A SAT candidate is accepted only after the independent primitive K16
   verifier succeeds.
4. An `UNSAT` result closes only the named signed child.
5. `UNKNOWN` remains open and is written to the final resumable ledger.

The two CDCL implementations deliberately provide different branching and
inprocessing behavior.  SMS is not used indiscriminately on these already
deep, symmetry-poor leaves.

## Workflow modes

The workflow `.github/workflows/v24a-v22-cube-conquer.yml` has two modes.

- `smoke` builds the pinned Kissat binary, validates the V22 provenance,
  constructs and audits all 19 trees, checks both solver binaries, and runs
  each solver for ten seconds on one identical signed child.
- `formal` launches the complete CaDiCaL matrix with 20-way concurrency,
  selects only logical `UNKNOWN` children for the Kissat matrix, and publishes
  `v24a-ledger.json`.

The smoke status may be `UNKNOWN`; its purpose is environment and provenance
validation.  Only the formal ledger changes the mathematical exclusion map.
