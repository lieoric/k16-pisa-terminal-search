#!/usr/bin/env python3
"""Solve one exact v11 cube with ordinary CaDiCaL and verify any witness."""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

from pysat.formula import CNF
from pysat.solvers import Solver

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from pisa_verify import verify


def arc_var(n: int, u: int, v: int) -> int:
    if u == v:
        raise ValueError("loops have no arc variable")
    return u * (n - 1) + v + 1 - (1 if v > u else 0)


def read_cube(path: Path, line_number: int) -> list[int]:
    lines = path.read_text(encoding="utf-8").splitlines()
    if not 1 <= line_number <= len(lines):
        raise ValueError(f"cube line {line_number} is outside 1..{len(lines)}")
    tokens = lines[line_number - 1].strip().lstrip("\ufeff").split()
    if not tokens or tokens[0] != "a" or tokens[-1] != "0":
        raise ValueError(f"line {line_number} is not an SMS cube")
    return [int(token) for token in tokens[1:-1]]


def model_to_masks(model: list[int], n: int) -> list[int]:
    positive = {lit for lit in model if lit > 0}
    out = [0] * n
    for u in range(n):
        for v in range(n):
            if u != v and arc_var(n, u, v) in positive:
                out[u] |= 1 << v
    return out


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cnf", type=Path, required=True)
    parser.add_argument("--cube-file", type=Path, required=True)
    parser.add_argument("--cube-line", type=int, required=True)
    parser.add_argument("--n", type=int, default=16)
    parser.add_argument("--solver", default="cadical195")
    parser.add_argument(
        "--model-version",
        default="k16-pisa-v11-canonical-cube-cadical-20260727",
    )
    parser.add_argument("--result", type=Path, required=True)
    args = parser.parse_args()

    assumptions = read_cube(args.cube_file, args.cube_line)
    formula = CNF(from_file=args.cnf)
    started = time.perf_counter()
    with Solver(name=args.solver, bootstrap_with=formula.clauses) as solver:
        sat = solver.solve(assumptions=assumptions)
        record: dict[str, object] = {
            "model_version": args.model_version,
            "status": "SAT" if sat else "UNSAT",
            "solver": args.solver,
            "seconds": round(time.perf_counter() - started, 3),
            "n": args.n,
            "cube_line": args.cube_line,
            "cube_literals": len(assumptions),
            "variables": formula.nv,
            "clauses": len(formula.clauses),
        }
        if sat:
            check = verify(model_to_masks(solver.get_model(), args.n))
            if not check["is_pisa"]:
                raise RuntimeError("cube SAT model failed independent verification")
            record["verified"] = True
            record["witness"] = check

    args.result.parent.mkdir(parents=True, exist_ok=True)
    args.result.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(record, indent=2), flush=True)


if __name__ == "__main__":
    main()
