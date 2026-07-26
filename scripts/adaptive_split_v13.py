#!/usr/bin/env python3
"""Exactly split SMS parent cubes and solve every selected child.

Each parent cube is refined by the first ``split_depth`` still-unassigned
unordered tournament edges.  The 2^depth sign patterns are mutually exclusive
and exhaustive inside that parent.  A parent is marked CLOSED only when every
child is proved UNSAT.  Timeout is UNKNOWN and closes nothing.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

from pysat.formula import CNF
from pysat.solvers import Solver

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from pisa_verify import verify


MODEL_VERSION = "k16-pisa-v13-adaptive-canonical-refinement-20260727"


def arc_var(n: int, u: int, v: int) -> int:
    if u == v:
        raise ValueError("loops have no arc variable")
    return u * (n - 1) + v + 1 - (1 if v > u else 0)


def read_cube(path: Path, line_number: int) -> list[int]:
    lines = path.read_text(encoding="utf-8").splitlines()
    if not 1 <= line_number <= len(lines):
        raise ValueError(
            f"cube line {line_number} is outside 1..{len(lines)}"
        )
    tokens = lines[line_number - 1].strip().lstrip("\ufeff").split()
    if not tokens or tokens[0] != "a" or tokens[-1] != "0":
        raise ValueError(f"line {line_number} is not an SMS cube")
    return [int(token) for token in tokens[1:-1]]


def choose_split_variables(
    parent: list[int],
    n: int,
    depth: int,
) -> list[int]:
    assigned = {abs(literal) for literal in parent}
    candidates = []
    for u in range(n):
        for v in range(u + 1, n):
            uv = arc_var(n, u, v)
            vu = arc_var(n, v, u)
            if uv not in assigned and vu not in assigned:
                candidates.append(uv)
    if len(candidates) < depth:
        raise ValueError(
            f"parent has only {len(candidates)} free unordered edges; "
            f"cannot split to depth {depth}"
        )
    return candidates[:depth]


def model_to_masks(model: list[int], n: int) -> list[int]:
    positive = {literal for literal in model if literal > 0}
    out = [0] * n
    for u in range(n):
        for v in range(n):
            if u != v and arc_var(n, u, v) in positive:
                out[u] |= 1 << v
    return out


def solve_one(cnf_path: Path, assumptions: list[int], n: int) -> dict:
    formula = CNF(from_file=cnf_path)
    started = time.perf_counter()
    with Solver(
        name="cadical195",
        bootstrap_with=formula.clauses,
    ) as solver:
        sat = solver.solve(assumptions=assumptions)
        record: dict[str, object] = {
            "model_version": MODEL_VERSION,
            "status": "SAT" if sat else "UNSAT",
            "solver": "cadical195",
            "seconds": round(time.perf_counter() - started, 3),
            "assumption_literals": len(assumptions),
        }
        if sat:
            check = verify(model_to_masks(solver.get_model(), n))
            if not check["is_pisa"]:
                raise RuntimeError(
                    "adaptive child SAT model failed independent verification"
                )
            record["verified"] = True
            record["witness"] = check
        return record


def run_child_subprocess(
    script: Path,
    cnf_path: Path,
    assumptions: list[int],
    n: int,
    timeout_seconds: int,
    parent_line: int,
    pattern: int,
) -> dict:
    command = [
        sys.executable,
        str(script),
        "--solve-one",
        "--cnf",
        str(cnf_path),
        "--n",
        str(n),
        "--assumptions="
        + ",".join(str(literal) for literal in assumptions),
    ]
    started = time.perf_counter()
    try:
        completed = subprocess.run(
            command,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout_seconds,
            check=False,
        )
    except subprocess.TimeoutExpired:
        return {
            "model_version": MODEL_VERSION,
            "status": "UNKNOWN",
            "reason": "TIMEOUT",
            "seconds": timeout_seconds,
            "parent_line": parent_line,
            "pattern": pattern,
        }

    elapsed = time.perf_counter() - started
    if completed.returncode != 0:
        return {
            "model_version": MODEL_VERSION,
            "status": "ERROR",
            "seconds": round(elapsed, 3),
            "parent_line": parent_line,
            "pattern": pattern,
            "returncode": completed.returncode,
            "tail": completed.stdout[-2000:],
        }
    try:
        record = json.loads(completed.stdout)
    except json.JSONDecodeError:
        return {
            "model_version": MODEL_VERSION,
            "status": "ERROR",
            "seconds": round(elapsed, 3),
            "parent_line": parent_line,
            "pattern": pattern,
            "reason": "child returned non-JSON output",
            "tail": completed.stdout[-2000:],
        }
    record["parent_line"] = parent_line
    record["pattern"] = pattern
    record["wall_seconds"] = round(elapsed, 3)
    return record


def child_assumptions(
    parent: list[int],
    split_variables: list[int],
    pattern: int,
) -> list[int]:
    refinements = [
        variable if (pattern >> index) & 1 else -variable
        for index, variable in enumerate(split_variables)
    ]
    return parent + refinements


def parse_int_list(value: str) -> list[int]:
    return [
        int(piece)
        for piece in value.split(",")
        if piece.strip()
    ]


def run_campaign(args: argparse.Namespace) -> dict:
    parent_lines = parse_int_list(args.parent_lines)
    if not parent_lines:
        raise ValueError("at least one parent line is required")

    parents = {
        line: read_cube(args.cube_file, line)
        for line in parent_lines
    }
    split_variables = {
        line: choose_split_variables(
            parents[line],
            args.n,
            args.split_depth,
        )
        for line in parent_lines
    }
    pattern_count = 1 << args.split_depth
    tasks = [
        (
            line,
            pattern,
            child_assumptions(
                parents[line],
                split_variables[line],
                pattern,
            ),
        )
        for line in parent_lines
        for pattern in range(pattern_count)
    ]

    script = Path(__file__).resolve()
    started = time.perf_counter()
    records = []
    with ThreadPoolExecutor(max_workers=args.workers) as executor:
        futures = {
            executor.submit(
                run_child_subprocess,
                script,
                args.cnf,
                assumptions,
                args.n,
                args.child_timeout,
                line,
                pattern,
            ): (line, pattern)
            for line, pattern, assumptions in tasks
        }
        for future in as_completed(futures):
            record = future.result()
            records.append(record)
            print(
                "child",
                record["parent_line"],
                record["pattern"],
                record["status"],
                record.get("seconds"),
                flush=True,
            )

    records.sort(
        key=lambda record: (
            int(record["parent_line"]),
            int(record["pattern"]),
        )
    )
    parent_summaries = []
    for line in parent_lines:
        children = [
            record
            for record in records
            if int(record["parent_line"]) == line
        ]
        counts = {
            status.lower(): sum(
                child["status"] == status
                for child in children
            )
            for status in ("SAT", "UNSAT", "UNKNOWN", "ERROR")
        }
        parent_summaries.append(
            {
                "parent_line": line,
                "parent_literals": len(parents[line]),
                "split_variables": split_variables[line],
                "split_depth": args.split_depth,
                "children_expected": pattern_count,
                "children_completed": len(children),
                "counts": counts,
                "parent_closed": (
                    len(children) == pattern_count
                    and counts["unsat"] == pattern_count
                ),
            }
        )

    summary = {
        "model_version": MODEL_VERSION,
        "status": (
            "SAT"
            if any(record["status"] == "SAT" for record in records)
            else "COMPLETE"
        ),
        "coverage": (
            "For each parent, every 2^split_depth orientation pattern on "
            "the selected free unordered edges is solved exactly once."
        ),
        "n": args.n,
        "parent_lines": parent_lines,
        "split_depth": args.split_depth,
        "child_timeout_seconds": args.child_timeout,
        "workers": args.workers,
        "parents": parent_summaries,
        "children": records,
        "wall_seconds": round(time.perf_counter() - started, 3),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(summary, indent=2) + "\n",
        encoding="utf-8",
    )
    if any(record["status"] == "ERROR" for record in records):
        raise RuntimeError("one or more adaptive child solvers errored")
    return summary


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--solve-one", action="store_true")
    parser.add_argument("--cnf", type=Path, required=True)
    parser.add_argument("--n", type=int, default=16)
    parser.add_argument("--assumptions")
    parser.add_argument("--cube-file", type=Path)
    parser.add_argument("--parent-lines")
    parser.add_argument("--split-depth", type=int, default=4)
    parser.add_argument("--child-timeout", type=int, default=30)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--output", type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.solve_one:
        if args.assumptions is None:
            raise SystemExit("--solve-one requires --assumptions")
        record = solve_one(
            args.cnf,
            parse_int_list(args.assumptions),
            args.n,
        )
        print(json.dumps(record), flush=True)
        return 0

    for required, value in (
        ("--cube-file", args.cube_file),
        ("--parent-lines", args.parent_lines),
        ("--output", args.output),
    ):
        if value is None:
            raise SystemExit(f"campaign mode requires {required}")
    if args.split_depth < 1:
        raise SystemExit("--split-depth must be positive")
    if args.workers < 1:
        raise SystemExit("--workers must be positive")

    summary = run_campaign(args)
    print(
        json.dumps(
            {
                "status": summary["status"],
                "parents": summary["parents"],
                "wall_seconds": summary["wall_seconds"],
                "output": str(args.output),
            },
            indent=2,
        ),
        flush=True,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
