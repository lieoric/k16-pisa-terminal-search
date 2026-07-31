#!/usr/bin/env python3
"""Manage exact SMS cube queues without treating timeouts as exclusions."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def read_cubes(path: Path) -> list[tuple[int, str]]:
    cubes: list[tuple[int, str]] = []
    for line_number, raw in enumerate(
        path.read_text(encoding="utf-8").splitlines(),
        start=1,
    ):
        line = raw.strip().lstrip("\ufeff")
        if line.startswith("a ") and line.endswith(" 0"):
            cubes.append((line_number, line))
    return cubes


def write_matrix(cubes: list[tuple[int, str]], path: Path) -> None:
    payload = {
        "include": [
            {"cube_line": line_number, "cube": cube}
            for line_number, cube in cubes
        ]
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, separators=(",", ":")) + "\n", encoding="utf-8")


def aggregate(results: list[Path], output: Path) -> None:
    records = [json.loads(path.read_text(encoding="utf-8")) for path in results]
    summary = {
        "total": len(records),
        "sat": sum(r.get("status") == "SAT" for r in records),
        "unsat": sum(r.get("status") == "UNSAT" for r in records),
        "unknown": sum(r.get("status") == "UNKNOWN" for r in records),
        "unresolved_cube_lines": [
            r.get("cube_line")
            for r in records
            if r.get("status") == "UNKNOWN"
        ],
        "records": records,
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in summary.items() if k != "records"}, indent=2))


def main() -> None:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)

    matrix = sub.add_parser("matrix")
    matrix.add_argument("--cube-file", type=Path, required=True)
    matrix.add_argument("--output", type=Path, required=True)

    extract = sub.add_parser("extract")
    extract.add_argument("--solver-log", type=Path, required=True)
    extract.add_argument("--cube-file", type=Path, required=True)
    extract.add_argument("--matrix", type=Path, required=True)

    merge = sub.add_parser("aggregate")
    merge.add_argument("--results", type=Path, nargs="+", required=True)
    merge.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    if args.command == "matrix":
        cubes = read_cubes(args.cube_file)
        if not cubes:
            raise SystemExit("no SMS cubes found")
        write_matrix(cubes, args.output)
        print(f"wrote {len(cubes)} cubes to {args.output}")
    elif args.command == "extract":
        cubes = read_cubes(args.solver_log)
        if not cubes:
            raise SystemExit("no SMS cubes found")
        args.cube_file.parent.mkdir(parents=True, exist_ok=True)
        args.cube_file.write_text(
            "\n".join(cube for _, cube in cubes) + "\n",
            encoding="utf-8",
        )
        normalized = list(
            enumerate((cube for _, cube in cubes), start=1)
        )
        write_matrix(normalized, args.matrix)
        print(f"extracted {len(cubes)} cubes to {args.cube_file}")
    else:
        aggregate(args.results, args.output)


if __name__ == "__main__":
    main()
