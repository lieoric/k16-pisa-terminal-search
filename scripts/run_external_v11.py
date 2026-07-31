#!/usr/bin/env python3
"""Run an external v11 solver, normalize its status, and verify SAT witnesses."""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import time
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from k16_pisa_solver import verify


ARC_LINE = re.compile(r"^\[(?:\(\d+,\d+\)(?:,\(\d+,\d+\))*)?\]$")
ARC_PAIR = re.compile(r"\((\d+),(\d+)\)")


def arc_var(n: int, u: int, v: int) -> int:
    """SMS row-major directed-edge variable, with the diagonal omitted."""
    if u == v:
        raise ValueError("loops have no arc variable")
    return u * (n - 1) + v + 1 - (1 if v > u else 0)


def parse_sms_arcs(text: str, n: int) -> list[list[int]] | None:
    for raw in reversed(text.splitlines()):
        line = raw.strip()
        if not ARC_LINE.fullmatch(line):
            continue
        arcs = [[int(u), int(v)] for u, v in ARC_PAIR.findall(line)]
        if len(arcs) == n * (n - 1) // 2:
            return arcs
    return None


def parse_roundingsat_arcs(text: str, n: int) -> list[list[int]] | None:
    model_line = next(
        (line.strip() for line in reversed(text.splitlines()) if line.startswith("v")),
        None,
    )
    if model_line is None:
        return None
    true_vars: set[int] = set()
    for token in model_line.split()[1:]:
        token = token.removeprefix("x")
        if token.startswith("-x"):
            continue
        if token.startswith("-"):
            continue
        true_vars.add(int(token))
    return [
        [u, v]
        for u in range(n)
        for v in range(n)
        if u != v and arc_var(n, u, v) in true_vars
    ]


def arcs_to_masks(arcs: list[list[int]], n: int) -> list[int]:
    out = [0] * n
    for u, v in arcs:
        if not (0 <= u < n and 0 <= v < n and u != v):
            raise ValueError(f"invalid arc ({u},{v})")
        out[u] |= 1 << v
    return out


def classify(kind: str, returncode: int, text: str, timed_out: bool) -> str:
    if timed_out:
        return "UNKNOWN"
    if returncode == 10:
        return "SAT"
    if returncode == 20:
        return "UNSAT"
    upper = text.upper()
    if "S UNSATISFIABLE" in upper:
        return "UNSAT"
    if "S SATISFIABLE" in upper and "UNSATISFIABLE" not in upper:
        return "SAT"
    if kind == "sms":
        match = re.findall(r"RESULT:\s*(\d+)", upper)
        if match:
            return {"10": "SAT", "20": "UNSAT"}.get(match[-1], "UNKNOWN")
    return "UNKNOWN"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--kind", choices=("sms", "roundingsat"), required=True)
    parser.add_argument("--binary", required=True)
    parser.add_argument("--input", required=True)
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--timeout", type=int, default=300)
    parser.add_argument("--result", required=True)
    parser.add_argument("--log", required=True)
    parser.add_argument("--cube-file")
    parser.add_argument("--cube-line", type=int)
    parser.add_argument("--solver-arg", action="append", default=[])
    args = parser.parse_args()

    if args.kind == "sms":
        command = [
            args.binary,
            "--vertices",
            str(args.n),
            "--directed",
            "--dimacs",
            args.input,
            "--timeout",
            str(args.timeout),
        ]
        if args.cube_file:
            command.extend(
                [
                    "--cube-file",
                    args.cube_file,
                    "--cube-line",
                    str(args.cube_line),
                    "--cube-timeout",
                    str(args.timeout),
                ]
            )
    else:
        command = [args.binary, args.input]
    command.extend(args.solver_arg)

    started = time.monotonic()
    timed_out = False
    try:
        completed = subprocess.run(
            command,
            capture_output=True,
            text=True,
            timeout=args.timeout + 15,
            check=False,
        )
        returncode = completed.returncode
        output = completed.stdout + completed.stderr
    except subprocess.TimeoutExpired as exc:
        timed_out = True
        returncode = 0
        stdout = exc.stdout.decode() if isinstance(exc.stdout, bytes) else (exc.stdout or "")
        stderr = exc.stderr.decode() if isinstance(exc.stderr, bytes) else (exc.stderr or "")
        output = stdout + stderr + "\nWRAPPER TIMEOUT\n"
    seconds = round(time.monotonic() - started, 3)

    status = classify(args.kind, returncode, output, timed_out)
    record: dict[str, object] = {
        "solver": args.kind,
        "status": status,
        "seconds": seconds,
        "solver_exit_code": returncode,
        "timed_out": timed_out,
        "n": args.n,
        "input": str(Path(args.input)),
        "command": command,
    }
    if args.cube_line is not None:
        record["cube_line"] = args.cube_line

    if status == "SAT":
        arcs = (
            parse_sms_arcs(output, args.n)
            if args.kind == "sms"
            else parse_roundingsat_arcs(output, args.n)
        )
        if arcs is None:
            record["verified"] = False
            record["verification_error"] = "SAT status had no parseable tournament"
        else:
            check = verify(arcs_to_masks(arcs, args.n))
            record["verified"] = bool(check["is_pisa"])
            record["witness"] = check
            if not check["is_pisa"]:
                record["verification_error"] = "parsed SAT witness is not Pisa"

    result_path = Path(args.result)
    log_path = Path(args.log)
    result_path.parent.mkdir(parents=True, exist_ok=True)
    log_path.parent.mkdir(parents=True, exist_ok=True)
    result_path.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    log_path.write_text(output, encoding="utf-8")
    print(json.dumps(record, indent=2))

    if status == "SAT" and not record.get("verified", False):
        raise SystemExit(3)


if __name__ == "__main__":
    main()
