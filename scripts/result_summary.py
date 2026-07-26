#!/usr/bin/env python3
"""Render one solver JSON file as a GitHub Actions step summary."""

import argparse
import json
import sys
from pathlib import Path


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("result", type=Path)
    parser.add_argument("--fail-on-unknown", action="store_true")
    args = parser.parse_args()

    if not args.result.exists():
        print("## K16 Pisa result\n\n**ERROR:** result JSON was not produced.")
        return 1

    data = json.loads(args.result.read_text(encoding="utf-8"))
    print("## K16 Pisa result")
    print()
    print(f"- Model: `{data.get('model_version')}`")
    print(f"- Mode: `{data.get('run_mode')}`")
    if data.get("selected_box"):
        print(f"- Box: `{data['selected_box']}`")
    print(f"- Wall time: `{data.get('wall_seconds')} s`")

    error = data.get("error")
    if error:
        print(f"- Status: **ERROR** — `{error.get('type')}: {error.get('message')}`")
        return 1

    gates = data.get("gates") or []
    if gates:
        gate_ok = all(g.get("status") == "SAT" and g.get("verified") for g in gates)
        print(f"- Gates: **{'PASS' if gate_ok else 'FAIL'}** ({len(gates)}/3 recorded)")
        if not gate_ok:
            return 1

    results = data.get("results") or []
    if not results:
        status = "GATES_PASS" if data.get("run_mode") == "gates" else "NO_RESULT"
    else:
        status = results[-1].get("status", "NO_RESULT")
    print(f"- Logical status: **{status}**")

    if data.get("found"):
        print("- Independent verifier: **PASS**")
        print("- A SAT witness is stored in the JSON artifact.")

    print()
    print("`SAT` is an independently verified witness; `UNSAT` closes only this box; "
          "`UNKNOWN` closes nothing.")

    if status in {"NO_RESULT"}:
        return 1
    if status == "UNKNOWN" and args.fail_on_unknown:
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
