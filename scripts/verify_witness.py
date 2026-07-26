#!/usr/bin/env python3
"""Independent verifier for K16 witness-hunter JSON artifacts."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


def reach(out: list[int], reverse: bool = False) -> int:
    n = len(out)
    if reverse:
        graph = [0] * n
        for u, mask in enumerate(out):
            bits = mask
            while bits:
                bit = bits & -bits
                v = bit.bit_length() - 1
                graph[v] |= 1 << u
                bits ^= bit
    else:
        graph = out

    seen = frontier = 1
    full = (1 << n) - 1
    while frontier:
        nxt = 0
        bits = frontier
        while bits:
            bit = bits & -bits
            u = bit.bit_length() - 1
            nxt |= graph[u]
            bits ^= bit
        nxt &= full ^ seen
        seen |= nxt
        frontier = nxt
    return seen


def verify_masks(out: list[int]) -> dict:
    n = len(out)
    if n != 16:
        return {"valid": False, "reason": f"expected 16 masks, got {n}"}
    full = (1 << n) - 1

    for u in range(n):
        if (out[u] >> u) & 1:
            return {"valid": False, "reason": f"loop at {u}"}
        if out[u] & ~full:
            return {"valid": False, "reason": f"mask {u} exceeds 16 bits"}
        for v in range(u + 1, n):
            if ((out[u] >> v) & 1) + ((out[v] >> u) & 1) != 1:
                return {"valid": False, "reason": f"bad pair {u},{v}"}

    strong = reach(out) == full and reach(out, reverse=True) == full
    degrees, second_sizes, margins, blockers = [], [], [], []
    for v in range(n):
        n2 = 0
        bits = out[v]
        while bits:
            bit = bits & -bits
            u = bit.bit_length() - 1
            n2 |= out[u]
            bits ^= bit
        n2 &= full ^ out[v]
        n2 &= full ^ (1 << v)

        degree = out[v].bit_count()
        second = n2.bit_count()
        incoming = (full ^ out[v]) & (full ^ (1 << v))
        blocked = incoming & (full ^ n2)
        degrees.append(degree)
        second_sizes.append(second)
        margins.append(second - degree)
        blockers.append(blocked.bit_count())

    return {
        "valid": True,
        "strong": strong,
        "is_pisa": strong and max(margins) == 0,
        "outdegrees": degrees,
        "second_sizes": second_sizes,
        "margins": margins,
        "blockers": blockers,
        "sum_blockers": sum(blockers),
        "arcs": [
            [u, v]
            for u in range(n)
            for v in range(n)
            if (out[u] >> v) & 1
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("result", type=Path)
    parser.add_argument("--write-check", type=Path)
    args = parser.parse_args()

    payload = json.loads(args.result.read_text(encoding="utf-8"))
    check = verify_masks([int(value) for value in payload["out_masks"]])
    check["declared_status"] = payload.get("status")
    check["source"] = str(args.result)

    if payload.get("status") == "WITNESS" and not check["is_pisa"]:
        print(json.dumps(check, indent=2), file=sys.stderr)
        raise SystemExit("declared witness failed independent verification")

    if args.write_check:
        args.write_check.parent.mkdir(parents=True, exist_ok=True)
        args.write_check.write_text(
            json.dumps(check, indent=2) + "\n", encoding="utf-8"
        )
    print(
        f"VERIFIED status={payload.get('status')} "
        f"is_pisa={check.get('is_pisa')} "
        f"max_margin={max(check.get('margins', [-999]))}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
