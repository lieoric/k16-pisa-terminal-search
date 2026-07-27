#!/usr/bin/env python3
"""Standalone audit for a claimed primitive K16 Pisa tournament.

This file intentionally imports no model builder, SAT helper, or project
verifier.  It receives only an arc list and recomputes the tournament,
strong connectivity, strict second neighbourhoods, margins, blocker sets,
and modular decomposition predicates from scratch.
"""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path


def arcs_to_masks(arcs: list[list[int]], n: int) -> list[int]:
    out = [0] * n
    seen: set[tuple[int, int]] = set()
    for raw_u, raw_v in arcs:
        u = int(raw_u)
        v = int(raw_v)
        if not (0 <= u < n and 0 <= v < n) or u == v:
            raise ValueError(f"invalid arc {(u, v)}")
        if (u, v) in seen:
            raise ValueError(f"duplicate arc {(u, v)}")
        seen.add((u, v))
        out[u] |= 1 << v
    return out


def arc(out: list[int], u: int, v: int) -> int:
    return (out[u] >> v) & 1


def closure(out: list[int], reverse: bool) -> int:
    n = len(out)
    graph = [0] * n
    if reverse:
        for u in range(n):
            bits = out[u]
            while bits:
                bit = bits & -bits
                v = bit.bit_length() - 1
                graph[v] |= 1 << u
                bits ^= bit
    else:
        graph = list(out)

    seen = frontier = 1
    while frontier:
        nxt = 0
        bits = frontier
        while bits:
            bit = bits & -bits
            v = bit.bit_length() - 1
            nxt |= graph[v]
            bits ^= bit
        nxt &= ~seen
        seen |= nxt
        frontier = nxt
    return seen


def tournament_check(out: list[int]) -> tuple[bool, str | None]:
    n = len(out)
    for u in range(n):
        if arc(out, u, u):
            return False, f"loop at {u}"
        for v in range(u + 1, n):
            if arc(out, u, v) + arc(out, v, u) != 1:
                return False, f"bad unordered pair {u},{v}"
    return True, None


def find_module(
    out: list[int],
    vertices: tuple[int, ...] | None = None,
) -> list[int] | None:
    """Return a non-trivial module of the induced tournament, if one exists."""
    if vertices is None:
        vertices = tuple(range(len(out)))
    if len(set(vertices)) != len(vertices):
        raise ValueError("core vertices must be distinct")

    for size in range(2, len(vertices)):
        for module_tuple in itertools.combinations(vertices, size):
            module = set(module_tuple)
            first = module_tuple[0]
            is_module = True
            for x in vertices:
                if x in module:
                    continue
                direction = arc(out, x, first)
                if any(arc(out, x, u) != direction for u in module_tuple[1:]):
                    is_module = False
                    break
            if is_module:
                return list(module_tuple)
    return None


def verify_pisa(out: list[int]) -> dict:
    n = len(out)
    valid_tournament, reason = tournament_check(out)
    if not valid_tournament:
        return {"valid": False, "reason": reason}

    full = (1 << n) - 1
    strong = (
        closure(out, reverse=False) == full
        and closure(out, reverse=True) == full
    )
    degrees: list[int] = []
    second_sizes: list[int] = []
    margins: list[int] = []
    blockers: list[int] = []
    blocker_sets: list[list[int]] = []

    for v in range(n):
        second = 0
        bits = out[v]
        while bits:
            bit = bits & -bits
            middle = bit.bit_length() - 1
            second |= out[middle]
            bits ^= bit
        second &= full ^ out[v]
        second &= full ^ (1 << v)

        degree = out[v].bit_count()
        incoming = (full ^ out[v]) & (full ^ (1 << v))
        blocked = incoming & (full ^ second)
        degrees.append(degree)
        second_sizes.append(second.bit_count())
        margins.append(second.bit_count() - degree)
        blockers.append(blocked.bit_count())
        blocker_sets.append(
            [x for x in range(n) if (blocked >> x) & 1]
        )

    zeros = [v for v, margin in enumerate(margins) if margin == 0]
    return {
        "valid": True,
        "strong": strong,
        "is_pisa": strong and max(margins) == 0,
        "outdegrees": degrees,
        "second_sizes": second_sizes,
        "margins": margins,
        "zeros": zeros,
        "degree_six_zeros": [v for v in zeros if degrees[v] == 6],
        "blockers": blockers,
        "blocker_sets": blocker_sets,
        "sum_blockers": sum(blockers),
        "arcs": [
            [u, v]
            for u in range(n)
            for v in range(n)
            if arc(out, u, v)
        ],
    }


def box_accepts(box: str | None, check: dict) -> bool:
    if box is None:
        return True
    a = len(check["degree_six_zeros"])
    z = len(check["zeros"])
    a_label, z_label = box.split("_", maxsplit=1)
    a_ok = {
        "a0": a == 0,
        "a1": a == 1,
        "a2p": a >= 2,
    }[a_label]
    z_ok = {
        "z2": z == 2,
        "z3": z == 3,
        "z4p": z >= 4,
    }[z_label]
    return a_ok and z_ok


def audit(
    payload: dict,
    *,
    required_cores: list[tuple[int, ...]],
    box: str | None,
) -> dict:
    n = int(payload["n"])
    out = arcs_to_masks(payload["arcs"], n)
    check = verify_pisa(out)
    if not check.get("valid"):
        return {
            "valid": False,
            "pisa": check,
            "reason": check.get("reason"),
        }

    full_module = find_module(out)
    core_audits = []
    for core in required_cores:
        module = find_module(out, core)
        core_audits.append({
            "vertices": list(core),
            "primitive": module is None,
            "module": module,
        })

    primitive = full_module is None
    box_valid = box_accepts(box, check)
    valid = (
        bool(check["is_pisa"])
        and primitive
        and all(item["primitive"] for item in core_audits)
        and box_valid
    )
    return {
        "schema": "k16-primitive-independent-audit-v1",
        "valid": valid,
        "is_pisa": bool(check["is_pisa"]),
        "primitive": primitive,
        "module": full_module,
        "required_core_audits": core_audits,
        "box": box,
        "box_valid": box_valid,
        "pisa": check,
    }


def parse_core(value: str) -> tuple[int, ...]:
    vertices = tuple(int(part) for part in value.split(",") if part)
    if not vertices:
        raise argparse.ArgumentTypeError("a core cannot be empty")
    return vertices


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--core", action="append", type=parse_core, default=[])
    parser.add_argument(
        "--box",
        choices=(
            "a0_z2", "a0_z3", "a0_z4p",
            "a1_z2", "a1_z3", "a1_z4p",
            "a2p_z2", "a2p_z3", "a2p_z4p",
        ),
    )
    args = parser.parse_args()

    payload = json.loads(args.input.read_text(encoding="utf-8"))
    record = audit(
        payload,
        required_cores=args.core,
        box=args.box,
    )
    text = json.dumps(record, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    print(text, end="")
    if not record["valid"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
