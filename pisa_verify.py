"""Dependency-free bit-mask verifier for tournament Pisa witnesses."""

from __future__ import annotations


def arc(out: list[int], u: int, v: int) -> int:
    return (out[u] >> v) & 1


def reach(out: list[int], reverse: bool = False) -> int:
    n = len(out)
    if reverse:
        graph = [0] * n
        for u in range(n):
            bits = out[u]
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


def verify(out: list[int]) -> dict:
    n = len(out)
    full = (1 << n) - 1
    for u in range(n):
        if arc(out, u, u):
            return {"valid": False, "reason": f"loop at {u}"}
        for v in range(u + 1, n):
            if arc(out, u, v) + arc(out, v, u) != 1:
                return {"valid": False, "reason": f"bad pair {u},{v}"}

    strong = reach(out) == full and reach(out, reverse=True) == full
    degrees = []
    second_sizes = []
    margins = []
    blockers = []
    blocker_sets = []
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
        second_size = n2.bit_count()
        incoming = (full ^ out[v]) & (full ^ (1 << v))
        blocked = incoming & (full ^ n2)
        degrees.append(degree)
        second_sizes.append(second_size)
        margins.append(second_size - degree)
        blockers.append(blocked.bit_count())
        blocker_sets.append(
            [x for x in range(n) if (blocked >> x) & 1]
        )

    return {
        "valid": True,
        "strong": strong,
        "is_pisa": strong and max(margins) == 0,
        "outdegrees": degrees,
        "second_sizes": second_sizes,
        "margins": margins,
        "blockers": blockers,
        "blocker_sets": blocker_sets,
        "sum_blockers": sum(blockers),
        "arcs": [
            (u, v)
            for u in range(n)
            for v in range(n)
            if arc(out, u, v)
        ],
    }
