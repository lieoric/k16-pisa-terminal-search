# K16 PISA v4.1 — score-sorted, zero-partition terminal campaign
# GitHub Actions edition: one terminal box per process/job.
#
# Dependencies used as exact cuts:
#   (T-NR) proved near-regular classification excludes degree profile 7^8 8^8.
#   (F-A)  v3 Frontier solver-level UNSAT excludes profile 6^1 7^6 8^9.
#   (F-B)  v3 Frontier solver-level UNSAT excludes profile 7^9 8^6 9^1.
# Hence every remaining K16 Pisa tournament has sum_v b(v) >= 10.
#
# The remaining space is partitioned by a chosen zero-margin vertex:
#   (d,b) = (7,1),(6,3),(5,5),(4,7),(3,9),(2,11),
# and each branch is split into total-b layers 10, 11, and >=12.
#
# SAT is unconditional after independent verification.
# INFEASIBLE closes exactly the named box. UNKNOWN closes nothing.

import argparse
import json
import os
import sys
import time
from math import comb
from pathlib import Path

from ortools.sat.python import cp_model

MODEL_VERSION = "k16-pisa-v4.1-github-matrix-20260726"
SMOKE = False
WORKERS = max(1, min(4, os.cpu_count() or 4))
SEEDS = [20260726, 314159, 271828, 161803]
OUT_DIR = Path(os.environ.get("K16_OUTPUT_DIR", "results"))
OUT = OUT_DIR / "k16_pisa_unconfigured.json"
START = time.time()
RESULTS = []
FOUND = None
GATE_RESULTS = []
RUN_MODE = "unconfigured"
SELECTED_BOX = None
ERROR = None

BUDGET = {
    "gate": 60,
    "exact_layer": 900,
    "residual_layer": 1800,
}
if SMOKE:
    BUDGET = {key: 5 for key in BUDGET}

# These are logically sound only together with the cited theorem/frontier results.
EXCLUDED_PROFILES = [
    {7: 8, 8: 8},          # proved near-regular theorem
    {6: 1, 7: 6, 8: 9},    # v3 Frontier THIN-A closure
    {7: 9, 8: 6, 9: 1},    # v3 Frontier THIN-B closure
]


# ---------------------------------------------------------------------------
# Independent bit-mask verifier and relabelling helpers
# ---------------------------------------------------------------------------

def arc(out, u, v):
    return (out[u] >> v) & 1


def reach(out, reverse=False):
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


def verify(out):
    n = len(out)
    full = (1 << n) - 1
    for u in range(n):
        if arc(out, u, u):
            return {"valid": False, "reason": f"loop at {u}"}
        for v in range(u + 1, n):
            if arc(out, u, v) + arc(out, v, u) != 1:
                return {"valid": False, "reason": f"bad pair {u},{v}"}

    strong = reach(out) == full and reach(out, reverse=True) == full
    degrees, second_sizes, margins, blockers, blocker_sets = [], [], [], [], []

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

        d = out[v].bit_count()
        s = n2.bit_count()
        in_mask = (full ^ out[v]) & (full ^ (1 << v))
        blocked_mask = in_mask & (full ^ n2)
        degrees.append(d)
        second_sizes.append(s)
        margins.append(s - d)
        blockers.append(blocked_mask.bit_count())
        blocker_sets.append([x for x in range(n) if (blocked_mask >> x) & 1])

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
        "arcs": [(u, v) for u in range(n) for v in range(n) if arc(out, u, v)],
    }


def cyclic_odd(n):
    out = [0] * n
    for i in range(n):
        for step in range(1, (n - 1) // 2 + 1):
            out[i] |= 1 << ((i + step) % n)
    return out


def near_regular_even(n):
    out = [0] * n
    half = n // 2
    for i in range(n):
        for j in range(i + 1, n):
            delta = j - i
            if delta < half:
                out[i] |= 1 << j
            elif delta > half:
                out[j] |= 1 << i
            elif i % 2 == 0:
                out[i] |= 1 << j
            else:
                out[j] |= 1 << i
    return out


def relabel(out, order):
    n = len(out)
    if sorted(order) != list(range(n)):
        raise ValueError("order is not a permutation")
    old_to_new = {old: new for new, old in enumerate(order)}
    new_out = [0] * n
    for old_u in range(n):
        new_u = old_to_new[old_u]
        bits = out[old_u]
        while bits:
            bit = bits & -bits
            old_v = bit.bit_length() - 1
            new_out[new_u] |= 1 << old_to_new[old_v]
            bits ^= bit
    return new_out


def canonicalize_zero_branch(out, zero_vertex=None):
    """Relabel a known Pisa witness into the exact WLOG role order used by
    TerminalTournamentModel.

    Vertex 0 is the chosen zero-margin point. The remaining vertices are
    grouped as:
      1) out-neighbours of 0,
      2) blockers of 0,
      3) other in-neighbours of 0.

    The model additionally imposes nondecreasing out-degree inside each role
    class as a safe label-symmetry break. Therefore a fixed regression witness
    must be sorted by degree inside the same classes before all of its edges are
    pinned. Sorting merely relabels vertices and does not change the tournament.
    """
    check = verify(out)
    if not check["is_pisa"]:
        raise ValueError("not a Pisa tournament")
    if zero_vertex is None:
        zero_vertex = next(v for v, margin in enumerate(check["margins"]) if margin == 0)
    if check["margins"][zero_vertex] != 0:
        raise ValueError("chosen vertex is not zero-margin")

    out_neighbors = [v for v in range(len(out)) if arc(out, zero_vertex, v)]
    blockers = list(check["blocker_sets"][zero_vertex])
    blocker_set = set(blockers)
    other_in = [
        v for v in range(len(out))
        if v != zero_vertex and not arc(out, zero_vertex, v) and v not in blocker_set
    ]

    covered_counts = [0] * len(out)
    for blocked_vertex in range(len(out)):
        for covering_vertex in check["blocker_sets"][blocked_vertex]:
            covered_counts[covering_vertex] += 1

    def role_key(v):
        return (
            check["outdegrees"][v],
            check["blockers"][v],
            covered_counts[v],
            v,
        )

    out_neighbors.sort(key=role_key)
    blockers.sort(key=role_key)
    other_in.sort(key=role_key)

    order = [zero_vertex] + out_neighbors + blockers + other_in
    canon = relabel(out, order)

    # Regression assertion: fixed positive gates must already satisfy the same
    # degree-order symmetry break imposed by TerminalTournamentModel.
    canon_check = verify(canon)
    d0 = len(out_neighbors)
    b0 = len(blockers)
    groups = (
        list(range(1, d0 + 1)),
        list(range(d0 + 1, d0 + b0 + 1)),
        list(range(d0 + b0 + 1, len(out))),
    )
    for group in groups:
        degrees = [canon_check["outdegrees"][v] for v in group]
        if degrees != sorted(degrees):
            raise AssertionError("canonical role group is not degree-sorted")

    return canon, d0, b0


def fixed_edges_from_out(out):
    n = len(out)
    return {
        (i, j): int(arc(out, i, j))
        for i in range(n)
        for j in range(i + 1, n)
    }


def save():
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    OUT.write_text(
        json.dumps(
            {
                "model_version": MODEL_VERSION,
                "run_mode": RUN_MODE,
                "selected_box": SELECTED_BOX,
                "smoke": SMOKE,
                "workers": WORKERS,
                "budgets_seconds": BUDGET,
                "dependencies": {
                    "near_regular_theorem": "profile 7^8 8^8 excluded",
                    "frontier_thin_a": "profile 6^1 7^6 8^9 excluded",
                    "frontier_thin_b": "profile 7^9 8^6 9^1 excluded",
                },
                "gates": GATE_RESULTS,
                "found": FOUND,
                "results": RESULTS,
                "error": ERROR,
                "wall_seconds": round(time.time() - START, 2),
            },
            indent=2,
        ),
        encoding="utf-8",
    )


def report_witness(name, out):
    global FOUND
    check = verify(out)
    if not check.get("is_pisa"):
        raise RuntimeError(f"{name}: candidate failed independent verification: {check}")

    print("\n" + "=" * 92)
    print("### K16 PISA WITNESS FOUND:", name)
    print("=" * 92)
    print("v | d+ | N2 | margin | b | blockers")
    for v in range(len(out)):
        print(
            f"{v:2d}|{check['outdegrees'][v]:4d}|{check['second_sizes'][v]:4d}|"
            f"{check['margins'][v]:7d}|{check['blockers'][v]:3d}|"
            f"{check['blocker_sets'][v]}"
        )
    print("sum b =", check["sum_blockers"])
    print("\nARCS")
    print(" ".join(f"{u}>{v}" for u, v in check["arcs"]))

    FOUND = {"box": name, **check}
    RESULTS.append({"box": name, "status": "SAT", "verified": True})
    save()


def exact_and(model, target, literals):
    for lit in literals:
        model.AddImplication(target, lit)
    model.AddBoolOr([target] + [lit.Not() for lit in literals])


# ---------------------------------------------------------------------------
# Full tournament model with exact score-sequence strongness
# ---------------------------------------------------------------------------

class TerminalTournamentModel:
    def __init__(
        self,
        n,
        *,
        fixed=None,
        zero_partition=None,       # (d,b), WLOG vertex 0; labels grouped by role
        min_degree=2,
        total_b_eq=None,
        total_b_min=None,
        excluded_profiles=None,
        strongness_mode="score",
        anchor_refinement=None,
        invariant_role_sort=False,
        role_symmetry_break=True,
    ):
        self.n = n
        self.model = cp_model.CpModel()
        m = self.model
        fixed = fixed or {}

        self.edge = {
            (i, j): m.NewBoolVar(f"e_{i}_{j}")
            for i in range(n)
            for j in range(i + 1, n)
        }

        def A(u, v):
            if u == v:
                raise ValueError("loop literal requested")
            return self.edge[(u, v)] if u < v else self.edge[(v, u)].Not()

        self.A = A
        for (i, j), value in fixed.items():
            m.Add(self.edge[(i, j)] == int(value))

        # Exact directed 3-cycle variables. v->u->x->v means x is reachable
        # from v in two steps and therefore does not block v.
        path_cycles = {(v, x): [] for v in range(n) for x in range(n) if v != x}
        for a in range(n):
            for b in range(a + 1, n):
                for c in range(b + 1, n):
                    fwd = m.NewBoolVar(f"cyc_{a}_{b}_{c}_f")
                    rev = m.NewBoolVar(f"cyc_{a}_{b}_{c}_r")
                    exact_and(m, fwd, [A(a, b), A(b, c), A(c, a)])
                    exact_and(m, rev, [A(a, c), A(c, b), A(b, a)])
                    path_cycles[(a, c)].append(fwd)
                    path_cycles[(b, a)].append(fwd)
                    path_cycles[(c, b)].append(fwd)
                    path_cycles[(a, b)].append(rev)
                    path_cycles[(c, a)].append(rev)
                    path_cycles[(b, c)].append(rev)

        # q[v,x] iff x blocks v.
        self.blocker = {}
        for v in range(n):
            for x in range(n):
                if x == v:
                    continue
                q = m.NewBoolVar(f"q_{v}_{x}")
                self.blocker[(v, x)] = q
                cycles = path_cycles[(v, x)]
                m.AddImplication(q, A(x, v))
                for cyc in cycles:
                    m.AddImplication(q, cyc.Not())
                m.AddBoolOr([q, A(v, x)] + cycles)

        self.degree = []
        self.bcount = []
        zero_flags = []
        for v in range(n):
            d = m.NewIntVar(0, n - 1, f"d_{v}")
            b = m.NewIntVar(0, n - 1, f"b_{v}")
            m.Add(d == sum(A(v, u) for u in range(n) if u != v))
            m.Add(b == sum(self.blocker[(v, x)] for x in range(n) if x != v))
            m.Add(b >= (n - 1) - 2 * d)
            if min_degree is not None:
                m.Add(d >= min_degree)

            z = m.NewBoolVar(f"zero_{v}")
            m.Add(b == (n - 1) - 2 * d).OnlyEnforceIf(z)
            zero_flags.append(z)
            self.degree.append(d)
            self.bcount.append(b)
        m.AddBoolOr(zero_flags)

        self.covered_count = []
        for x in range(n):
            covered = m.NewIntVar(0, n - 1, f"covered_count_{x}")
            m.Add(
                covered
                == sum(self.blocker[(v, x)] for v in range(n) if v != x)
            )
            self.covered_count.append(covered)

        # Exact cover cuts.
        for (v, x), q in self.blocker.items():
            m.Add(self.degree[x] >= self.degree[v] + 1).OnlyEnforceIf(q)
            m.Add(self.bcount[v] >= self.bcount[x] + 1).OnlyEnforceIf(q)

        for v in range(n):
            for x in range(n):
                if x == v:
                    continue
                for y in range(n):
                    if y == v or y == x:
                        continue
                    m.AddBoolOr([
                        self.blocker[(v, x)].Not(),
                        self.blocker[(x, y)].Not(),
                        self.blocker[(v, y)],
                    ])

        # WLOG role partition around the chosen zero point 0.
        if zero_partition is not None:
            d0, b0 = zero_partition
            if b0 != (n - 1) - 2 * d0:
                raise ValueError("zero_partition is not zero-margin")
            if d0 + b0 > n - 1:
                raise ValueError("bad zero partition")

            out_group = list(range(1, d0 + 1))
            blocker_group = list(range(d0 + 1, d0 + b0 + 1))
            other_in_group = list(range(d0 + b0 + 1, n))
            self.out_group = out_group
            self.zero_blocker_group = blocker_group
            self.other_in_group = other_in_group

            m.Add(self.degree[0] == d0)
            m.Add(self.bcount[0] == b0)
            for u in out_group:
                m.Add(A(0, u) == 1)
                m.Add(self.blocker[(0, u)] == 0)
            for x in blocker_group:
                m.Add(A(x, 0) == 1)
                m.Add(self.blocker[(0, x)] == 1)
                for u in out_group:
                    m.Add(A(x, u) == 1)
            for x in other_in_group:
                m.Add(A(x, 0) == 1)
                m.Add(self.blocker[(0, x)] == 0)
                # Explicit witness that x is not a blocker of 0.
                m.Add(sum(A(u, x) for u in out_group) >= 1)

            # If a blocker x of the selected zero point has the minimum
            # possible degree d(0)+1, then
            #
            #     N+(x) = N+(0) union {0}.
            #
            # Hence x and 0 have identical orientation to every third
            # vertex.  Encoding this "ordered twin" consequence explicitly
            # is much stronger than waiting for the degree and cover
            # constraints to rediscover it late in search.  Two distinct
            # blockers cannot both be such twins, so at most one gap-one
            # blocker exists.
            gap_one_blockers = []
            for x in blocker_group:
                gap_one = m.NewBoolVar(f"zero_blocker_{x}_degree_gap_one")
                m.Add(self.degree[x] == d0 + 1).OnlyEnforceIf(gap_one)
                m.Add(self.degree[x] >= d0 + 2).OnlyEnforceIf(gap_one.Not())
                for u in range(1, n):
                    if u != x:
                        m.Add(A(x, u) == A(0, u)).OnlyEnforceIf(gap_one)
                gap_one_blockers.append(gap_one)
            if gap_one_blockers:
                m.Add(sum(gap_one_blockers) <= 1)

            symmetry_groups = [out_group, blocker_group, other_in_group]
            if anchor_refinement is not None:
                anchor = blocker_group[0]
                anchor_degree = int(anchor_refinement["degree"])
                pattern = tuple(anchor_refinement.get("other_blocker_pattern", ()))
                if len(pattern) != max(0, b0 - 1):
                    raise ValueError("bad anchor-versus-blockers pattern")
                if any(bit not in (0, 1) for bit in pattern):
                    raise ValueError("anchor pattern must be binary")

                m.Add(self.degree[anchor] == anchor_degree)
                for x in blocker_group[1:]:
                    m.Add(self.degree[anchor] <= self.degree[x])
                for bit, x in zip(pattern, blocker_group[1:]):
                    m.Add(A(anchor, x) == bit)

                base_wins = d0 + 1 + sum(pattern)
                wins_in_other = anchor_degree - base_wins
                if not 0 <= wins_in_other <= len(other_in_group):
                    raise ValueError("anchor degree and pattern are incompatible")
                anchor_wins = other_in_group[:wins_in_other]
                anchor_losses = other_in_group[wins_in_other:]
                for x in anchor_wins:
                    m.Add(A(anchor, x) == 1)
                for x in anchor_losses:
                    m.Add(A(x, anchor) == 1)

                blocker_subgroups = []
                for relation in (0, 1):
                    subgroup = [
                        x for bit, x in zip(pattern, blocker_group[1:])
                        if bit == relation
                    ]
                    if subgroup:
                        blocker_subgroups.append(subgroup)
                symmetry_groups = [
                    out_group,
                    *blocker_subgroups,
                    anchor_wins,
                    anchor_losses,
                ]

            if role_symmetry_break:
                for group in symmetry_groups:
                    if invariant_role_sort:
                        self._add_invariant_role_sort(group)
                    else:
                        for i in range(len(group) - 1):
                            m.Add(
                                self.degree[group[i]]
                                <= self.degree[group[i + 1]]
                            )

        if strongness_mode == "score":
            # Strongness from a sorted score sequence. p is a permutation of
            # labels, score[k] = degree[p[k]], and every proper Landau prefix
            # is strict.
            self.score_perm = [
                m.NewIntVar(0, n - 1, f"score_perm_{k}") for k in range(n)
            ]
            self.score = [
                m.NewIntVar(0, n - 1, f"score_{k}") for k in range(n)
            ]
            m.AddAllDifferent(self.score_perm)
            for k in range(n):
                m.AddElement(self.score_perm[k], self.degree, self.score[k])
            for k in range(n - 1):
                m.Add(self.score[k] <= self.score[k + 1])
                equal = m.NewBoolVar(f"score_equal_{k}")
                m.Add(self.score[k] == self.score[k + 1]).OnlyEnforceIf(equal)
                m.Add(self.score[k] != self.score[k + 1]).OnlyEnforceIf(
                    equal.Not()
                )
                m.Add(
                    self.score_perm[k] < self.score_perm[k + 1]
                ).OnlyEnforceIf(equal)
            for k in range(1, n):
                m.Add(sum(self.score[:k]) >= comb(k, 2) + 1)
            m.Add(sum(self.score) == comb(n, 2))
        elif strongness_mode == "rooted_role_cuts":
            if zero_partition is None:
                raise ValueError("rooted role cuts require zero_partition")
            # Every non-blocker in-neighbour of 0 is reached in two steps
            # from 0, and every in-neighbour reaches 0 directly.  Therefore
            # only the chosen blockers can fail to be reached from 0, while
            # only the chosen out-neighbours can fail to reach 0.
            #
            # Enumerating nonempty subsets of those two small role classes
            # gives an exact rooted strong-connectivity encoding: no subset
            # of blockers may be closed to incoming arcs, and no subset of
            # out-neighbours may be closed to outgoing arcs.
            all_vertices = list(range(n))
            for mask in range(1, 1 << len(blocker_group)):
                subset = [
                    blocker_group[i]
                    for i in range(len(blocker_group))
                    if (mask >> i) & 1
                ]
                outside = [v for v in all_vertices if v not in subset]
                m.AddBoolOr([A(y, x) for x in subset for y in outside])
            for mask in range(1, 1 << len(out_group)):
                subset = [
                    out_group[i]
                    for i in range(len(out_group))
                    if (mask >> i) & 1
                ]
                outside = [v for v in all_vertices if v not in subset]
                m.AddBoolOr([A(x, y) for x in subset for y in outside])
        elif strongness_mode == "external":
            # A specialized caller may provide its own exact strong-connectivity
            # encoding.  For example, a fixed local median order is a directed
            # Hamiltonian path, so one reverse arc across each proper prefix is
            # necessary and sufficient for strongness.
            pass
        else:
            raise ValueError(f"unknown strongness mode: {strongness_mode}")

        self.total_b = m.NewIntVar(0, n * (n - 1), "total_b")
        m.Add(self.total_b == sum(self.bcount))
        if total_b_eq is not None:
            m.Add(self.total_b == total_b_eq)
        if total_b_min is not None:
            m.Add(self.total_b >= total_b_min)

        # Reuse theorem/frontier closures as exact profile nogoods.
        self._add_profile_exclusions(excluded_profiles or [])

    def _add_invariant_role_sort(self, group):
        """Safe lexicographic ordering of interchangeable role vertices."""
        m = self.model
        for left, right in zip(group, group[1:]):
            m.Add(self.degree[left] <= self.degree[right])
            degree_equal = m.NewBoolVar(
                f"role_degree_equal_{left}_{right}"
            )
            m.Add(
                self.degree[left] == self.degree[right]
            ).OnlyEnforceIf(degree_equal)
            m.Add(
                self.degree[left] != self.degree[right]
            ).OnlyEnforceIf(degree_equal.Not())
            m.Add(
                self.bcount[left] <= self.bcount[right]
            ).OnlyEnforceIf(degree_equal)

            blocker_equal = m.NewBoolVar(
                f"role_blocker_equal_{left}_{right}"
            )
            m.Add(
                self.bcount[left] == self.bcount[right]
            ).OnlyEnforceIf(blocker_equal)
            m.Add(
                self.bcount[left] != self.bcount[right]
            ).OnlyEnforceIf(blocker_equal.Not())
            both_equal = m.NewBoolVar(
                f"role_degree_blocker_equal_{left}_{right}"
            )
            exact_and(m, both_equal, [degree_equal, blocker_equal])
            m.Add(
                self.covered_count[left] <= self.covered_count[right]
            ).OnlyEnforceIf(both_equal)

    def _add_profile_exclusions(self, profiles):
        if not profiles:
            return
        m = self.model
        degrees_needed = sorted({degree for p in profiles for degree in p})
        counts = {}
        for degree in degrees_needed:
            flags = []
            for v in range(self.n):
                flag = m.NewBoolVar(f"is_degree_{degree}_{v}")
                m.Add(self.degree[v] == degree).OnlyEnforceIf(flag)
                m.Add(self.degree[v] != degree).OnlyEnforceIf(flag.Not())
                flags.append(flag)
            count = m.NewIntVar(0, self.n, f"count_degree_{degree}")
            m.Add(count == sum(flags))
            counts[degree] = count

        for p_index, profile in enumerate(profiles):
            if sum(profile.values()) != self.n:
                raise ValueError("excluded profile does not sum to n")
            differences = []
            for degree, target in profile.items():
                diff = m.NewBoolVar(f"profile_{p_index}_diff_degree_{degree}")
                m.Add(counts[degree] != target).OnlyEnforceIf(diff)
                m.Add(counts[degree] == target).OnlyEnforceIf(diff.Not())
                differences.append(diff)
            m.AddBoolOr(differences)


# ---------------------------------------------------------------------------
# Positive quotient regression gate: regular K7 quotient -> Pisa K14
# ---------------------------------------------------------------------------

class PairQuotientGateModel:
    def __init__(self, modules=7):
        if modules % 2 == 0:
            raise ValueError("regular quotient order must be odd")
        self.modules = modules
        self.model = cp_model.CpModel()
        m = self.model
        self.edge = {
            (i, j): m.NewBoolVar(f"Q_{i}_{j}")
            for i in range(modules)
            for j in range(i + 1, modules)
        }

        def A(i, j):
            return self.edge[(i, j)] if i < j else self.edge[(j, i)].Not()

        self.A = A
        target = modules - 1  # external weighted outdegree = 2*((m-1)/2)
        for i in range(modules):
            m.Add(sum(2 * A(i, j) for j in range(modules) if j != i) == target)
        # Safe orientation break among identical modules.
        m.Add(A(0, 1) == 1)

    def expand(self, solver):
        members = [[2 * i, 2 * i + 1] for i in range(self.modules)]
        out = [0] * (2 * self.modules)
        for low, high in members:
            out[high] |= 1 << low
        for i in range(self.modules):
            for j in range(i + 1, self.modules):
                left, right = (i, j) if solver.Value(self.edge[(i, j)]) else (j, i)
                for u in members[left]:
                    for v in members[right]:
                        out[u] |= 1 << v
        return out


# ---------------------------------------------------------------------------
# Solver helpers and gates
# ---------------------------------------------------------------------------

def extract_full(solver, tm):
    out = [0] * tm.n
    for i in range(tm.n):
        for j in range(i + 1, tm.n):
            if solver.Value(tm.edge[(i, j)]):
                out[i] |= 1 << j
            else:
                out[j] |= 1 << i
    return out


def configure_solver(seconds, seed):
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = seconds
    solver.parameters.num_search_workers = WORKERS
    solver.parameters.random_seed = seed
    solver.parameters.randomize_search = True
    solver.parameters.stop_after_first_solution = True
    solver.parameters.cp_model_presolve = True
    solver.parameters.symmetry_level = 2
    solver.parameters.log_search_progress = False
    return solver


def solve_gate(name, model_object, extractor):
    solver = configure_solver(BUDGET["gate"], SEEDS[0])
    t0 = time.time()
    status = solver.Solve(model_object.model)
    dt = time.time() - t0
    print(name + ":", solver.StatusName(status), f"[{dt:.2f}s]")
    if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        raise RuntimeError(name + " failed or timed out; aborting")
    out = extractor(solver, model_object)
    check = verify(out)
    if not check["is_pisa"]:
        raise RuntimeError(name + " candidate failed independent verification")
    return check


def run_gates():
    global GATE_RESULTS
    print("\nGATE 1: fixed K12 witness under score-sort and zero-role pinning")
    gate12 = [
        0x1C6, 0x9C4, 0x618, 0xC33, 0xC23, 0x9C7,
        0x69C, 0x71C, 0x65C, 0xC3B, 0x823, 0x1C5,
    ]
    canon12, d12, b12 = canonicalize_zero_branch(gate12)
    check12 = solve_gate(
        "GATE K12",
        TerminalTournamentModel(
            12,
            fixed=fixed_edges_from_out(canon12),
            zero_partition=(d12, b12),
            min_degree=2,
            total_b_min=6,
        ),
        extract_full,
    )
    print("  degree set=", sorted(set(check12["outdegrees"])), "sum b=", check12["sum_blockers"])

    print("\nGATE 2: fixed near-regular K14 under the same score-sort machinery")
    gate14 = near_regular_even(14)
    canon14, d14, b14 = canonicalize_zero_branch(gate14)
    check14 = solve_gate(
        "GATE K14 SCORE",
        TerminalTournamentModel(
            14,
            fixed=fixed_edges_from_out(canon14),
            zero_partition=(d14, b14),
            min_degree=2,
            total_b_eq=7,
        ),
        extract_full,
    )
    print("  profile=", sorted(check14["outdegrees"]), "sum b=", check14["sum_blockers"])

    print("\nGATE 3: positive quotient expansion K7 -> near-regular Pisa K14")
    qgate = PairQuotientGateModel(7)
    check_q = solve_gate("GATE K14 QUOTIENT", qgate, lambda s, q: q.expand(s))
    print("  profile=", sorted(check_q["outdegrees"]), "sum b=", check_q["sum_blockers"])
    GATE_RESULTS = [
        {
            "gate": "GATE K12",
            "status": "SAT",
            "verified": True,
            "degree_profile": sorted(check12["outdegrees"]),
            "sum_blockers": check12["sum_blockers"],
        },
        {
            "gate": "GATE K14 SCORE",
            "status": "SAT",
            "verified": True,
            "degree_profile": sorted(check14["outdegrees"]),
            "sum_blockers": check14["sum_blockers"],
        },
        {
            "gate": "GATE K14 QUOTIENT",
            "status": "SAT",
            "verified": True,
            "degree_profile": sorted(check_q["outdegrees"]),
            "sum_blockers": check_q["sum_blockers"],
        },
    ]
    save()


def run_box(name, builder, seconds, seeds):
    global FOUND
    print(f"\n{name}: {seconds}s/seed, seeds={seeds}", flush=True)
    attempts = []
    for seed in seeds:
        tm = builder()
        solver = configure_solver(seconds, seed)
        t0 = time.time()
        status = solver.Solve(tm.model)
        dt = time.time() - t0
        status_name = solver.StatusName(status)
        attempts.append({"seed": seed, "status": status_name, "seconds": round(dt, 2)})
        print(" ", seed, status_name, f"[{dt:.1f}s]", flush=True)

        if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            report_witness(name, extract_full(solver, tm))
            return "SAT"
        if status == cp_model.INFEASIBLE:
            RESULTS.append({
                "box": name,
                "status": "UNSAT",
                "attempts": attempts,
                "solver_level_exact": True,
            })
            save()
            return "UNSAT"
        if status == cp_model.MODEL_INVALID:
            raise RuntimeError(name + ": MODEL_INVALID")

    RESULTS.append({"box": name, "status": "UNKNOWN", "attempts": attempts})
    save()
    return "UNKNOWN"


# ---------------------------------------------------------------------------
# Terminal campaign
# ---------------------------------------------------------------------------

def terminal_box_specs():
    specs = {}
    for degree, blockers in [(7, 1), (6, 3), (5, 5), (4, 7), (3, 9), (2, 11)]:
        branch = f"d{degree}_b{blockers}"
        for total_b in (10, 11):
            key = f"{branch}_eq{total_b}"
            specs[key] = {
                "name": f"FINAL_{branch}_sum_b_eq_{total_b}",
                "degree": degree,
                "blockers": blockers,
                "total_b_eq": total_b,
                "total_b_min": None,
                "budget": "exact_layer",
                "seeds": SEEDS[:1],
            }
        key = f"{branch}_ge12"
        specs[key] = {
            "name": f"FINAL_{branch}_sum_b_ge_12",
            "degree": degree,
            "blockers": blockers,
            "total_b_eq": None,
            "total_b_min": 12,
            "budget": "residual_layer",
            "seeds": SEEDS[:2],
        }
    return specs


TERMINAL_BOXES = terminal_box_specs()


def residual_refinement_box_specs():
    """Refine only the two hard residual terminal boxes.

    For each remaining zero-point branch, the old total_b >= 12 box is
    partitioned exactly into total_b = 12,...,19 and total_b >= 20.
    The boxes are pairwise disjoint and their union is the original residual
    box, so the refinement introduces neither gaps nor duplicated cases.
    """
    specs = {}
    for degree, blockers in [(7, 1), (6, 3)]:
        branch = f"d{degree}_b{blockers}"
        for total_b in range(12, 20):
            key = f"{branch}_eq{total_b}"
            specs[key] = {
                "name": f"REFINE_{branch}_sum_b_eq_{total_b}",
                "degree": degree,
                "blockers": blockers,
                "total_b_eq": total_b,
                "total_b_min": None,
                "budget": "exact_layer",
                "seeds": SEEDS[:1],
            }
        key = f"{branch}_ge20"
        specs[key] = {
            "name": f"REFINE_{branch}_sum_b_ge_20",
            "degree": degree,
            "blockers": blockers,
            "total_b_eq": None,
            "total_b_min": 20,
            "budget": "residual_layer",
            "seeds": SEEDS[:2],
        }
    return specs


REFINEMENT_BOXES = residual_refinement_box_specs()
ALL_BOXES = {**TERMINAL_BOXES, **REFINEMENT_BOXES}


def build_terminal_box(spec):
    return TerminalTournamentModel(
        16,
        zero_partition=(spec["degree"], spec["blockers"]),
        min_degree=2,
        total_b_eq=spec["total_b_eq"],
        total_b_min=spec["total_b_min"],
        excluded_profiles=EXCLUDED_PROFILES,
    )


def run_terminal(selected_box=None):
    if selected_box is not None and selected_box not in ALL_BOXES:
        raise ValueError(f"unknown terminal box: {selected_box}")

    selected = (
        [(selected_box, ALL_BOXES[selected_box])]
        if selected_box is not None
        else list(TERMINAL_BOXES.items())
    )
    statuses = {}
    for key, spec in selected:
        statuses[key] = run_box(
            spec["name"],
            lambda spec=spec: build_terminal_box(spec),
            BUDGET[spec["budget"]],
            seeds=spec["seeds"],
        )
        if FOUND:
            return statuses

    if selected_box is None and all(status == "UNSAT" for status in statuses.values()):
        print("\n" + "#" * 92)
        print("ALL 18 TERMINAL BOXES ARE UNSAT")
        print("Combining these results with:")
        print("  (i) the proved near-regular twin-pair theorem, and")
        print("  (ii) the v3 Frontier THIN-A and THIN-B UNSAT closures,")
        print("there is no Pisa orientation of K16, conditional on model correctness.")
        print("#" * 92)
    elif selected_box is None:
        incomplete = {name: status for name, status in statuses.items() if status != "UNSAT"}
        print("\nTerminal campaign incomplete:", incomplete)
    return statuses


def parse_args():
    parser = argparse.ArgumentParser(
        description="Run the K16 Pisa v4.1 positive gates and one terminal box."
    )
    target = parser.add_mutually_exclusive_group()
    target.add_argument(
        "--gates-only",
        action="store_true",
        help="Run only the three positive regression gates.",
    )
    target.add_argument(
        "--box",
        choices=sorted(ALL_BOXES),
        help=(
            "Run one original terminal box or one residual-refinement box "
            "after the gates."
        ),
    )
    parser.add_argument(
        "--smoke",
        action="store_true",
        help="Use five-second budgets for environment and wiring validation.",
    )
    parser.add_argument(
        "--output-dir",
        default=os.environ.get("K16_OUTPUT_DIR", "results"),
        help="Directory for the JSON result artifact.",
    )
    parser.add_argument(
        "--workers",
        type=int,
        default=max(1, min(4, os.cpu_count() or 4)),
        help="CP-SAT workers (GitHub ubuntu-latest currently uses four here).",
    )
    parser.add_argument("--gate-seconds", type=int, default=60)
    parser.add_argument("--exact-seconds", type=int, default=900)
    parser.add_argument("--residual-seconds", type=int, default=1800)
    return parser.parse_args()


def configure_run(args):
    global SMOKE, WORKERS, OUT_DIR, OUT, RUN_MODE, SELECTED_BOX, BUDGET
    SMOKE = args.smoke
    WORKERS = max(1, args.workers)
    OUT_DIR = Path(args.output_dir)
    SELECTED_BOX = args.box
    RUN_MODE = "gates" if args.gates_only else ("box" if args.box else "all")

    BUDGET = {
        "gate": args.gate_seconds,
        "exact_layer": args.exact_seconds,
        "residual_layer": args.residual_seconds,
    }
    if SMOKE:
        BUDGET = {key: 5 for key in BUDGET}

    suffix = (
        "gates"
        if args.gates_only
        else (args.box if args.box else "all_terminal_boxes")
    )
    flavor = "smoke" if SMOKE else "formal"
    OUT = OUT_DIR / f"k16_pisa_{flavor}_{suffix}.json"


def main():
    args = parse_args()
    configure_run(args)

    print("=" * 92)
    print("K16 PISA v4.1 GitHub matrix campaign")
    print("model:", MODEL_VERSION)
    print("mode:", RUN_MODE, "box:", SELECTED_BOX)
    print("smoke:", SMOKE)
    print("workers:", WORKERS, "budgets:", BUDGET)
    print("output:", OUT)
    print("dependencies: near-regular theorem + v3 Frontier THIN-A/THIN-B closures")
    print("=" * 92)

    assert verify(cyclic_odd(15))["is_pisa"]
    assert verify(near_regular_even(14))["is_pisa"]
    run_gates()
    if not args.gates_only:
        run_terminal(args.box)
    save()

    print("\nFINAL:", "SAT witness found" if FOUND else "no SAT witness in completed boxes")
    print("Results saved to", OUT)
    print("Wall time", round(time.time() - START, 1), "seconds")


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:
        ERROR = {
            "type": type(exc).__name__,
            "message": str(exc),
        }
        try:
            save()
        finally:
            print(f"FATAL: {type(exc).__name__}: {exc}", file=sys.stderr)
        raise
