#!/usr/bin/env python3
"""Exact CPU repair of the 54 v8 Kaggle GPU near-witness elites.

The GPU campaign repeatedly reached a tournament with exactly one
margin-one offender (raw loss 10201).  This script does not restart that
heuristic.  Instead it searches disjoint Hamming shells around every saved
elite with the exact CP-SAT Pisa model.

Every SAT result is independently verified.  INFEASIBLE closes only the
stated labelled Hamming shell around that elite.  UNKNOWN is not treated as
an exclusion.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import glob
import json
import os
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from ortools.sat.python import cp_model

from k16_pisa_solver import (
    EXCLUDED_PROFILES,
    TerminalTournamentModel,
    canonicalize_zero_branch,
    extract_full,
    near_regular_even,
    verify,
)

N = 16
MODEL_VERSION = "k16-pisa-v9-v8-elite-exact-shells-20260727"


def arc(out: list[int], u: int, v: int) -> bool:
    return bool((out[u] >> v) & 1)


def relabel(out: list[int], order: list[int]) -> list[int]:
    old_to_new = {old: new for new, old in enumerate(order)}
    new_out = [0] * len(out)
    for old_u in range(len(out)):
        new_u = old_to_new[old_u]
        bits = out[old_u]
        while bits:
            bit = bits & -bits
            old_v = bit.bit_length() - 1
            new_out[new_u] |= 1 << old_to_new[old_v]
            bits ^= bit
    return new_out


def covered_counts(check: dict) -> list[int]:
    counts = [0] * len(check["outdegrees"])
    for blocked in range(len(counts)):
        for covering in check["blocker_sets"][blocked]:
            counts[covering] += 1
    return counts


def canonicalize_elite(record: dict) -> list[int]:
    """Put the saved near-witness into the zero-role label partition.

    Unlike the positive-gate helper, this accepts a near-witness rather than
    requiring the whole tournament to be Pisa.
    """

    out = [int(value) for value in record["out_masks"]]
    check = verify(out)
    degree = int(record["target_degree"])
    blockers = int(record["target_blockers"])
    if check["outdegrees"][0] != degree:
        raise ValueError("elite does not match its zero-degree branch")
    if check["blockers"][0] != blockers:
        raise ValueError("elite does not match its zero-blocker branch")
    if check["margins"][0] != 0:
        raise ValueError("elite vertex 0 is not zero-margin")
    if sum(margin > 0 for margin in check["margins"]) != 1:
        raise ValueError("elite is not a one-offender near-witness")
    if max(check["margins"]) != 1:
        raise ValueError("elite offender does not have margin one")

    out_neighbours = [v for v in range(1, N) if arc(out, 0, v)]
    blocker_vertices = list(check["blocker_sets"][0])
    blocker_set = set(blocker_vertices)
    other_in = [
        v
        for v in range(1, N)
        if not arc(out, 0, v) and v not in blocker_set
    ]
    covered = covered_counts(check)

    def role_key(v: int) -> tuple[int, int, int, int]:
        return (
            check["outdegrees"][v],
            check["blockers"][v],
            covered[v],
            v,
        )

    out_neighbours.sort(key=role_key)
    blocker_vertices.sort(key=role_key)
    other_in.sort(key=role_key)
    return relabel(out, [0] + out_neighbours + blocker_vertices + other_in)


def load_records(patterns: list[str]) -> list[dict]:
    paths: dict[int, Path] = {}
    for pattern in patterns:
        for raw_path in glob.glob(pattern, recursive=True):
            path = Path(raw_path)
            try:
                payload = json.loads(path.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError):
                continue
            if payload.get("campaign") != "K16-PISA-v8-endpoint-aware-triangle-search":
                continue
            shard = int(payload["shard"])
            paths[shard] = path

    missing = sorted(set(range(54)) - set(paths))
    if missing:
        raise RuntimeError(
            "Expected all 54 v8 shard JSON files. Missing: "
            + ",".join(map(str, missing))
        )

    records = []
    for shard in range(54):
        record = json.loads(paths[shard].read_text(encoding="utf-8"))
        if record["status"] == "WITNESS":
            raise RuntimeError(f"source shard {shard} already contains a witness")
        canonicalize_elite(record)
        records.append(record)
    return records


def endpoint_total_b(record: dict) -> tuple[int | None, int | None]:
    endpoint = record["target_endpoint"]
    value = int(endpoint["total_b"])
    if endpoint["total_b_is_floor"]:
        return None, value
    return value, None


def solve_shell(task: dict) -> dict:
    record = task["record"]
    lower = int(task["lower"])
    upper = int(task["upper"])
    seconds = int(task["seconds"])
    workers = int(task["workers"])
    seed = int(task["seed"])
    degree = int(record["target_degree"])
    blockers = int(record["target_blockers"])
    center = canonicalize_elite(record)
    total_b_eq, total_b_min = endpoint_total_b(record)

    tm = TerminalTournamentModel(
        N,
        zero_partition=(degree, blockers),
        min_degree=2,
        total_b_eq=total_b_eq,
        total_b_min=total_b_min,
        excluded_profiles=EXCLUDED_PROFILES,
        strongness_mode="rooted_role_cuts",
        role_symmetry_break=False,
    )

    differences = []
    for u in range(N):
        for v in range(u + 1, N):
            edge = tm.edge[(u, v)]
            value = int(arc(center, u, v))
            differences.append(edge.Not() if value else edge)
            tm.model.AddHint(edge, value)
    distance = tm.model.NewIntVar(0, N * (N - 1) // 2, "elite_distance")
    tm.model.Add(distance == sum(differences))
    tm.model.Add(distance >= lower)
    tm.model.Add(distance <= upper)

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = seconds
    solver.parameters.num_search_workers = workers
    solver.parameters.random_seed = seed
    solver.parameters.randomize_search = True
    solver.parameters.stop_after_first_solution = True
    solver.parameters.cp_model_presolve = True
    solver.parameters.symmetry_level = 2

    started = time.time()
    status = solver.Solve(tm.model)
    elapsed = time.time() - started
    status_name = solver.StatusName(status)
    logical_status = (
        "SAT"
        if status in (cp_model.OPTIMAL, cp_model.FEASIBLE)
        else "UNSAT"
        if status == cp_model.INFEASIBLE
        else status_name
    )
    result = {
        "model_version": MODEL_VERSION,
        "status": logical_status,
        "solver_status": status_name,
        "solver_level_exact": status == cp_model.INFEASIBLE,
        "source_shard": int(record["shard"]),
        "source_best_loss": int(record["best_loss"]),
        "source_endpoint": record["target_endpoint"],
        "zero_type": [degree, blockers],
        "hamming_shell": [lower, upper],
        "coverage": (
            "Every labelled tournament in this exact Hamming shell after "
            "canonical zero-role relabelling; no role-sort symmetry filter."
        ),
        "seconds": round(elapsed, 3),
        "time_limit_seconds": seconds,
        "workers": workers,
        "seed": seed,
    }
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        out = extract_full(solver, tm)
        check = verify(out)
        if not check["is_pisa"]:
            raise RuntimeError("CP-SAT candidate failed independent verification")
        result["verified"] = True
        result["distance"] = int(solver.Value(distance))
        result["witness"] = check
    return result


def solve_score_fiber(task: dict) -> dict:
    """Search the elite's complete labelled score-vector fiber.

    Ryser's triangle-reversal theorem says this is exactly the state-space
    component explored by degree-preserving directed-triangle reversals.  The
    GPU sampled it heuristically; this model searches it systematically.
    """

    record = task["record"]
    seconds = int(task["seconds"])
    workers = int(task["workers"])
    seed = int(task["seed"])
    degree = int(record["target_degree"])
    blockers = int(record["target_blockers"])
    center = canonicalize_elite(record)
    center_check = verify(center)
    total_b_eq, total_b_min = endpoint_total_b(record)

    tm = TerminalTournamentModel(
        N,
        zero_partition=(degree, blockers),
        min_degree=2,
        total_b_eq=total_b_eq,
        total_b_min=total_b_min,
        excluded_profiles=EXCLUDED_PROFILES,
        strongness_mode="rooted_role_cuts",
        role_symmetry_break=False,
    )
    for v in range(N):
        tm.model.Add(tm.degree[v] == int(center_check["outdegrees"][v]))
    for u in range(N):
        for v in range(u + 1, N):
            tm.model.AddHint(tm.edge[(u, v)], int(arc(center, u, v)))

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = seconds
    solver.parameters.num_search_workers = workers
    solver.parameters.random_seed = seed
    solver.parameters.randomize_search = True
    solver.parameters.stop_after_first_solution = True
    solver.parameters.cp_model_presolve = True
    solver.parameters.symmetry_level = 2

    started = time.time()
    status = solver.Solve(tm.model)
    elapsed = time.time() - started
    status_name = solver.StatusName(status)
    logical_status = (
        "SAT"
        if status in (cp_model.OPTIMAL, cp_model.FEASIBLE)
        else "UNSAT"
        if status == cp_model.INFEASIBLE
        else status_name
    )
    result = {
        "model_version": MODEL_VERSION,
        "status": logical_status,
        "solver_status": status_name,
        "solver_level_exact": status == cp_model.INFEASIBLE,
        "source_shard": int(record["shard"]),
        "source_best_loss": int(record["best_loss"]),
        "source_endpoint": record["target_endpoint"],
        "zero_type": [degree, blockers],
        "labelled_score_vector": center_check["outdegrees"],
        "coverage": (
            "The complete labelled score-vector fiber of the canonical elite "
            "inside its exact endpoint box (the Ryser C3-reversal component)."
        ),
        "seconds": round(elapsed, 3),
        "time_limit_seconds": seconds,
        "workers": workers,
        "seed": seed,
    }
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        out = extract_full(solver, tm)
        check = verify(out)
        if not check["is_pisa"]:
            raise RuntimeError("score-fiber candidate failed verification")
        result["verified"] = True
        result["witness"] = check
    return result


def positive_gate(seconds: int = 30) -> dict:
    """A known K14 Pisa tournament must survive the repair model machinery."""

    center, degree, blockers = canonicalize_zero_branch(
        near_regular_even(14)
    )
    tm = TerminalTournamentModel(
        14,
        zero_partition=(degree, blockers),
        min_degree=2,
        strongness_mode="rooted_role_cuts",
        role_symmetry_break=False,
    )
    for u in range(14):
        for v in range(u + 1, 14):
            tm.model.Add(tm.edge[(u, v)] == int(arc(center, u, v)))
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = seconds
    solver.parameters.num_search_workers = 1
    status = solver.Solve(tm.model)
    if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        raise RuntimeError(
            "K14 positive repair gate failed: " + solver.StatusName(status)
        )
    candidate = extract_full(solver, tm)
    if not verify(candidate)["is_pisa"]:
        raise RuntimeError("K14 positive repair gate failed verification")
    return {"status": "SAT", "verified": True}


def save_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def run_wave(
    records: list[dict],
    lower: int,
    upper: int,
    seconds: int,
    parallel: int,
    workers: int,
    seed: int,
    output_dir: Path,
) -> tuple[list[dict], dict | None]:
    results = []
    witness = None
    for start in range(0, len(records), parallel):
        wave = records[start : start + parallel]
        tasks = [
            {
                "record": record,
                "lower": lower,
                "upper": upper,
                "seconds": seconds,
                "workers": workers,
                "seed": seed ^ (int(record["shard"]) << 8) ^ (lower << 20),
            }
            for record in wave
        ]
        with concurrent.futures.ProcessPoolExecutor(
            max_workers=len(tasks)
        ) as executor:
            futures = [executor.submit(solve_shell, task) for task in tasks]
            for future in concurrent.futures.as_completed(futures):
                result = future.result()
                results.append(result)
                shard = result["source_shard"]
                path = (
                    output_dir
                    / f"shell-{lower}-{upper}"
                    / f"shard-{shard:02d}.json"
                )
                save_json(path, result)
                print(
                    "ELITE_REPAIR_RESULT "
                    f"shard={shard} shell={lower}-{upper} "
                    f"status={result['status']} seconds={result['seconds']}",
                    flush=True,
                )
                if result["status"] == "SAT":
                    witness = result
        if witness is not None:
            break
    return results, witness


def run_fiber_wave(
    records: list[dict],
    seconds: int,
    parallel: int,
    workers: int,
    seed: int,
    output_dir: Path,
) -> tuple[list[dict], dict | None]:
    results = []
    witness = None
    for start in range(0, len(records), parallel):
        wave = records[start : start + parallel]
        tasks = [
            {
                "record": record,
                "seconds": seconds,
                "workers": workers,
                "seed": seed ^ (int(record["shard"]) << 8) ^ 0xC3,
            }
            for record in wave
        ]
        with concurrent.futures.ProcessPoolExecutor(
            max_workers=len(tasks)
        ) as executor:
            futures = [
                executor.submit(solve_score_fiber, task) for task in tasks
            ]
            for future in concurrent.futures.as_completed(futures):
                result = future.result()
                results.append(result)
                shard = result["source_shard"]
                save_json(
                    output_dir / "score-fibers" / f"shard-{shard:02d}.json",
                    result,
                )
                print(
                    "ELITE_SCORE_FIBER_RESULT "
                    f"shard={shard} status={result['status']} "
                    f"seconds={result['seconds']}",
                    flush=True,
                )
                if result["status"] == "SAT":
                    witness = result
        if witness is not None:
            break
    return results, witness


def parse_shell(value: str) -> tuple[int, int, int]:
    try:
        lower, upper, seconds = map(int, value.split(":"))
    except ValueError as exc:
        raise argparse.ArgumentTypeError(
            "shell must have LOWER:UPPER:SECONDS"
        ) from exc
    if not (1 <= lower <= upper and seconds >= 1):
        raise argparse.ArgumentTypeError("invalid shell bounds or budget")
    return lower, upper, seconds


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--input-glob",
        action="append",
        required=True,
        help="Recursive glob containing the 54 v8 shard JSON files.",
    )
    parser.add_argument(
        "--shell",
        action="append",
        type=parse_shell,
        default=[],
        help="Disjoint exact shell as LOWER:UPPER:SECONDS.",
    )
    parser.add_argument("--parallel", type=int, default=4)
    parser.add_argument("--solver-workers", type=int, default=1)
    parser.add_argument("--fiber-seconds", type=int, default=600)
    parser.add_argument("--seed", type=int, default=20260727)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("/kaggle/working/k16_elite_repair_v9"),
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    shells = args.shell or [(1, 2, 120), (3, 4, 600), (5, 6, 1200)]
    print("K16_PISA_V9_ELITE_EXACT_REPAIR", flush=True)
    print("positive_gate=", positive_gate(), flush=True)
    records = load_records(args.input_glob)
    print(f"loaded_v8_elites={len(records)}", flush=True)

    campaign = {
        "model_version": MODEL_VERSION,
        "status": "NO_WITNESS",
        "source_elites": len(records),
        "shells": [],
    }
    for shell_index, (lower, upper, seconds) in enumerate(shells):
        results, witness = run_wave(
            records,
            lower,
            upper,
            seconds,
            args.parallel,
            args.solver_workers,
            args.seed,
            args.output_dir,
        )
        counts: dict[str, int] = {}
        for result in results:
            counts[result["status"]] = counts.get(result["status"], 0) + 1
        campaign["shells"].append(
            {
                "range": [lower, upper],
                "time_limit_per_elite": seconds,
                "result_counts": counts,
            }
        )
        save_json(args.output_dir / "campaign.json", campaign)
        if witness is not None:
            campaign["status"] = "WITNESS"
            campaign["witness"] = witness
            save_json(args.output_dir / "campaign.json", campaign)
            print("K16_PISA_WITNESS_FOUND_AND_VERIFIED", flush=True)
            print(
                " ".join(
                    f"{u}>{v}" for u, v in witness["witness"]["arcs"]
                ),
                flush=True,
            )
            return 0

        # After the two closest shell bands, systematically search the whole
        # degree-preserving triangle-reversal fiber before spending the largest
        # budget on the outer shell.
        if shell_index == min(1, len(shells) - 1):
            fiber_results, witness = run_fiber_wave(
                records,
                args.fiber_seconds,
                args.parallel,
                args.solver_workers,
                args.seed,
                args.output_dir,
            )
            fiber_counts: dict[str, int] = {}
            for result in fiber_results:
                fiber_counts[result["status"]] = (
                    fiber_counts.get(result["status"], 0) + 1
                )
            campaign["score_fibers"] = {
                "time_limit_per_elite": args.fiber_seconds,
                "result_counts": fiber_counts,
            }
            save_json(args.output_dir / "campaign.json", campaign)
            if witness is not None:
                campaign["status"] = "WITNESS"
                campaign["witness"] = witness
                save_json(args.output_dir / "campaign.json", campaign)
                print("K16_PISA_WITNESS_FOUND_AND_VERIFIED", flush=True)
                print(
                    " ".join(
                        f"{u}>{v}" for u, v in witness["witness"]["arcs"]
                    ),
                    flush=True,
                )
                return 0

    print(
        "NO_WITNESS_IN_COMPLETED_EXACT_SHELLS; "
        "UNKNOWN RESULTS ARE NOT EXCLUSIONS",
        flush=True,
    )
    print("V9_ELITE_REPAIR_CAMPAIGN_COMPLETE", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
