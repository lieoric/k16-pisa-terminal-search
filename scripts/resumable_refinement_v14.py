#!/usr/bin/env python3
"""Resume-safe exact refinement of the remaining v13 K16 Pisa cubes.

The queue is an exact disjoint cover of the selected v13 UNKNOWN children.
Every timed-out leaf is replaced by its two children on one still-free
unordered tournament edge.  Confirmed UNSAT leaves are never retried.

An optional progressive schedule assigns larger time budgets to deeper
children.  For example, ``180,1800,7200`` means: try an initial leaf for
three minutes, split a timeout and try each child for thirty minutes, then
split another timeout and give every deeper descendant two hours.

The checkpoint persists mathematical coverage, not a solver's private CDCL
state.  Restarting therefore loses only learned clauses from the current
process, never a proved UNSAT leaf or a pending portion of the search space.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import signal
import sys
import threading
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from pysat.formula import CNF
from pysat.solvers import Solver

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from pisa_verify import verify


MODEL_VERSION = "k16-pisa-v14-resumable-adaptive-refinement-20260727"
WORKER_SOLVER: Solver | None = None
WORKER_N = 16


def utc_now() -> str:
    return datetime.now(UTC).isoformat()


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
    assumptions: list[int],
    n: int,
    depth: int,
) -> list[int]:
    assigned = {abs(literal) for literal in assumptions}
    candidates = []
    for u in range(n):
        for v in range(u + 1, n):
            uv = arc_var(n, u, v)
            vu = arc_var(n, v, u)
            if uv not in assigned and vu not in assigned:
                candidates.append(uv)
    if len(candidates) < depth:
        raise ValueError(
            f"only {len(candidates)} free unordered edges remain; "
            f"cannot split by {depth}"
        )
    return candidates[:depth]


def free_split_variables(
    assumptions: list[int],
    n: int,
) -> list[int]:
    assigned = {abs(literal) for literal in assumptions}
    candidates = []
    for u in range(n):
        for v in range(u + 1, n):
            uv = arc_var(n, u, v)
            vu = arc_var(n, v, u)
            if uv not in assigned and vu not in assigned:
                candidates.append(uv)
    return candidates


def propagation_split_variable(
    solver: Solver,
    assumptions: list[int],
    n: int,
    candidate_limit: int = 32,
) -> tuple[int, dict[int, dict[str, Any]]]:
    """Choose a balanced split using cheap two-polarity propagation.

    This is a lightweight propagation-rate heuristic in the spirit of
    Cube-and-Conquer.  Exactness does not depend on the score: every returned
    variable is still split into both exhaustive polarities.
    """

    candidates = free_split_variables(assumptions, n)
    if not candidates:
        raise ValueError("no free unordered tournament edge remains")
    if len(candidates) > candidate_limit:
        last = len(candidates) - 1
        indexes = {
            round(index * last / (candidate_limit - 1))
            for index in range(candidate_limit)
        }
        candidates = [candidates[index] for index in sorted(indexes)]

    best_variable = candidates[0]
    best_score = (-1, -1, -1)
    best_profiles: dict[int, dict[str, Any]] = {}
    for variable in candidates:
        branch_sizes = []
        conflicts = 0
        profiles = {}
        for literal in (variable, -variable):
            consistent, propagated = solver.propagate(
                assumptions=assumptions + [literal]
            )
            if not consistent:
                conflicts += 1
            propagated_count = len(propagated or [])
            branch_sizes.append(propagated_count)
            profiles[literal] = {
                "consistent": bool(consistent),
                "propagated": propagated_count,
            }
        low, high = sorted(branch_sizes)
        score = (conflicts, low, (low + 1) * (high + 1))
        if score > best_score:
            best_score = score
            best_variable = variable
            best_profiles = profiles
    return best_variable, best_profiles


def model_to_masks(model: list[int], n: int) -> list[int]:
    positive = {literal for literal in model if literal > 0}
    out = [0] * n
    for u in range(n):
        for v in range(n):
            if u != v and arc_var(n, u, v) in positive:
                out[u] |= 1 << v
    return out


def parse_pattern_spec(value: Any) -> list[int]:
    if isinstance(value, list):
        return [int(item) for item in value]
    if isinstance(value, str) and "-" in value:
        first, last = (int(piece) for piece in value.split("-", 1))
        return list(range(first, last + 1))
    raise ValueError(f"unsupported pattern specification: {value!r}")


def load_residual_roots(manifest_path: Path) -> list[dict[str, int]]:
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    roots = []
    for parent_text, pattern_spec in manifest["unknown_by_parent"].items():
        parent = int(parent_text)
        for pattern in parse_pattern_spec(pattern_spec):
            roots.append({"parent_line": parent, "pattern": pattern})
    roots.sort(key=lambda item: (item["parent_line"], item["pattern"]))
    expected = int(manifest["source"]["unknown_children"])
    if len(roots) != expected:
        raise ValueError(f"manifest has {len(roots)} roots, expected {expected}")
    return roots


def base_assumptions(
    cube_file: Path,
    parent_line: int,
    pattern: int,
    n: int,
    source_split_depth: int,
) -> list[int]:
    parent = read_cube(cube_file, parent_line)
    variables = choose_split_variables(parent, n, source_split_depth)
    refinement = [
        variable if (pattern >> index) & 1 else -variable
        for index, variable in enumerate(variables)
    ]
    return parent + refinement


def root_key(item: dict[str, Any]) -> str:
    return f"{int(item['parent_line'])}:{int(item['pattern'])}"


def item_id(item: dict[str, Any]) -> str:
    return f"{root_key(item)}:{item['path'] or '-'}"


def atomic_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    if os.name == "nt" and path.exists():
        path.unlink()
    os.replace(temporary, path)


def config_fingerprint(config: dict[str, Any]) -> str:
    encoded = json.dumps(config, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def selected_roots(args: argparse.Namespace) -> list[dict[str, int]]:
    roots = load_residual_roots(args.manifest)
    selected = []
    for source_index, root in enumerate(roots):
        if source_index % args.partition_count != args.partition_index:
            continue
        platform_index = source_index // args.partition_count
        if platform_index % args.shard_count != args.shard_index:
            continue
        selected.append({**root, "source_index": source_index})
    return selected


def initialize_queue(
    args: argparse.Namespace,
    roots: list[dict[str, int]],
) -> list[dict[str, Any]]:
    queue = []
    for root in roots:
        base = base_assumptions(
            args.cube_file,
            root["parent_line"],
            root["pattern"],
            args.n,
            args.source_split_depth,
        )
        variables = choose_split_variables(base, args.n, args.pre_split_depth)
        for presplit_pattern in range(1 << args.pre_split_depth):
            refinements = [
                variable if (presplit_pattern >> index) & 1 else -variable
                for index, variable in enumerate(variables)
            ]
            path = "".join(
                "1" if literal > 0 else "0" for literal in refinements
            )
            queue.append(
                {
                    **root,
                    "path": path,
                    "refinements": refinements,
                    "depth": (
                        args.source_split_depth + args.pre_split_depth
                    ),
                }
            )
    return queue


def new_checkpoint(args: argparse.Namespace) -> dict[str, Any]:
    roots = selected_roots(args)
    config = {
        "model_version": MODEL_VERSION,
        "n": args.n,
        "manifest_sha256": hashlib.sha256(
            args.manifest.read_bytes()
        ).hexdigest(),
        "source_split_depth": args.source_split_depth,
        "pre_split_depth": args.pre_split_depth,
        "partition_count": args.partition_count,
        "partition_index": args.partition_index,
        "shard_count": args.shard_count,
        "shard_index": args.shard_index,
    }
    return {
        "model_version": MODEL_VERSION,
        "config": config,
        "config_fingerprint": config_fingerprint(config),
        "created_at": utc_now(),
        "updated_at": utc_now(),
        "selected_roots": roots,
        "queue": initialize_queue(args, roots),
        "closed_unsat": [],
        "errors": [],
        "found": None,
        "stats": {
            "attempts": 0,
            "unsat_leaves": 0,
            "timeouts_split": 0,
            "errors": 0,
            "solver_seconds": 0.0,
            "sessions": 0,
            "attempts_by_budget": {},
            "timeouts_by_budget": {},
            "batches": 0,
            "unit_unsat_children": 0,
        },
        "sessions": [],
    }


def validate_checkpoint(
    checkpoint: dict[str, Any],
    args: argparse.Namespace,
) -> None:
    fresh = new_checkpoint(args)
    if checkpoint.get("config_fingerprint") != fresh["config_fingerprint"]:
        raise ValueError(
            "checkpoint configuration does not match this campaign shard"
        )


def _init_worker(cnf_path: str, n: int, solver_name: str) -> None:
    global WORKER_SOLVER, WORKER_N
    formula = CNF(from_file=cnf_path)
    WORKER_SOLVER = Solver(
        name=solver_name,
        bootstrap_with=formula.clauses,
    )
    WORKER_N = n


def _worker_solve(
    assumptions: list[int],
    timeout_seconds: int,
) -> dict[str, Any]:
    if WORKER_SOLVER is None:
        raise RuntimeError("worker solver was not initialized")
    before = WORKER_SOLVER.accum_stats()
    started = time.perf_counter()
    timer = threading.Timer(timeout_seconds, WORKER_SOLVER.interrupt)
    timer.daemon = True
    timer.start()
    try:
        result = WORKER_SOLVER.solve_limited(
            assumptions=assumptions,
            expect_interrupt=True,
        )
    finally:
        timer.cancel()
        WORKER_SOLVER.clear_interrupt()
    elapsed = round(time.perf_counter() - started, 3)
    after = WORKER_SOLVER.accum_stats()
    counters = {
        name: int(after.get(name, 0)) - int(before.get(name, 0))
        for name in ("conflicts", "decisions", "propagations")
    }
    if result is None:
        split_variable, branch_profiles = propagation_split_variable(
            WORKER_SOLVER,
            assumptions,
            WORKER_N,
        )
        return {
            "status": "UNKNOWN",
            "seconds": elapsed,
            **counters,
            "split_var": split_variable,
            "branch_profiles": branch_profiles,
        }
    if result is False:
        return {"status": "UNSAT", "seconds": elapsed, **counters}
    check = verify(model_to_masks(WORKER_SOLVER.get_model(), WORKER_N))
    if not check["is_pisa"]:
        raise RuntimeError("SAT model failed independent Pisa verification")
    return {
        "status": "SAT",
        "seconds": elapsed,
        **counters,
        "verified": True,
        "witness": check,
    }


def assumptions_for_item(
    item: dict[str, Any],
    args: argparse.Namespace,
) -> list[int]:
    return base_assumptions(
        args.cube_file,
        int(item["parent_line"]),
        int(item["pattern"]),
        args.n,
        args.source_split_depth,
    ) + [int(literal) for literal in item["refinements"]]


def split_item(
    item: dict[str, Any],
    assumptions: list[int],
    n: int,
    variable: int | None = None,
    branch_profiles: dict[int, dict[str, Any]] | None = None,
    parent_result: dict[str, Any] | None = None,
) -> list[dict[str, Any]]:
    free_variables = free_split_variables(assumptions, n)
    if variable is None:
        variable = free_variables[0]
    if variable not in free_variables:
        raise ValueError(f"invalid split variable {variable}")
    branch_profiles = branch_profiles or {}
    propagated = {
        literal: int(
            branch_profiles.get(literal, {}).get("propagated", 0)
        )
        for literal in (variable, -variable)
    }
    children = []
    for bit, literal in (("0", -variable), ("1", variable)):
        sibling_literal = -literal
        relative_hardness = (
            (propagated[sibling_literal] + 1)
            / (propagated[literal] + 1)
        ) ** 0.5
        budget_factor = max(0.5, min(2.0, relative_hardness))
        children.append(
            {
                **item,
                "path": str(item["path"]) + bit,
                "refinements": list(item["refinements"]) + [literal],
                "depth": int(item["depth"]) + 1,
                "difficulty": {
                    "budget_factor": round(budget_factor, 4),
                    "lookahead_propagated": propagated[literal],
                    "sibling_propagated": propagated[sibling_literal],
                    "parent_conflicts": int(
                        (parent_result or {}).get("conflicts", 0)
                    ),
                    "parent_seconds": float(
                        (parent_result or {}).get("seconds", 0.0)
                    ),
                },
            }
        )
    return children


def refinement_generation(
    item: dict[str, Any],
    args: argparse.Namespace,
) -> int:
    initial_depth = args.source_split_depth + args.pre_split_depth
    return max(0, int(item["depth"]) - initial_depth)


def item_slice_seconds(
    item: dict[str, Any],
    args: argparse.Namespace,
) -> int:
    generation = refinement_generation(item, args)
    schedule = args.slice_schedule
    base = int(schedule[min(generation, len(schedule) - 1)])
    factor = float(
        item.get("difficulty", {}).get("budget_factor", 1.0)
    )
    adaptive = max(1, round(base * factor))
    return min(max(schedule), adaptive)


def select_batch(
    queue: list[dict[str, Any]],
    args: argparse.Namespace,
    batch_number: int,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]], str]:
    """Choose between cumulative closure and deep survivor lanes."""

    lane = "closure"
    reverse = False
    if args.queue_policy == "survivor":
        lane = "survivor"
        reverse = True
    elif args.queue_policy == "balanced" and batch_number % 4 == 0:
        lane = "survivor"
        reverse = True

    ranked = sorted(
        queue,
        key=lambda item: (
            refinement_generation(item, args),
            item_slice_seconds(item, args),
            item_id(item),
        ),
        reverse=reverse,
    )
    batch = ranked[: args.workers]
    selected = {item_id(item) for item in batch}
    remainder = [
        item for item in queue if item_id(item) not in selected
    ]
    return batch, remainder, lane


def compact_unsat_record(
    item: dict[str, Any],
    result: dict[str, Any],
) -> dict[str, Any]:
    record = {
        "id": item_id(item),
        "parent_line": int(item["parent_line"]),
        "pattern": int(item["pattern"]),
        "source_index": int(item["source_index"]),
        "path": str(item["path"]),
        "depth": int(item["depth"]),
        "seconds": float(result["seconds"]),
    }
    if result.get("proof"):
        record["proof"] = str(result["proof"])
    return record


def derive_progress(checkpoint: dict[str, Any]) -> dict[str, Any]:
    pending_roots = {root_key(item) for item in checkpoint["queue"]}
    all_roots = {
        f"{root['parent_line']}:{root['pattern']}"
        for root in checkpoint["selected_roots"]
    }
    return {
        "selected_root_count": len(all_roots),
        "roots_closed": len(all_roots - pending_roots),
        "roots_open": len(pending_roots),
        "pending_leaves": len(checkpoint["queue"]),
        "closed_unsat_leaves": len(checkpoint["closed_unsat"]),
        "max_depth_reached": max(
            [
                int(item["depth"])
                for item in checkpoint["queue"]
                + checkpoint["closed_unsat"]
            ],
            default=0,
        ),
    }


def save_state(
    checkpoint: dict[str, Any],
    args: argparse.Namespace,
) -> None:
    checkpoint["updated_at"] = utc_now()
    checkpoint["progress"] = derive_progress(checkpoint)
    atomic_json(args.checkpoint, checkpoint)
    summary = {
        "model_version": MODEL_VERSION,
        "status": (
            "SAT"
            if checkpoint["found"]
            else (
                "CLOSED"
                if not checkpoint["queue"]
                else "CHECKPOINTED"
            )
        ),
        "updated_at": checkpoint["updated_at"],
        "config": checkpoint["config"],
        "stats": checkpoint["stats"],
        "progress": checkpoint["progress"],
        "found": checkpoint["found"],
        "checkpoint": str(args.checkpoint),
    }
    atomic_json(args.output, summary)


def run(args: argparse.Namespace) -> dict[str, Any]:
    if args.checkpoint.exists():
        checkpoint = json.loads(
            args.checkpoint.read_text(encoding="utf-8")
        )
        validate_checkpoint(checkpoint, args)
        resumed = True
    else:
        checkpoint = new_checkpoint(args)
        resumed = False

    session = {
        "started_at": utc_now(),
        "resumed": resumed,
        "wall_budget_seconds": args.wall_seconds,
        "slice_seconds": args.slice_seconds,
        "slice_schedule": args.slice_schedule,
        "workers": args.workers,
        "starting_progress": derive_progress(checkpoint),
    }
    checkpoint["stats"].setdefault("attempts_by_budget", {})
    checkpoint["stats"].setdefault("timeouts_by_budget", {})
    checkpoint["stats"].setdefault("batches", 0)
    checkpoint["stats"].setdefault("unit_unsat_children", 0)
    checkpoint["stats"]["sessions"] += 1
    checkpoint["sessions"].append(session)
    save_state(checkpoint, args)

    stop_requested = False

    def request_stop(_signum: int, _frame: object) -> None:
        nonlocal stop_requested
        stop_requested = True

    signal.signal(signal.SIGTERM, request_stop)
    if hasattr(signal, "SIGINT"):
        signal.signal(signal.SIGINT, request_stop)

    started = time.monotonic()
    with ProcessPoolExecutor(
        max_workers=args.workers,
        initializer=_init_worker,
        initargs=(str(args.cnf), args.n, args.solver),
    ) as executor:
        while checkpoint["queue"] and not checkpoint["found"]:
            elapsed = time.monotonic() - started
            batch_number = int(checkpoint["stats"]["batches"]) + 1
            batch, remainder, lane = select_batch(
                checkpoint["queue"],
                args,
                batch_number,
            )
            batch_budgets = [
                item_slice_seconds(item, args) for item in batch
            ]
            reserve = max(30, max(batch_budgets) + 10)
            if (
                stop_requested
                or elapsed + reserve >= args.wall_seconds
            ):
                break

            checkpoint["queue"] = remainder
            checkpoint["stats"]["batches"] = batch_number
            futures = {}
            for item, slice_seconds in zip(batch, batch_budgets):
                assumptions = assumptions_for_item(item, args)
                future = executor.submit(
                    _worker_solve,
                    assumptions,
                    slice_seconds,
                )
                futures[future] = (item, assumptions, slice_seconds)

            batch_results = []
            for future in as_completed(futures):
                item, assumptions, slice_seconds = futures[future]
                try:
                    result = future.result()
                except Exception as error:
                    result = {
                        "status": "ERROR",
                        "seconds": 0.0,
                        "error": repr(error),
                    }
                batch_results.append(
                    (item, assumptions, slice_seconds, result)
                )

            batch_results.sort(key=lambda entry: item_id(entry[0]))
            for item, assumptions, slice_seconds, result in batch_results:
                status = result["status"]
                checkpoint["stats"]["attempts"] += 1
                budget_key = str(slice_seconds)
                attempts_by_budget = checkpoint["stats"][
                    "attempts_by_budget"
                ]
                attempts_by_budget[budget_key] = (
                    int(attempts_by_budget.get(budget_key, 0)) + 1
                )
                checkpoint["stats"]["solver_seconds"] = round(
                    float(checkpoint["stats"]["solver_seconds"])
                    + float(result.get("seconds", 0.0)),
                    3,
                )
                if status == "UNSAT":
                    checkpoint["closed_unsat"].append(
                        compact_unsat_record(item, result)
                    )
                    checkpoint["stats"]["unsat_leaves"] += 1
                elif status == "SAT":
                    checkpoint["found"] = {
                        "item": item,
                        "result": result,
                    }
                elif status == "UNKNOWN":
                    raw_profiles = result.get("branch_profiles", {})
                    branch_profiles = {
                        int(literal): profile
                        for literal, profile in raw_profiles.items()
                    }
                    children = split_item(
                        item,
                        assumptions,
                        args.n,
                        int(result["split_var"]),
                        branch_profiles,
                        result,
                    )
                    for child in children:
                        literal = int(child["refinements"][-1])
                        profile = branch_profiles.get(literal, {})
                        if not profile.get("consistent", True):
                            checkpoint["closed_unsat"].append(
                                compact_unsat_record(
                                    child,
                                    {
                                        "status": "UNSAT",
                                        "seconds": 0.0,
                                        "proof": (
                                            "unit propagation after "
                                            "timed parent solve"
                                        ),
                                    },
                                )
                            )
                            checkpoint["stats"]["unsat_leaves"] += 1
                            checkpoint["stats"][
                                "unit_unsat_children"
                            ] += 1
                        else:
                            checkpoint["queue"].append(child)
                    checkpoint["stats"]["timeouts_split"] += 1
                    timeouts_by_budget = checkpoint["stats"][
                        "timeouts_by_budget"
                    ]
                    timeouts_by_budget[budget_key] = (
                        int(timeouts_by_budget.get(budget_key, 0)) + 1
                    )
                else:
                    checkpoint["queue"].append(item)
                    checkpoint["stats"]["errors"] += 1
                    checkpoint["errors"].append(
                        {
                            "id": item_id(item),
                            "at": utc_now(),
                            "error": result.get("error", "unknown worker error"),
                        }
                    )
                    stop_requested = True

                print(
                    "leaf",
                    item_id(item),
                    status,
                    result.get("seconds"),
                    "conflicts",
                    result.get("conflicts"),
                    "generation",
                    refinement_generation(item, args),
                    "budget",
                    slice_seconds,
                    "lane",
                    lane,
                    "pending",
                    len(checkpoint["queue"]),
                    flush=True,
                )

            save_state(checkpoint, args)

    session["finished_at"] = utc_now()
    session["wall_seconds"] = round(time.monotonic() - started, 3)
    session["ending_progress"] = derive_progress(checkpoint)
    save_state(checkpoint, args)
    return checkpoint


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cnf", type=Path, required=True)
    parser.add_argument("--cube-file", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--checkpoint", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--n", type=int, default=16)
    parser.add_argument("--source-split-depth", type=int, default=6)
    parser.add_argument("--pre-split-depth", type=int, default=3)
    parser.add_argument("--partition-count", type=int, default=1)
    parser.add_argument("--partition-index", type=int, default=0)
    parser.add_argument("--shard-count", type=int, default=1)
    parser.add_argument("--shard-index", type=int, default=0)
    parser.add_argument("--slice-seconds", type=int, default=180)
    parser.add_argument(
        "--slice-schedule",
        default="",
        help=(
            "Comma-separated per-generation budgets. The last value is "
            "reused for every deeper generation. Example: 180,1800,7200. "
            "If omitted, --slice-seconds is used at every depth."
        ),
    )
    parser.add_argument("--wall-seconds", type=int, default=3600)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument(
        "--queue-policy",
        choices=("closure", "survivor", "balanced"),
        default="balanced",
        help=(
            "closure prefers shallow leaves, survivor follows deepest "
            "timeouts, and balanced sends every fourth batch down the "
            "survivor lane."
        ),
    )
    parser.add_argument(
        "--solver",
        default="glucose42",
        help=(
            "PySAT backend with interrupt support. CaDiCaL cannot be used "
            "here because PySAT does not expose its interruptible solve."
        ),
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.slice_schedule:
        try:
            args.slice_schedule = [
                int(piece.strip())
                for piece in args.slice_schedule.split(",")
                if piece.strip()
            ]
        except ValueError as error:
            raise SystemExit(
                "--slice-schedule must contain integers"
            ) from error
    else:
        args.slice_schedule = [args.slice_seconds]
    if not args.slice_schedule or any(
        seconds < 1 for seconds in args.slice_schedule
    ):
        raise SystemExit("--slice-schedule budgets must be positive")
    for name in ("partition", "shard"):
        count = getattr(args, f"{name}_count")
        index = getattr(args, f"{name}_index")
        if count < 1 or not 0 <= index < count:
            raise SystemExit(f"bad {name} index/count: {index}/{count}")
    if args.workers < 1:
        raise SystemExit("--workers must be positive")
    if args.slice_seconds < 1:
        raise SystemExit("--slice-seconds must be positive")
    if args.wall_seconds <= min(args.slice_schedule) + 30:
        raise SystemExit(
            "wall budget must exceed the shortest scheduled slice "
            "plus 30 seconds"
        )

    checkpoint = run(args)
    print(
        json.dumps(
            {
                "status": (
                    "SAT"
                    if checkpoint["found"]
                    else (
                        "CLOSED"
                        if not checkpoint["queue"]
                        else "CHECKPOINTED"
                    )
                ),
                "progress": derive_progress(checkpoint),
                "stats": checkpoint["stats"],
                "checkpoint": str(args.checkpoint),
                "output": str(args.output),
            },
            indent=2,
        ),
        flush=True,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
