#!/usr/bin/env python3
"""V19 strategy pilot on a fixed sample of the v18 UNKNOWN frontier.

The pilot compares three exact routes on the same 24 open leaves:

* SMS on the unsplit leaf for 900 seconds;
* a four-way exact MOMS split, with 120 seconds per child;
* plain CaDiCaL 3.0.1 on the SMS-enriched CNF for 900 seconds.

The pilot is deliberately small.  It chooses the next full campaign by
complete parent closures per CPU hour instead of blindly doubling every
UNKNOWN leaf.
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
import time
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = REPO_ROOT / "scripts"
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from k16_smart_deepen import (  # noqa: E402
    ARC_LINE,
    ARC_PAIR,
    CUBE_RESULT,
    Dimacs,
    N,
    cube_hash,
    cube_line,
    parse_sms_arcs,
    read_cubes,
    sha256,
    write_json,
)


MODEL_VERSION = "k16-pisa-v19-strategy-pilot-20260728"
CADICAL_VERSION = "3.0.1"
CADICAL_COMMIT = "c60730422e758ef1cebe7aeddf2dda31c996bf04"
INDEPENDENT_VERIFIER = SCRIPTS / "verify_primitive_witness.py"
METHODS = {
    "sms900": {
        "solver": "sms",
        "seconds": 900,
        "children_per_parent": 1,
    },
    "deep4_sms120": {
        "solver": "sms",
        "seconds": 120,
        "maximum_children_per_parent": 4,
    },
    "cadical900": {
        "solver": "cadical",
        "seconds": 900,
        "children_per_parent": 1,
    },
}
QUOTAS = {
    ("a1_z3", "untested_original"): 9,
    ("a1_z3", "split_unknown"): 3,
    ("a2p_z4p", "untested_original"): 9,
    ("a2p_z4p", "split_unknown"): 3,
}


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def locate_one(root: Path, name: str) -> Path:
    matches = sorted(root.rglob(name))
    if len(matches) != 1:
        raise RuntimeError(f"expected one {name} below {root}, got {matches}")
    return matches[0]


def stratified(items: list[dict], wanted: int) -> list[dict]:
    if wanted <= 0:
        return []
    if len(items) < wanted:
        raise RuntimeError(f"cannot draw {wanted} records from {len(items)}")
    if wanted == 1:
        return [items[len(items) // 2]]
    indexes = {
        round(position * (len(items) - 1) / (wanted - 1))
        for position in range(wanted)
    }
    if len(indexes) != wanted:
        raise RuntimeError("stratified selection produced duplicate positions")
    return [items[index] for index in sorted(indexes)]


def copy_file_tree(source: Path, destination: Path) -> None:
    if destination.exists():
        shutil.rmtree(destination)
    shutil.copytree(source, destination)


def deep4(dimacs: Dimacs, root: list[int]) -> tuple[list[list[int]], dict]:
    _, root_contradiction = dimacs.propagate(root)
    if root_contradiction:
        raise RuntimeError("a v18 solver UNKNOWN root is unit-inconsistent")
    frontier = [root]
    planner_unsat: list[list[int]] = []
    levels: list[list[dict]] = []
    for depth in range(2):
        next_frontier = []
        level_record = []
        for cube in frontier:
            variable, moms = dimacs.moms_arc_variable(cube)
            node = {
                "depth": depth,
                "parent_sha256": cube_hash(cube),
                "branch_variable": variable,
                "moms": moms,
                "children": [],
            }
            for literal in (variable, -variable):
                child = cube + [literal]
                _, contradiction = dimacs.propagate(child)
                node["children"].append({
                    "literal": literal,
                    "cube_sha256": cube_hash(child),
                    "unit_contradiction": contradiction,
                })
                if contradiction:
                    planner_unsat.append(child)
                else:
                    next_frontier.append(child)
            level_record.append(node)
        levels.append(level_record)
        frontier = next_frontier
    terminal_hashes = {
        cube_hash(cube) for cube in frontier + planner_unsat
    }
    if len(terminal_hashes) != len(frontier) + len(planner_unsat):
        raise RuntimeError("adaptive deep4 produced duplicate terminals")
    return frontier, {
        "levels": levels,
        "open_children": len(frontier),
        "planner_unit_unsat_children": len(planner_unsat),
        "planner_unit_unsat_sha256": [
            cube_hash(cube) for cube in planner_unsat
        ],
        "coverage": (
            "Two consecutive complementary binary decisions exactly cover "
            "the selected v18 UNKNOWN leaf. Unit-inconsistent terminals are "
            "closed by deterministic propagation; only consistent terminals "
            "become SMS tasks."
        ),
    }


def plan(
    *,
    v18_source: Path,
    v18_ledger_path: Path,
    cadical_source: Path | None,
    output: Path,
    matrix_output: Path,
    source_run_id: str,
) -> dict:
    queue_manifest_path = v18_source / "queue-manifest.json"
    queue_manifest = json.loads(
        queue_manifest_path.read_text(encoding="utf-8")
    )
    ledger = json.loads(v18_ledger_path.read_text(encoding="utf-8"))
    if ledger["logical_conclusion"] != "V18_COMPLETE_TARGETS_STILL_OPEN":
        raise RuntimeError("unexpected v18 ledger conclusion")
    if ledger["results_received"] != 237 or ledger["missing_queue_ids"]:
        raise RuntimeError("v18 ledger is incomplete")
    if ledger["verified_sat_witnesses"]:
        raise RuntimeError("v18 already contains a verified SAT witness")

    queue_by_id = {
        item["queue_id"]: item for item in queue_manifest["queue"]
    }
    open_results = [
        result for result in ledger["results"]
        if result["status"] == "UNKNOWN"
    ]
    if len(open_results) != 139:
        raise RuntimeError(f"expected 139 UNKNOWN leaves, got {len(open_results)}")

    groups: dict[tuple[str, str], list[dict]] = defaultdict(list)
    for result in open_results:
        item = queue_by_id.get(result["queue_id"])
        if item is None:
            raise RuntimeError(f"queue item missing for {result['queue_id']}")
        if item["cube_literals"] != result["cube_literals"]:
            raise RuntimeError(f"cube mismatch for {result['queue_id']}")
        groups[(item["box"], item["kind"])].append(item)
    for items in groups.values():
        items.sort(key=lambda item: item["queue_id"])

    selected: list[dict] = []
    for key, wanted in QUOTAS.items():
        selected.extend(stratified(groups[key], wanted))
    selected.sort(key=lambda item: (item["box"], item["kind"], item["queue_id"]))
    if len(selected) != 24 or len({item["queue_id"] for item in selected}) != 24:
        raise RuntimeError("pilot selection is not 24 distinct leaves")

    output.mkdir(parents=True, exist_ok=True)
    copy_file_tree(v18_source / "bundle", output / "bundle")
    for box in ("a1_z3", "a2p_z4p"):
        destination = output / "boxes" / box
        destination.mkdir(parents=True, exist_ok=True)
        for name in ("enriched.cnf", "manifest.json"):
            shutil.copy2(v18_source / "boxes" / box / name, destination / name)
    if cadical_source is not None:
        cadical = locate_one(cadical_source, "cadical")
        destination = output / "cadical"
        destination.mkdir(parents=True, exist_ok=True)
        shutil.copy2(cadical, destination / "cadical")

    dimacs_by_box = {
        box: Dimacs(output / "boxes" / box / "enriched.cnf")
        for box in ("a1_z3", "a2p_z4p")
    }
    tasks: list[dict] = []
    split_trees: dict[str, dict] = {}
    sms_queues: dict[str, list[dict]] = {
        "sms900": [],
        "deep4_sms120": [],
    }

    for parent in selected:
        root_id = parent["queue_id"]
        cube = list(parent["cube_literals"])
        common = {
            "box": parent["box"],
            "root_id": root_id,
            "root_kind": parent["kind"],
            "root_cube_sha256": cube_hash(cube),
        }
        sms_queues["sms900"].append({
            **common,
            "method": "sms900",
            "child_index": 0,
            "cube_literals": cube,
        })
        tasks.append({
            **common,
            "method": "cadical900",
            "child_index": 0,
            "cube_literals": cube,
            "task_id": f"cadical900-{root_id}",
        })

        children, tree = deep4(dimacs_by_box[parent["box"]], cube)
        split_trees[root_id] = tree
        for child_index, child in enumerate(children):
            sms_queues["deep4_sms120"].append({
                **common,
                "method": "deep4_sms120",
                "child_index": child_index,
                "cube_literals": child,
            })

    for method, items in sms_queues.items():
        queue_path = output / "queues" / f"{method}.cubes"
        queue_path.parent.mkdir(parents=True, exist_ok=True)
        queue_path.write_text(
            "\n".join(cube_line(item["cube_literals"]) for item in items) + "\n",
            encoding="utf-8",
        )
        for queue_line, item in enumerate(items, start=1):
            task = {
                **item,
                "queue_line": queue_line,
                "queue_file": f"queues/{method}.cubes",
                "task_id": (
                    f"{method}-{item['root_id']}-g{item['child_index']:02d}"
                ),
            }
            tasks.append(task)

    tasks.sort(key=lambda item: item["task_id"])
    for task in tasks:
        task["cube_depth"] = len(task["cube_literals"])
        task["cube_sha256"] = cube_hash(task["cube_literals"])
        task["seconds"] = METHODS[task["method"]]["seconds"]
        task["solver"] = METHODS[task["method"]]["solver"]
    if len(tasks) != len({task["task_id"] for task in tasks}):
        raise RuntimeError("pilot task matrix contains duplicate jobs")

    method_counts = Counter(task["method"] for task in tasks)
    if (
        method_counts["sms900"] != 24
        or method_counts["cadical900"] != 24
        or not 0 <= method_counts["deep4_sms120"] <= 96
    ):
        raise RuntimeError(f"bad pilot matrix: {method_counts}")

    record = {
        "schema": "k16-v19-strategy-plan-v1",
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "source_run_id": source_run_id,
        "v18_source_manifest_sha256": sha256(queue_manifest_path),
        "v18_ledger_sha256": sha256(v18_ledger_path),
        "cadical": {
            "version": CADICAL_VERSION,
            "commit": CADICAL_COMMIT,
            "binary_sha256": (
                sha256(output / "cadical" / "cadical")
                if cadical_source is not None else None
            ),
        },
        "selection": {
            "frontier_unknown_leaves": len(open_results),
            "quotas": {
                f"{box}:{kind}": count
                for (box, kind), count in QUOTAS.items()
            },
            "selected_leaves": [
                {
                    "queue_id": item["queue_id"],
                    "box": item["box"],
                    "kind": item["kind"],
                    "cube_sha256": cube_hash(item["cube_literals"]),
                }
                for item in selected
            ],
        },
        "methods": METHODS,
        "split_trees": split_trees,
        "tasks": tasks,
        "coverage": (
            "This is a strategy pilot over 24 fixed v18 UNKNOWN leaves. "
            "Each deep4 family exactly covers its selected leaf, but the "
            "pilot does not cover the other 115 UNKNOWN frontier leaves."
        ),
    }
    write_json(output / "pilot-manifest.json", record)
    matrix = {
        "include": [
            {
                "task_id": task["task_id"],
                "method": task["method"],
                "box": task["box"],
            }
            for task in tasks
        ]
    }
    matrix_output.write_text(
        json.dumps(matrix, separators=(",", ":")) + "\n",
        encoding="utf-8",
    )
    print(json.dumps({
        "selected": len(selected),
        "tasks": len(tasks),
        "method_counts": dict(method_counts),
    }), flush=True)
    return record


def run_limited(
    command: list[str],
    *,
    timeout_seconds: int,
) -> tuple[int, str, bool, float]:
    started = time.monotonic()
    try:
        completed = subprocess.run(
            command,
            capture_output=True,
            text=True,
            check=False,
            timeout=timeout_seconds,
        )
        return (
            completed.returncode,
            completed.stdout + completed.stderr,
            False,
            time.monotonic() - started,
        )
    except subprocess.TimeoutExpired as exc:
        stdout = (
            exc.stdout.decode()
            if isinstance(exc.stdout, bytes)
            else (exc.stdout or "")
        )
        stderr = (
            exc.stderr.decode()
            if isinstance(exc.stderr, bytes)
            else (exc.stderr or "")
        )
        return (
            0,
            stdout + stderr + "\nV19 WRAPPER TIMEOUT\n",
            True,
            time.monotonic() - started,
        )


def write_assumption_cnf(source: Path, destination: Path, cube: list[int]) -> None:
    destination.parent.mkdir(parents=True, exist_ok=True)
    with source.open("r", encoding="utf-8") as reader:
        header = reader.readline().strip()
        fields = header.split()
        if len(fields) != 4 or fields[:2] != ["p", "cnf"]:
            raise RuntimeError("unexpected enriched DIMACS header")
        variables = int(fields[2])
        clauses = int(fields[3])
        with destination.open("w", encoding="utf-8") as writer:
            writer.write(f"p cnf {variables} {clauses + len(cube)}\n")
            shutil.copyfileobj(reader, writer)
            for literal in cube:
                writer.write(f"{literal} 0\n")


def parse_cadical_assignment(text: str) -> dict[int, bool]:
    assignment: dict[int, bool] = {}
    for raw in text.splitlines():
        line = raw.strip()
        if not line.startswith("v "):
            continue
        for field in line.split()[1:]:
            literal = int(field)
            if literal == 0:
                continue
            assignment[abs(literal)] = literal > 0
    return assignment


def arc_variable(u: int, v: int) -> int:
    if u == v:
        raise ValueError((u, v))
    offset = v + 1 if v < u else v
    return u * (N - 1) + offset


def assignment_to_arcs(assignment: dict[int, bool]) -> list[list[int]]:
    arcs: list[list[int]] = []
    for u in range(N):
        for v in range(u + 1, N):
            forward = arc_variable(u, v)
            reverse = arc_variable(v, u)
            if forward not in assignment or reverse not in assignment:
                raise RuntimeError("CaDiCaL model omitted an arc variable")
            if assignment[forward] == assignment[reverse]:
                raise RuntimeError("CaDiCaL model violates tournament orientation")
            arcs.append([u, v] if assignment[forward] else [v, u])
    return arcs


def independent_audit(
    *,
    arcs: list[list[int]],
    box: str,
    directory: Path,
) -> tuple[bool, dict]:
    candidate = directory / "candidate.json"
    audit_path = directory / "audit.json"
    write_json(candidate, {"n": N, "arcs": arcs})
    completed = subprocess.run(
        [
            sys.executable,
            str(INDEPENDENT_VERIFIER),
            "--input", str(candidate),
            "--output", str(audit_path),
            "--box", box,
        ],
        capture_output=True,
        text=True,
        check=False,
    )
    audit = (
        json.loads(audit_path.read_text(encoding="utf-8"))
        if audit_path.exists()
        else {"valid": False, "error": "standalone verifier wrote no audit"}
    )
    audit["process_exit_code"] = completed.returncode
    return completed.returncode == 0 and bool(audit.get("valid")), audit


def solve(
    *,
    source: Path,
    task_id: str,
    result_path: Path,
    log_path: Path,
) -> dict:
    manifest = json.loads(
        (source / "pilot-manifest.json").read_text(encoding="utf-8")
    )
    matches = [task for task in manifest["tasks"] if task["task_id"] == task_id]
    if len(matches) != 1:
        raise RuntimeError(f"task lookup failed: {task_id}")
    task = matches[0]
    seconds = int(task["seconds"])
    box = task["box"]
    cnf = source / "boxes" / box / "enriched.cnf"
    work = result_path.parent / f"{task_id}-work"
    work.mkdir(parents=True, exist_ok=True)

    if task["solver"] == "sms":
        queue_file = source / task["queue_file"]
        cubes = read_cubes(queue_file)
        cube = cubes[int(task["queue_line"]) - 1]
        if cube != task["cube_literals"]:
            raise RuntimeError("SMS queue line differs from pilot manifest")
        command = [
            str(source / "bundle" / "smsg"),
            "--vertices", str(N),
            "--directed",
            "--dimacs", str(cnf),
            "--cube-file", str(queue_file),
            "--cube-line", str(task["queue_line"]),
            "--cube-timeout", str(seconds),
        ]
        returncode, text, timed_out, elapsed = run_limited(
            command,
            timeout_seconds=seconds + 90,
        )
        matches = CUBE_RESULT.findall(text)
        raw_result = int(matches[-1]) if matches else 0
        status = {10: "SAT", 20: "UNSAT"}.get(raw_result, "UNKNOWN")
        arcs = parse_sms_arcs(text) if status == "SAT" else None
    else:
        assumption_cnf = work / "assumption.cnf"
        write_assumption_cnf(cnf, assumption_cnf, task["cube_literals"])
        command = [str(source / "cadical" / "cadical"), str(assumption_cnf)]
        returncode, text, timed_out, elapsed = run_limited(
            command,
            timeout_seconds=seconds,
        )
        status = {10: "SAT", 20: "UNSAT"}.get(returncode, "UNKNOWN")
        raw_result = returncode if returncode in {10, 20} else 0
        arcs = (
            assignment_to_arcs(parse_cadical_assignment(text))
            if status == "SAT" else None
        )
    if timed_out:
        status = "UNKNOWN"
    log_path.parent.mkdir(parents=True, exist_ok=True)
    log_path.write_text(text, encoding="utf-8")

    record: dict = {
        "schema": "k16-v19-strategy-result-v1",
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "task_id": task_id,
        "method": task["method"],
        "solver": task["solver"],
        "box": box,
        "root_id": task["root_id"],
        "root_kind": task["root_kind"],
        "child_index": task["child_index"],
        "cube_literals": task["cube_literals"],
        "cube_sha256": task["cube_sha256"],
        "status": status,
        "seconds": round(elapsed, 3),
        "time_limit_seconds": seconds,
        "returncode": returncode,
        "raw_result": raw_result,
        "timed_out": timed_out,
        "solver_level_exact": status == "UNSAT",
        "verified": False,
    }
    if status == "SAT":
        if arcs is None:
            write_json(result_path, record)
            raise RuntimeError("SAT result has no parseable tournament")
        verified, audit = independent_audit(
            arcs=arcs,
            box=box,
            directory=work,
        )
        record["candidate_arcs"] = arcs
        record["independent_audit"] = audit
        record["verified"] = verified
        if not verified:
            write_json(result_path, record)
            raise RuntimeError("SAT candidate failed independent verification")

    write_json(result_path, record)
    print(json.dumps(record, indent=2), flush=True)
    return record


def aggregate(
    *,
    source: Path,
    results_root: Path,
    output: Path,
) -> dict:
    manifest = json.loads(
        (source / "pilot-manifest.json").read_text(encoding="utf-8")
    )
    records = []
    for path in sorted(results_root.rglob("*.json")):
        record = json.loads(path.read_text(encoding="utf-8"))
        if record.get("schema") == "k16-v19-strategy-result-v1":
            records.append(record)
    by_id = {record["task_id"]: record for record in records}
    missing = [
        task["task_id"] for task in manifest["tasks"]
        if task["task_id"] not in by_id
    ]
    if len(by_id) != len(records):
        raise RuntimeError("duplicate v19 result identifiers")

    selected_ids = {
        item["queue_id"] for item in manifest["selection"]["selected_leaves"]
    }
    method_summary: dict[str, dict] = {}
    closure_sets: dict[str, set[str]] = {}
    for method, settings in manifest["methods"].items():
        method_records = [
            record for record in records if record["method"] == method
        ]
        by_root: dict[str, list[dict]] = defaultdict(list)
        for record in method_records:
            by_root[record["root_id"]].append(record)
        closed = {
            root_id
            for root_id in selected_ids
            if (
                (
                    manifest["split_trees"][root_id]["open_children"]
                    if method == "deep4_sms120" else 1
                )
                == len(by_root.get(root_id, []))
                and all(
                    item["status"] == "UNSAT"
                    for item in by_root.get(root_id, [])
                )
            )
        }
        closure_sets[method] = closed
        cpu_seconds = sum(float(record["seconds"]) for record in method_records)
        expected_results = (
            sum(
                manifest["split_trees"][root_id]["open_children"]
                for root_id in selected_ids
            )
            if method == "deep4_sms120"
            else len(selected_ids)
        )
        method_missing = expected_results - len(method_records)
        planner_closed = (
            sum(
                manifest["split_trees"][root_id][
                    "planner_unit_unsat_children"
                ]
                for root_id in selected_ids
            )
            if method == "deep4_sms120" else 0
        )
        method_summary[method] = {
            "solver": settings["solver"],
            "seconds_per_task": settings["seconds"],
            "expected_results": expected_results,
            "planner_unit_unsat_terminals": planner_closed,
            "results": len(method_records),
            "missing_results": method_missing,
            "statuses": dict(Counter(
                record["status"] for record in method_records
            )),
            "cpu_seconds": round(cpu_seconds, 3),
            "cpu_hours": round(cpu_seconds / 3600, 4),
            "parents_closed": len(closed),
            "closed_root_ids": sorted(closed),
            "parent_closure_rate": round(len(closed) / len(selected_ids), 4),
            "closures_per_cpu_hour": (
                round(len(closed) * 3600 / cpu_seconds, 4)
                if cpu_seconds else 0.0
            ),
        }

    verified_sat = [
        record["task_id"] for record in records
        if record["status"] == "SAT" and record.get("verified")
    ]
    eligible = [
        (method, summary)
        for method, summary in method_summary.items()
        if summary["missing_results"] == 0
    ]
    winner = (
        max(
            eligible,
            key=lambda pair: (
                pair[1]["closures_per_cpu_hour"],
                pair[1]["parents_closed"],
            ),
        )[0]
        if eligible else None
    )
    union_closed = set().union(*closure_sets.values()) if closure_sets else set()
    if verified_sat:
        conclusion = "SAT_K16_VERIFIED"
    elif missing:
        conclusion = "V19_PARTIAL_INFRASTRUCTURE_FAILURE"
    else:
        conclusion = "V19_PILOT_COMPLETE_K16_OPEN"
    record = {
        "schema": "k16-v19-strategy-ledger-v1",
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "source_run_id": manifest["source_run_id"],
        "selected_parent_leaves": len(selected_ids),
        "results_received": len(records),
        "missing_task_ids": missing,
        "verified_sat_witnesses": verified_sat,
        "method_summary": method_summary,
        "recommended_method": winner,
        "parents_closed_by_any_method": len(union_closed),
        "parent_ids_closed_by_any_method": sorted(union_closed),
        "logical_conclusion": conclusion,
        "next_action": (
            "Use the recommended method on the untouched v18 UNKNOWN "
            "frontier, retaining every solver-level UNSAT result. Do not "
            "treat UNKNOWN as an exclusion."
        ),
        "results": records,
    }
    write_json(output, record)
    print(json.dumps({
        "conclusion": conclusion,
        "recommended_method": winner,
        "method_summary": method_summary,
    }, indent=2), flush=True)
    return record


def main() -> None:
    parser = argparse.ArgumentParser()
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--plan", action="store_true")
    modes.add_argument("--solve", action="store_true")
    modes.add_argument("--aggregate", action="store_true")
    parser.add_argument("--v18-source", type=Path)
    parser.add_argument("--v18-ledger", type=Path)
    parser.add_argument("--cadical-source", type=Path)
    parser.add_argument("--source-run-id", default="30332755449")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--matrix-output", type=Path)
    parser.add_argument("--source", type=Path)
    parser.add_argument("--task-id")
    parser.add_argument("--result", type=Path)
    parser.add_argument("--log", type=Path)
    parser.add_argument("--results-root", type=Path)
    args = parser.parse_args()

    if args.plan:
        required = (
            args.v18_source, args.v18_ledger,
            args.output, args.matrix_output,
        )
        if any(value is None for value in required):
            parser.error(
                "--plan requires --v18-source --v18-ledger "
                "--output --matrix-output"
            )
        plan(
            v18_source=args.v18_source,
            v18_ledger_path=args.v18_ledger,
            cadical_source=args.cadical_source,
            output=args.output,
            matrix_output=args.matrix_output,
            source_run_id=args.source_run_id,
        )
    elif args.solve:
        required = (args.source, args.task_id, args.result, args.log)
        if any(value is None for value in required):
            parser.error("--solve requires --source --task-id --result --log")
        solve(
            source=args.source,
            task_id=args.task_id,
            result_path=args.result,
            log_path=args.log,
        )
    else:
        required = (args.source, args.results_root, args.output)
        if any(value is None for value in required):
            parser.error(
                "--aggregate requires --source --results-root --output"
            )
        aggregate(
            source=args.source,
            results_root=args.results_root,
            output=args.output,
        )


if __name__ == "__main__":
    main()
