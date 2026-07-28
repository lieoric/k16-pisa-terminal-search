#!/usr/bin/env python3
"""V21 theorem-cut, complexity-budgeted continuation of the V20 ledger.

The campaign starts from exactly the 81 logical UNKNOWN leaves in the final
V20 ledger.  It never resubmits a V20 closure.  Historical SMS preprocessing
clauses are retained after a byte-for-byte base-CNF compatibility check, and
only proved theorem clauses are appended.

Each surviving leaf receives a depth-dependent long budget:

* depth <= 6: CaDiCaL 60 minutes, SMS 120 minutes;
* depth == 7: CaDiCaL 45 minutes, SMS 90 minutes;
* depth >= 8: CaDiCaL 30 minutes, SMS 60 minutes.

SAT is accepted only after the standalone primitive K16 verifier succeeds.
UNSAT is a solver-level exact closure.  UNKNOWN remains open.
"""

from __future__ import annotations

import argparse
import itertools
import json
import re
import shutil
import subprocess
import sys
import time
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path

from pysat.solvers import Solver

REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = REPO_ROOT / "scripts"
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from k16_primitive_sms import (  # noqa: E402
    LANES,
    Lane,
    fixed_arcs,
    mathematical_acceptance,
)
from k16_smart_deepen import (  # noqa: E402
    CUBE_RESULT,
    N,
    cube_hash,
    cube_line,
    parse_sms_arcs,
    sha256,
    write_json,
)
from k16_staged_cascade import (  # noqa: E402
    assignment_to_arcs,
    independent_audit,
    parse_cadical_assignment,
    run_limited,
    write_assumption_cnf,
)
from k16_theorem_cuts import (  # noqa: E402
    MODEL_VERSION as CUT_MODEL_VERSION,
    build_theorem_cnf,
)


MODEL_VERSION = "k16-pisa-v21-theorem-long-cascade-20260728"
PLAN_SCHEMA = "k16-v21-theorem-cascade-plan-v1"
RESULT_SCHEMA = "k16-v21-theorem-cascade-result-v1"
CADICAL_LEDGER_SCHEMA = "k16-v21-cadical-stage-ledger-v1"
FINAL_LEDGER_SCHEMA = "k16-v21-theorem-cascade-ledger-v1"
V20_LEDGER_SCHEMA = "k16-v20-cascade-ledger-v1"
V20_FRONTIER_SIZE = 139
EXPECTED_V20_CLOSED = 58
EXPECTED_V20_OPEN = 81


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def collect_records(root: Path) -> list[dict]:
    records = []
    for path in sorted(root.rglob("*.json")):
        record = load_json(path)
        if record.get("schema") == RESULT_SCHEMA:
            records.append(record)
    task_ids = [record["task_id"] for record in records]
    if len(task_ids) != len(set(task_ids)):
        raise RuntimeError("duplicate V21 result identifiers")
    return records


def locate_file(root: Path, name: str) -> Path:
    matches = sorted(
        path for path in root.rglob(name) if path.is_file()
    )
    if len(matches) != 1:
        raise RuntimeError(
            f"expected one file {name} below {root}, got {matches}"
        )
    return matches[0]


def budget_for_depth(depth: int) -> tuple[int, int, str]:
    if depth <= 6:
        return 3600, 7200, "large"
    if depth == 7:
        return 2700, 5400, "medium"
    return 1800, 3600, "small"


def parse_dimacs_header(path: Path) -> tuple[int, int]:
    with path.open("rb") as handle:
        header = handle.readline().decode("ascii").strip()
    match = re.fullmatch(r"p cnf (\d+) (\d+)", header)
    if not match:
        raise RuntimeError(f"invalid DIMACS header in {path}: {header}")
    return int(match.group(1)), int(match.group(2))


def write_historical_base_copy(encoding, path: Path) -> None:
    # Binary LF output reproduces the Linux artifact hash on every host.
    with path.open("wb") as handle:
        handle.write(
            (
                f"p cnf {encoding.base_variable_count} "
                f"{encoding.base_clause_count}\n"
            ).encode("ascii")
        )
        for clause in encoding.cnf.clauses[
            : encoding.base_clause_count
        ]:
            handle.write(
                (" ".join(str(lit) for lit in clause) + " 0\n").encode(
                    "ascii"
                )
            )


def append_theorem_clauses(
    *,
    historical_enriched: Path,
    destination: Path,
    encoding,
) -> None:
    old_variables, old_clauses = parse_dimacs_header(historical_enriched)
    theorem_clauses = encoding.cnf.clauses[
        encoding.base_clause_count :
    ]
    new_variables = max(old_variables, encoding.cnf.nv, encoding.pool.top)
    destination.parent.mkdir(parents=True, exist_ok=True)
    with historical_enriched.open("rb") as reader:
        reader.readline()
        with destination.open("wb") as writer:
            writer.write(
                (
                    f"p cnf {new_variables} "
                    f"{old_clauses + len(theorem_clauses)}\n"
                ).encode("ascii")
            )
            shutil.copyfileobj(reader, writer)
            for clause in theorem_clauses:
                writer.write(
                    (" ".join(str(lit) for lit in clause) + " 0\n").encode(
                        "ascii"
                    )
                )


def exhaustive_theorem_gate(n: int) -> dict:
    lane = Lane(
        lane_id=f"v21_gate_n{n}",
        partition=(n,),
        proper_cores=(),
        description="exhaustive theorem-cut gate",
    )
    core = tuple(range(n))
    encoding = build_theorem_cnf(
        n=n,
        lane=lane,
        box=None,
        primitive_cores=(core,),
    )
    pairs = list(itertools.combinations(range(n), 2))
    accepted = 0
    with Solver(
        name="cadical195",
        bootstrap_with=encoding.cnf.clauses,
    ) as solver:
        for mask in range(1 << len(pairs)):
            out = [0] * n
            for index, (u, v) in enumerate(pairs):
                if (mask >> index) & 1:
                    out[u] |= 1 << v
                else:
                    out[v] |= 1 << u
            encoded = solver.solve(
                assumptions=fixed_arcs(out, encoding.base)
            )
            expected = mathematical_acceptance(out, (core,))
            if encoded != expected:
                raise RuntimeError(
                    "theorem gate mismatch: "
                    f"n={n} mask={mask} "
                    f"encoded={encoded} expected={expected}"
                )
            accepted += int(encoded)
    return {
        "n": n,
        "tournaments": 1 << len(pairs),
        "accepted": accepted,
        "status": "PASS",
    }


def validate_v20(ledger_path: Path) -> tuple[dict, dict[str, dict]]:
    ledger = load_json(ledger_path)
    if ledger.get("schema") != V20_LEDGER_SCHEMA:
        raise RuntimeError("unexpected V20 ledger schema")
    if ledger.get("logical_conclusion") != "V20_COMPLETE_K16_OPEN":
        raise RuntimeError("V20 is not a completed open frontier")
    if ledger.get("verified_sat_witnesses"):
        raise RuntimeError("V20 already contains a verified SAT witness")
    if (
        ledger.get("closed_count") != EXPECTED_V20_CLOSED
        or ledger.get("open_count") != EXPECTED_V20_OPEN
    ):
        raise RuntimeError("unexpected V20 closure/open counts")
    closed = set(ledger["closed_queue_ids"])
    open_ids = set(ledger["open_queue_ids"])
    if closed & open_ids or len(closed | open_ids) != V20_FRONTIER_SIZE:
        raise RuntimeError("V20 ledger is not a disjoint complete frontier")
    by_root = {
        record["root_id"]: record
        for record in ledger["cadical_results"]
    }
    if not open_ids <= set(by_root):
        raise RuntimeError("V20 open leaf lacks its signed cube")
    return ledger, by_root


def plan(
    *,
    v18_source: Path,
    v20_ledger_path: Path,
    cadical_source: Path,
    output: Path,
    matrix_output: Path,
    v18_run_id: str,
    v20_run_id: str,
) -> dict:
    ledger, by_root = validate_v20(v20_ledger_path)
    output.mkdir(parents=True, exist_ok=True)
    shutil.copytree(
        v18_source / "bundle",
        output / "bundle",
        dirs_exist_ok=True,
    )
    cadical = locate_file(cadical_source, "cadical")
    (output / "cadical").mkdir(exist_ok=True)
    shutil.copy2(cadical, output / "cadical" / "cadical")

    gate_records = [
        exhaustive_theorem_gate(5),
        exhaustive_theorem_gate(6),
    ]
    unit_closed: set[str] = set()
    theorem_metadata: dict[str, dict] = {}
    base_hashes: dict[str, str] = {}
    enriched_hashes: dict[str, str] = {}
    encodings = {}

    for box in ("a1_z3", "a2p_z4p"):
        encoding = build_theorem_cnf(
            n=N,
            lane=LANES["full_s16"],
            box=box,
        )
        encodings[box] = encoding
        destination = output / "boxes" / box
        destination.mkdir(parents=True, exist_ok=True)
        historical_manifest = load_json(
            v18_source / "boxes" / box / "manifest.json"
        )
        historical_base = destination / "historical-base.cnf"
        write_historical_base_copy(encoding, historical_base)
        expected_hash = historical_manifest["base_cnf"]["sha256"]
        actual_hash = sha256(historical_base)
        if actual_hash != expected_hash:
            raise RuntimeError(
                f"{box} historical base hash mismatch: "
                f"{actual_hash} != {expected_hash}"
            )
        base_hashes[box] = actual_hash
        historical_base.unlink()
        enriched = destination / "enriched-theorem.cnf"
        append_theorem_clauses(
            historical_enriched=(
                v18_source / "boxes" / box / "enriched.cnf"
            ),
            destination=enriched,
            encoding=encoding,
        )
        enriched_hashes[box] = sha256(enriched)
        theorem_metadata[box] = encoding.metadata()
        write_json(destination / "theorem-meta.json", theorem_metadata[box])

    # Cheap exact sieve: a failed unit propagation under a signed cube is a
    # permanent closure.  No bounded search result is interpreted here.
    for box, encoding in encodings.items():
        box_open = [
            root_id
            for root_id in ledger["open_queue_ids"]
            if by_root[root_id]["box"] == box
        ]
        with Solver(
            name="cadical195",
            bootstrap_with=encoding.cnf.clauses,
        ) as solver:
            for root_id in box_open:
                cube = list(by_root[root_id]["cube_literals"])
                consistent, _ = solver.propagate(assumptions=cube)
                if not consistent:
                    unit_closed.add(root_id)

    tasks = []
    for root_id in sorted(
        set(ledger["open_queue_ids"]) - unit_closed
    ):
        parent = by_root[root_id]
        depth = int(parent["cube_depth"])
        cadical_seconds, sms_seconds, size = budget_for_depth(depth)
        tasks.append(
            {
                "task_id": f"cadical{cadical_seconds}-{root_id}",
                "stage": "cadical",
                "method": f"cadical{cadical_seconds}",
                "solver": "cadical",
                "seconds": cadical_seconds,
                "sms_seconds": sms_seconds,
                "complexity_class": size,
                "box": parent["box"],
                "root_id": root_id,
                "root_kind": parent["root_kind"],
                "cube_literals": list(parent["cube_literals"]),
                "cube_depth": depth,
                "cube_sha256": cube_hash(parent["cube_literals"]),
            }
        )

    plan_record = {
        "schema": PLAN_SCHEMA,
        "model_version": MODEL_VERSION,
        "cut_model_version": CUT_MODEL_VERSION,
        "created_utc": utc_now(),
        "source_runs": {"v18": v18_run_id, "v20": v20_run_id},
        "source_hashes": {
            "v20_ledger": sha256(v20_ledger_path),
            "historical_base": base_hashes,
            "theorem_enriched": enriched_hashes,
            "cadical": sha256(output / "cadical" / "cadical"),
        },
        "gates": gate_records,
        "baseline": {
            "frontier_leaves": V20_FRONTIER_SIZE,
            "v20_closed": len(ledger["closed_queue_ids"]),
            "v20_open": len(ledger["open_queue_ids"]),
            "unit_propagation_new_closed": len(unit_closed),
            "open_before_cadical": len(tasks),
        },
        "v20_closed_queue_ids": sorted(ledger["closed_queue_ids"]),
        "v20_open_queue_ids": sorted(ledger["open_queue_ids"]),
        "unit_closed_queue_ids": sorted(unit_closed),
        "cadical_tasks": tasks,
        "theorem_metadata": theorem_metadata,
        "coverage": (
            "Tasks are exactly the 81 V20 UNKNOWN leaves minus any exact "
            "unit-propagation contradictions under the theorem-augmented "
            "formula. All 58 V20 closures are excluded from the matrix."
        ),
    }
    write_json(output / "v21-manifest.json", plan_record)
    matrix_output.write_text(
        json.dumps(
            {
                "include": [
                    {
                        "task_id": task["task_id"],
                        "box": task["box"],
                        "seconds": task["seconds"],
                    }
                    for task in tasks
                ]
            },
            separators=(",", ":"),
        )
        + "\n",
        encoding="utf-8",
    )
    print(
        json.dumps(
            {
                "v20_open": EXPECTED_V20_OPEN,
                "unit_closed": len(unit_closed),
                "cadical_tasks": len(tasks),
                "budgets": dict(
                    Counter(task["seconds"] for task in tasks)
                ),
            },
            indent=2,
        ),
        flush=True,
    )
    return plan_record


def solve(
    *,
    source: Path,
    manifest_path: Path,
    task_id: str,
    result_path: Path,
    log_path: Path,
) -> dict:
    manifest = load_json(manifest_path)
    tasks = manifest.get("cadical_tasks", []) + manifest.get("sms_tasks", [])
    matches = [task for task in tasks if task["task_id"] == task_id]
    if len(matches) != 1:
        raise RuntimeError(f"task lookup failed: {task_id}")
    task = matches[0]
    seconds = int(task["seconds"])
    box = task["box"]
    cnf = source / "boxes" / box / "enriched-theorem.cnf"
    work = result_path.parent.parent / "work" / task_id
    work.mkdir(parents=True, exist_ok=True)

    if task["solver"] == "cadical":
        assumption_cnf = work / "assumption.cnf"
        write_assumption_cnf(cnf, assumption_cnf, task["cube_literals"])
        command = [
            str(source / "cadical" / "cadical"),
            str(assumption_cnf),
        ]
        returncode, text, timed_out, elapsed = run_limited(
            command,
            timeout_seconds=seconds,
        )
        status = {10: "SAT", 20: "UNSAT"}.get(returncode, "UNKNOWN")
        raw_result = returncode if returncode in {10, 20} else 0
        arcs = (
            assignment_to_arcs(parse_cadical_assignment(text))
            if status == "SAT"
            else None
        )
    elif task["solver"] == "sms":
        queue_file = manifest_path.parent / task["queue_file"]
        command = [
            str(source / "bundle" / "smsg"),
            "--vertices",
            str(N),
            "--directed",
            "--dimacs",
            str(cnf),
            "--cube-file",
            str(queue_file),
            "--cube-line",
            str(task["queue_line"]),
            "--cube-timeout",
            str(seconds),
        ]
        returncode, text, timed_out, elapsed = run_limited(
            command,
            timeout_seconds=seconds + 120,
        )
        cube_results = CUBE_RESULT.findall(text)
        raw_result = int(cube_results[-1]) if cube_results else 0
        status = {10: "SAT", 20: "UNSAT"}.get(raw_result, "UNKNOWN")
        arcs = parse_sms_arcs(text) if status == "SAT" else None
    else:
        raise RuntimeError(f"unknown solver: {task['solver']}")

    if timed_out:
        status = "UNKNOWN"
    log_path.parent.mkdir(parents=True, exist_ok=True)
    log_path.write_text(text, encoding="utf-8")
    record: dict = {
        "schema": RESULT_SCHEMA,
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "task_id": task_id,
        "stage": task["stage"],
        "method": task["method"],
        "solver": task["solver"],
        "box": box,
        "root_id": task["root_id"],
        "root_kind": task["root_kind"],
        "complexity_class": task["complexity_class"],
        "cube_literals": task["cube_literals"],
        "cube_depth": task["cube_depth"],
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


def select_sms(
    *,
    source: Path,
    cadical_results_root: Path,
    output: Path,
    matrix_output: Path,
) -> dict:
    plan_record = load_json(source / "v21-manifest.json")
    expected = {
        task["task_id"]: task
        for task in plan_record["cadical_tasks"]
    }
    records = collect_records(cadical_results_root)
    by_id = {record["task_id"]: record for record in records}
    missing = sorted(set(expected) - set(by_id))
    unexpected = sorted(set(by_id) - set(expected))
    if missing or unexpected:
        raise RuntimeError(
            f"CaDiCaL result mismatch: missing={missing}, "
            f"unexpected={unexpected}"
        )
    bad_sat = [
        record["task_id"]
        for record in records
        if record["status"] == "SAT" and not record.get("verified")
    ]
    if bad_sat:
        raise RuntimeError(f"unverified CaDiCaL SAT: {bad_sat}")
    verified_sat = [
        record["task_id"]
        for record in records
        if record["status"] == "SAT" and record.get("verified")
    ]
    unknown_records = (
        []
        if verified_sat
        else sorted(
            (
                record
                for record in records
                if record["status"] == "UNKNOWN"
            ),
            key=lambda item: item["root_id"],
        )
    )

    output.mkdir(parents=True, exist_ok=True)
    queue_path = output / "sms-long.cubes"
    queue_path.write_text(
        "\n".join(cube_line(r["cube_literals"]) for r in unknown_records)
        + ("\n" if unknown_records else ""),
        encoding="utf-8",
    )
    parent_by_root = {
        task["root_id"]: task
        for task in plan_record["cadical_tasks"]
    }
    sms_tasks = []
    for queue_line, record in enumerate(unknown_records, start=1):
        parent = parent_by_root[record["root_id"]]
        seconds = int(parent["sms_seconds"])
        sms_tasks.append(
            {
                "task_id": f"sms{seconds}-{record['root_id']}",
                "stage": "sms",
                "method": f"sms{seconds}",
                "solver": "sms",
                "seconds": seconds,
                "complexity_class": parent["complexity_class"],
                "box": parent["box"],
                "root_id": parent["root_id"],
                "root_kind": parent["root_kind"],
                "cube_literals": parent["cube_literals"],
                "cube_depth": parent["cube_depth"],
                "cube_sha256": parent["cube_sha256"],
                "queue_file": "sms-long.cubes",
                "queue_line": queue_line,
            }
        )

    sms_manifest = {
        "schema": PLAN_SCHEMA,
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "cadical_tasks": [],
        "sms_tasks": sms_tasks,
        "coverage": (
            "SMS receives exactly CaDiCaL UNKNOWN leaves. SAT and UNSAT "
            "leaves are never resubmitted."
        ),
    }
    write_json(output / "v21-sms-manifest.json", sms_manifest)
    cadical_ledger = {
        "schema": CADICAL_LEDGER_SCHEMA,
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "expected_results": len(expected),
        "results_received": len(records),
        "missing_task_ids": missing,
        "statuses": dict(Counter(r["status"] for r in records)),
        "exact_closed_queue_ids": sorted(
            r["root_id"] for r in records if r["status"] == "UNSAT"
        ),
        "unknown_queue_ids": [r["root_id"] for r in unknown_records],
        "verified_sat_witnesses": verified_sat,
        "cpu_seconds": round(sum(float(r["seconds"]) for r in records), 3),
        "results": sorted(records, key=lambda item: item["task_id"]),
    }
    write_json(output / "v21-cadical-stage-ledger.json", cadical_ledger)
    matrix_output.write_text(
        json.dumps(
            {
                "include": [
                    {
                        "task_id": task["task_id"],
                        "box": task["box"],
                        "seconds": task["seconds"],
                    }
                    for task in sms_tasks
                ]
            },
            separators=(",", ":"),
        )
        + "\n",
        encoding="utf-8",
    )
    print(
        json.dumps(
            {
                "cadical_statuses": cadical_ledger["statuses"],
                "sms_tasks": len(sms_tasks),
                "sms_budgets": dict(Counter(t["seconds"] for t in sms_tasks)),
            },
            indent=2,
        ),
        flush=True,
    )
    return cadical_ledger


def aggregate(
    *,
    source: Path,
    cadical_stage_ledger_path: Path,
    sms_results_root: Path,
    output: Path,
    workflow_run_id: str | None,
) -> dict:
    plan_record = load_json(source / "v21-manifest.json")
    cadical = load_json(cadical_stage_ledger_path)
    if cadical.get("schema") != CADICAL_LEDGER_SCHEMA:
        raise RuntimeError("unexpected V21 CaDiCaL ledger")
    sms_records = collect_records(sms_results_root)
    sms_by_root = {record["root_id"]: record for record in sms_records}
    expected_sms = set(cadical["unknown_queue_ids"])
    missing_sms = sorted(expected_sms - set(sms_by_root))
    unexpected_sms = sorted(set(sms_by_root) - expected_sms)
    if missing_sms or unexpected_sms:
        raise RuntimeError(
            f"SMS result mismatch: missing={missing_sms}, "
            f"unexpected={unexpected_sms}"
        )
    bad_sat = [
        record["task_id"]
        for record in sms_records
        if record["status"] == "SAT" and not record.get("verified")
    ]
    if bad_sat:
        raise RuntimeError(f"unverified SMS SAT: {bad_sat}")

    prior_closed = set(plan_record["v20_closed_queue_ids"])
    unit_closed = set(plan_record["unit_closed_queue_ids"])
    cadical_closed = set(cadical["exact_closed_queue_ids"])
    sms_closed = {
        record["root_id"]
        for record in sms_records
        if record["status"] == "UNSAT"
    }
    closed = prior_closed | unit_closed | cadical_closed | sms_closed
    full_frontier = (
        set(plan_record["v20_closed_queue_ids"])
        | set(plan_record["v20_open_queue_ids"])
    )
    if not closed <= full_frontier:
        raise RuntimeError("V21 closure escapes the signed frontier")
    remaining = sorted(full_frontier - closed)
    verified_sat = list(cadical["verified_sat_witnesses"]) + [
        record["task_id"]
        for record in sms_records
        if record["status"] == "SAT" and record.get("verified")
    ]
    if verified_sat:
        conclusion = "SAT_K16_VERIFIED"
    elif not remaining:
        conclusion = "V21_TWO_TARGET_ROOTS_EXACTLY_EXCLUDED_K16_OPEN"
    else:
        conclusion = "V21_COMPLETE_K16_OPEN"

    record = {
        "schema": FINAL_LEDGER_SCHEMA,
        "model_version": MODEL_VERSION,
        "cut_model_version": CUT_MODEL_VERSION,
        "created_utc": utc_now(),
        "workflow_run_id": workflow_run_id,
        "source_runs": plan_record["source_runs"],
        "logical_conclusion": conclusion,
        "baseline": plan_record["baseline"],
        "unit_stage": {
            "new_exact_closures": len(unit_closed),
            "closed_queue_ids": sorted(unit_closed),
        },
        "cadical_stage": {
            "expected_results": cadical["expected_results"],
            "results_received": cadical["results_received"],
            "statuses": cadical["statuses"],
            "new_exact_closures": len(cadical_closed),
            "cpu_seconds": cadical["cpu_seconds"],
        },
        "sms_stage": {
            "expected_results": len(expected_sms),
            "results_received": len(sms_records),
            "statuses": dict(Counter(r["status"] for r in sms_records)),
            "new_exact_closures": len(sms_closed),
            "cpu_seconds": round(
                sum(float(r["seconds"]) for r in sms_records),
                3,
            ),
        },
        "prior_closed_queue_ids": sorted(prior_closed),
        "new_closed_queue_ids": sorted(
            unit_closed | cadical_closed | sms_closed
        ),
        "closed_queue_ids": sorted(closed),
        "open_queue_ids": remaining,
        "closed_count": len(closed),
        "open_count": len(remaining),
        "verified_sat_witnesses": verified_sat,
        "theorem_metadata": plan_record["theorem_metadata"],
        "next_action": (
            "Reuse only open_queue_ids. UNKNOWN is not exclusion. "
            "Never resubmit closed_queue_ids."
        ),
        "cadical_results": cadical["results"],
        "sms_results": sorted(
            sms_records, key=lambda item: item["task_id"]
        ),
    }
    write_json(output, record)
    print(
        json.dumps(
            {
                "conclusion": conclusion,
                "unit_new_closed": len(unit_closed),
                "cadical_new_closed": len(cadical_closed),
                "sms_new_closed": len(sms_closed),
                "total_closed": len(closed),
                "remaining_open": len(remaining),
                "verified_sat": len(verified_sat),
            },
            indent=2,
        ),
        flush=True,
    )
    return record


def main() -> None:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--plan", action="store_true")
    mode.add_argument("--solve", action="store_true")
    mode.add_argument("--select-sms", action="store_true")
    mode.add_argument("--aggregate", action="store_true")
    parser.add_argument("--v18-source", type=Path)
    parser.add_argument("--v20-ledger", type=Path)
    parser.add_argument("--cadical-source", type=Path)
    parser.add_argument("--source", type=Path)
    parser.add_argument("--manifest", type=Path)
    parser.add_argument("--cadical-results-root", type=Path)
    parser.add_argument("--cadical-stage-ledger", type=Path)
    parser.add_argument("--sms-results-root", type=Path)
    parser.add_argument("--task-id")
    parser.add_argument("--result", type=Path)
    parser.add_argument("--log", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--matrix-output", type=Path)
    parser.add_argument("--v18-run-id", default="")
    parser.add_argument("--v20-run-id", default="")
    parser.add_argument("--workflow-run-id")
    args = parser.parse_args()

    if args.plan:
        plan(
            v18_source=args.v18_source,
            v20_ledger_path=args.v20_ledger,
            cadical_source=args.cadical_source,
            output=args.output,
            matrix_output=args.matrix_output,
            v18_run_id=args.v18_run_id,
            v20_run_id=args.v20_run_id,
        )
    elif args.solve:
        solve(
            source=args.source,
            manifest_path=args.manifest,
            task_id=args.task_id,
            result_path=args.result,
            log_path=args.log,
        )
    elif args.select_sms:
        select_sms(
            source=args.source,
            cadical_results_root=args.cadical_results_root,
            output=args.output,
            matrix_output=args.matrix_output,
        )
    else:
        aggregate(
            source=args.source,
            cadical_stage_ledger_path=args.cadical_stage_ledger,
            sms_results_root=args.sms_results_root,
            output=args.output,
            workflow_run_id=args.workflow_run_id,
        )


if __name__ == "__main__":
    main()
