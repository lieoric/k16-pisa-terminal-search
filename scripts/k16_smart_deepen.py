#!/usr/bin/env python3
"""Exact continuation of the v17.1 SMS-aware K16 cube ledger.

The v18 campaign never repeats a cube already proved UNSAT:

* every untested leaf of the complete v17.1 lookahead partitions is queued;
* every v17.1 UNKNOWN leaf is replaced by two complementary MOMS children;
* every v17.1 UNSAT leaf remains permanently closed.

The two children ``C + x`` and ``C - x`` are an exact partition of their
parent cube ``C``.  UNKNOWN remains open.  A SAT result is accepted only
after the standalone verifier recomputes the tournament, Pisa margins, and
primitivity without importing the model builder.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys
import time
from collections import Counter, defaultdict, deque
from datetime import datetime, timezone
from pathlib import Path


MODEL_VERSION = "k16-pisa-v18-exact-smart-deepen-20260728"
N = 16
ARC_VARIABLES = N * (N - 1)
EXPECTED_ROOT_LEAVES = 239
EXPECTED_PRIOR_UNSAT = 17
EXPECTED_PRIOR_UNKNOWN = 15
EXPECTED_UNTESTED = 207
EXPECTED_QUEUE = 237
CUBE_RESULT = re.compile(r"Cube result:\s*(0|10|20)")
ARC_LINE = re.compile(r"^\[(?:\(\d+,\d+\)(?:,\(\d+,\d+\))*)?\]$")
ARC_PAIR = re.compile(r"\((\d+),(\d+)\)")
REPO_ROOT = Path(__file__).resolve().parents[1]
INDEPENDENT_VERIFIER = REPO_ROOT / "scripts" / "verify_primitive_witness.py"


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def write_json(path: Path, record: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def cube_hash(literals: list[int]) -> str:
    payload = " ".join(str(literal) for literal in literals)
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def cube_line(literals: list[int]) -> str:
    return "a " + " ".join(str(literal) for literal in literals) + " 0"


def read_cubes(path: Path) -> list[list[int]]:
    cubes: list[list[int]] = []
    for line_number, raw in enumerate(
        path.read_text(encoding="utf-8").splitlines(),
        start=1,
    ):
        stripped = raw.strip()
        if not stripped:
            continue
        fields = stripped.split()
        if fields[0] != "a" or fields[-1] != "0":
            raise ValueError(f"malformed cube at {path}:{line_number}")
        literals = [int(value) for value in fields[1:-1]]
        if any(not 1 <= abs(literal) <= ARC_VARIABLES for literal in literals):
            raise ValueError(f"non-arc literal at {path}:{line_number}")
        if len({abs(literal) for literal in literals}) != len(literals):
            raise ValueError(f"repeated cube variable at {path}:{line_number}")
        cubes.append(literals)
    return cubes


class Dimacs:
    """A compact DIMACS reader with deterministic unit propagation."""

    def __init__(self, path: Path) -> None:
        self.path = path
        self.variables = 0
        self.declared_clauses = 0
        self.clauses: list[tuple[int, ...]] = []
        with path.open("r", encoding="utf-8") as handle:
            for raw in handle:
                line = raw.strip()
                if not line or line.startswith("c"):
                    continue
                if line.startswith("p "):
                    fields = line.split()
                    if len(fields) != 4 or fields[1] != "cnf":
                        raise ValueError(f"unsupported DIMACS header: {line}")
                    self.variables = int(fields[2])
                    self.declared_clauses = int(fields[3])
                    continue
                fields = [int(value) for value in line.split()]
                if not fields or fields[-1] != 0:
                    raise ValueError(f"unterminated DIMACS clause: {line[:80]}")
                clause = tuple(fields[:-1])
                if not clause:
                    raise ValueError("input CNF already contains an empty clause")
                self.clauses.append(clause)
        if not self.variables:
            raise ValueError(f"missing DIMACS header in {path}")
        if len(self.clauses) != self.declared_clauses:
            raise ValueError(
                f"DIMACS clause mismatch: {len(self.clauses)} != "
                f"{self.declared_clauses}"
            )

        self.occurrences: dict[int, list[int]] = defaultdict(list)
        self.units: list[int] = []
        for index, clause in enumerate(self.clauses):
            if len(clause) == 1:
                self.units.append(clause[0])
            for literal in clause:
                self.occurrences[literal].append(index)

    def propagate(self, assumptions: list[int]) -> tuple[dict[int, bool], bool]:
        assignment: dict[int, bool] = {}
        remaining = [len(clause) for clause in self.clauses]
        satisfied = bytearray(len(self.clauses))
        pending: deque[int] = deque()
        contradiction = False

        def enqueue(literal: int) -> None:
            nonlocal contradiction
            variable = abs(literal)
            value = literal > 0
            previous = assignment.get(variable)
            if previous is None:
                assignment[variable] = value
                pending.append(literal)
            elif previous != value:
                contradiction = True

        for literal in self.units:
            enqueue(literal)
        for literal in assumptions:
            enqueue(literal)

        while pending and not contradiction:
            true_literal = pending.popleft()
            for clause_index in self.occurrences.get(true_literal, ()):
                satisfied[clause_index] = 1
            for clause_index in self.occurrences.get(-true_literal, ()):
                if satisfied[clause_index]:
                    continue
                remaining[clause_index] -= 1
                if remaining[clause_index] == 0:
                    contradiction = True
                    break
                if remaining[clause_index] != 1:
                    continue
                unit = None
                clause_satisfied = False
                for literal in self.clauses[clause_index]:
                    value = assignment.get(abs(literal))
                    if value is None:
                        unit = literal
                    elif value == (literal > 0):
                        clause_satisfied = True
                        break
                if clause_satisfied:
                    satisfied[clause_index] = 1
                    continue
                if unit is None:
                    contradiction = True
                    break
                enqueue(unit)

        return assignment, contradiction

    def moms_arc_variable(
        self,
        assumptions: list[int],
    ) -> tuple[int, dict]:
        assignment, contradiction = self.propagate(assumptions)
        if contradiction:
            raise RuntimeError("an SMS UNKNOWN parent is unit-inconsistent")

        best_length: int | None = None
        residuals: list[list[int]] = []
        for clause in self.clauses:
            residual: list[int] = []
            clause_satisfied = False
            has_unassigned_arc = False
            for literal in clause:
                value = assignment.get(abs(literal))
                if value is None:
                    residual.append(literal)
                    if abs(literal) <= ARC_VARIABLES:
                        has_unassigned_arc = True
                elif value == (literal > 0):
                    clause_satisfied = True
                    break
            if clause_satisfied or not has_unassigned_arc:
                continue
            length = len(residual)
            if best_length is None or length < best_length:
                best_length = length
                residuals = [residual]
            elif length == best_length:
                residuals.append(residual)

        if best_length is None:
            raise RuntimeError("no unassigned directed-arc variable remains")

        positive: Counter[int] = Counter()
        negative: Counter[int] = Counter()
        for clause in residuals:
            for literal in clause:
                variable = abs(literal)
                if variable > ARC_VARIABLES or variable in assignment:
                    continue
                if literal > 0:
                    positive[variable] += 1
                else:
                    negative[variable] += 1
        candidates = set(positive) | set(negative)
        if not candidates:
            raise RuntimeError("MOMS residual layer contains no arc candidate")

        def score(variable: int) -> tuple[int, int, int, int]:
            pos = positive[variable]
            neg = negative[variable]
            moms = 2 * (pos + neg) + pos * neg
            return moms, min(pos, neg), pos + neg, -variable

        variable = max(candidates, key=score)
        return variable, {
            "rule": "MOMS over the shortest residual clauses containing arcs",
            "residual_clause_length": best_length,
            "residual_clause_count": len(residuals),
            "positive_occurrences": positive[variable],
            "negative_occurrences": negative[variable],
            "score": score(variable)[0],
            "implied_assignments": len(assignment),
        }


def locate_one(root: Path, name: str) -> Path:
    matches = sorted(root.rglob(name))
    if len(matches) != 1:
        raise RuntimeError(f"expected one {name} below {root}, got {matches}")
    return matches[0]


def parse_box_source(value: str) -> tuple[str, Path]:
    box, separator, raw_path = value.partition("=")
    if not separator or not box or not raw_path:
        raise argparse.ArgumentTypeError("expected BOX=PATH")
    return box, Path(raw_path)


def copy_bundle(binary_source: Path, output: Path) -> dict:
    binary = locate_one(binary_source, "smsg")
    bundle = binary.parent
    destination = output / "bundle"
    if destination.exists():
        shutil.rmtree(destination)
    shutil.copytree(bundle, destination)
    copied_binary = destination / "smsg"
    return {
        "binary": "bundle/smsg",
        "sha256": sha256(copied_binary),
    }


def plan(
    *,
    ledger_path: Path,
    box_sources: list[tuple[str, Path]],
    binary_source: Path | None,
    output: Path,
    matrix_output: Path,
    source_run_id: str,
) -> dict:
    output.mkdir(parents=True, exist_ok=True)
    ledger = json.loads(ledger_path.read_text(encoding="utf-8"))
    previous = {
        (record["box"], int(record["cube_line"])): record
        for record in ledger["cube_results"]
        if record["strategy"] == "lookahead"
    }
    if len(previous) != 32:
        raise RuntimeError(f"expected 32 prior lookahead results, got {len(previous)}")

    binary_record = None
    if binary_source is not None:
        binary_record = copy_bundle(binary_source, output)

    queue: list[dict] = []
    closed: list[dict] = []
    split_parents: list[dict] = []
    boxes_record: dict[str, dict] = {}
    untested_count = 0

    for box, source in sorted(box_sources):
        manifest_path = locate_one(source, "manifest.json")
        enriched_path = locate_one(source, "enriched.cnf")
        lookahead_path = locate_one(source, "lookahead.cubes")
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        partition = manifest["partitions"]["lookahead"]
        if not (
            partition["generator_complete"]
            and partition["coverage"]["complete"]
            and partition["coverage"]["status"] == "UNSAT"
        ):
            raise RuntimeError(f"{box} is not a proved-complete partition")
        if sha256(enriched_path) != manifest["enriched_cnf"]["sha256"]:
            raise RuntimeError(f"{box} enriched CNF hash mismatch")
        if sha256(lookahead_path) != partition["cube_sha256"]:
            raise RuntimeError(f"{box} cube-file hash mismatch")

        cubes = read_cubes(lookahead_path)
        if len(cubes) != int(partition["cubes"]):
            raise RuntimeError(f"{box} cube count mismatch")
        dimacs = Dimacs(enriched_path)

        destination = output / "boxes" / box
        destination.mkdir(parents=True, exist_ok=True)
        shutil.copy2(enriched_path, destination / "enriched.cnf")
        shutil.copy2(lookahead_path, destination / "lookahead.cubes")
        shutil.copy2(manifest_path, destination / "manifest.json")

        box_queue: list[dict] = []
        for original_line, literals in enumerate(cubes, start=1):
            prior = previous.get((box, original_line))
            parent_id = f"{box}-lookahead-c{original_line:06d}"
            if prior is not None:
                if prior["cube_literals"] != literals:
                    raise RuntimeError(f"prior ledger mismatch for {parent_id}")
                if prior["status"] == "UNSAT":
                    closed.append({
                        "box": box,
                        "original_line": original_line,
                        "parent_id": parent_id,
                        "cube_sha256": cube_hash(literals),
                        "source": "v17.1 exact SMS UNSAT",
                        "seconds": prior["seconds"],
                    })
                    continue
                if prior["status"] == "SAT":
                    if not prior.get("verified"):
                        raise RuntimeError(f"unverified prior SAT: {parent_id}")
                    continue
                if prior["status"] != "UNKNOWN":
                    raise RuntimeError(f"unexpected prior status: {prior['status']}")

                variable, moms = dimacs.moms_arc_variable(literals)
                parent = {
                    "box": box,
                    "original_line": original_line,
                    "parent_id": parent_id,
                    "parent_literals": literals,
                    "parent_sha256": cube_hash(literals),
                    "branch_variable": variable,
                    "moms": moms,
                }
                split_parents.append(parent)
                for sign, label in ((variable, "pos"), (-variable, "neg")):
                    child = literals + [sign]
                    item = {
                        "box": box,
                        "kind": "split_unknown",
                        "parent_id": parent_id,
                        "original_line": original_line,
                        "branch_literal": sign,
                        "branch_variable": variable,
                        "polarity": label,
                        "cube_literals": child,
                        "cube_depth": len(child),
                        "cube_sha256": cube_hash(child),
                        "queue_id": (
                            f"{box}-split-c{original_line:06d}-"
                            f"v{variable:06d}-{label}"
                        ),
                    }
                    box_queue.append(item)
                continue

            untested_count += 1
            box_queue.append({
                "box": box,
                "kind": "untested_original",
                "parent_id": parent_id,
                "original_line": original_line,
                "branch_literal": None,
                "branch_variable": None,
                "polarity": None,
                "cube_literals": literals,
                "cube_depth": len(literals),
                "cube_sha256": cube_hash(literals),
                "queue_id": f"{box}-original-c{original_line:06d}",
            })

        queue_path = output / "queues" / f"{box}.cubes"
        queue_path.parent.mkdir(parents=True, exist_ok=True)
        queue_path.write_text(
            "\n".join(cube_line(item["cube_literals"]) for item in box_queue)
            + ("\n" if box_queue else ""),
            encoding="utf-8",
        )
        for line_number, item in enumerate(box_queue, start=1):
            item["queue_line"] = line_number
            item["queue_file"] = f"queues/{box}.cubes"
            queue.append(item)
        boxes_record[box] = {
            "original_partition_leaves": len(cubes),
            "already_closed": sum(1 for item in closed if item["box"] == box),
            "split_unknown_parents": sum(
                1 for item in split_parents if item["box"] == box
            ),
            "queued": len(box_queue),
            "enriched_cnf_sha256": sha256(enriched_path),
            "original_cubes_sha256": sha256(lookahead_path),
            "queue_cubes_sha256": sha256(queue_path),
        }

    # Exact-cover integrity gates.
    for parent in split_parents:
        children = [
            item for item in queue if item["parent_id"] == parent["parent_id"]
        ]
        if len(children) != 2:
            raise RuntimeError(f"split parent lacks two children: {parent['parent_id']}")
        positive, negative = sorted(
            children,
            key=lambda item: item["branch_literal"] < 0,
        )
        variable = parent["branch_variable"]
        if {
            positive["branch_literal"],
            negative["branch_literal"],
        } != {variable, -variable}:
            raise RuntimeError(f"non-complementary split: {parent['parent_id']}")
        if (
            positive["cube_literals"][:-1] != parent["parent_literals"]
            or negative["cube_literals"][:-1] != parent["parent_literals"]
        ):
            raise RuntimeError(f"split children changed parent: {parent['parent_id']}")

    totals = {
        "root_leaves": sum(
            item["original_partition_leaves"] for item in boxes_record.values()
        ),
        "prior_exact_unsat": len(closed),
        "prior_unknown_split_parents": len(split_parents),
        "untested_originals": untested_count,
        "queued_children_and_originals": len(queue),
    }
    expected = {
        "root_leaves": EXPECTED_ROOT_LEAVES,
        "prior_exact_unsat": EXPECTED_PRIOR_UNSAT,
        "prior_unknown_split_parents": EXPECTED_PRIOR_UNKNOWN,
        "untested_originals": EXPECTED_UNTESTED,
        "queued_children_and_originals": EXPECTED_QUEUE,
    }
    if totals != expected:
        raise RuntimeError(f"v18 coverage gate failed: {totals} != {expected}")

    matrix = {
        "include": [
            {
                "box": item["box"],
                "queue_line": item["queue_line"],
                "queue_id": item["queue_id"],
                "kind": item["kind"],
            }
            for item in queue
        ]
    }
    matrix_output.parent.mkdir(parents=True, exist_ok=True)
    matrix_output.write_text(
        json.dumps(matrix, separators=(",", ":")) + "\n",
        encoding="utf-8",
    )
    record = {
        "schema": "k16-smart-deepen-plan-v1",
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "source_run_id": source_run_id,
        "source_ledger_sha256": sha256(ledger_path),
        "binary": binary_record,
        "boxes": boxes_record,
        "totals": totals,
        "coverage_invariant": (
            "Each complete v17.1 root partition equals permanent UNSAT leaves "
            "plus queued original leaves plus complementary child pairs that "
            "exactly replace each prior UNKNOWN parent."
        ),
        "permanent_closed": closed,
        "split_parents": split_parents,
        "queue": queue,
    }
    write_json(output / "queue-manifest.json", record)
    print(json.dumps(totals), flush=True)
    return record


def run_process(command: list[str], seconds: int) -> tuple[int, str, bool, float]:
    started = time.monotonic()
    try:
        completed = subprocess.run(
            command,
            capture_output=True,
            text=True,
            check=False,
            timeout=seconds + 90,
        )
        return (
            completed.returncode,
            completed.stdout + completed.stderr,
            False,
            time.monotonic() - started,
        )
    except subprocess.TimeoutExpired as exc:
        stdout = exc.stdout.decode() if isinstance(exc.stdout, bytes) else (exc.stdout or "")
        stderr = exc.stderr.decode() if isinstance(exc.stderr, bytes) else (exc.stderr or "")
        return 0, stdout + stderr + "\nV18 WRAPPER TIMEOUT\n", True, time.monotonic() - started


def parse_sms_arcs(text: str) -> list[list[int]] | None:
    for raw in reversed(text.splitlines()):
        line = raw.strip()
        if not ARC_LINE.fullmatch(line):
            continue
        arcs = [[int(u), int(v)] for u, v in ARC_PAIR.findall(line)]
        if len(arcs) == N * (N - 1) // 2:
            return arcs
    return None


def solve(
    *,
    source: Path,
    box: str,
    queue_line_number: int,
    seconds: int,
    result_path: Path,
    log_path: Path,
) -> dict:
    manifest = json.loads(
        (source / "queue-manifest.json").read_text(encoding="utf-8")
    )
    matches = [
        item for item in manifest["queue"]
        if item["box"] == box and int(item["queue_line"]) == queue_line_number
    ]
    if len(matches) != 1:
        raise RuntimeError(f"queue lookup failed: {box}:{queue_line_number}")
    item = matches[0]
    queue_file = source / item["queue_file"]
    cubes = read_cubes(queue_file)
    literals = cubes[queue_line_number - 1]
    if literals != item["cube_literals"] or cube_hash(literals) != item["cube_sha256"]:
        raise RuntimeError("queue cube does not match signed manifest")

    binary = source / "bundle" / "smsg"
    cnf = source / "boxes" / box / "enriched.cnf"
    command = [
        str(binary),
        "--vertices", str(N),
        "--directed",
        "--dimacs", str(cnf),
        "--cube-file", str(queue_file),
        "--cube-line", str(queue_line_number),
        "--cube-timeout", str(seconds),
    ]
    returncode, text, timed_out, elapsed = run_process(command, seconds)
    log_path.parent.mkdir(parents=True, exist_ok=True)
    log_path.write_text(text, encoding="utf-8")
    results = CUBE_RESULT.findall(text)
    raw_result = int(results[-1]) if results else 0
    status = {10: "SAT", 20: "UNSAT"}.get(raw_result, "UNKNOWN")
    if timed_out:
        status = "UNKNOWN"

    record: dict = {
        "schema": "k16-smart-deepen-result-v1",
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "box": box,
        "queue_id": item["queue_id"],
        "queue_line": queue_line_number,
        "kind": item["kind"],
        "parent_id": item["parent_id"],
        "original_line": item["original_line"],
        "branch_literal": item["branch_literal"],
        "cube_literals": literals,
        "cube_depth": len(literals),
        "cube_sha256": item["cube_sha256"],
        "status": status,
        "seconds": round(elapsed, 3),
        "time_limit_seconds": seconds,
        "solver_exit_code": returncode,
        "sms_cube_result": raw_result,
        "timed_out": timed_out,
        "solver_level_exact": status == "UNSAT",
        "verified": False,
        "meaning": (
            "UNSAT permanently closes this exact queue leaf. "
            "UNKNOWN remains open and is eligible for another split."
        ),
    }

    if status == "SAT":
        arcs = parse_sms_arcs(text)
        if arcs is None:
            write_json(result_path, record)
            raise RuntimeError("SMS reported SAT without a parseable tournament")
        candidate = result_path.parent / f"{item['queue_id']}-candidate.json"
        audit_path = result_path.parent / f"{item['queue_id']}-audit.json"
        write_json(candidate, {"n": N, "arcs": arcs})
        verifier = subprocess.run(
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
            else {"valid": False, "error": "no audit file"}
        )
        record["candidate_arcs"] = arcs
        record["independent_audit"] = audit
        record["independent_verifier_exit_code"] = verifier.returncode
        record["verified"] = verifier.returncode == 0 and bool(audit.get("valid"))
        if not record["verified"]:
            write_json(result_path, record)
            raise RuntimeError("SAT candidate failed zero-shared-code verification")

    write_json(result_path, record)
    print(json.dumps(record, indent=2), flush=True)
    return record


def aggregate(
    *,
    source: Path,
    results_root: Path,
    output: Path,
) -> dict:
    plan_record = json.loads(
        (source / "queue-manifest.json").read_text(encoding="utf-8")
    )
    paths = sorted(results_root.rglob("*.json"))
    results = []
    for path in paths:
        record = json.loads(path.read_text(encoding="utf-8"))
        if record.get("schema") == "k16-smart-deepen-result-v1":
            results.append(record)
    by_id = {record["queue_id"]: record for record in results}
    if len(by_id) != len(results):
        raise RuntimeError("duplicate v18 result identifiers")

    verified_sat = [
        record for record in results
        if record["status"] == "SAT" and record.get("verified")
    ]
    per_box: dict[str, dict] = {}
    next_open: list[dict] = []
    for box, box_info in sorted(plan_record["boxes"].items()):
        permanently_closed_lines = {
            int(item["original_line"])
            for item in plan_record["permanent_closed"]
            if item["box"] == box
        }
        parents = defaultdict(list)
        for item in plan_record["queue"]:
            if item["box"] != box:
                continue
            result = by_id.get(item["queue_id"])
            if result is not None:
                parents[item["parent_id"]].append(result)
            else:
                parents[item["parent_id"]].append({
                    "queue_id": item["queue_id"],
                    "status": "MISSING",
                    "kind": item["kind"],
                    "original_line": item["original_line"],
                })

        closed_now = []
        open_parents = []
        for parent_id, children in sorted(parents.items()):
            original_line = int(children[0]["original_line"])
            if all(child["status"] == "UNSAT" for child in children):
                permanently_closed_lines.add(original_line)
                closed_now.append(parent_id)
            else:
                open_parents.append(parent_id)
                for child in children:
                    if child["status"] not in {"UNSAT", "SAT"}:
                        next_open.append({
                            "box": box,
                            "parent_id": parent_id,
                            "queue_id": child["queue_id"],
                            "status": child["status"],
                        })

        total = int(box_info["original_partition_leaves"])
        per_box[box] = {
            "original_partition_leaves": total,
            "closed_before_v18": int(box_info["already_closed"]),
            "newly_closed_parent_leaves": len(closed_now),
            "total_closed_parent_leaves": len(permanently_closed_lines),
            "remaining_open_parent_leaves": total - len(permanently_closed_lines),
            "root_exactly_excluded": len(permanently_closed_lines) == total,
            "newly_closed_parent_ids": closed_now,
            "open_parent_ids": open_parents,
        }

    missing = [
        item["queue_id"]
        for item in plan_record["queue"]
        if item["queue_id"] not in by_id
    ]
    statuses = Counter(record["status"] for record in results)
    all_roots_closed = all(
        record["root_exactly_excluded"] for record in per_box.values()
    )
    if verified_sat:
        conclusion = "SAT_K16_VERIFIED"
    elif missing:
        conclusion = "V18_PARTIAL_INFRASTRUCTURE_FAILURE"
    elif all_roots_closed:
        conclusion = "V18_TARGET_ROOTS_EXACTLY_EXCLUDED"
    else:
        conclusion = "V18_COMPLETE_TARGETS_STILL_OPEN"

    record = {
        "schema": "k16-smart-deepen-ledger-v1",
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "source_run_id": plan_record["source_run_id"],
        "plan_totals": plan_record["totals"],
        "results_received": len(results),
        "result_statuses": dict(statuses),
        "missing_queue_ids": missing,
        "verified_sat_witnesses": [
            item["queue_id"] for item in verified_sat
        ],
        "per_box": per_box,
        "next_open_queue": next_open,
        "logical_conclusion": conclusion,
        "unknown_policy": (
            "UNKNOWN is not an exclusion. Only UNSAT leaves are accumulated; "
            "open leaves should be split again rather than blindly rerun."
        ),
        "results": results,
    }
    write_json(output, record)
    print(json.dumps({
        "logical_conclusion": conclusion,
        "statuses": dict(statuses),
        "per_box": per_box,
    }, indent=2), flush=True)
    return record


def main() -> None:
    parser = argparse.ArgumentParser()
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--plan", action="store_true")
    modes.add_argument("--solve", action="store_true")
    modes.add_argument("--aggregate", action="store_true")
    parser.add_argument("--ledger", type=Path)
    parser.add_argument(
        "--box-source",
        action="append",
        type=parse_box_source,
        default=[],
    )
    parser.add_argument("--binary-source", type=Path)
    parser.add_argument("--source-run-id", default="30330960933")
    parser.add_argument("--source", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--matrix-output", type=Path)
    parser.add_argument("--box")
    parser.add_argument("--queue-line", type=int)
    parser.add_argument("--seconds", type=int, default=300)
    parser.add_argument("--result", type=Path)
    parser.add_argument("--log", type=Path)
    parser.add_argument("--results-root", type=Path)
    args = parser.parse_args()

    if args.plan:
        required = (args.ledger, args.output, args.matrix_output)
        if any(value is None for value in required) or not args.box_source:
            parser.error(
                "--plan requires --ledger --box-source --output --matrix-output"
            )
        plan(
            ledger_path=args.ledger,
            box_sources=args.box_source,
            binary_source=args.binary_source,
            output=args.output,
            matrix_output=args.matrix_output,
            source_run_id=args.source_run_id,
        )
    elif args.solve:
        required = (
            args.source, args.box, args.queue_line, args.result, args.log,
        )
        if any(value is None for value in required):
            parser.error(
                "--solve requires --source --box --queue-line --result --log"
            )
        solve(
            source=args.source,
            box=args.box,
            queue_line_number=args.queue_line,
            seconds=args.seconds,
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
