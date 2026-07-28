#!/usr/bin/env python3
"""SMS-aware adaptive cubing for the primitive K16 Pisa endgame.

This is the v17 pilot described by the smart-cubing literature:

1. run SMS before cubing, so the cuber inherits dynamic symmetry information;
2. compare SMS's CDCL cutoff with its propagation-balanced lookahead cuber;
3. conquer every sampled cube with SMS still enabled;
4. record a hash-addressed cube ledger so UNKNOWN leaves can be split later.

The nine semantic ``a/z`` boxes remain the exact root partition.  This file
does not turn a timeout into an exclusion and never claims a sampled
partition is exhausted.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
import time
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from h14_module3_sms import (
    SMS_COMMIT,
    arcs_to_masks,
    classify,
    parse_sms_arcs,
)
from k16_primitive_sms import (
    BOXES,
    LANES,
    MODEL_VERSION as ROOT_MODEL_VERSION,
    N,
    build_cnf,
    independent_audit,
)


MODEL_VERSION = "k16-pisa-v17-sms-aware-smart-cubing-pilot-20260728"
PATCH_ID = "sms-v17-edge-only-cutoff-and-cube-result"
ARC_VARIABLES = N * (N - 1)
DECISIONS = re.compile(r"^Decisions:\s*(.*)$")
CUBE_RESULT = re.compile(r"Cube result:\s*(0|10|20)")


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def write_json(path: Path, record: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")


def run_process(
    command: list[str],
    *,
    wrapper_seconds: int,
) -> tuple[int, str, bool, float]:
    started = time.monotonic()
    timed_out = False
    try:
        completed = subprocess.run(
            command,
            capture_output=True,
            text=True,
            timeout=wrapper_seconds,
            check=False,
        )
        returncode = completed.returncode
        text = completed.stdout + completed.stderr
    except subprocess.TimeoutExpired as exc:
        timed_out = True
        returncode = 0
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
        text = stdout + stderr + "\nV17 WRAPPER TIMEOUT\n"
    return returncode, text, timed_out, time.monotonic() - started


def sms_base_command(binary: Path, cnf: Path) -> list[str]:
    return [
        str(binary),
        "--vertices",
        str(N),
        "--directed",
        "--dimacs",
        str(cnf),
    ]


def extract_cubes(text: str, strategy: str) -> list[str]:
    raw: list[list[int]] = []
    for line in text.splitlines():
        stripped = line.strip().lstrip("\ufeff")
        if strategy == "lookahead":
            match = DECISIONS.fullmatch(stripped)
            if match is None:
                continue
            payload = match.group(1).strip()
            literals = [] if not payload else [int(x) for x in payload.split()]
        else:
            if not (stripped.startswith("a ") and stripped.endswith(" 0")):
                continue
            literals = [
                int(x)
                for x in stripped.split()[1:-1]
            ]

        if any(not 1 <= abs(lit) <= ARC_VARIABLES for lit in literals):
            raise RuntimeError(
                f"{strategy} cube contains a non-arc decision: {literals}"
            )
        if len({abs(lit) for lit in literals}) != len(literals):
            raise RuntimeError(f"{strategy} cube repeats an arc variable")
        raw.append(literals)

    cubes: list[str] = []
    seen: set[tuple[int, ...]] = set()
    for literals in raw:
        key = tuple(literals)
        if key in seen:
            continue
        seen.add(key)
        cubes.append("a " + " ".join(str(x) for x in literals) + " 0")
    return cubes


def read_cube(path: Path, line_number: int) -> list[int]:
    lines = [
        line.strip()
        for line in path.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]
    if not 1 <= line_number <= len(lines):
        raise ValueError(f"cube line {line_number} outside 1..{len(lines)}")
    fields = lines[line_number - 1].split()
    if fields[0] != "a" or fields[-1] != "0":
        raise ValueError(f"malformed cube line {line_number}")
    return [int(value) for value in fields[1:-1]]


def stratified_lines(total: int, wanted: int) -> list[int]:
    if total <= wanted:
        return list(range(1, total + 1))
    return sorted({
        1 + round(position * (total - 1) / (wanted - 1))
        for position in range(wanted)
    })


def verify_partition_coverage(
    *,
    binary: Path,
    cnf: Path,
    cubes: Path,
    seconds: int,
    log: Path,
) -> dict:
    command = (
        sms_base_command(binary, cnf)
        + [
            "--cube-file-test",
            str(cubes),
            "--timeout",
            str(seconds),
        ]
    )
    returncode, text, timed_out, elapsed = run_process(
        command,
        wrapper_seconds=seconds + 90,
    )
    log.write_text(text, encoding="utf-8")
    status = classify(returncode, text, timed_out)
    return {
        "status": status,
        "complete": status == "UNSAT",
        "seconds": round(elapsed, 3),
        "returncode": returncode,
        "timed_out": timed_out,
        "command": command,
        "meaning": (
            "UNSAT proves that blocking every emitted cube closes the "
            "SMS-canonical enriched formula."
        ),
    }


def prepare_box(
    *,
    binary: Path,
    box: str,
    work: Path,
    prerun_seconds: int,
    cuber_prerun_seconds: int,
    cutoff: int,
    partition_seconds: int,
    coverage_seconds: int,
    strategies: tuple[str, ...],
) -> dict:
    if box not in BOXES:
        raise ValueError(box)
    if any(strategy not in {"lookahead", "cdcl"} for strategy in strategies):
        raise ValueError(strategies)

    work.mkdir(parents=True, exist_ok=True)
    logs = work / "logs"
    logs.mkdir(exist_ok=True)
    lane = LANES["full_s16"]

    built = build_cnf(lane=lane, box=box)
    base = work / "base.cnf"
    enriched = work / "enriched.cnf"
    built.cnf.to_file(base)
    write_json(work / "base.meta.json", built.metadata())

    prerun_command = (
        sms_base_command(binary, base)
        + [
            "--prerun",
            str(prerun_seconds),
            "--simplify",
            str(enriched),
            "--max-learned-clause-size",
            "5",
        ]
    )
    returncode, text, timed_out, elapsed = run_process(
        prerun_command,
        wrapper_seconds=prerun_seconds + 180,
    )
    (logs / "prerun.log").write_text(text, encoding="utf-8")
    prerun_status = classify(returncode, text, timed_out)
    record: dict = {
        "schema": "k16-smart-cubing-partition-v1",
        "model_version": MODEL_VERSION,
        "root_model_version": ROOT_MODEL_VERSION,
        "sms_commit": SMS_COMMIT,
        "sms_patch": PATCH_ID,
        "created_utc": utc_now(),
        "lane": "full_s16",
        "box": box,
        "root_slice_id": f"full_s16-{box}",
        "base_cnf": {
            "sha256": sha256(base),
            "metadata": built.metadata(),
        },
        "prerun": {
            "status": prerun_status,
            "seconds": round(elapsed, 3),
            "time_limit_seconds": prerun_seconds,
            "returncode": returncode,
            "timed_out": timed_out,
            "command": prerun_command,
        },
        "partitions": {},
    }

    if prerun_status in {"SAT", "UNSAT"}:
        if prerun_status == "SAT":
            arcs = parse_sms_arcs(text, N)
            if arcs is None:
                raise RuntimeError("prerun SAT had no parseable tournament")
            audit = independent_audit(
                arcs,
                lane=lane,
                box=box,
                directory=work / "prerun-audit",
            )
            record["prerun"]["candidate_arcs"] = arcs
            record["prerun"]["independent_audit"] = audit
            record["prerun"]["verified"] = bool(audit.get("valid"))
            if not record["prerun"]["verified"]:
                raise RuntimeError("prerun SAT failed independent audit")
        record["root_status"] = prerun_status
        write_json(work / "manifest.json", record)
        return record

    if not enriched.exists():
        raise RuntimeError("SMS prerun produced no enriched CNF")
    record["enriched_cnf"] = {
        "sha256": sha256(enriched),
        "bytes": enriched.stat().st_size,
    }

    for strategy in strategies:
        cube_file = work / f"{strategy}.cubes"
        partition_log = logs / f"{strategy}-partition.log"
        if strategy == "lookahead":
            command = (
                sms_base_command(binary, enriched)
                + [
                    "--prerun",
                    str(cuber_prerun_seconds),
                    "--assignment-cutoff",
                    str(cutoff),
                    "--lookahead-only-edge-vars",
                    "--cube-only-decisions",
                ]
            )
        else:
            command = (
                sms_base_command(binary, enriched)
                + [
                    "--prerun",
                    str(cuber_prerun_seconds),
                    "--simple-assignment-cutoff",
                    str(cutoff),
                    "--timeout",
                    str(partition_seconds),
                ]
            )
        ret, output, wrapper_timeout, partition_elapsed = run_process(
            command,
            wrapper_seconds=partition_seconds + 120,
        )
        partition_log.write_text(output, encoding="utf-8")
        cubes = extract_cubes(output, strategy)
        cube_file.write_text(
            "\n".join(cubes) + ("\n" if cubes else ""),
            encoding="utf-8",
        )

        if strategy == "lookahead":
            generator_complete = not wrapper_timeout and ret == 0 and bool(cubes)
        else:
            generator_complete = (
                classify(ret, output, wrapper_timeout) == "UNSAT"
                and bool(cubes)
            )

        coverage = {
            "status": "SKIPPED",
            "complete": False,
            "meaning": "generator did not return a complete nonempty partition",
        }
        if generator_complete:
            coverage = verify_partition_coverage(
                binary=binary,
                cnf=enriched,
                cubes=cube_file,
                seconds=coverage_seconds,
                log=logs / f"{strategy}-coverage.log",
            )

        depths = [len(read_cube(cube_file, line)) for line in range(1, len(cubes) + 1)]
        record["partitions"][strategy] = {
            "strategy": strategy,
            "cutoff": cutoff,
            "cuber_prerun_seconds": cuber_prerun_seconds,
            "partition_seconds": round(partition_elapsed, 3),
            "partition_time_limit_seconds": partition_seconds,
            "returncode": ret,
            "timed_out": wrapper_timeout,
            "generator_complete": generator_complete,
            "coverage": coverage,
            "cubes": len(cubes),
            "cube_file": cube_file.name,
            "cube_sha256": sha256(cube_file),
            "decision_depth": {
                "minimum": min(depths) if depths else None,
                "maximum": max(depths) if depths else None,
                "mean": (
                    round(sum(depths) / len(depths), 3) if depths else None
                ),
            },
            "command": command,
        }
        print(
            json.dumps(
                {
                    "box": box,
                    "strategy": strategy,
                    "cubes": len(cubes),
                    "generator_complete": generator_complete,
                    "coverage": coverage["status"],
                    "seconds": round(partition_elapsed, 3),
                }
            ),
            flush=True,
        )

    record["root_status"] = "PARTITIONED"
    write_json(work / "manifest.json", record)
    return record


def cube_matrix(manifests: list[Path], sample_size: int) -> dict:
    include: list[dict] = []
    for manifest_path in manifests:
        record = json.loads(manifest_path.read_text(encoding="utf-8"))
        if record.get("root_status") != "PARTITIONED":
            continue
        box = record["box"]
        for strategy, partition in record["partitions"].items():
            if not partition.get("generator_complete"):
                continue
            total = int(partition["cubes"])
            for line in stratified_lines(total, sample_size):
                include.append({
                    "box": box,
                    "strategy": strategy,
                    "cube_line": line,
                    "cube_id": f"{box}-{strategy}-c{line:06d}",
                })
    return {"include": include}


def solve_cube(
    *,
    binary: Path,
    box: str,
    strategy: str,
    work: Path,
    cube_line: int,
    seconds: int,
    result_path: Path,
    log_path: Path,
) -> dict:
    if box not in BOXES:
        raise ValueError(box)
    manifest = json.loads((work / "manifest.json").read_text(encoding="utf-8"))
    partition = manifest["partitions"][strategy]
    cnf = work / "enriched.cnf"
    cubes = work / partition["cube_file"]
    literals = read_cube(cubes, cube_line)
    cube_text = " ".join(str(x) for x in literals)
    cube_hash = hashlib.sha256(cube_text.encode()).hexdigest()

    command = (
        sms_base_command(binary, cnf)
        + [
            "--cube-file",
            str(cubes),
            "--cube-line",
            str(cube_line),
            "--cube-timeout",
            str(seconds),
        ]
    )
    returncode, text, timed_out, elapsed = run_process(
        command,
        wrapper_seconds=seconds + 90,
    )
    log_path.parent.mkdir(parents=True, exist_ok=True)
    log_path.write_text(text, encoding="utf-8")

    matches = CUBE_RESULT.findall(text)
    raw_result = int(matches[-1]) if matches else 0
    status = {10: "SAT", 20: "UNSAT"}.get(raw_result, "UNKNOWN")
    if timed_out:
        status = "UNKNOWN"

    record: dict = {
        "schema": "k16-smart-cubing-cube-result-v1",
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "root_slice_id": f"full_s16-{box}",
        "box": box,
        "strategy": strategy,
        "cube_line": cube_line,
        "cube_id": f"{box}-{strategy}-c{cube_line:06d}",
        "cube_literals": literals,
        "cube_depth": len(literals),
        "cube_sha256": cube_hash,
        "parent_cube_sha256": partition["cube_sha256"],
        "enriched_cnf_sha256": manifest["enriched_cnf"]["sha256"],
        "status": status,
        "seconds": round(elapsed, 3),
        "time_limit_seconds": seconds,
        "solver_exit_code": returncode,
        "sms_cube_result": raw_result,
        "timed_out": timed_out,
        "solver_level_exact": status == "UNSAT",
        "command": command,
        "coverage": (
            "One sampled leaf of a complete SMS-generated partition. "
            "UNSAT closes only this leaf; UNKNOWN remains open."
        ),
    }
    if status == "SAT":
        arcs = parse_sms_arcs(text, N)
        if arcs is None:
            record["verified"] = False
            record["verification_error"] = "no parseable SMS tournament"
        else:
            audit = independent_audit(
                arcs,
                lane=LANES["full_s16"],
                box=box,
                directory=result_path.parent / f"{record['cube_id']}-audit",
            )
            record["candidate_arcs"] = arcs
            record["independent_audit"] = audit
            record["verified"] = bool(audit.get("valid"))
            if not record["verified"]:
                raise RuntimeError("cube SAT failed independent audit")

    write_json(result_path, record)
    print(json.dumps(record, indent=2), flush=True)
    return record


def summarize(
    *,
    manifests: list[Path],
    results: list[Path],
    output: Path,
) -> dict:
    partition_records = [
        json.loads(path.read_text(encoding="utf-8"))
        for path in manifests
    ]
    cube_records = [
        json.loads(path.read_text(encoding="utf-8"))
        for path in results
        if json.loads(path.read_text(encoding="utf-8")).get("schema")
        == "k16-smart-cubing-cube-result-v1"
    ]
    by_strategy: dict[str, list[dict]] = defaultdict(list)
    for record in cube_records:
        by_strategy[record["strategy"]].append(record)
    strategy_summary = {}
    for strategy, items in sorted(by_strategy.items()):
        runtimes = [float(item["seconds"]) for item in items]
        strategy_summary[strategy] = {
            "sampled": len(items),
            "statuses": dict(Counter(item["status"] for item in items)),
            "unsat_closed_cube_ids": sorted(
                item["cube_id"] for item in items if item["status"] == "UNSAT"
            ),
            "unknown_cube_ids": sorted(
                item["cube_id"] for item in items if item["status"] == "UNKNOWN"
            ),
            "mean_seconds": (
                round(sum(runtimes) / len(runtimes), 3) if runtimes else None
            ),
        }

    def score(item: tuple[str, dict]) -> tuple[int, int, float]:
        _, summary = item
        statuses = summary["statuses"]
        return (
            statuses.get("UNSAT", 0),
            -statuses.get("UNKNOWN", 0),
            -(summary["mean_seconds"] or 0.0),
        )

    winner = (
        max(strategy_summary.items(), key=score)[0]
        if strategy_summary
        else None
    )
    verified_sat = [
        record["cube_id"]
        for record in cube_records
        if record["status"] == "SAT" and record.get("verified")
    ]
    summary = {
        "schema": "k16-smart-cubing-pilot-ledger-v1",
        "model_version": MODEL_VERSION,
        "created_utc": utc_now(),
        "partitions": partition_records,
        "cube_results": cube_records,
        "strategy_summary": strategy_summary,
        "recommended_strategy": winner,
        "verified_sat_witnesses": verified_sat,
        "logical_conclusion": (
            "SAT_K16_VERIFIED" if verified_sat else "PILOT_COMPLETE_K16_OPEN"
        ),
        "next_action": (
            "Split only UNKNOWN leaves of the recommended strategy; retain "
            "every UNSAT cube in the permanent coverage ledger."
        ),
    }
    write_json(output, summary)
    print(json.dumps(summary, indent=2), flush=True)
    return summary


def main() -> None:
    parser = argparse.ArgumentParser()
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--prepare", action="store_true")
    modes.add_argument("--matrix", action="store_true")
    modes.add_argument("--solve-cube", action="store_true")
    modes.add_argument("--summarize", action="store_true")
    parser.add_argument("--binary", type=Path)
    parser.add_argument("--box", choices=BOXES)
    parser.add_argument("--strategy", choices=("lookahead", "cdcl"))
    parser.add_argument("--strategies", default="lookahead,cdcl")
    parser.add_argument("--work", type=Path)
    parser.add_argument("--prerun-seconds", type=int, default=600)
    parser.add_argument("--cuber-prerun-seconds", type=int, default=30)
    parser.add_argument("--cutoff", type=int, default=32)
    parser.add_argument("--partition-seconds", type=int, default=900)
    parser.add_argument("--coverage-seconds", type=int, default=600)
    parser.add_argument("--cube-line", type=int)
    parser.add_argument("--cube-seconds", type=int, default=300)
    parser.add_argument("--sample-size", type=int, default=16)
    parser.add_argument("--manifest", type=Path, action="append", default=[])
    parser.add_argument("--result-input", type=Path, action="append", default=[])
    parser.add_argument("--result", type=Path)
    parser.add_argument("--log", type=Path)
    args = parser.parse_args()

    if args.prepare:
        if args.binary is None or args.box is None or args.work is None:
            parser.error("--prepare requires --binary --box --work")
        prepare_box(
            binary=args.binary,
            box=args.box,
            work=args.work,
            prerun_seconds=args.prerun_seconds,
            cuber_prerun_seconds=args.cuber_prerun_seconds,
            cutoff=args.cutoff,
            partition_seconds=args.partition_seconds,
            coverage_seconds=args.coverage_seconds,
            strategies=tuple(
                item.strip()
                for item in args.strategies.split(",")
                if item.strip()
            ),
        )
        return
    if args.matrix:
        print(json.dumps(
            cube_matrix(args.manifest, args.sample_size),
            separators=(",", ":"),
        ))
        return
    if args.solve_cube:
        required = (
            args.binary,
            args.box,
            args.strategy,
            args.work,
            args.cube_line,
            args.result,
            args.log,
        )
        if any(value is None for value in required):
            parser.error(
                "--solve-cube requires --binary --box --strategy --work "
                "--cube-line --result --log"
            )
        solve_cube(
            binary=args.binary,
            box=args.box,
            strategy=args.strategy,
            work=args.work,
            cube_line=args.cube_line,
            seconds=args.cube_seconds,
            result_path=args.result,
            log_path=args.log,
        )
        return
    if args.summarize:
        if args.result is None:
            parser.error("--summarize requires --result")
        summarize(
            manifests=args.manifest,
            results=args.result_input,
            output=args.result,
        )
        return


if __name__ == "__main__":
    main()
