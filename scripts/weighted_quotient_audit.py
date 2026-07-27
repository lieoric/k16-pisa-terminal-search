#!/usr/bin/env python3
"""Independent audit of the weighted quotient claims for K16 Pisa.

The audit deliberately does not import the project's SAT encodings.  It uses
Brendan McKay's published non-isomorphic tournament catalogues, an independent
Python implementation for gates and h <= 6, and a separate OpenMP C++ scanner
for h <= 9.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import os
import platform
import random
import shutil
import subprocess
import sys
import time
import urllib.request
from datetime import datetime, timezone
from pathlib import Path


BASE_URL = "https://users.cecs.anu.edu.au/~bdm/data"
CATALOGUES = {
    3: {
        "lines": 2,
        "strong": 1,
        "sha256": "bd80212b5dec58aa23efffad0820023557b925e6203524c183471c6db056a08d",
    },
    4: {
        "lines": 4,
        "strong": 1,
        "sha256": "94683551f4a9be3f7182dfe60b6d880bfb88889382029e1ca47a43af1576f4af",
    },
    5: {
        "lines": 12,
        "strong": 6,
        "sha256": "712da2b5b6402f230f8f9e3cdad044f8115073d42e3ccbcf1f3502ee620172cc",
    },
    6: {
        "lines": 56,
        "strong": 35,
        "sha256": "d9c85e10aaa6a1a71d0358f828ee01a2c5a7a8ad5cb7705ee503231d7d73c8f7",
    },
    7: {
        "lines": 456,
        "strong": 353,
        "sha256": "0cfe541b63bbb90eecda8d6e1f717aaba021c1a6d8ba6fe7cf6ba7bd58b9fd86",
    },
    8: {
        "lines": 6880,
        "strong": 6008,
        "sha256": "26203e97cc710e14aa64a426512618add39b9f42f7a619dcf3058c35df15b37a",
    },
    9: {
        "lines": 191536,
        "strong": 178133,
        "sha256": "1f71781ef5b9a27858b1af167f2fda4346e61f1e4fb78faf2bddfa5948de9b62",
    },
}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def download_catalogues(data_dir: Path) -> list[dict]:
    data_dir.mkdir(parents=True, exist_ok=True)
    records = []
    for h, expected in CATALOGUES.items():
        target = data_dir / f"tourn{h}.txt"
        if not target.exists() or sha256(target) != expected["sha256"]:
            urllib.request.urlretrieve(
                f"{BASE_URL}/tourn{h}.txt",
                target,
            )
        actual_hash = sha256(target)
        lines = sum(1 for line in target.read_text().splitlines() if line)
        if actual_hash != expected["sha256"]:
            raise RuntimeError(
                f"SHA-256 mismatch for {target.name}: {actual_hash}"
            )
        if lines != expected["lines"]:
            raise RuntimeError(
                f"line-count mismatch for {target.name}: {lines}"
            )
        records.append(
            {
                "h": h,
                "url": f"{BASE_URL}/tourn{h}.txt",
                "bytes": target.stat().st_size,
                "lines": lines,
                "sha256": actual_hash,
            }
        )
        print(
            f"CATALOGUE h={h} lines={lines} "
            f"sha256={actual_hash[:16]}...",
            flush=True,
        )
    return records


def decode_tournament(bits: str, h: int) -> list[int]:
    expected = h * (h - 1) // 2
    if len(bits) != expected:
        raise ValueError((h, len(bits), expected))
    out = [0] * h
    k = 0
    for i in range(h):
        for j in range(i + 1, h):
            if bits[k] == "1":
                out[i] |= 1 << j
            elif bits[k] == "0":
                out[j] |= 1 << i
            else:
                raise ValueError("non-bit in tournament catalogue")
            k += 1
    return out


def is_strong(out: list[int]) -> bool:
    n = len(out)
    all_mask = (1 << n) - 1

    def closure(reverse: bool) -> int:
        seen = frontier = 1
        while frontier:
            next_mask = 0
            for u in range(n):
                if not (frontier >> u) & 1:
                    continue
                if not reverse:
                    next_mask |= out[u]
                else:
                    for v in range(n):
                        if (out[v] >> u) & 1:
                            next_mask |= 1 << v
            next_mask &= ~seen
            seen |= next_mask
            frontier = next_mask
        return seen

    return closure(False) == all_mask and closure(True) == all_mask


def strict_second_mask(out: list[int], v: int) -> int:
    second = 0
    for u in range(len(out)):
        if (out[v] >> u) & 1:
            second |= out[u]
    return second & ~out[v] & ~(1 << v)


def margins(out: list[int]) -> list[int]:
    return [
        strict_second_mask(out, v).bit_count() - out[v].bit_count()
        for v in range(len(out))
    ]


def weighted_margins(out: list[int], weights: tuple[int, ...]) -> list[int]:
    result = []
    for v in range(len(out)):
        second = strict_second_mask(out, v)
        positive = sum(
            weights[x] for x in range(len(out)) if (second >> x) & 1
        )
        negative = sum(
            weights[x] for x in range(len(out)) if (out[v] >> x) & 1
        )
        result.append(positive - negative)
    return result


def positive_compositions(total: int, parts: int):
    for cuts in itertools.combinations(range(1, total), parts - 1):
        boundaries = (0, *cuts, total)
        yield tuple(
            boundaries[i + 1] - boundaries[i] for i in range(parts)
        )


def transitive_tournament(size: int) -> list[int]:
    return [
        sum(1 << j for j in range(i + 1, size))
        for i in range(size)
    ]


def random_tournament(size: int, rng: random.Random) -> list[int]:
    out = [0] * size
    for i in range(size):
        for j in range(i + 1, size):
            if rng.getrandbits(1):
                out[i] |= 1 << j
            else:
                out[j] |= 1 << i
    return out


def lexicographic_sum(
    quotient: list[int],
    fibers: list[list[int]],
) -> tuple[list[int], list[int]]:
    offsets = []
    total = 0
    for fiber in fibers:
        offsets.append(total)
        total += len(fiber)

    out = [0] * total
    owner = [0] * total
    for p, fiber in enumerate(fibers):
        offset = offsets[p]
        for v in range(len(fiber)):
            owner[offset + v] = p
            for x in range(len(fiber)):
                if (fiber[v] >> x) & 1:
                    out[offset + v] |= 1 << (offset + x)

    for p in range(len(quotient)):
        for q in range(len(quotient)):
            if p == q or not ((quotient[p] >> q) & 1):
                continue
            for v in range(offsets[p], offsets[p] + len(fibers[p])):
                for x in range(offsets[q], offsets[q] + len(fibers[q])):
                    out[v] |= 1 << x
    return out, owner


def run_identity_gates(rounds: int = 250) -> dict:
    rng = random.Random(20260727)
    checked_vertices = 0

    for _ in range(rounds):
        h = rng.randint(3, 7)
        quotient = random_tournament(h, rng)
        fibers = [
            random_tournament(rng.randint(1, 4), rng)
            for _ in range(h)
        ]
        weights = tuple(map(len, fibers))
        expanded, owner = lexicographic_sum(quotient, fibers)
        expanded_margins = margins(expanded)
        quotient_margins = weighted_margins(quotient, weights)
        local_margins = [margins(fiber) for fiber in fibers]

        local_index = [0] * h
        for vertex, p in enumerate(owner):
            index = local_index[p]
            expected = quotient_margins[p] + local_margins[p][index]
            if expanded_margins[vertex] != expected:
                raise RuntimeError(
                    "lexicographic margin identity gate failed"
                )
            local_index[p] += 1
            checked_vertices += 1

    c3 = [0b010, 0b100, 0b001]
    if weighted_margins(c3, (2, 2, 2)) != [0, 0, 0]:
        raise RuntimeError("C3 positive weighted gate failed")
    c3_expanded, _ = lexicographic_sum(
        c3,
        [transitive_tournament(2) for _ in range(3)],
    )
    if not is_strong(c3_expanded) or max(margins(c3_expanded)) != 0:
        raise RuntimeError("C3 -> K6 construction gate failed")

    c7 = [0] * 7
    for i in range(7):
        for step in (1, 2, 3):
            c7[i] |= 1 << ((i + step) % 7)
    if weighted_margins(c7, (2,) * 7) != [0] * 7:
        raise RuntimeError("C7 positive weighted gate failed")
    c7_expanded, _ = lexicographic_sum(
        c7,
        [transitive_tournament(2) for _ in range(7)],
    )
    if not is_strong(c7_expanded) or max(margins(c7_expanded)) != 0:
        raise RuntimeError("C7 -> K14 construction gate failed")

    c3_sum16_feasible = sum(
        all(value <= 0 for value in weighted_margins(c3, weights))
        for weights in positive_compositions(16, 3)
    )
    if c3_sum16_feasible != 0:
        raise RuntimeError("C3 sum-16 negative gate failed")

    result = {
        "random_lexicographic_tests": rounds,
        "random_vertices_checked": checked_vertices,
        "positive_gate_c3_weights_2": True,
        "positive_gate_c7_weights_2": True,
        "negative_gate_c3_sum_16": True,
    }
    print("IDENTITY_AND_POSITIVE_GATES: PASS", json.dumps(result), flush=True)
    return result


def python_small_audit(data_dir: Path) -> list[dict]:
    rows = []
    for h in range(3, 7):
        weights = list(positive_compositions(16, h))
        strong_count = 0
        feasible_pairs = 0
        path = data_dir / f"tourn{h}.txt"
        for bits in path.read_text().splitlines():
            if not bits:
                continue
            out = decode_tournament(bits, h)
            if not is_strong(out):
                continue
            strong_count += 1
            for weight in weights:
                if all(value <= 0 for value in weighted_margins(out, weight)):
                    feasible_pairs += 1

        if strong_count != CATALOGUES[h]["strong"]:
            raise RuntimeError(f"Python strong count failed for h={h}")
        if feasible_pairs != 0:
            raise RuntimeError(f"Python found feasible pair for h={h}")
        row = {
            "h": h,
            "strong_tournaments": strong_count,
            "weight_vectors": len(weights),
            "tested_pairs": strong_count * len(weights),
            "feasible_pairs": feasible_pairs,
        }
        rows.append(row)
        print(f"PYTHON_CROSSCHECK {json.dumps(row, sort_keys=True)}", flush=True)
    return rows


def compile_and_run_cpp(
    repo_root: Path,
    data_dir: Path,
    output_dir: Path,
    threads: int,
) -> tuple[dict, dict]:
    compiler = shutil.which("g++")
    if not compiler:
        raise RuntimeError("g++ is unavailable")
    source = repo_root / "src" / "weighted_quotient_audit.cpp"
    binary = output_dir / "weighted_quotient_audit"
    if platform.system() == "Windows":
        binary = binary.with_suffix(".exe")
    cpp_json = output_dir / "weighted_quotient_cpp.json"

    base_compile_command = [
        compiler,
        "-O3",
        "-std=c++17",
        str(source),
        "-o",
        str(binary),
    ]
    if platform.system() != "Windows":
        base_compile_command.insert(2, "-march=native")

    compile_command = base_compile_command[:3] + [
        "-fopenmp",
    ] + base_compile_command[3:]
    compile_attempt = subprocess.run(
        compile_command,
        text=True,
        capture_output=True,
    )
    openmp_enabled = compile_attempt.returncode == 0
    if not openmp_enabled:
        print(
            "OPENMP_COMPILE_FALLBACK:",
            compile_attempt.stderr.strip().splitlines()[-1],
            flush=True,
        )
        compile_command = base_compile_command
        subprocess.run(compile_command, check=True)

    version = subprocess.run(
        [compiler, "--version"],
        check=True,
        text=True,
        capture_output=True,
    ).stdout.splitlines()[0]
    environment = os.environ.copy()
    environment["OMP_NUM_THREADS"] = str(max(1, threads))
    started = time.monotonic()
    subprocess.run(
        [str(binary), str(data_dir), str(cpp_json)],
        check=True,
        env=environment,
    )
    wall_seconds = time.monotonic() - started
    cpp_result = json.loads(cpp_json.read_text())
    metadata = {
        "compiler": version,
        "compile_command": compile_command,
        "source_sha256": sha256(source),
        "wall_seconds": wall_seconds,
        "requested_threads": threads,
        "openmp_enabled": openmp_enabled,
    }
    return cpp_result, metadata


def validate_cpp_result(
    cpp_result: dict,
    python_rows: list[dict],
) -> None:
    rows = {row["h"]: row for row in cpp_result["rows"]}
    for h, expected in CATALOGUES.items():
        row = rows[h]
        expected_weights = len(list(positive_compositions(16, h)))
        if row["catalogue_tournaments"] != expected["lines"]:
            raise RuntimeError(f"C++ catalogue count failed for h={h}")
        if row["strong_tournaments"] != expected["strong"]:
            raise RuntimeError(f"C++ strong count failed for h={h}")
        if row["weight_vectors"] != expected_weights:
            raise RuntimeError(f"C++ weight count failed for h={h}")
        if row["tested_pairs"] != expected["strong"] * expected_weights:
            raise RuntimeError(f"C++ tested-pair count failed for h={h}")
        if row["feasible_pairs"] != 0:
            raise RuntimeError(f"C++ found a feasible pair for h={h}")

    python_by_h = {row["h"]: row for row in python_rows}
    for h in range(3, 7):
        for key in (
            "strong_tournaments",
            "weight_vectors",
            "tested_pairs",
            "feasible_pairs",
        ):
            if rows[h][key] != python_by_h[h][key]:
                raise RuntimeError(
                    f"Python/C++ disagreement at h={h}, key={key}"
                )


def write_markdown(report: dict, path: Path) -> None:
    lines = [
        "# K16 weighted quotient audit",
        "",
        f"- Status: **{report['status']}**",
        f"- UTC: `{report['created_utc']}`",
        f"- Target total weight: `{report['target_weight']}`",
        f"- Catalogue source: `{BASE_URL}`",
        "",
        "| h | catalogue | strong | weights | tested pairs | feasible | seconds |",
        "|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for row in report["cpp"]["rows"]:
        lines.append(
            f"| {row['h']} | {row['catalogue_tournaments']} | "
            f"{row['strong_tournaments']} | {row['weight_vectors']} | "
            f"{row['tested_pairs']} | {row['feasible_pairs']} | "
            f"{row['seconds']:.3f} |"
        )
    lines.extend(
        [
            "",
            "All `feasible = 0` rows are exact exhaustive results over the",
            "published non-isomorphic tournament representatives and all",
            "ordered positive weight compositions summing to 16.",
            "",
            "Logical consequence used here:",
            "`no feasible quotient with h <= 9` implies that a K16 Pisa",
            "witness has no module of size at least 8.  The converse is not",
            "claimed.",
        ]
    )
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("/kaggle/working")
        if Path("/kaggle/working").exists()
        else Path("worktest/weighted-quotient-audit"),
    )
    parser.add_argument(
        "--threads",
        type=int,
        default=max(1, min(4, os.cpu_count() or 1)),
    )
    args = parser.parse_args()

    repo_root = args.repo_root.resolve()
    output_dir = args.output_dir.resolve()
    output_dir.mkdir(parents=True, exist_ok=True)
    data_dir = output_dir / "mckay-tournaments"

    print("=" * 88)
    print("K16 PISA WEIGHTED QUOTIENT INDEPENDENT AUDIT")
    print("repo:", repo_root)
    print("output:", output_dir)
    print("threads:", args.threads)
    print("=" * 88, flush=True)

    created = datetime.now(timezone.utc).isoformat()
    catalogues = download_catalogues(data_dir)
    gates = run_identity_gates()
    python_rows = python_small_audit(data_dir)
    cpp_result, cpp_metadata = compile_and_run_cpp(
        repo_root,
        data_dir,
        output_dir,
        args.threads,
    )
    validate_cpp_result(cpp_result, python_rows)

    report = {
        "schema": "k16-pisa-weighted-quotient-audit-v1",
        "status": "PASS_EXHAUSTIVE_H3_TO_H9",
        "created_utc": created,
        "target_weight": 16,
        "catalogue_source": BASE_URL,
        "catalogues": catalogues,
        "gates": gates,
        "python_crosscheck_h3_to_h6": python_rows,
        "cpp": cpp_result,
        "cpp_metadata": cpp_metadata,
        "environment": {
            "python": sys.version,
            "platform": platform.platform(),
            "cpu_count": os.cpu_count(),
        },
        "logical_scope": {
            "proved_by_computation": (
                "No strong weighted quotient of order 3 through 9 "
                "with positive integer weights summing to 16 satisfies "
                "all strict-second-neighborhood weighted margins <= 0."
            ),
            "module_consequence": (
                "Any K16 Pisa witness has no module of size at least 8."
            ),
            "not_claimed": [
                "The converse between h <= 9 quotients and module size.",
                "Nonexistence of a K16 Pisa witness.",
                "Any conclusion about quotient orders 10 through 16.",
            ],
        },
    }

    json_path = output_dir / "k16_weighted_quotient_audit.json"
    markdown_path = output_dir / "k16_weighted_quotient_audit.md"
    json_path.write_text(
        json.dumps(report, indent=2, sort_keys=True),
        encoding="utf-8",
    )
    write_markdown(report, markdown_path)

    print("=" * 88)
    print("AUDIT_STATUS: PASS_EXHAUSTIVE_H3_TO_H9")
    print("JSON:", json_path)
    print("MARKDOWN:", markdown_path)
    print("=" * 88, flush=True)


if __name__ == "__main__":
    main()
