#!/usr/bin/env python3
"""Create a lightweight publication audit from the completed K16 campaign.

This program does not call a SAT solver.  It independently checks the frozen
terminal manifest emitted by the V24-F forest reconstructor, rematerializes
every terminal CNF hash using only the Python standard library, verifies the
four historical ledger hashes, and emits a compact paper-facing audit bundle.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path


SCHEMA = "k16-v24i-publication-computation-audit-v2"
EXPECTED_PLAN_SCHEMA = "k16-v24f-complete-certificate-plan-v1"
EXPECTED_RUNS = {
    "v23": "30417759253",
    "v24b": "30490334948",
    "v24c": "30587970184",
    "v24d": "30602758451",
}
EXPECTED_COMMITS = {
    "v23": "d25d25169f216f36da9c12766493049d376eb0d7",
    "v24b": "1ef79e1343ee510247fbfae566741ced4a4acc60",
    "v24c": "be45be4731385dfc8d34fa718fccd98b141bc00b",
    "v24d": "7e639de2d6b68ec903e375c8f05dfa593b89f5d2",
}
EXPECTED_LEDGER_SCHEMAS = {
    "v23": "k16-v23-atlas-cleanup-ledger-v1",
    "v24b": "k16-v24b-ledger-v1",
    "v24c": "k16-v24c-ledger-v1",
    "v24d": "k16-v24d-ledger-v1",
}
EXPECTED_LEDGER_HASHES = {
    "v23": "c67993b60cd20e6531c1e4cc02f2ef1b5ac3de4aa88316a16e8a85701d4d0e65",
    "v24b": "93809424b3a12ce660f7cc08c9a0511c445f25fffba0b30d384102a1d1d9619e",
    "v24c": "7b55891d92d3827c9891a62e2d196ce664cd6953b103a4daa956ebb245bace97",
    "v24d": "09bc7efaf6f4860addb9706724fefe6f9498b62f949bcf256e50e655537172b0",
}
EXPECTED_BOX_COUNTS = {
    "a0_z2": 141,
    "a0_z3": 208,
    "a0_z4p": 251,
    "a1_z2": 121,
    "a1_z4p": 151,
    "a2p_z2": 101,
    "a2p_z3": 151,
}
EXPECTED_STAGE_COUNTS = {
    "v23": 581,
    "v24b": 353,
    "v24b_unit": 3,
    "v24c": 177,
    "v24c_unit": 2,
    "v24d": 8,
}
EXPECTED_METHOD_COUNTS = {
    "cadical1800": 530,
    "cadical3600": 469,
    "kissat3600": 69,
    "sms3600": 51,
    "unit_propagation": 5,
}
EXPECTED_THEOREM_CNFS = {
    "a0_z2": "d3f94b91771d8ac1017f2a5ff349c56fc05dd2fd491d46b13c30ae543014a752",
    "a0_z3": "a300817544532da961677934274bb9ec5f362dcc10e5dbf4e68a8b84a5584f93",
    "a0_z4p": "7ac29953e3ecb042043da00354510e016b9e1d9ba2da50f9677a2ded54eef56a",
    "a1_z2": "3dde2ce5c197d0faf48f772c30659097258ddd49b07b98184186d6ef7c91f8c9",
    "a1_z4p": "7922e2434ec5182e1598d89310e085f3da21fcaed644568e7e07ac2fac677016",
    "a2p_z2": "dd36630569200777982d146f2320e0a26788e5b86475881a3c3196befbedb84d",
    "a2p_z3": "4b1adc390f7daf8f9a9ac4e8161a2b08f6a6de87096585e896d174f83ec012e8",
}


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def object_sha256(value: object) -> str:
    payload = json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def cube_sha256(literals: list[int]) -> str:
    payload = " ".join(str(literal) for literal in literals)
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def assumption_cnf_payload(
    source: Path,
    cube: list[int],
) -> list[str]:
    """Return the logical DIMACS lines for one theorem CNF plus its cube."""
    text = source.read_text(encoding="utf-8")
    lines = text.splitlines()
    if not lines:
        raise RuntimeError(f"empty DIMACS file: {source}")
    match = re.fullmatch(r"p cnf (\d+) (\d+)", lines[0])
    if not match:
        raise RuntimeError(f"invalid DIMACS header: {source}")
    variables = int(match.group(1))
    clauses = int(match.group(2))
    return [
        f"p cnf {variables} {clauses + len(cube)}",
        *lines[1:],
        *(f"{literal} 0" for literal in cube),
    ]


def assumption_cnf_sha256(
    source: Path,
    cube: list[int],
    newline: str = "\n",
) -> str:
    logical_lines = assumption_cnf_payload(source, cube)
    return hashlib.sha256(
        (newline.join(logical_lines) + newline).encode("utf-8")
    ).hexdigest()


def assumption_cnf_sha256_variants(
    source: Path,
    cube: list[int],
) -> set[str]:
    """Hash the exact LF and CRLF outputs of the historical text writer."""
    # Python's text writer uses the host newline convention.  The frozen
    # GitHub run is LF; allowing CRLF also makes the audit locally repeatable
    # on Windows without weakening any content check.
    return {
        assumption_cnf_sha256(source, cube, newline)
        for newline in ("\n", "\r\n")
    }


def require_equal(actual: object, expected: object, label: str) -> None:
    if actual != expected:
        raise RuntimeError(
            f"{label} mismatch: expected {expected!r}, got {actual!r}"
        )


def validate_historical_ledgers(
    ledger_paths: dict[str, Path],
    manifest: dict,
) -> dict[str, dict]:
    records = {}
    for stage, path in ledger_paths.items():
        digest = sha256(path)
        require_equal(digest, EXPECTED_LEDGER_HASHES[stage], f"{stage} hash")
        require_equal(
            digest,
            manifest["source_hashes"][f"{stage}_ledger"],
            f"{stage} manifest hash",
        )
        record = load_json(path)
        require_equal(
            record.get("schema"),
            EXPECTED_LEDGER_SCHEMAS[stage],
            f"{stage} schema",
        )
        records[stage] = record
    require_equal(
        records["v24d"].get("logical_conclusion"),
        "V24D_ALL_676_PARTITION_LEAVES_EXACTLY_CLOSED",
        "V24-D endpoint",
    )
    return records


def validate_manifest(
    source: Path,
    ledger_paths: dict[str, Path],
) -> tuple[dict, list[dict], dict]:
    manifest_path = source / "v24f-certificate-manifest.json"
    manifest = load_json(manifest_path)
    require_equal(manifest.get("schema"), EXPECTED_PLAN_SCHEMA, "plan schema")
    require_equal(manifest["historical_runs"], EXPECTED_RUNS, "run IDs")
    require_equal(
        manifest["historical_commits"],
        EXPECTED_COMMITS,
        "source commits",
    )
    validate_historical_ledgers(ledger_paths, manifest)

    coverage = manifest["coverage"]
    require_equal(coverage["original_partition_leaves"], 676, "root leaves")
    require_equal(coverage["v23_direct_unsat_leaves"], 581, "V23 UNSAT")
    require_equal(coverage["v23_refined_leaves"], 95, "V23 refinements")
    require_equal(
        coverage["v24b_refined_unknown_children"], 23, "V24-B refinements"
    )
    require_equal(
        coverage["v24c_refined_unknown_children"], 1, "V24-C refinements"
    )
    require_equal(
        coverage["terminal_certificate_tasks"], 1124, "terminal count"
    )
    if not coverage.get("all_historical_tree_audits_passed"):
        raise RuntimeError("historical binary-tree audit was not passed")

    tasks = manifest["certificate_tasks"]
    require_equal(len(tasks), 1124, "terminal records")
    identifiers = [task["certificate_task_id"] for task in tasks]
    require_equal(len(set(identifiers)), len(identifiers), "unique task IDs")
    require_equal(
        dict(Counter(task["stage"] for task in tasks)),
        EXPECTED_STAGE_COUNTS,
        "stage counts",
    )
    require_equal(
        dict(Counter(task["box"] for task in tasks)),
        EXPECTED_BOX_COUNTS,
        "box counts",
    )
    require_equal(
        dict(Counter(task["historical_method"] for task in tasks)),
        EXPECTED_METHOD_COUNTS,
        "solver-method counts",
    )

    roots: defaultdict[str, list[str]] = defaultdict(list)
    for task in tasks:
        literals = [int(value) for value in task["cube_literals"]]
        if len({abs(value) for value in literals}) != len(literals):
            raise RuntimeError(
                f"repeated or contradictory cube variable: "
                f"{task['certificate_task_id']}"
            )
        require_equal(task["cube_depth"], len(literals), "cube depth")
        require_equal(
            task["cube_sha256"],
            cube_sha256(literals),
            f"{task['certificate_task_id']} cube hash",
        )
        root = task["lineage"].get("v23_source_leaf_id")
        if not root:
            raise RuntimeError(
                f"terminal lacks a V23 root: {task['certificate_task_id']}"
            )
        roots[root].append(task["certificate_task_id"])
        if task["historical_method"] == "unit_propagation":
            if task.get("historical_result_task_id") is not None:
                raise RuntimeError("unit terminal unexpectedly has solver ID")
        elif (
            not task.get("historical_result_task_id")
            or float(task.get("historical_seconds", 0)) <= 0
        ):
            raise RuntimeError(
                f"terminal lacks exact solver provenance: "
                f"{task['certificate_task_id']}"
            )

    require_equal(len(roots), 676, "covered V23 roots")
    require_equal(
        sum(len(values) for values in roots.values()),
        1124,
        "root-to-terminal incidence",
    )

    formula_hashes = {}
    for box, expected_hash in EXPECTED_THEOREM_CNFS.items():
        cnf = source / "boxes" / box / "enriched.cnf"
        actual_hash = sha256(cnf)
        require_equal(actual_hash, expected_hash, f"{box} CNF hash")
        require_equal(
            actual_hash,
            manifest["source_hashes"]["theorem_cnfs"][box],
            f"{box} manifest CNF hash",
        )
        formula_hashes[box] = actual_hash

    for index, task in enumerate(tasks, start=1):
        theorem_cnf = source / "boxes" / task["box"] / "enriched.cnf"
        actual_hashes = assumption_cnf_sha256_variants(
            theorem_cnf, task["cube_literals"]
        )
        if task["assumption_cnf_sha256"] not in actual_hashes:
            raise RuntimeError(
                f"terminal formula {index}/1124 hash mismatch: "
                f"{task['certificate_task_id']}"
            )
        task["canonical_assumption_cnf_sha256"] = assumption_cnf_sha256(
            theorem_cnf, task["cube_literals"]
        )

    logical_terminals = []
    ignored_fields = {
        "wave",
        "assumption_cnf_sha256",
        "canonical_assumption_cnf_sha256",
    }
    for task in sorted(tasks, key=lambda item: item["certificate_task_id"]):
        logical_terminal = {
                key: value
                for key, value in task.items()
                if key not in ignored_fields
        }
        logical_terminal["assumption_cnf_sha256"] = task[
            "canonical_assumption_cnf_sha256"
        ]
        logical_terminals.append(logical_terminal)
    publication_hash = object_sha256(
        {
            "historical_runs": EXPECTED_RUNS,
            "historical_commits": EXPECTED_COMMITS,
            "ledger_hashes": EXPECTED_LEDGER_HASHES,
            "theorem_cnfs": formula_hashes,
            "coverage": coverage,
            "terminal_records": logical_terminals,
        }
    )
    details = {
        "roots": roots,
        "formula_hashes": formula_hashes,
        "publication_hash": publication_hash,
        "manifest_sha256": sha256(manifest_path),
    }
    return manifest, tasks, details


def write_terminal_csv(path: Path, tasks: list[dict]) -> None:
    fields = (
        "certificate_task_id",
        "v23_source_leaf_id",
        "stage",
        "box",
        "cube_depth",
        "cube_sha256",
        "assumption_cnf_sha256",
        "historical_method",
        "historical_seconds",
        "historical_result_task_id",
    )
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for task in sorted(
            tasks, key=lambda item: item["certificate_task_id"]
        ):
            writer.writerow(
                {
                    "certificate_task_id": task["certificate_task_id"],
                    "v23_source_leaf_id": task["lineage"][
                        "v23_source_leaf_id"
                    ],
                    "stage": task["stage"],
                    "box": task["box"],
                    "cube_depth": task["cube_depth"],
                    "cube_sha256": task["cube_sha256"],
                    "assumption_cnf_sha256": task[
                        "canonical_assumption_cnf_sha256"
                    ],
                    "historical_method": task["historical_method"],
                    "historical_seconds": task["historical_seconds"],
                    "historical_result_task_id": (
                        task.get("historical_result_task_id") or ""
                    ),
                }
            )


def write_checksums(output: Path) -> None:
    targets = sorted(
        path
        for path in output.iterdir()
        if path.is_file() and path.name != "SHA256SUMS"
    )
    content = "".join(
        f"{sha256(path)}  {path.name}\n" for path in targets
    )
    (output / "SHA256SUMS").write_text(content, encoding="utf-8")


def run(args: argparse.Namespace) -> dict:
    ledger_paths = {
        "v23": args.v23_ledger,
        "v24b": args.v24b_ledger,
        "v24c": args.v24c_ledger,
        "v24d": args.v24d_ledger,
    }
    manifest, tasks, details = validate_manifest(args.source, ledger_paths)
    output = args.output
    output.mkdir(parents=True, exist_ok=True)

    audit = {
        "schema": SCHEMA,
        "created_utc": utc_now(),
        "logical_conclusion": (
            "K16_PRIMITIVE_676_OF_676_SOLVER_LEVEL_UNSAT_AUDITED"
        ),
        "publication_audit_sha256": details["publication_hash"],
        "source_manifest_sha256": details["manifest_sha256"],
        "historical_runs": EXPECTED_RUNS,
        "historical_commits": EXPECTED_COMMITS,
        "historical_ledger_sha256": EXPECTED_LEDGER_HASHES,
        "theorem_cnf_sha256": details["formula_hashes"],
        "coverage": {
            "original_partition_leaves": 676,
            "covered_original_partition_leaves": len(details["roots"]),
            "terminal_formulas": len(tasks),
            "unknown_terminal_formulas": 0,
            "missing_terminal_formulas": 0,
            "sat_terminal_formulas": 0,
            "solver_level_unsat_terminal_formulas": 1119,
            "unit_propagation_unsat_terminal_formulas": 5,
        },
        "stage_counts": EXPECTED_STAGE_COUNTS,
        "box_counts": EXPECTED_BOX_COUNTS,
        "solver_method_counts": EXPECTED_METHOD_COUNTS,
        "historical_solver_cpu_seconds": round(
            sum(float(task["historical_seconds"]) for task in tasks),
            3,
        ),
        "checks": {
            "historical_run_ids_frozen": True,
            "historical_commits_frozen": True,
            "historical_ledger_hashes_verified": True,
            "binary_refinement_tree_audits_passed": True,
            "all_676_roots_have_terminal_cover": True,
            "all_1124_terminal_formulas_rematerialized": True,
            "all_terminal_formula_hashes_verified": True,
            "no_unknown_terminal": True,
            "no_missing_terminal": True,
            "no_sat_terminal": True,
        },
        "claim_boundary": (
            "This audit establishes the reproducible solver-level closure "
            "of the frozen 676-leaf primitive K16 computation. It does not "
            "replace the paper's human proofs that the seven root boxes are "
            "exhaustive or that each CNF faithfully encodes the stated "
            "Pisa-tournament conditions."
        ),
        "optional_partial_certificates": (
            "Any separately stored DRAT/LRAT samples are supplementary "
            "spot checks and are not required by this audit conclusion."
        ),
        "source_plan_coverage": manifest["coverage"],
    }
    (output / "publication-audit.json").write_text(
        json.dumps(audit, indent=2) + "\n",
        encoding="utf-8",
    )
    write_terminal_csv(output / "terminal-formulas.csv", tasks)
    (output / "PUBLICATION_AUDIT.md").write_text(
        "# K16 primitive computation publication audit\n\n"
        f"- Conclusion: `{audit['logical_conclusion']}`\n"
        f"- Original leaves covered: `676 / 676`\n"
        f"- Exact terminal formulas: `{len(tasks)}`\n"
        "- Terminal status: `1119 solver UNSAT + 5 unit UNSAT`\n"
        "- Remaining UNKNOWN/SAT/missing terminals: `0 / 0 / 0`\n"
        f"- Publication audit SHA-256: "
        f"`{details['publication_hash']}`\n\n"
        "This is a reproducible computation audit, not a per-leaf formal "
        "proof-certificate archive. See `publication-audit.json` for the "
        "precise claim boundary.\n",
        encoding="utf-8",
    )
    write_checksums(output)
    print(json.dumps(audit, indent=2), flush=True)
    return audit


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser()
    result.add_argument("--source", type=Path, required=True)
    result.add_argument("--v23-ledger", type=Path, required=True)
    result.add_argument("--v24b-ledger", type=Path, required=True)
    result.add_argument("--v24c-ledger", type=Path, required=True)
    result.add_argument("--v24d-ledger", type=Path, required=True)
    result.add_argument("--output", type=Path, required=True)
    return result


if __name__ == "__main__":
    run(parser().parse_args())
