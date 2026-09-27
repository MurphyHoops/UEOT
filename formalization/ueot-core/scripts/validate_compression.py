#!/usr/bin/env python3
"""Zero-dependency validator for UEOT Core compression governance.

COMPRESSION_LEDGER.yaml is intentionally JSON-compatible YAML so validation can
use only Python's standard library on GitHub runners.
"""

from __future__ import annotations

import argparse
import csv
import json
import re
import subprocess
import sys
from pathlib import Path


PID_RE = re.compile(r"^P-[A-Z]+-\d{2}$")
MID_RE = re.compile(r"^M-[A-Z]{2,4}-\d{2}$")

GENERATOR_STATES = {
    "candidate",
    "schema_locked",
    "lean_wip",
    "lean_green",
    "cross_family_green",
    "integration_green",
    "main_green",
    "ledger_green",
    "counted_generator",
    "rejected",
}

MAPPING_STATES = {
    "conjectured",
    "source_aligned",
    "statement_matched",
    "lean_rederived_partial",
    "lean_rederived",
    "assumption_audited",
    "main_green",
    "counted",
    "rejected",
}

PROTECTED_BASELINE_FILES = {
    "formalization/ueot-core/docs/V3_COVERAGE_STATUS.md",
    "formalization/ueot-core/docs/PID_STATUS.yaml",
}

FROZEN_LEAN_ROOT = "formalization/ueot-core/UEOT/"
COMPRESSION_LEAN_ALLOWLIST = {
    "formalization/ueot-core/UEOT/V3/Compression.lean",
}
COMPRESSION_LEAN_PREFIXES = (
    "formalization/ueot-core/UEOT/V3/Compression/",
)
LEAN_DECL_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$")


def fail(message: str) -> None:
    print(f"ERROR: {message}", file=sys.stderr)
    raise SystemExit(1)


def git(repo: Path, *args: str) -> str:
    return subprocess.check_output(
        ["git", *args], cwd=repo, text=True, stderr=subprocess.STDOUT
    ).strip()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", default=".")
    parser.add_argument("--baseline-ref")
    parser.add_argument(
        "--emit-lean-witness-audit",
        help="write a generated Lean file that #check's every ledger theorem witness",
    )
    args = parser.parse_args()

    repo = Path(args.repo_root).resolve()
    core = repo / "formalization/ueot-core"
    index_path = core / "docs/CORE_COMPRESSION_THEOREM_INDEX.csv"
    ledger_path = core / "docs/compression/COMPRESSION_LEDGER.yaml"
    coverage_path = core / "docs/compression/COMPRESSION_COVERAGE.md"
    operations_path = core / "docs/compression/COMPRESSION_OPERATIONS.md"
    bootstrap_path = core / "docs/compression/COMPRESSION_BOOTSTRAP.md"

    for path in (
        index_path,
        ledger_path,
        coverage_path,
        operations_path,
        bootstrap_path,
    ):
        if not path.is_file():
            fail(f"required compression governance file missing: {path}")

    with index_path.open(newline="", encoding="utf-8") as f:
        rows = list(csv.DictReader(f))
    pids = [row["pid"] for row in rows]
    if len(rows) != 106:
        fail(f"compression theorem index must have 106 rows, found {len(rows)}")
    if len(set(pids)) != 106:
        fail("compression theorem index contains duplicate P-IDs")
    bad_pids = [pid for pid in pids if not PID_RE.fullmatch(pid)]
    if bad_pids:
        fail(f"invalid P-ID format in theorem index: {bad_pids}")
    pid_set = set(pids)

    try:
        ledger = json.loads(ledger_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        fail(f"COMPRESSION_LEDGER.yaml must remain JSON-compatible YAML: {exc}")

    if ledger.get("schema_version") != 1:
        fail("unsupported compression ledger schema_version")

    baseline = ledger.get("baseline", {})
    if baseline.get("source_pids") != 106 or baseline.get("source_proved") != 106:
        fail("compression ledger must preserve the 106/106 frozen source baseline")
    if baseline.get("source_sha256") != (
        "ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303"
    ):
        fail("compression ledger source hash does not match the frozen source")

    coverage = ledger.get("coverage", {})
    required_counts = {
        "analyzed_pids",
        "schema_classified_pids",
        "lean_rederived_pids",
        "counted_compressed_pids",
        "confirmed_adapter_pids",
        "counted_generators",
    }
    missing_counts = required_counts - set(coverage)
    if missing_counts:
        fail(f"compression coverage missing fields: {sorted(missing_counts)}")
    for key in required_counts:
        value = coverage[key]
        if not isinstance(value, int) or value < 0:
            fail(f"compression coverage {key} must be a nonnegative integer")
        if key != "counted_generators" and value > 106:
            fail(f"compression coverage {key} cannot exceed 106")

    if coverage["counted_compressed_pids"] > coverage["lean_rederived_pids"]:
        fail("counted compressed P-IDs cannot exceed Lean-rederived P-IDs")
    if coverage["lean_rederived_pids"] > coverage["schema_classified_pids"]:
        fail("Lean-rederived P-IDs cannot exceed schema-classified P-IDs")
    if coverage["schema_classified_pids"] > coverage["analyzed_pids"]:
        fail("schema-classified P-IDs cannot exceed analyzed P-IDs")

    generators = ledger.get("generators", {})
    if not isinstance(generators, dict) or not generators:
        fail("compression ledger must contain at least one generator")

    exact_rederived: set[str] = set()
    counted_pids: set[str] = set()
    counted_generators = 0
    lean_witnesses: set[str] = set()

    for mid, generator in generators.items():
        if not MID_RE.fullmatch(mid):
            fail(f"invalid M-ID: {mid}")
        state = generator.get("state")
        if state not in GENERATOR_STATES:
            fail(f"{mid}: invalid generator state {state!r}")
        theorems = generator.get("canonical_theorems", [])
        if state not in {"candidate", "schema_locked", "lean_wip", "rejected"} and not theorems:
            fail(f"{mid}: Lean-green-or-later generator needs canonical_theorems")
        for theorem in theorems:
            if not isinstance(theorem, str) or not LEAN_DECL_RE.fullmatch(theorem):
                fail(f"{mid}: invalid canonical theorem name {theorem!r}")
            lean_witnesses.add(theorem)

        mappings = generator.get("mappings", {})
        if not isinstance(mappings, dict):
            fail(f"{mid}: mappings must be an object")

        cross_family_exact = set()
        for pid, mapping in mappings.items():
            if pid not in pid_set:
                fail(f"{mid}: mapping references unknown frozen P-ID {pid}")
            mstate = mapping.get("state")
            if mstate not in MAPPING_STATES:
                fail(f"{mid}/{pid}: invalid mapping state {mstate!r}")
            conclusion = mapping.get("conclusion_relation")
            assumptions = mapping.get("assumption_relation")

            if mstate in {
                "lean_rederived_partial",
                "lean_rederived",
                "assumption_audited",
                "main_green",
                "counted",
            }:
                witnesses = mapping.get("witness_theorems")
                if not witnesses:
                    fail(f"{mid}/{pid}: Lean-derived mapping needs witness_theorems")
                for theorem in witnesses:
                    if not isinstance(theorem, str) or not LEAN_DECL_RE.fullmatch(theorem):
                        fail(f"{mid}/{pid}: invalid witness theorem name {theorem!r}")
                    lean_witnesses.add(theorem)
                if not assumptions or not conclusion:
                    fail(f"{mid}/{pid}: Lean-derived mapping needs assumption/conclusion relations")

            if mstate == "lean_rederived_partial" and conclusion == "exact":
                fail(f"{mid}/{pid}: partial rederivation cannot claim exact conclusion")

            if mstate in {"lean_rederived", "assumption_audited", "main_green", "counted"}:
                if conclusion != "exact":
                    fail(f"{mid}/{pid}: full rederivation must have exact conclusion relation")
                exact_rederived.add(pid)
                cross_family_exact.add(pid.split("-")[1])

            if mstate == "counted":
                if not mapping.get("promotion"):
                    fail(f"{mid}/{pid}: counted mapping needs promotion evidence")
                counted_pids.add(pid)

        if state in {
            "cross_family_green",
            "integration_green",
            "main_green",
            "ledger_green",
            "counted_generator",
        } and len(cross_family_exact) < 2:
            fail(f"{mid}: cross-family state requires exact mappings in at least two P-ID families")

        if state == "counted_generator":
            counted_generators += 1
            if not generator.get("promotion"):
                fail(f"{mid}: counted generator needs promotion evidence")

    if coverage["lean_rederived_pids"] != len(exact_rederived):
        fail(
            "lean_rederived_pids disagrees with exact Lean-derived mappings: "
            f"ledger={coverage['lean_rederived_pids']} derived={len(exact_rederived)}"
        )
    if coverage["counted_compressed_pids"] != len(counted_pids):
        fail("counted_compressed_pids disagrees with counted mappings")
    if coverage["counted_generators"] != counted_generators:
        fail("counted_generators disagrees with counted generator states")

    coverage_text = coverage_path.read_text(encoding="utf-8")
    if "106/106 FULL-GREEN" not in coverage_text:
        fail("human compression coverage file must preserve 106/106 baseline wording")

    if args.baseline_ref:
        try:
            changed = set(
                git(repo, "diff", "--name-only", f"{args.baseline_ref}...HEAD").splitlines()
            )
        except subprocess.CalledProcessError as exc:
            fail(f"could not compare against baseline ref {args.baseline_ref}: {exc.output}")
        protected_changed = PROTECTED_BASELINE_FILES & changed
        if protected_changed:
            fail(
                "compression branch modified protected source-proof ledgers: "
                + ", ".join(sorted(protected_changed))
            )

        frozen_lean_changed = sorted(
            path
            for path in changed
            if path.startswith(FROZEN_LEAN_ROOT)
            and path not in COMPRESSION_LEAN_ALLOWLIST
            and not any(path.startswith(prefix) for prefix in COMPRESSION_LEAN_PREFIXES)
        )
        if frozen_lean_changed:
            fail(
                "compression work modified frozen/non-compression Lean modules: "
                + ", ".join(frozen_lean_changed)
            )

    if args.emit_lean_witness_audit:
        audit_path = Path(args.emit_lean_witness_audit)
        audit_path.parent.mkdir(parents=True, exist_ok=True)
        lines = [
            "import UEOT.V3.Compression",
            "",
            "-- Generated from COMPRESSION_LEDGER.yaml by validate_compression.py.",
            "-- CI compiles this file so stale/typo/fabricated theorem names cannot pass.",
        ]
        lines.extend(f"#check {name}" for name in sorted(lean_witnesses))
        audit_path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    print("Compression governance validation PASS")
    print("source_index=106 unique=106")
    print(f"generators={len(generators)}")
    print(f"exact_lean_rederived_pids={len(exact_rederived)}")
    print(f"counted_compressed_pids={len(counted_pids)}")
    print(f"counted_generators={counted_generators}")


if __name__ == "__main__":
    main()
