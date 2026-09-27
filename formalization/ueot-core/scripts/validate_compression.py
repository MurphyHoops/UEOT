#!/usr/bin/env python3
"""Zero-dependency validator for UEOT Core compression governance.

COMPRESSION_LEDGER.yaml is intentionally JSON-compatible YAML so validation can
use only Python's standard library on GitHub runners.
"""

from __future__ import annotations

import argparse
import csv
import json
import os
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

MISSION_STATES = {"active", "ready_for_finalization", "final"}
DISPOSITION_STATES = {"generated", "retained_adapter", "retained_boundary"}
MINIMAL_CORE_STATES = {"open", "candidate", "frozen"}
ABLATION_STATES = {"not_started", "in_progress", "complete"}
MINIMALITY_CLAIMS = {
    "not_established",
    "nonredundant_under_declared_derivation_system",
}
NONREDUNDANT_ABLATION = "nonredundant_under_declared_derivation_system"
SOURCE_FAITHFUL_ASSUMPTION_RELATIONS = {"exact", "weaker"}
REPO_FULL_NAME = "MurphyHoops/UEOT"
MIN_RATIONALE_LENGTH = 20

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


def nonempty_string(value: object, *, min_length: int = 1) -> bool:
    return isinstance(value, str) and len(value.strip()) >= min_length


def validate_audit_evidence(
    repo: Path,
    refs: object,
    lean_witnesses: set[str],
    context: str,
) -> None:
    if not isinstance(refs, list) or not refs:
        fail(f"{context}: needs nonempty audit_evidence references")

    for raw_ref in refs:
        if not nonempty_string(raw_ref):
            fail(f"{context}: audit_evidence entries must be nonempty strings")
        prefix, sep, payload = raw_ref.partition(":")
        if not sep or not payload.strip():
            fail(f"{context}: malformed audit evidence reference {raw_ref!r}")
        payload = payload.strip()

        if prefix == "theorem":
            if not LEAN_DECL_RE.fullmatch(payload):
                fail(f"{context}: invalid theorem audit reference {payload!r}")
            lean_witnesses.add(payload)
        elif prefix == "doc":
            rel_path = payload.split("#", 1)[0]
            candidate = (repo / rel_path).resolve()
            try:
                candidate.relative_to(repo)
            except ValueError:
                fail(f"{context}: doc audit reference escapes repository")
            if not candidate.is_file():
                fail(f"{context}: doc audit reference does not exist: {rel_path}")
        elif prefix == "commit":
            if not re.fullmatch(r"[0-9a-f]{40}", payload):
                fail(f"{context}: commit audit reference must be a full SHA")
            try:
                git(repo, "cat-file", "-e", f"{payload}^{{commit}}")
            except subprocess.CalledProcessError:
                fail(f"{context}: commit audit reference does not exist: {payload}")
        else:
            fail(
                f"{context}: unsupported audit evidence prefix {prefix!r}; "
                "use theorem:, doc:, or commit:"
            )


def gh_json(repo: Path, *args: str) -> dict:
    if not os.environ.get("GH_TOKEN"):
        fail("GH_TOKEN is required to verify FINAL GitHub references")
    try:
        raw = subprocess.check_output(
            ["gh", *args],
            cwd=repo,
            text=True,
            stderr=subprocess.STDOUT,
        )
    except (FileNotFoundError, subprocess.CalledProcessError) as exc:
        fail(f"could not verify GitHub finalization reference: {exc}")
    try:
        return json.loads(raw)
    except json.JSONDecodeError as exc:
        fail(f"GitHub finalization reference returned invalid JSON: {exc}")


def verify_finalization_references(repo: Path, evidence: dict) -> None:
    candidate = str(evidence["candidate_main_sha"])
    try:
        git(repo, "cat-file", "-e", f"{candidate}^{{commit}}")
        git(repo, "merge-base", "--is-ancestor", candidate, "origin/main")
    except subprocess.CalledProcessError:
        fail("finalization candidate_main_sha is not an audited main ancestor")

    for key, expected_name in (
        ("core_lean_run", "UEOT Core Lean"),
        ("compression_guard_run", "UEOT Core Compression Guard"),
    ):
        run = gh_json(
            repo,
            "run",
            "view",
            str(evidence[key]),
            "--repo",
            REPO_FULL_NAME,
            "--json",
            "name,status,conclusion,headSha,event",
        )
        if (
            run.get("name") != expected_name
            or run.get("status") != "completed"
            or run.get("conclusion") != "success"
            or run.get("event") != "push"
            or run.get("headSha") != candidate
        ):
            fail(
                f"finalization evidence {key} is not a successful "
                f"{expected_name} push run for candidate_main_sha"
            )

    pr = gh_json(
        repo,
        "pr",
        "view",
        str(evidence["closure_pr"]),
        "--repo",
        REPO_FULL_NAME,
        "--json",
        "number,state,mergedAt,baseRefName,baseRefOid,headRefOid,mergeCommit",
    )
    if pr.get("baseRefName") != "main":
        fail("finalization closure PR must target main")

    current_sha = os.environ.get("COMPRESSION_VALIDATION_SHA") or os.environ.get("GITHUB_SHA")
    state = pr.get("state")
    if state == "OPEN":
        if pr.get("baseRefOid") != candidate:
            fail("open finalization closure PR is not based on candidate_main_sha")
        if current_sha and pr.get("headRefOid") != current_sha:
            fail("open finalization closure PR does not match current closure head")
    elif state == "MERGED":
        merge_commit = (pr.get("mergeCommit") or {}).get("oid")
        if not merge_commit:
            fail("merged finalization closure PR has no merge commit")
        target = current_sha or "HEAD"
        try:
            git(repo, "merge-base", "--is-ancestor", merge_commit, target)
            parents = git(repo, "show", "-s", "--format=%P", merge_commit).split()
        except subprocess.CalledProcessError:
            fail("could not verify finalization closure merge ancestry")
        if candidate not in parents:
            fail("finalization closure merge is not based on candidate_main_sha")
        head_oid = pr.get("headRefOid")
        if head_oid and head_oid not in parents:
            fail("finalization closure merge does not include the recorded PR head")
    else:
        fail("finalization closure PR must be open-current or merged")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", default=".")
    parser.add_argument("--baseline-ref")
    parser.add_argument(
        "--verify-finalization-refs",
        action="store_true",
        help="verify FINAL Git/GitHub evidence against the live repository",
    )
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
    mission_path = core / "docs/compression/COMPRESSION_MISSION.md"
    bootstrap_path = core / "docs/compression/COMPRESSION_BOOTSTRAP.md"

    for path in (
        index_path,
        ledger_path,
        coverage_path,
        operations_path,
        mission_path,
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
    index_by_pid = {row["pid"]: row for row in rows}

    try:
        ledger = json.loads(ledger_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        fail(f"COMPRESSION_LEDGER.yaml must remain JSON-compatible YAML: {exc}")

    if ledger.get("schema_version") != 2:
        fail("unsupported compression ledger schema_version")

    mission = ledger.get("mission_contract", {})
    if mission.get("version") != 1:
        fail("unsupported compression mission contract version")
    if mission.get("path") != (
        "formalization/ueot-core/docs/compression/COMPRESSION_MISSION.md"
    ):
        fail("compression mission contract path is not canonical")
    mission_state = mission.get("state")
    if mission_state not in MISSION_STATES:
        fail(f"invalid compression mission state {mission_state!r}")
    mission_text = mission_path.read_text(encoding="utf-8")
    if (
        "Mission Contract v1" not in mission_text
        or "Formal Definition of Done" not in mission_text
    ):
        fail("COMPRESSION_MISSION.md is missing the v1 Definition of Done markers")

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
        "counted_generators",
        "final_disposition_pids",
        "generated_pids",
        "retained_adapter_pids",
        "retained_boundary_pids",
        "unresolved_pids",
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

    audit_records = ledger.get("audit_records", {})
    if not isinstance(audit_records, dict):
        fail("audit_records must be an object keyed by frozen P-ID")
    unknown_audits = sorted(set(audit_records) - pid_set)
    if unknown_audits:
        fail(f"audit_records contains unknown P-IDs: {unknown_audits}")

    analyzed_pids: set[str] = set()
    schema_classified_pids: set[str] = set()
    audit_lean_witnesses: set[str] = set()
    for pid, record in audit_records.items():
        if not isinstance(record, dict):
            fail(f"{pid}: audit record must be an object")
        source_row = index_by_pid[pid]
        expected_line = int(source_row["source_line"])
        if record.get("source_line") != expected_line:
            fail(
                f"{pid}: audit source_line must match theorem index "
                f"({expected_line})"
            )
        if record.get("source_title") != source_row["source_title"]:
            fail(f"{pid}: audit source_title must match frozen theorem index")
        lean_theorems = record.get("lean_theorems")
        if not isinstance(lean_theorems, list) or not lean_theorems:
            fail(f"{pid}: audit record needs canonical Lean theorem identities")
        for theorem in lean_theorems:
            if not isinstance(theorem, str) or not LEAN_DECL_RE.fullmatch(theorem):
                fail(f"{pid}: invalid audited Lean theorem name {theorem!r}")
            audit_lean_witnesses.add(theorem)
        if not nonempty_string(record.get("lean_identity_relation")):
            fail(f"{pid}: audit record needs lean_identity_relation")
        if not nonempty_string(record.get("analysis_summary"), min_length=40):
            fail(f"{pid}: audit record needs a substantive analysis_summary")
        labels = record.get("schema_labels")
        if (
            not isinstance(labels, list)
            or any(not nonempty_string(label) for label in labels)
            or len(labels) != len(set(labels))
        ):
            fail(f"{pid}: schema_labels must be unique nonempty strings")
        if labels and not nonempty_string(record.get("schema_rationale"), min_length=40):
            fail(f"{pid}: schema classification needs a substantive rationale")
        candidate_mids = record.get("candidate_generator_ids")
        if not isinstance(candidate_mids, list) or any(
            not isinstance(mid, str) or not MID_RE.fullmatch(mid)
            for mid in candidate_mids
        ):
            fail(f"{pid}: candidate_generator_ids must contain valid M-IDs")
        roles = record.get("scientific_roles")
        if (
            not isinstance(roles, list)
            or not roles
            or any(not nonempty_string(role) for role in roles)
            or len(roles) != len(set(roles))
        ):
            fail(f"{pid}: scientific_roles must be unique nonempty strings")
        analyzed_pids.add(pid)
        if labels:
            schema_classified_pids.add(pid)

    if coverage["analyzed_pids"] != len(analyzed_pids):
        fail("analyzed_pids disagrees with explicit per-P-ID audit records")
    if coverage["schema_classified_pids"] != len(schema_classified_pids):
        fail(
            "schema_classified_pids disagrees with explicit per-P-ID "
            "schema labels"
        )
    if coverage["lean_rederived_pids"] > coverage["schema_classified_pids"]:
        fail("Lean-rederived P-IDs cannot exceed schema-classified P-IDs")
    if coverage["counted_compressed_pids"] > coverage["lean_rederived_pids"]:
        fail("counted compressed P-IDs cannot exceed Lean-rederived P-IDs")

    generators = ledger.get("generators", {})
    if not isinstance(generators, dict) or not generators:
        fail("compression ledger must contain at least one generator")

    for pid, record in audit_records.items():
        unknown_candidates = [
            mid for mid in record.get("candidate_generator_ids", [])
            if mid not in generators
        ]
        if unknown_candidates:
            fail(f"{pid}: audit references unknown candidate M-IDs {unknown_candidates}")

    exact_rederived: set[str] = set()
    counted_pids: set[str] = set()
    counted_generators = 0
    counted_mapping_pairs: set[tuple[str, str]] = set()
    counted_generator_ids: set[str] = set()
    lean_witnesses: set[str] = set(audit_lean_witnesses)

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
                if assumptions not in SOURCE_FAITHFUL_ASSUMPTION_RELATIONS:
                    fail(
                        f"{mid}/{pid}: full rederivation cannot strengthen "
                        "the frozen source assumptions"
                    )
                exact_rederived.add(pid)
                cross_family_exact.add(pid.split("-")[1])

            if mstate == "counted":
                if not mapping.get("promotion"):
                    fail(f"{mid}/{pid}: counted mapping needs promotion evidence")
                counted_pids.add(pid)
                counted_mapping_pairs.add((mid, pid))

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
            counted_generator_ids.add(mid)
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

    dispositions = ledger.get("final_dispositions", {})
    if not isinstance(dispositions, dict):
        fail("final_dispositions must be an object keyed by frozen P-ID")
    unknown_dispositions = sorted(set(dispositions) - pid_set)
    if unknown_dispositions:
        fail(f"final_dispositions contains unknown P-IDs: {unknown_dispositions}")

    generated: set[str] = set()
    retained_adapter: set[str] = set()
    retained_boundary: set[str] = set()
    for pid, entry in dispositions.items():
        if not isinstance(entry, dict):
            fail(f"{pid}: final disposition must be an object")
        disposition = entry.get("status")
        if disposition not in DISPOSITION_STATES:
            fail(f"{pid}: invalid final disposition {disposition!r}")
        if pid not in analyzed_pids or pid not in schema_classified_pids:
            fail(f"{pid}: final disposition requires a completed audit + schema record")
        if audit_records[pid].get("lean_identity_relation") != "source_facing_exact":
            fail(f"{pid}: final disposition requires an exact source-facing Lean identity")

        if disposition == "generated":
            mids = entry.get("generator_ids")
            if (
                not isinstance(mids, list)
                or not mids
                or len(mids) != len(set(mids))
            ):
                fail(f"{pid}: generated disposition needs unique nonempty generator_ids")
            bad_mids = [mid for mid in mids if mid not in generators]
            if bad_mids:
                fail(f"{pid}: generated disposition references unknown M-IDs {bad_mids}")
            if any(mid not in counted_generator_ids for mid in mids):
                fail(
                    f"{pid}: every generated dependency must be a counted generator"
                )
            missing_pairs = [
                mid for mid in mids if (mid, pid) not in counted_mapping_pairs
            ]
            if missing_pairs:
                fail(
                    f"{pid}: every generated dependency needs a counted exact "
                    f"mapping; missing {missing_pairs}"
                )
            generated.add(pid)
        elif disposition == "retained_adapter":
            rationale = entry.get("rationale")
            if not nonempty_string(rationale, min_length=MIN_RATIONALE_LENGTH):
                fail(f"{pid}: retained adapter needs a substantive string rationale")
            validate_audit_evidence(
                repo, entry.get("audit_evidence"), lean_witnesses, f"{pid} retained adapter"
            )
            retained_adapter.add(pid)
        else:
            rationale = entry.get("rationale")
            if not nonempty_string(rationale, min_length=MIN_RATIONALE_LENGTH):
                fail(f"{pid}: retained boundary needs a substantive string rationale")
            validate_audit_evidence(
                repo, entry.get("audit_evidence"), lean_witnesses, f"{pid} retained boundary"
            )
            retained_boundary.add(pid)

    final_count = len(dispositions)
    unresolved_count = 106 - final_count
    derived_counts = {
        "final_disposition_pids": final_count,
        "generated_pids": len(generated),
        "retained_adapter_pids": len(retained_adapter),
        "retained_boundary_pids": len(retained_boundary),
        "unresolved_pids": unresolved_count,
    }
    for key, expected in derived_counts.items():
        if coverage[key] != expected:
            fail(
                f"{key} disagrees with per-P-ID final dispositions: "
                f"ledger={coverage[key]} derived={expected}"
            )
    missing_audits = sorted(set(dispositions) - analyzed_pids)
    if missing_audits:
        fail(f"final dispositions lack per-P-ID audit records: {missing_audits}")
    missing_schema = sorted(set(dispositions) - schema_classified_pids)
    if missing_schema:
        fail(
            f"final dispositions lack per-P-ID schema classification: {missing_schema}"
        )

    minimal_core = ledger.get("minimal_core", {})
    core_state = minimal_core.get("state")
    if core_state not in MINIMAL_CORE_STATES:
        fail(f"invalid minimal_core state {core_state!r}")
    core_ids = minimal_core.get("generator_ids")
    if not isinstance(core_ids, list) or len(core_ids) != len(set(core_ids)):
        fail("minimal_core.generator_ids must be a unique list")
    if any(mid not in generators for mid in core_ids):
        fail("minimal_core references unknown generator IDs")

    ablation_state = minimal_core.get("ablation_state")
    if ablation_state not in ABLATION_STATES:
        fail(f"invalid minimal_core ablation_state {ablation_state!r}")
    minimality_claim = minimal_core.get("minimality_claim")
    if minimality_claim not in MINIMALITY_CLAIMS:
        fail(f"invalid minimal_core minimality_claim {minimality_claim!r}")

    if core_state == "frozen":
        if not core_ids:
            fail("frozen minimal core must contain at least one generator")
        if ablation_state != "complete":
            fail("frozen minimal core requires complete ablation")
        if minimality_claim != NONREDUNDANT_ABLATION:
            fail("frozen minimal core must use the scoped nonredundancy claim")
        for mid in core_ids:
            generator = generators[mid]
            if generator.get("state") != "counted_generator":
                fail(f"{mid}: final minimal-core generator must be counted")
            ablation = generator.get("ablation", {})
            if ablation.get("result") != NONREDUNDANT_ABLATION:
                fail(
                    f"{mid}: final minimal-core generator lacks "
                    "nonredundant ablation evidence"
                )
            broken_pids = ablation.get("broken_pids")
            if not isinstance(broken_pids, list) or not broken_pids:
                fail(f"{mid}: final ablation must record affected P-IDs")
            if any(pid not in pid_set for pid in broken_pids):
                fail(f"{mid}: ablation references unknown P-IDs")
            unrelated = [
                pid
                for pid in broken_pids
                if pid not in generated
                or mid not in dispositions[pid].get("generator_ids", [])
                or (mid, pid) not in counted_mapping_pairs
            ]
            if unrelated:
                fail(
                    f"{mid}: ablation broken_pids must be final generated "
                    f"mappings that directly depend on this generator: {unrelated}"
                )
            if not nonempty_string(
                ablation.get("rationale"), min_length=MIN_RATIONALE_LENGTH
            ):
                fail(f"{mid}: final ablation needs a substantive string rationale")

    if mission_state in {"ready_for_finalization", "final"}:
        final_gate_errors = []
        if len(analyzed_pids) != 106:
            final_gate_errors.append("per-P-ID audit records are not 106/106")
        if len(schema_classified_pids) != 106:
            final_gate_errors.append("per-P-ID schema classifications are not 106/106")
        if final_count != 106 or unresolved_count != 0:
            final_gate_errors.append("final dispositions are not 106/106 resolved")
        if core_state != "frozen":
            final_gate_errors.append("minimal core is not frozen")
        if ablation_state != "complete":
            final_gate_errors.append("minimal-core ablation is incomplete")
        if minimality_claim != NONREDUNDANT_ABLATION:
            final_gate_errors.append("scoped minimality claim is not established")
        if final_gate_errors:
            fail("mission finalization gate failed: " + "; ".join(final_gate_errors))

    if mission_state == "final":
        evidence = ledger.get("finalization_evidence", {})
        required_evidence = {
            "candidate_main_sha",
            "core_lean_run",
            "compression_guard_run",
            "closure_pr",
        }
        missing = required_evidence - set(evidence)
        if missing:
            fail(f"final mission state missing finalization evidence: {sorted(missing)}")
        if not re.fullmatch(r"[0-9a-f]{40}", str(evidence["candidate_main_sha"])):
            fail("finalization candidate_main_sha must be a full Git SHA")
        for key in ("core_lean_run", "compression_guard_run", "closure_pr"):
            if not isinstance(evidence[key], int) or evidence[key] <= 0:
                fail(f"finalization evidence {key} must be a positive integer")
        if not args.verify_finalization_refs:
            fail("FINAL mission state requires live Git/GitHub reference verification")
        verify_finalization_references(repo, evidence)

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
    print(
        f"audit_records={len(analyzed_pids)} "
        f"schema_classified={len(schema_classified_pids)}"
    )
    print(f"final_dispositions={final_count} unresolved={unresolved_count}")
    print(f"mission_state={mission_state} minimal_core_state={core_state}")


if __name__ == "__main__":
    main()
