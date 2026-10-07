#!/usr/bin/env python3
"""Zero-dependency validator for UEOT Core compression governance.

COMPRESSION_LEDGER.yaml is intentionally JSON-compatible YAML so validation can
use only Python's standard library on GitHub runners.
"""

from __future__ import annotations

import argparse
import csv
from datetime import datetime, timezone
import hashlib
import json
import os
import re
import subprocess
import sys
import time
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
FINALIZATION_RECEIPT_SCHEMA_VERSION = 1
FINALIZATION_RECEIPT_DIR = Path(
    "formalization/ueot-core/docs/compression/finalization_receipts"
)
FINALIZATION_RECEIPT_TYPES = {
    "retrospective_live_reverification",
    "finalization_live_capture",
}
GITHUB_API_ATTEMPTS = 3
MIN_RATIONALE_LENGTH = 20
FROZEN_THEOREM_INDEX_SHA256 = "8ff2a25512e0e99524fb5afc2b90bf628f9e931b590131354d0d1a0232372032"
NOT_DERIVABLE_STATUS = "not_derivable_under_declared_derivation_system"

PROTECTED_BASELINE_FILES = {
    "formalization/ueot-core/docs/V3_COVERAGE_STATUS.md",
    "formalization/ueot-core/docs/PID_STATUS.yaml",
    "formalization/ueot-core/docs/CORE_COMPRESSION_THEOREM_INDEX.csv",
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


class GitHubReferenceError(RuntimeError):
    def __init__(self, message: str, *, status: int | None = None) -> None:
        super().__init__(message)
        self.status = status


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
    if any(not nonempty_string(raw_ref) for raw_ref in refs):
        fail(f"{context}: audit_evidence entries must be nonempty strings")
    if len(refs) != len(set(refs)):
        fail(f"{context}: audit_evidence references must be unique")

    for raw_ref in refs:
        prefix, sep, payload = raw_ref.partition(":")
        if not sep or not payload.strip():
            fail(f"{context}: malformed audit evidence reference {raw_ref!r}")
        payload = payload.strip()

        if prefix == "theorem":
            if not LEAN_DECL_RE.fullmatch(payload):
                fail(f"{context}: invalid theorem audit reference {payload!r}")
            lean_witnesses.add(payload)
        elif prefix == "doc":
            if "#" in payload:
                fail(
                    f"{context}: doc audit fragments are not supported; "
                    "reference the audited file itself"
                )
            rel_path = payload
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


def gh_api_json(repo: Path, endpoint: str) -> dict:
    last_error: GitHubReferenceError | None = None
    for attempt in range(1, GITHUB_API_ATTEMPTS + 1):
        try:
            completed = subprocess.run(
                ["gh", "api", endpoint],
                cwd=repo,
                text=True,
                capture_output=True,
                check=False,
            )
        except FileNotFoundError as exc:
            raise GitHubReferenceError(f"GitHub CLI is unavailable: {exc}") from exc
        if completed.returncode == 0:
            try:
                return json.loads(completed.stdout)
            except json.JSONDecodeError as exc:
                raise GitHubReferenceError(
                    f"GitHub API returned invalid JSON for {endpoint}: {exc}"
                ) from exc

        output = (completed.stdout + completed.stderr).strip()
        match = re.search(
            r"(?:HTTP\s+(\d{3})|\"status\"\s*:\s*\"?(\d{3}))",
            output,
        )
        status = int(next(value for value in match.groups() if value)) if match else None
        last_error = GitHubReferenceError(
            f"GitHub API request failed for {endpoint}: {output}", status=status
        )
        retryable = status is None or status >= 500
        if not retryable or attempt == GITHUB_API_ATTEMPTS:
            raise last_error
        time.sleep(attempt)

    assert last_error is not None
    raise last_error


def finalization_receipt_relpath(evidence: dict) -> Path:
    return FINALIZATION_RECEIPT_DIR / f"{evidence['candidate_main_sha']}.json"


def finalization_event_payload(evidence: dict, runs: dict[str, dict]) -> dict:
    candidate = str(evidence["candidate_main_sha"])

    def normalize_run(key: str, expected_name: str) -> dict:
        run = runs[key]
        return {
            "id": run.get("id"),
            "name": run.get("name"),
            "event": run.get("event"),
            "status": run.get("status"),
            "conclusion": run.get("conclusion"),
            "head_sha": run.get("head_sha"),
            "run_attempt": run.get("run_attempt"),
            "created_at": run.get("created_at"),
            "updated_at": run.get("updated_at"),
            "html_url": run.get("html_url"),
            "expected_workflow": expected_name,
        }

    return {
        "candidate_main_sha": candidate,
        "closure_pr": evidence["closure_pr"],
        "core_lean_run": normalize_run("core_lean_run", "UEOT Core Lean"),
        "compression_guard_run": normalize_run(
            "compression_guard_run", "UEOT Core Compression Guard"
        ),
    }


def finalization_event_digest(event: dict) -> str:
    payload = json.dumps(event, sort_keys=True, separators=(",", ":")).encode(
        "utf-8"
    )
    return hashlib.sha256(payload).hexdigest()


def validate_run_record(
    run: dict, *, run_id: int, expected_name: str, candidate: str
) -> None:
    if (
        run.get("id") != run_id
        or run.get("name") != expected_name
        or run.get("status") != "completed"
        or run.get("conclusion") != "success"
        or run.get("event") != "push"
        or run.get("head_sha") != candidate
    ):
        fail(
            f"finalization evidence run {run_id} is not a successful "
            f"{expected_name} push run for candidate_main_sha"
        )


def load_baseline_receipt(repo: Path, baseline_ref: str, rel_path: Path) -> bytes:
    try:
        return subprocess.check_output(
            ["git", "show", f"{baseline_ref}:{rel_path.as_posix()}"],
            cwd=repo,
            stderr=subprocess.STDOUT,
        )
    except subprocess.CalledProcessError as exc:
        fail(
            "historical Actions evidence is unavailable and no immutable baseline "
            f"finalization receipt exists at {rel_path}: {exc.output.decode(errors='replace').strip()}"
        )


def validate_receipt_history_immutability(repo: Path, baseline_ref: str) -> None:
    try:
        paths = git(
            repo,
            "ls-tree",
            "-r",
            "--name-only",
            baseline_ref,
            FINALIZATION_RECEIPT_DIR.as_posix(),
        ).splitlines()
    except subprocess.CalledProcessError as exc:
        fail(
            f"could not inspect baseline finalization receipts at {baseline_ref}: "
            f"{exc.output}"
        )
    for raw_path in paths:
        if not raw_path:
            continue
        rel_path = Path(raw_path)
        baseline_bytes = load_baseline_receipt(repo, baseline_ref, rel_path)
        candidate_path = repo / rel_path
        if not candidate_path.is_file():
            fail(f"immutable baseline finalization receipt was deleted: {rel_path}")
        if candidate_path.read_bytes() != baseline_bytes:
            fail(f"immutable baseline finalization receipt was modified: {rel_path}")


def validate_finalization_receipt_data(
    receipt: dict, evidence: dict
) -> dict[str, dict]:
    if receipt.get("schema_version") != FINALIZATION_RECEIPT_SCHEMA_VERSION:
        fail("unsupported finalization receipt schema_version")
    if receipt.get("repository") != REPO_FULL_NAME:
        fail("finalization receipt repository mismatch")
    if receipt.get("capture_mode") not in FINALIZATION_RECEIPT_TYPES:
        fail("finalization receipt capture_mode is invalid")
    if receipt.get("source_status") != "ONLINE_VERIFIED_AT_CAPTURE":
        fail("finalization receipt does not attest online verification at capture")
    if not nonempty_string(receipt.get("captured_at")):
        fail("finalization receipt captured_at is missing")
    event = receipt.get("event")
    if not isinstance(event, dict):
        fail("finalization receipt event is missing")
    if receipt.get("event_sha256") != finalization_event_digest(event):
        fail("finalization receipt event digest mismatch")
    if event.get("candidate_main_sha") != evidence["candidate_main_sha"]:
        fail("finalization receipt candidate_main_sha mismatch")
    if event.get("closure_pr") != evidence["closure_pr"]:
        fail("finalization receipt closure_pr mismatch")

    runs = {}
    for key, expected_name in (
        ("core_lean_run", "UEOT Core Lean"),
        ("compression_guard_run", "UEOT Core Compression Guard"),
    ):
        run = event.get(key)
        if not isinstance(run, dict):
            fail(f"finalization receipt missing {key}")
        validate_run_record(
            run,
            run_id=evidence[key],
            expected_name=expected_name,
            candidate=str(evidence["candidate_main_sha"]),
        )
        runs[key] = run
    return runs


def validate_finalization_receipt(
    repo: Path, baseline_ref: str, evidence: dict
) -> dict[str, dict]:
    rel_path = finalization_receipt_relpath(evidence)
    baseline_bytes = load_baseline_receipt(repo, baseline_ref, rel_path)
    candidate_path = repo / rel_path
    if not candidate_path.is_file():
        fail(f"immutable baseline finalization receipt was deleted: {rel_path}")
    candidate_bytes = candidate_path.read_bytes()
    if candidate_bytes != baseline_bytes:
        fail(f"immutable baseline finalization receipt was modified: {rel_path}")

    try:
        receipt = json.loads(baseline_bytes.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        fail(f"baseline finalization receipt is invalid JSON: {exc}")
    return validate_finalization_receipt_data(receipt, evidence)


def write_finalization_receipt(
    repo: Path, evidence: dict, runs: dict[str, dict], capture_mode: str
) -> Path:
    event = finalization_event_payload(evidence, runs)
    receipt = {
        "schema_version": FINALIZATION_RECEIPT_SCHEMA_VERSION,
        "repository": REPO_FULL_NAME,
        "capture_mode": capture_mode,
        "source_status": "ONLINE_VERIFIED_AT_CAPTURE",
        "captured_at": datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace(
            "+00:00", "Z"
        ),
        "event": event,
        "event_sha256": finalization_event_digest(event),
        "note": (
            "This repository receipt preserves live-verified Actions metadata for the "
            "recorded finalization event. A retrospective capture does not claim that "
            "the receipt existed at the original finalization time."
        ),
    }
    rel_path = finalization_receipt_relpath(evidence)
    path = repo / rel_path
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists():
        fail(f"refusing to overwrite immutable finalization receipt: {rel_path}")
    path.write_text(
        json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    return path


def verify_finalization_references(
    repo: Path,
    evidence: dict,
    *,
    baseline_ref: str | None = None,
    capture_mode: str | None = None,
) -> None:
    candidate = str(evidence["candidate_main_sha"])
    try:
        git(repo, "cat-file", "-e", f"{candidate}^{{commit}}")
        git(repo, "merge-base", "--is-ancestor", candidate, "origin/main")
    except subprocess.CalledProcessError:
        fail("finalization candidate_main_sha is not an audited main ancestor")

    if baseline_ref:
        validate_receipt_history_immutability(repo, baseline_ref)

    runs: dict[str, dict] = {}
    run_404 = False
    for key, expected_name in (
        ("core_lean_run", "UEOT Core Lean"),
        ("compression_guard_run", "UEOT Core Compression Guard"),
    ):
        try:
            run = gh_api_json(
                repo, f"repos/{REPO_FULL_NAME}/actions/runs/{evidence[key]}"
            )
        except GitHubReferenceError as exc:
            if exc.status == 404:
                run_404 = True
                continue
            fail(str(exc))
        validate_run_record(
            run,
            run_id=evidence[key],
            expected_name=expected_name,
            candidate=candidate,
        )
        runs[key] = run

    if run_404:
        if capture_mode:
            fail("cannot capture a finalization receipt while an Actions run is unavailable")
        if not baseline_ref:
            fail(
                "historical Actions evidence returned HTTP 404; immutable receipt fallback "
                "requires --baseline-ref"
            )
        runs = validate_finalization_receipt(repo, baseline_ref, evidence)

    try:
        pr = gh_api_json(
            repo, f"repos/{REPO_FULL_NAME}/pulls/{evidence['closure_pr']}"
        )
    except GitHubReferenceError as exc:
        fail(str(exc))
    base = pr.get("base") or {}
    head = pr.get("head") or {}
    if base.get("ref") != "main":
        fail("finalization closure PR must target main")

    current_sha = os.environ.get("COMPRESSION_VALIDATION_SHA") or os.environ.get("GITHUB_SHA")
    state = pr.get("state")
    if state == "open":
        if base.get("sha") != candidate:
            fail("open finalization closure PR is not based on candidate_main_sha")
        if current_sha and head.get("sha") != current_sha:
            fail("open finalization closure PR does not match current closure head")
    elif state == "closed" and pr.get("merged_at"):
        merge_commit = pr.get("merge_commit_sha")
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
        head_oid = head.get("sha")
        if head_oid and head_oid not in parents:
            fail("finalization closure merge does not include the recorded PR head")
    else:
        fail("finalization closure PR must be open-current or merged")

    if capture_mode:
        if set(runs) != {"core_lean_run", "compression_guard_run"}:
            fail("cannot capture finalization receipt without both live Actions runs")
        path = write_finalization_receipt(repo, evidence, runs, capture_mode)
        print(f"finalization_receipt_written={path.relative_to(repo)}")


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
        "--capture-finalization-receipt",
        choices=sorted(FINALIZATION_RECEIPT_TYPES),
        help=(
            "after successful live FINAL verification, write an immutable Actions "
            "receipt for the recorded event; never overwrites an existing receipt"
        ),
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

    index_digest = hashlib.sha256(index_path.read_bytes()).hexdigest()
    if index_digest != FROZEN_THEOREM_INDEX_SHA256:
        fail(
            "compression theorem index digest drifted from the frozen "
            f"106-row seed: {index_digest}"
        )

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
    if baseline.get("theorem_index_sha256") != FROZEN_THEOREM_INDEX_SHA256:
        fail("compression ledger theorem-index hash is not the frozen digest")

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
        used_generator_ids = {
            mid
            for pid in generated
            for mid in dispositions[pid].get("generator_ids", [])
        }
        if set(core_ids) != used_generator_ids:
            fail(
                "frozen minimal core must exactly match generators used by "
                "final generated dispositions: "
                f"core={sorted(core_ids)} used={sorted(used_generator_ids)}"
            )
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

            derivability = ablation.get("remaining_core_derivability")
            if not isinstance(derivability, dict):
                fail(f"{mid}: final ablation needs remaining_core_derivability")
            remaining_ids = derivability.get("remaining_generator_ids")
            expected_remaining = sorted(set(core_ids) - {mid})
            if (
                not isinstance(remaining_ids, list)
                or len(remaining_ids) != len(set(remaining_ids))
                or sorted(remaining_ids) != expected_remaining
            ):
                fail(
                    f"{mid}: remaining_generator_ids must exactly equal "
                    f"the frozen core without this generator: {expected_remaining}"
                )
            if derivability.get("status") != NOT_DERIVABLE_STATUS:
                fail(
                    f"{mid}: remaining-core derivability status must be "
                    f"{NOT_DERIVABLE_STATUS!r}"
                )
            derivability_assumptions = derivability.get("assumptions")
            if (
                not isinstance(derivability_assumptions, list)
                or not derivability_assumptions
                or any(
                    not nonempty_string(item)
                    for item in derivability_assumptions
                )
                or len(derivability_assumptions)
                != len(set(derivability_assumptions))
            ):
                fail(
                    f"{mid}: remaining-core non-derivability needs unique "
                    "nonempty assumptions"
                )
            validate_audit_evidence(
                repo,
                derivability.get("audit_evidence"),
                lean_witnesses,
                f"{mid} remaining-core non-derivability",
            )

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
        verify_finalization_references(
            repo,
            evidence,
            baseline_ref=args.baseline_ref,
            capture_mode=args.capture_finalization_receipt,
        )
    elif args.capture_finalization_receipt:
        fail("finalization receipt capture is valid only when mission_state is final")

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
