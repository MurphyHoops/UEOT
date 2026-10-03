#!/usr/bin/env python3
"""Regression tests for post-FINAL research-track ownership rules."""

from __future__ import annotations

import argparse
import copy
import importlib.util
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path


def validator(
    repo: Path, branch: str, changed_file: Path, extra_args: list[str] | None = None
) -> list[str]:
    command = [
        sys.executable,
        str(repo / "formalization/ueot-core/scripts/validate_compression_research.py"),
        "--repo-root",
        str(repo),
        "--branch-name",
        branch,
        "--changed-path-file",
        str(changed_file),
    ]
    if extra_args:
        command.extend(extra_args)
    return command


def run_case(
    repo: Path,
    branch: str,
    paths: list[str],
    should_pass: bool,
    expected: str,
    extra_args: list[str] | None = None,
) -> None:
    with tempfile.NamedTemporaryFile("w", encoding="utf-8", delete=False) as handle:
        handle.write("\n".join(paths) + "\n")
        path_file = Path(handle.name)
    try:
        completed = subprocess.run(
            validator(repo, branch, path_file, extra_args),
            text=True,
            capture_output=True,
            check=False,
        )
    finally:
        path_file.unlink(missing_ok=True)

    output = completed.stdout + completed.stderr
    if should_pass:
        if completed.returncode != 0:
            raise AssertionError(f"expected PASS for {branch}\n{output}")
    else:
        if completed.returncode == 0 or expected not in output:
            raise AssertionError(
                f"expected rejection containing {expected!r} for {branch}\n{output}"
            )


def load_validator_module(repo: Path):
    path = repo / "formalization/ueot-core/scripts/validate_compression_research.py"
    spec = importlib.util.spec_from_file_location("compression_research_validator", path)
    if spec is None or spec.loader is None:
        raise AssertionError("could not load compression research validator module")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_rename_reports_source_and_destination(repo: Path) -> None:
    module = load_validator_module(repo)
    with tempfile.TemporaryDirectory() as tmp:
        git_repo = Path(tmp)
        subprocess.run(["git", "init", "-q"], cwd=git_repo, check=True)
        subprocess.run(
            ["git", "config", "user.name", "Regression Test"],
            cwd=git_repo,
            check=True,
        )
        subprocess.run(
            ["git", "config", "user.email", "regression@example.invalid"],
            cwd=git_repo,
            check=True,
        )
        old = git_repo / "formalization/ueot-core/UEOT/V3/Compression/TrackS.lean"
        old.parent.mkdir(parents=True)
        old.write_text("-- source\n", encoding="utf-8")
        subprocess.run(["git", "add", "."], cwd=git_repo, check=True)
        subprocess.run(["git", "commit", "-qm", "base"], cwd=git_repo, check=True)
        base = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=git_repo, text=True
        ).strip()

        new = git_repo / "formalization/ueot-core/UEOT/V3/Compression/Hierarchy/TrackS.lean"
        new.parent.mkdir(parents=True)
        subprocess.run(["git", "mv", str(old.relative_to(git_repo)), str(new.relative_to(git_repo))], cwd=git_repo, check=True)
        subprocess.run(["git", "commit", "-qam", "rename"], cwd=git_repo, check=True)
        head = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=git_repo, text=True
        ).strip()

        paths = module.changed_paths(git_repo, base, None, head)
        expected = {
            "formalization/ueot-core/UEOT/V3/Compression/TrackS.lean",
            "formalization/ueot-core/UEOT/V3/Compression/Hierarchy/TrackS.lean",
        }
        if not expected.issubset(set(paths)):
            raise AssertionError(
                f"rename path audit lost source/destination: expected {expected}, got {paths}"
            )


def test_policy_reauthorizes_on_base_edit(repo: Path) -> None:
    workflow = (
        repo / ".github/workflows/ueot-compression-research-policy.yml"
    ).read_text(encoding="utf-8")
    marker = "types: [opened, synchronize, reopened, ready_for_review, edited]"
    if marker not in workflow:
        raise AssertionError(
            "base-policy workflow must reauthorize on pull-request edited/base-change events"
        )


def test_candidate_ref_policy_drives_objecthood_transition(repo: Path) -> None:
    """The immutable base validator must inspect candidate registry *data*.

    This reproduces the pull_request_target layout: the worktree remains at the
    baseline commit while --candidate-ref names a different commit object.  A
    candidate that rewrites prior Objecthood completion history is statically
    well-formed, so only the base->candidate transition check should reject it.
    """

    module = load_validator_module(repo)
    base = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=repo, text=True
    ).strip()
    config = module.load_json(repo / module.TRACKS_REL)
    history = config.get("objecthood_completion_history")
    if not isinstance(history, list) or not history:
        raise AssertionError("candidate-ref regression requires completed Objecthood history")

    candidate = copy.deepcopy(config)
    candidate["objecthood_completion_history"][0]["tracker_issue"] = 999

    with tempfile.TemporaryDirectory() as tmp:
        tmpdir = Path(tmp)
        registry = tmpdir / "candidate.json"
        registry.write_text(json.dumps(candidate, indent=2) + "\n", encoding="utf-8")
        index = tmpdir / "index"
        env = os.environ.copy()
        env["GIT_INDEX_FILE"] = str(index)
        env.update(
            {
                "GIT_AUTHOR_NAME": "UEOT Regression Test",
                "GIT_AUTHOR_EMAIL": "ueot-regression@example.invalid",
                "GIT_COMMITTER_NAME": "UEOT Regression Test",
                "GIT_COMMITTER_EMAIL": "ueot-regression@example.invalid",
            }
        )

        subprocess.run(
            ["git", "read-tree", base], cwd=repo, env=env, check=True
        )
        blob = subprocess.check_output(
            ["git", "hash-object", "-w", str(registry)], cwd=repo, text=True
        ).strip()
        subprocess.run(
            [
                "git",
                "update-index",
                "--add",
                "--cacheinfo",
                "100644",
                blob,
                module.TRACKS_REL.as_posix(),
            ],
            cwd=repo,
            env=env,
            check=True,
        )
        tree = subprocess.check_output(
            ["git", "write-tree"], cwd=repo, env=env, text=True
        ).strip()
        candidate_ref = subprocess.check_output(
            ["git", "commit-tree", tree, "-p", base],
            cwd=repo,
            env=env,
            input="candidate-ref policy regression\n",
            text=True,
        ).strip()

        with tempfile.NamedTemporaryFile(
            "w", encoding="utf-8", delete=False
        ) as handle:
            handle.write(module.TRACKS_REL.as_posix() + "\n")
            changed_file = Path(handle.name)
        try:
            completed = subprocess.run(
                validator(
                    repo,
                    "ops/compression-candidate-ref-regression",
                    changed_file,
                    [
                        "--baseline-ref",
                        base,
                        "--candidate-ref",
                        candidate_ref,
                    ],
                ),
                text=True,
                capture_output=True,
                check=False,
            )
        finally:
            changed_file.unlink(missing_ok=True)

    output = completed.stdout + completed.stderr
    if completed.returncode == 0 or "prior records are immutable" not in output:
        raise AssertionError(
            "base-checkout validator ignored candidate-ref governance data\n" + output
        )


def test_candidate_ref_resolves_candidate_only_evidence(repo: Path) -> None:
    """Candidate architecture evidence is resolved from candidate Git data.

    The pull_request_target worktree stays on the immutable base.  A governance
    candidate may nevertheless add an allowed evidence document and reference
    it from a new architecture record; validation must inspect the candidate
    tree rather than requiring that file to pre-exist in the base worktree.
    """

    module = load_validator_module(repo)
    base = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=repo, text=True
    ).strip()
    config = module.load_json(repo / module.TRACKS_REL)
    candidate = copy.deepcopy(config)
    evidence_rel = (
        "formalization/ueot-core/docs/compression/hierarchy/"
        "CANDIDATE_REF_EVIDENCE_REGRESSION.md"
    )
    candidate["architecture_records"].append(
        {
            "record_id": "H-CANDIDATE-REF-EVIDENCE-REGRESSION",
            "title": "Candidate-ref evidence resolution regression",
            "architecture_role": "G3",
            "lifecycle_status": "MERGED_UNCOUNTED",
            "track_owner": "H",
            "authority_provenance": "POST_FINAL_MERGED",
            "counted_core_impact": "NONE",
            "evidence_paths": [evidence_rel],
        }
    )

    with tempfile.TemporaryDirectory() as tmp:
        tmpdir = Path(tmp)
        registry = tmpdir / "candidate.json"
        registry.write_text(json.dumps(candidate, indent=2) + "\n", encoding="utf-8")
        evidence = tmpdir / "evidence.md"
        evidence.write_text("# Candidate-only evidence\n", encoding="utf-8")
        index = tmpdir / "index"
        env = os.environ.copy()
        env["GIT_INDEX_FILE"] = str(index)
        env.update(
            {
                "GIT_AUTHOR_NAME": "UEOT Regression Test",
                "GIT_AUTHOR_EMAIL": "ueot-regression@example.invalid",
                "GIT_COMMITTER_NAME": "UEOT Regression Test",
                "GIT_COMMITTER_EMAIL": "ueot-regression@example.invalid",
            }
        )

        subprocess.run(["git", "read-tree", base], cwd=repo, env=env, check=True)
        registry_blob = subprocess.check_output(
            ["git", "hash-object", "-w", str(registry)], cwd=repo, text=True
        ).strip()
        evidence_blob = subprocess.check_output(
            ["git", "hash-object", "-w", str(evidence)], cwd=repo, text=True
        ).strip()
        subprocess.run(
            [
                "git",
                "update-index",
                "--add",
                "--cacheinfo",
                "100644",
                registry_blob,
                module.TRACKS_REL.as_posix(),
            ],
            cwd=repo,
            env=env,
            check=True,
        )
        subprocess.run(
            [
                "git",
                "update-index",
                "--add",
                "--cacheinfo",
                "100644",
                evidence_blob,
                evidence_rel,
            ],
            cwd=repo,
            env=env,
            check=True,
        )
        tree = subprocess.check_output(
            ["git", "write-tree"], cwd=repo, env=env, text=True
        ).strip()
        candidate_ref = subprocess.check_output(
            ["git", "commit-tree", tree, "-p", base],
            cwd=repo,
            env=env,
            input="candidate-only evidence regression\n",
            text=True,
        ).strip()

        with tempfile.NamedTemporaryFile(
            "w", encoding="utf-8", delete=False
        ) as handle:
            handle.write(module.TRACKS_REL.as_posix() + "\n")
            handle.write(evidence_rel + "\n")
            changed_file = Path(handle.name)
        try:
            completed = subprocess.run(
                validator(
                    repo,
                    "ops/compression-candidate-evidence-regression",
                    changed_file,
                    [
                        "--baseline-ref",
                        base,
                        "--candidate-ref",
                        candidate_ref,
                    ],
                ),
                text=True,
                capture_output=True,
                check=False,
            )
        finally:
            changed_file.unlink(missing_ok=True)

    if completed.returncode != 0:
        raise AssertionError(
            "candidate-only architecture evidence was not resolved from candidate ref\n"
            + completed.stdout
            + completed.stderr
        )


def test_candidate_ref_rejects_deleted_declared_file(repo: Path) -> None:
    """Candidate-declared governance files must exist in the candidate tree.

    The immutable base worktree still contains COMPRESSION_OPERATIONS.md.  A
    candidate that deletes that file while retaining the registry reference
    must therefore fail only if declared-file resolution really uses the
    candidate ref rather than falling back to the base checkout.
    """

    module = load_validator_module(repo)
    base = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=repo, text=True
    ).strip()
    config = module.load_json(repo / module.TRACKS_REL)
    operations_rel = config.get("operations_manual")
    if not isinstance(operations_rel, str) or not operations_rel:
        raise AssertionError("candidate-ref regression requires operations_manual")

    with tempfile.TemporaryDirectory() as tmp:
        tmpdir = Path(tmp)
        index = tmpdir / "index"
        env = os.environ.copy()
        env["GIT_INDEX_FILE"] = str(index)
        env.update(
            {
                "GIT_AUTHOR_NAME": "UEOT Regression Test",
                "GIT_AUTHOR_EMAIL": "ueot-regression@example.invalid",
                "GIT_COMMITTER_NAME": "UEOT Regression Test",
                "GIT_COMMITTER_EMAIL": "ueot-regression@example.invalid",
            }
        )

        subprocess.run(["git", "read-tree", base], cwd=repo, env=env, check=True)
        subprocess.run(
            ["git", "update-index", "--force-remove", operations_rel],
            cwd=repo,
            env=env,
            check=True,
        )
        tree = subprocess.check_output(
            ["git", "write-tree"], cwd=repo, env=env, text=True
        ).strip()
        candidate_ref = subprocess.check_output(
            ["git", "commit-tree", tree, "-p", base],
            cwd=repo,
            env=env,
            input="deleted declared governance file regression\n",
            text=True,
        ).strip()

        with tempfile.NamedTemporaryFile(
            "w", encoding="utf-8", delete=False
        ) as handle:
            handle.write(operations_rel + "\n")
            changed_file = Path(handle.name)
        try:
            completed = subprocess.run(
                validator(
                    repo,
                    "ops/compression-declared-file-regression",
                    changed_file,
                    [
                        "--baseline-ref",
                        base,
                        "--candidate-ref",
                        candidate_ref,
                    ],
                ),
                text=True,
                capture_output=True,
                check=False,
            )
        finally:
            changed_file.unlink(missing_ok=True)

    output = completed.stdout + completed.stderr
    if completed.returncode == 0 or operations_rel not in output:
        raise AssertionError(
            "candidate deletion of a declared governance file was hidden by "
            "the base worktree\n" + output
        )


def expect_static_failure(repo: Path, mutate, expected: str) -> None:
    module = load_validator_module(repo)
    config = module.load_json(repo / module.TRACKS_REL)
    ledger = module.load_json(repo / module.LEDGER_REL)
    config = copy.deepcopy(config)
    mutate(config)

    original_fail = module.fail

    def capture(message: str) -> None:
        raise ValueError(message)

    module.fail = capture
    try:
        try:
            module.validate_static(repo, config, ledger)
        except ValueError as exc:
            if expected not in str(exc):
                raise AssertionError(
                    f"expected static rejection containing {expected!r}, got {exc!r}"
                ) from exc
        else:
            raise AssertionError(f"expected static governance rejection: {expected}")
    finally:
        module.fail = original_fail


def expect_objecthood_transition_failure(
    repo: Path, baseline: dict, candidate: dict, expected: str
) -> None:
    module = load_validator_module(repo)
    original_fail = module.fail

    def capture(message: str) -> None:
        raise ValueError(message)

    module.fail = capture
    try:
        try:
            module.validate_objecthood_completion_history_transition(
                baseline, candidate
            )
        except ValueError as exc:
            if expected not in str(exc):
                raise AssertionError(
                    f"expected Objecthood transition rejection containing "
                    f"{expected!r}, got {exc!r}"
                ) from exc
        else:
            raise AssertionError(
                f"expected Objecthood completion-history rejection: {expected}"
            )
    finally:
        module.fail = original_fail


def test_architecture_record_schema(repo: Path) -> None:
    module = load_validator_module(repo)
    config = module.load_json(repo / module.TRACKS_REL)
    ledger = module.load_json(repo / module.LEDGER_REL)
    module.validate_static(repo, config, ledger)

    def make_g1_counted(config: dict) -> None:
        record = next(
            item
            for item in config["architecture_records"]
            if item["record_id"] == "S-GOA-RESIDUAL-INVERSE"
        )
        record["lifecycle_status"] = "COUNTED"
        record["counted_core_impact"] = "COUNTED"

    expect_static_failure(repo, make_g1_counted, "only G0 + COUNTED")

    def research_claims_merged(config: dict) -> None:
        record = next(
            item
            for item in config["architecture_records"]
            if item["record_id"] == "S-GOA-RESIDUAL-INVERSE"
        )
        record["authority_provenance"] = "POST_FINAL_RESEARCH"

    expect_static_failure(
        repo,
        research_claims_merged,
        "POST_FINAL_RESEARCH provenance requires RESEARCH lifecycle",
    )

    def close_gate_without_closing_x(config: dict) -> None:
        config["cross_track_integration_gate"] = "closed"

    expect_static_failure(
        repo,
        close_gate_without_closing_x,
        "research-track governance must define exactly",
    )

    def make_closed_o_record_active(config: dict) -> None:
        config["objecthood_omega_gate"] = "closed"
        config["architecture_record_schema"]["track_status"]["O"] = "closed"
        config["tracks"].pop("O", None)
        record = next(
            item
            for item in config["architecture_records"]
            if item["record_id"] == "O-CONSTITUTIVE-LEGITIMACY"
        )
        record["lifecycle_status"] = "RESEARCH"
        record["authority_provenance"] = "POST_FINAL_RESEARCH"

    expect_static_failure(
        repo,
        make_closed_o_record_active,
        "closed Objecthood gate permits only historical",
    )

    def reopen_o(config: dict, tracker_issue: int, stage_plan: str) -> None:
        config["objecthood_omega_gate"] = "open"
        config["architecture_record_schema"]["track_status"]["O"] = "active"
        config["tracks"]["O"] = {
            "title": "Objecthood continuation",
            "status": "active",
            "tracker_issue": tracker_issue,
            "initial_gate": stage_plan,
            "preferred_branch_prefix": "compression/objecthood-",
            "branch_patterns": ["^compression/objecthood-.*$"],
            "owned_topics": ["repair-law self-reconstruction"],
            "allowed_path_prefixes": [
                "formalization/ueot-core/UEOT/V3/Compression/Objecthood/",
                "formalization/ueot-core/docs/compression/objecthood/",
            ],
            "allowed_exact_paths": [
                "formalization/ueot-core/UEOT/V3/Compression/Objecthood.lean",
                "formalization/ueot-core/UEOT/V3/Compression.lean",
            ],
            "dependency_rule": (
                "consume_frozen_core_and_merged_X_evidence_from_canonical_main_only"
            ),
            "source_track_reopen_policy": "forbidden_inside_O",
        }

    expect_static_failure(
        repo,
        lambda config: reopen_o(config, 230, "R0-R4"),
        "fresh tracker_issue",
    )
    expect_static_failure(
        repo,
        lambda config: reopen_o(config, True, "R0-R4"),
        "positive fresh tracker_issue",
    )
    expect_static_failure(
        repo,
        lambda config: reopen_o(config, 231, "   "),
        "nonempty fresh stage plan",
    )
    expect_static_failure(
        repo,
        lambda config: reopen_o(config, 231, " O0-O8 "),
        "must not have leading/trailing whitespace",
    )
    expect_static_failure(
        repo,
        lambda config: reopen_o(config, 231, "O0-O8"),
        "fresh stage plan",
    )

    def whitespace_completed_gate(config: dict) -> None:
        config["objecthood_completion_history"][0]["completed_gate"] = "   "

    expect_static_failure(
        repo,
        whitespace_completed_gate,
        "nonempty completed_gate",
    )

    def padded_completed_gate(config: dict) -> None:
        gate = config["objecthood_completion_history"][0]["completed_gate"]
        config["objecthood_completion_history"][0]["completed_gate"] = f" {gate} "

    expect_static_failure(
        repo,
        padded_completed_gate,
        "must not have leading/trailing whitespace",
    )

    def delete_history_and_reopen(config: dict) -> None:
        config.pop("objecthood_completion_history", None)
        reopen_o(config, 230, "O0-O8")

    expect_static_failure(
        repo,
        delete_history_and_reopen,
        "requires objecthood_completion_history",
    )

    reopened = copy.deepcopy(config)
    reopen_o(reopened, 231, "R0-R4")
    module.validate_static(repo, reopened, ledger)

    rewritten = copy.deepcopy(config)
    rewritten["objecthood_completion_history"][0]["tracker_issue"] = 999
    expect_objecthood_transition_failure(
        repo,
        config,
        rewritten,
        "prior records are immutable",
    )

    deleted = copy.deepcopy(config)
    deleted.pop("objecthood_completion_history")
    expect_objecthood_transition_failure(
        repo,
        config,
        deleted,
        "cannot be deleted",
    )

    reopened_base = copy.deepcopy(config)
    reopen_o(reopened_base, 231, "R0-R4")

    replaced_tracker = copy.deepcopy(reopened_base)
    replaced_tracker["tracks"]["O"]["tracker_issue"] = 232
    expect_objecthood_transition_failure(
        repo,
        reopened_base,
        replaced_tracker,
        "must keep its tracker_issue until closure",
    )

    replaced_stage = copy.deepcopy(reopened_base)
    replaced_stage["tracks"]["O"]["initial_gate"] = "R5-R8"
    expect_objecthood_transition_failure(
        repo,
        reopened_base,
        replaced_stage,
        "must keep its stage plan until closure",
    )

    closed_without_append = copy.deepcopy(reopened_base)
    closed_without_append["objecthood_omega_gate"] = "closed"
    closed_without_append["architecture_record_schema"]["track_status"]["O"] = "closed"
    closed_without_append["tracks"].pop("O")
    expect_objecthood_transition_failure(
        repo,
        reopened_base,
        closed_without_append,
        "must append exactly one completion record",
    )

    closed_with_append = copy.deepcopy(closed_without_append)
    closed_with_append["objecthood_completion_history"].append(
        {
            "completed_gate": "R0-R4",
            "tracker_issue": 231,
            "tracker_state": "closed",
            "merged_pr": 999,
            "reviewed_head": "1" * 40,
            "merge_commit": "2" * 40,
            "resulting_main_core_lean_run": 1,
            "resulting_main_compression_guard_run": 2,
            "current_boundary": "next_boundary",
            "gate_state": "closed",
        }
    )
    module.validate_static(repo, closed_with_append, ledger)
    module.validate_objecthood_completion_history_transition(
        reopened_base, closed_with_append
    )

    def lose_counted_generator(config: dict) -> None:
        config["architecture_records"] = [
            item
            for item in config["architecture_records"]
            if item["record_id"] != "M-OI-01"
        ]

    expect_static_failure(
        repo,
        lose_counted_generator,
        "COUNTED architecture records must exactly match the frozen live-ledger minimal core",
    )


def test_p0b_legacy_baseline_transition(repo: Path) -> None:
    """A P0a base policy may authorize P0b without already having P0b schema.

    The candidate registry must satisfy the new architecture-record schema, but
    a baseline registry is enforcement authority for branch/path ownership and
    may legitimately predate those new metadata fields.
    """
    module = load_validator_module(repo)
    config = module.load_json(repo / module.TRACKS_REL)
    ledger = module.load_json(repo / module.LEDGER_REL)
    legacy = copy.deepcopy(config)
    legacy.pop("architecture_record_schema", None)
    legacy.pop("architecture_records", None)

    module.validate_static(
        repo,
        legacy,
        ledger,
        require_architecture_records=False,
    )

    original_fail = module.fail

    def capture(message: str) -> None:
        raise ValueError(message)

    module.fail = capture
    try:
        try:
            module.validate_static(repo, legacy, ledger)
        except ValueError as exc:
            if "architecture_record_schema" not in str(exc):
                raise AssertionError(
                    f"unexpected legacy-candidate rejection: {exc!r}"
                ) from exc
        else:
            raise AssertionError(
                "legacy registry must not pass as a P0b candidate policy"
            )
    finally:
        module.fail = original_fail


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", default=".")
    args = parser.parse_args()
    repo = Path(args.repo_root).resolve()
    live_config = json.loads(
        (repo / "formalization/ueot-core/docs/compression/COMPRESSION_RESEARCH_TRACKS.json").read_text()
    )
    objecthood_open = live_config.get("objecthood_omega_gate") == "open"

    run_case(
        repo,
        "compression/hierarchy-inventory",
        [
            "formalization/ueot-core/docs/compression/hierarchy/"
            "HIERARCHY_INVENTORY.md"
        ],
        True,
        "",
    )
    print("hierarchy-owned-doc: PASS")

    run_case(
        repo,
        "compression/hierarchy-inventory",
        ["formalization/ueot-core/docs/compression/COMPRESSION_LEDGER.yaml"],
        False,
        "may not modify cross-owned/protected path",
    )
    print("hierarchy-ledger-protection: PASS")

    run_case(
        repo,
        "compression/hierarchy-assembly",
        [
            "formalization/ueot-core/UEOT/V3/Compression/"
            "TopologyChangingGoaSemantics.lean"
        ],
        False,
        "outside its owned Hierarchy namespace",
    )
    print("hierarchy-track-s-isolation: PASS")

    run_case(
        repo,
        "compression/topology-goa-spectral-isolation",
        [
            "formalization/ueot-core/UEOT/V3/Compression/Hierarchy/"
            "AssemblyAudit.lean"
        ],
        False,
        "may not modify cross-owned/protected path",
    )
    print("stability-track-h-isolation: PASS")

    run_case(
        repo,
        "compression/topology-goa-spectral-isolation",
        [
            "formalization/ueot-core/UEOT/V3/Compression/CrossTrack/"
            "ParentSemanticBoundary.lean"
        ],
        False,
        "may not modify cross-owned/protected path",
    )
    print("stability-track-x-isolation: PASS")

    run_case(
        repo,
        "compression/topology-goa-spectral-isolation",
        ["formalization/ueot-core/UEOT/V3/Compression/CrossTrack.lean"],
        False,
        "may not modify cross-owned/protected path",
    )
    print("stability-track-x-root-isolation: PASS")

    run_case(
        repo,
        "compression/cross-track-parent-semantic",
        [
            "formalization/ueot-core/docs/compression/cross_track/"
            "X1_PARENT_GOA_BOUNDARY.md"
        ],
        True,
        "",
    )
    print("cross-track-owned-doc: PASS")

    run_case(
        repo,
        "compression/cross-track-parent-semantic",
        [
            "formalization/ueot-core/UEOT/V3/Compression/Hierarchy/"
            "ParentAssemblyResidual.lean"
        ],
        False,
        "outside its owned CrossTrack namespace",
    )
    print("cross-track-hierarchy-isolation: PASS")

    run_case(
        repo,
        "compression/cross-track-parent-semantic",
        [
            "formalization/ueot-core/UEOT/V3/Compression/"
            "TopologyChangingGoaTrackSClosure.lean"
        ],
        False,
        "outside its owned CrossTrack namespace",
    )
    print("cross-track-track-s-isolation: PASS")

    run_case(
        repo,
        "compression/objecthood-self-repair",
        [
            "formalization/ueot-core/docs/compression/objecthood/"
            "O1_LEGITIMACY_AUDIT.md"
        ],
        objecthood_open,
        "" if objecthood_open else "unclassified compression research branch",
    )
    print("objecthood-live-gate-policy: PASS")

    run_case(
        repo,
        "compression/objecthood-self-repair",
        [
            "formalization/ueot-core/UEOT/V3/Compression/CrossTrack/"
            "EndogenousConstitutivePersistence.lean"
        ],
        False,
        (
            "outside its owned Objecthood namespace"
            if objecthood_open
            else "unclassified compression research branch"
        ),
    )
    print("objecthood-cross-track-isolation: PASS")

    run_case(
        repo,
        "compression/cross-track-parent-semantic",
        [
            "formalization/ueot-core/UEOT/V3/Compression/Objecthood/"
            "SelfRepair.lean"
        ],
        False,
        "outside its owned CrossTrack namespace",
    )
    print("cross-track-objecthood-isolation: PASS")

    run_case(
        repo,
        "ops/compression-research-governance",
        [
            "formalization/ueot-core/docs/compression/"
            "POST_FINAL_RESEARCH_GOVERNANCE.md"
        ],
        True,
        "",
    )
    print("ops-governance-exemption: PASS")

    run_case(
        repo,
        "compression/assembly-audit",
        [
            "formalization/ueot-core/UEOT/V3/Compression/Hierarchy/"
            "AssemblyAudit.lean"
        ],
        False,
        "unclassified compression research branch",
    )
    print("unclassified-compression-rejected: PASS")

    run_case(
        repo,
        "ops/compression-research-governance",
        [
            "formalization/ueot-core/UEOT/V3/Compression/"
            "TopologyChangingGoaSemantics.lean"
        ],
        False,
        "outside the registered governance surface",
    )
    print("ops-theorem-mutation-rejected: PASS")

    run_case(
        repo,
        "ops/compression-research-governance",
        ["README.md"],
        False,
        "outside the registered governance surface",
    )
    print("ops-arbitrary-file-rejected: PASS")

    run_case(
        repo,
        "compression/hierarchy-inventory",
        ["formalization/ueot-core/UEOT/V3/Compression.lean"],
        False,
        "outside its owned Hierarchy namespace",
    )
    print("hierarchy-global-root-rejected: PASS")

    with tempfile.NamedTemporaryFile("w", encoding="utf-8", delete=False) as handle:
        handle.write(
            "compression/topology-goa-residual-inverse-stability\n"
            "compression/topology-goa-spectral-isolation\n"
        )
        live_file = Path(handle.name)
    try:
        run_case(
            repo,
            "ops/compression-research-governance",
            [],
            False,
            "Track S has 2 active remote branches",
            ["--live-branches-file", str(live_file)],
        )
    finally:
        live_file.unlink(missing_ok=True)
    print("per-track-live-concurrency: PASS")

    with tempfile.NamedTemporaryFile("w", encoding="utf-8", delete=False) as handle:
        handle.write(
            "compression/topology-goa-residual-inverse-stability\n"
            "compression/hierarchy-inventory\n"
            "compression/cross-track-parent-semantic\n"
        )
        cap_file = Path(handle.name)
    try:
        run_case(
            repo,
            "ops/compression-research-governance",
            [],
            False,
            "post-FINAL mutation cap exceeded",
            ["--live-branches-file", str(cap_file)],
        )
    finally:
        cap_file.unlink(missing_ok=True)
    print("cross-track-global-concurrency-cap: PASS")

    with tempfile.NamedTemporaryFile("w", encoding="utf-8", delete=False) as handle:
        handle.write("compression/assembly-audit\n")
        unclassified_live_file = Path(handle.name)
    try:
        run_case(
            repo,
            "ops/compression-research-governance",
            [],
            False,
            "unclassified live compression branch",
            ["--live-branches-file", str(unclassified_live_file)],
        )
    finally:
        unclassified_live_file.unlink(missing_ok=True)
    print("unclassified-live-branch-rejected: PASS")

    run_case(
        repo,
        "main",
        [
            "formalization/ueot-core/docs/compression/hierarchy/"
            "HIERARCHY_INVENTORY.md"
        ],
        False,
        "direct-main research mutation is not allowed",
    )
    print("direct-main-research-rejected: PASS")

    test_rename_reports_source_and_destination(repo)
    print("rename-source-and-destination-audited: PASS")

    test_policy_reauthorizes_on_base_edit(repo)
    print("base-change-reauthorization-trigger: PASS")

    test_candidate_ref_policy_drives_objecthood_transition(repo)
    print("candidate-ref-policy-transition-audited: PASS")

    test_candidate_ref_resolves_candidate_only_evidence(repo)
    print("candidate-ref-evidence-resolution-audited: PASS")

    test_candidate_ref_rejects_deleted_declared_file(repo)
    print("candidate-ref-declared-file-deletion-rejected: PASS")

    run_case(
        repo,
        "compression/hierarchy-inventory",
        [
            "formalization/ueot-core/docs/compression/hierarchy/"
            "HIERARCHY_INVENTORY.md"
        ],
        False,
        "fork-based mutating Compression research/governance branches are not allowed",
        [
            "--head-repo",
            "someone/UEOT-fork",
            "--base-repo",
            "MurphyHoops/UEOT",
        ],
    )
    print("fork-mutating-research-rejected: PASS")

    run_case(
        repo,
        "compression/objecthood-self-repair",
        [
            "formalization/ueot-core/docs/compression/objecthood/"
            "O1_LEGITIMACY_AUDIT.md"
        ],
        False,
        (
            "fork-based mutating Compression research/governance branches are not allowed"
            if objecthood_open
            else "unclassified compression research branch"
        ),
        [
            "--head-repo",
            "someone/UEOT-fork",
            "--base-repo",
            "MurphyHoops/UEOT",
        ],
    )
    print("closed-objecthood-fork-mutation-rejected: PASS")

    test_architecture_record_schema(repo)
    print("architecture-record-schema-and-combinations: PASS")

    test_p0b_legacy_baseline_transition(repo)
    print("p0b-legacy-baseline-transition: PASS")


if __name__ == "__main__":
    main()
