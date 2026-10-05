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
    if (
        completed.returncode == 0
        or "freezes legacy Objecthood completion history" not in output
    ):
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

    def close_cross_track_namespace(config: dict) -> None:
        config["cross_track_integration_gate"] = "closed"

    expect_static_failure(
        repo,
        close_cross_track_namespace,
        "statically open",
    )

    def close_objecthood_namespace(config: dict) -> None:
        config["objecthood_omega_gate"] = "closed"

    expect_static_failure(
        repo,
        close_objecthood_namespace,
        "statically open",
    )

    def weaken_additive_policy(config: dict) -> None:
        config["tracks"]["O"]["change_policy"] = "mutable_shared_surface"

    expect_static_failure(
        repo,
        weaken_additive_policy,
        "additive_only_by_default",
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

    rewritten = copy.deepcopy(config)
    rewritten["objecthood_completion_history"][0]["tracker_issue"] = 999
    expect_objecthood_transition_failure(
        repo,
        config,
        rewritten,
        "freezes legacy Objecthood completion history",
    )

    deleted = copy.deepcopy(config)
    deleted.pop("objecthood_completion_history")
    expect_objecthood_transition_failure(
        repo,
        config,
        deleted,
        "freezes legacy Objecthood completion history",
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



def test_objecthood_root_import_guard(repo: Path) -> None:
    """Objecthood root may expose RH modules but may not be rewritten."""

    module = load_validator_module(repo)
    root = "formalization/ueot-core/UEOT/V3/Compression/Objecthood.lean"
    base = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=repo, text=True
    ).strip()
    base_bytes = subprocess.check_output(
        ["git", "show", f"{base}:{root}"], cwd=repo
    )
    base_text = base_bytes.decode("utf-8")

    def candidate_with(
        contents: str | bytes, label: str, parent: str | None = None
    ) -> str:
        parent = parent or base
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            index = tmpdir / "index"
            source = tmpdir / "Objecthood.lean"
            if isinstance(contents, bytes):
                source.write_bytes(contents)
            else:
                source.write_text(contents, encoding="utf-8")
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
                ["git", "read-tree", parent], cwd=repo, env=env, check=True
            )
            blob = subprocess.check_output(
                ["git", "hash-object", "-w", str(source)],
                cwd=repo,
                text=True,
            ).strip()
            subprocess.run(
                ["git", "update-index", "--add", "--cacheinfo", "100644", blob, root],
                cwd=repo,
                env=env,
                check=True,
            )
            tree = subprocess.check_output(
                ["git", "write-tree"], cwd=repo, env=env, text=True
            ).strip()
            return subprocess.check_output(
                ["git", "commit-tree", tree, "-p", parent],
                cwd=repo,
                env=env,
                input=label + "\n",
                text=True,
            ).strip()

    valid_text = base_text.replace(
        "\n\n/-!\n",
        "\nimport UEOT.V3.Compression.Objecthood.Homeostasis.RootGuardRegression\n\n/-!\n",
        1,
    )
    valid = candidate_with(valid_text, "valid Objecthood RH import")
    module.validate_objecthood_root_import_change(
        repo, base, valid, "O", [root]
    )

    rlsr_text = base_text.replace(
        "\n\n/-!\n",
        "\nimport UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction.RootGuardRegression\n\n/-!\n",
        1,
    )
    rlsr_valid = candidate_with(rlsr_text, "valid Objecthood future-task import")
    module.validate_objecthood_root_import_change(
        repo, base, rlsr_valid, "O", [root]
    )

    original_fail = module.fail

    def capture(message: str) -> None:
        raise ValueError(message)

    module.fail = capture
    try:
        invalid_decl = candidate_with(
            base_text + "\ntheorem root_guard_regression : True := trivial\n",
            "invalid Objecthood declaration",
        )
        try:
            module.validate_objecthood_root_import_change(
                repo, base, invalid_decl, "O", [root]
            )
        except ValueError as exc:
            if "import preamble" not in str(exc) and "insert only" not in str(exc):
                raise AssertionError(f"unexpected root declaration rejection: {exc}") from exc
        else:
            raise AssertionError("Objecthood root declaration mutation was not rejected")

        comment_bypass = candidate_with(
            "import UEOT.V3.Compression.Objecthood.Homeostasis.CommentOpen /-\n"
            + base_text
            + "import UEOT.V3.Compression.Objecthood.Homeostasis.CommentClose -/\n",
            "invalid Objecthood block-comment bypass",
        )
        try:
            module.validate_objecthood_root_import_change(
                repo, base, comment_bypass, "O", [root]
            )
        except ValueError as exc:
            if "import preamble" not in str(exc) and "insert only" not in str(exc):
                raise AssertionError(
                    f"unexpected trailing-syntax rejection: {exc}"
                ) from exc
        else:
            raise AssertionError(
                "Objecthood root trailing block-comment syntax was not rejected"
            )

        cr_injection = candidate_with(
            base_bytes.replace(
                b"\n\n/-!\n",
                b"\nimport UEOT.V3.Compression.Objecthood.Homeostasis.CRGuard"
                + b"\rtheorem injected : True := trivial\n\n/-!\n",
                1,
            ),
            "invalid Objecthood carriage-return injection",
        )
        try:
            module.validate_objecthood_root_import_change(
                repo, base, cr_injection, "O", [root]
            )
        except ValueError as exc:
            if "line-control" not in str(exc):
                raise AssertionError(
                    f"unexpected carriage-return rejection: {exc}"
                ) from exc
        else:
            raise AssertionError(
                "Objecthood root carriage-return command injection was not rejected"
            )

        # Simulate a later RH stage whose baseline already exposes one RH
        # module. Moving that old import into the doc-comment while adding a new
        # syntactically valid RH import must be rejected: the root policy is
        # insertion-only and position-preserving for all baseline imports.
        rh_baseline = valid
        rh_baseline_text = subprocess.check_output(
            ["git", "show", f"{rh_baseline}:{root}"], cwd=repo, text=True
        )
        old_rh = (
            "import UEOT.V3.Compression.Objecthood.Homeostasis."
            "RootGuardRegression\n"
        )
        moved_text = rh_baseline_text.replace(old_rh, "", 1)
        moved_text = moved_text.replace(
            "/-!\n",
            "/-!\n" + old_rh,
            1,
        )
        moved_text = moved_text.replace(
            "\n/-!\n",
            "\nimport UEOT.V3.Compression.Objecthood.Homeostasis.SecondStage\n\n/-!\n",
            1,
        )
        moved_old_import = candidate_with(
            moved_text,
            "invalid Objecthood RH import relocation",
            parent=rh_baseline,
        )
        try:
            module.validate_objecthood_root_import_change(
                repo, rh_baseline, moved_old_import, "O", [root]
            )
        except ValueError as exc:
            if "import preamble" not in str(exc) and "delete, move" not in str(exc):
                raise AssertionError(
                    f"unexpected RH-import relocation rejection: {exc}"
                ) from exc
        else:
            raise AssertionError(
                "relocating an existing RH import into the doc-comment was not rejected"
            )

        lines = base_text.splitlines(keepends=True)
        old_import = next(
            i
            for i, line in enumerate(lines)
            if line.startswith("import UEOT.V3.Compression.Objecthood.")
        )
        deleted_old = candidate_with(
            "".join(lines[:old_import] + lines[old_import + 1 :]),
            "invalid Objecthood prior-import deletion",
        )
        try:
            module.validate_objecthood_root_import_change(
                repo, base, deleted_old, "O", [root]
            )
        except ValueError as exc:
            if (
                "delete, move" not in str(exc)
                and "import preamble" not in str(exc)
                and "insert only complete imports" not in str(exc)
            ):
                raise AssertionError(f"unexpected old-import rejection: {exc}") from exc
        else:
            raise AssertionError("deleting a pre-RH Objecthood import was not rejected")
    finally:
        module.fail = original_fail


def test_v2_additive_only_guard(repo: Path) -> None:
    """L1 research may add new owned files but cannot rewrite merged surfaces."""

    module = load_validator_module(repo)
    config = module.load_json(repo / module.TRACKS_REL)
    ledger = module.load_json(repo / module.LEDGER_REL)
    compiled = module.validate_static(repo, config, ledger)
    baseline = "origin/main"
    existing = (
        "formalization/ueot-core/UEOT/V3/Compression/Objecthood/"
        "Homeostasis/RecurrentFaultSystem.lean"
    )
    new_path = (
        "formalization/ueot-core/UEOT/V3/Compression/Objecthood/"
        "FutureTask/NewScientificResult.lean"
    )

    original_fail = module.fail

    def capture(message: str) -> None:
        raise ValueError(message)

    module.fail = capture
    try:
        try:
            module.validate_track_paths(
                repo,
                baseline,
                "HEAD",
                "compression/objecthood-future-task",
                [existing],
                config,
                compiled,
            )
        except ValueError as exc:
            if "L1 additive research may not modify or delete existing path" not in str(exc):
                raise AssertionError(f"unexpected additive-only rejection: {exc}") from exc
        else:
            raise AssertionError("L1 existing Objecthood theorem mutation was not rejected")

        module.validate_track_paths(
            repo,
            baseline,
            "HEAD",
            "compression/objecthood-future-task",
            [new_path],
            config,
            compiled,
        )
    finally:
        module.fail = original_fail


def test_tc_forward_registration_compatibility(repo: Path) -> None:
    """The pre-TC validator must accept one later, explicitly registered TC track."""

    module = load_validator_module(repo)
    config = module.load_json(repo / module.TRACKS_REL)
    ledger = module.load_json(repo / module.LEDGER_REL)
    candidate = copy.deepcopy(config)
    candidate["governance"]["allowed_exact_paths"] = [
        path
        for path in candidate["governance"]["allowed_exact_paths"]
        if path not in (module.TC_BOOTSTRAP_DOCS | {module.TC_PUBLIC_ROOT})
    ]
    candidate["tracks"]["TC"] = {
        "title": "Theory Completion / Scientific Integration",
        "status": "active",
        "preferred_branch_prefix": "compression/theory-completion-",
        "branch_patterns": ["^compression/theory-completion-.*$"],
        "program_tracker_issue": 265,
        "owned_topics": ["semantic constitution"],
        "allowed_path_prefixes": sorted(module.TC_ALLOWED_PATH_PREFIXES),
        "allowed_exact_paths": sorted(module.TC_ALLOWED_EXACT_PATHS),
        "forbidden_exact_paths": sorted(module.TC_FORBIDDEN_EXACT_PATHS),
        "forbidden_path_prefixes": sorted(module.TC_FORBIDDEN_PATH_PREFIXES),
        "dependency_rule": (
            "consume_S_H_X_O_and_frozen_core_evidence_from_canonical_main_only"
        ),
        "source_track_reopen_policy": "forbidden_inside_TC",
        "change_policy": "additive_only_by_default",
    }
    candidate["architecture_record_schema"]["track_owners"].append("TC")
    candidate["architecture_record_schema"]["track_status"]["TC"] = "active"

    compiled = module.validate_static(repo, candidate, ledger)
    if "TC" not in compiled:
        raise AssertionError("forward-compatible validator did not compile Track TC")
    module.validate_track_paths(
        repo,
        "origin/main",
        "HEAD",
        "compression/theory-completion-semantic-constitution",
        [
            "formalization/ueot-core/docs/compression/theory_completion/"
            "P0_SEMANTIC_INVENTORY.md"
        ],
        candidate,
        compiled,
    )

    original_fail = module.fail

    def capture(message: str) -> None:
        raise ValueError(message)

    module.fail = capture
    try:
        widened = copy.deepcopy(candidate)
        widened["tracks"]["TC"]["allowed_exact_paths"].append(
            "formalization/ueot-core/UEOT/V3/Compression/Objecthood/SelfRepair.lean"
        )
        try:
            module.validate_static(repo, widened, ledger)
        except ValueError as exc:
            if "allowed_exact_paths must match the pre-authorized TC scope" not in str(exc):
                raise AssertionError(f"unexpected TC ownership rejection: {exc}") from exc
        else:
            raise AssertionError("widened TC exact ownership was not rejected")

        missing_s_prefix = copy.deepcopy(candidate)
        missing_s_prefix["tracks"]["S"]["forbidden_path_prefixes"].remove(
            module.TC_DOC_PREFIX
        )
        try:
            module.validate_static(repo, missing_s_prefix, ledger)
        except ValueError as exc:
            if "reciprocal Track S namespace exclusions" not in str(exc):
                raise AssertionError(
                    f"unexpected reciprocal S-prefix rejection: {exc}"
                ) from exc
        else:
            raise AssertionError(
                "TC registration without reciprocal Track S prefix exclusion passed"
            )

        missing_s_root = copy.deepcopy(candidate)
        missing_s_root["tracks"]["S"]["forbidden_exact_paths"].remove(
            module.TC_PUBLIC_ROOT
        )
        try:
            module.validate_static(repo, missing_s_root, ledger)
        except ValueError as exc:
            if "reciprocal Track S public-root exclusion" not in str(exc):
                raise AssertionError(
                    f"unexpected reciprocal S-root rejection: {exc}"
                ) from exc
        else:
            raise AssertionError(
                "TC registration without reciprocal Track S root exclusion passed"
            )

        retained_bootstrap = copy.deepcopy(candidate)
        retained_bootstrap["governance"]["allowed_exact_paths"].append(
            module.TC_PUBLIC_ROOT
        )
        try:
            module.validate_static(repo, retained_bootstrap, ledger)
        except ValueError as exc:
            if "retire governance exact-path access overlapping" not in str(exc):
                raise AssertionError(
                    f"unexpected TC bootstrap-retirement rejection: {exc}"
                ) from exc
        else:
            raise AssertionError(
                "registered TC retained temporary governance access"
            )

        governance_ancestor = copy.deepcopy(candidate)
        governance_ancestor["governance"]["allowed_path_prefixes"].append(
            "formalization/ueot-core/docs/compression/"
        )
        try:
            module.validate_static(repo, governance_ancestor, ledger)
        except ValueError as exc:
            if "semantically overlapping the Theory Completion scope" not in str(exc):
                raise AssertionError(
                    f"unexpected governance-prefix overlap rejection: {exc}"
                ) from exc
        else:
            raise AssertionError(
                "ancestor governance prefix overlapping TC scope was accepted"
            )

        governance_inside = copy.deepcopy(candidate)
        governance_inside["governance"]["allowed_exact_paths"].append(
            module.TC_DOC_PREFIX + "P0_SEMANTIC_INVENTORY.md"
        )
        try:
            module.validate_static(repo, governance_inside, ledger)
        except ValueError as exc:
            if "governance exact-path access overlapping" not in str(exc):
                raise AssertionError(
                    f"unexpected governance exact-path overlap rejection: {exc}"
                ) from exc
        else:
            raise AssertionError(
                "governance exact path inside TC scope was accepted"
            )

        ungoverned_tc = copy.deepcopy(candidate)
        ungoverned_tc["governed_path_prefixes"] = [
            "formalization/ueot-core/UEOT/V3/Elsewhere/"
        ]
        ungoverned_tc["governed_exact_paths"] = [
            "formalization/ueot-core/UEOT/V3/Elsewhere.lean"
        ]
        try:
            module.validate_static(repo, ungoverned_tc, ledger)
        except ValueError as exc:
            if "inside the top-level governed path surface" not in str(exc):
                raise AssertionError(
                    f"unexpected governed-surface rejection: {exc}"
                ) from exc
        else:
            raise AssertionError(
                "registered TC could be removed from the top-level governed surface"
            )

        required = set(module.TC_BOOTSTRAP_DOCS) | {module.TC_PUBLIC_ROOT}
        seen_required = set()
        original_require_file_at_ref = module.require_file_at_ref
        original_git_blob_bytes = module.git_blob_bytes

        def record_required(
            _repo: Path, _ref: str, rel: str, _context: str
        ) -> None:
            seen_required.add(rel)

        def tc_import_blob(_repo: Path, _ref: str, path: str) -> bytes:
            if path == module.COMPRESSION_PUBLIC_ROOT:
                return (
                    b"import UEOT.V3.Compression.Objecthood\n"
                    b"import UEOT.V3.Compression.TheoryCompletion\n"
                )
            return original_git_blob_bytes(_repo, _ref, path)

        module.require_file_at_ref = record_required
        module.git_blob_bytes = tc_import_blob
        try:
            module.validate_tc_registration_transition(
                repo, config, candidate, "synthetic-candidate"
            )
        finally:
            module.require_file_at_ref = original_require_file_at_ref
            module.git_blob_bytes = original_git_blob_bytes
        if seen_required != required:
            raise AssertionError(
                "first TC registration did not require the complete bootstrap "
                f"artifact set: expected={sorted(required)}, seen={sorted(seen_required)}"
            )

        def reject_one_required(
            _repo: Path, _ref: str, rel: str, _context: str
        ) -> None:
            if rel == module.TC_PUBLIC_ROOT:
                raise ValueError("missing required TC bootstrap artifact")

        module.require_file_at_ref = reject_one_required
        module.git_blob_bytes = tc_import_blob
        try:
            try:
                module.validate_tc_registration_transition(
                    repo, config, candidate, "synthetic-candidate"
                )
            except ValueError as exc:
                if "missing required TC bootstrap artifact" not in str(exc):
                    raise AssertionError(
                        f"unexpected missing-artifact rejection: {exc}"
                    ) from exc
            else:
                raise AssertionError(
                    "first TC registration passed with a missing bootstrap artifact"
                )
        finally:
            module.require_file_at_ref = original_require_file_at_ref
            module.git_blob_bytes = original_git_blob_bytes

        module.require_file_at_ref = record_required

        def no_tc_import_blob(_repo: Path, _ref: str, path: str) -> bytes:
            if path == module.COMPRESSION_PUBLIC_ROOT:
                return b"import UEOT.V3.Compression.Objecthood\n"
            return original_git_blob_bytes(_repo, _ref, path)

        module.git_blob_bytes = no_tc_import_blob
        try:
            try:
                module.validate_tc_registration_transition(
                    repo, config, candidate, "synthetic-candidate"
                )
            except ValueError as exc:
                if "requires exactly one semantic TheoryCompletion public-root import" not in str(exc):
                    raise AssertionError(
                        f"unexpected missing-public-import rejection: {exc}"
                    ) from exc
            else:
                raise AssertionError(
                    "first TC registration passed without the Compression.lean public import"
                )
        finally:
            module.require_file_at_ref = original_require_file_at_ref
            module.git_blob_bytes = original_git_blob_bytes

        module.require_file_at_ref = record_required

        def duplicate_whitespace_tc_import_blob(
            _repo: Path, _ref: str, path: str
        ) -> bytes:
            if path == module.COMPRESSION_PUBLIC_ROOT:
                return (
                    b"import UEOT.V3.Compression.TheoryCompletion\n"
                    b"  import UEOT.V3.Compression.TheoryCompletion\n"
                )
            return original_git_blob_bytes(_repo, _ref, path)

        module.git_blob_bytes = duplicate_whitespace_tc_import_blob
        try:
            try:
                module.validate_tc_registration_transition(
                    repo, config, candidate, "synthetic-candidate"
                )
            except ValueError as exc:
                if "requires exactly one semantic TheoryCompletion public-root import" not in str(exc):
                    raise AssertionError(
                        f"unexpected duplicate-public-import rejection: {exc}"
                    ) from exc
            else:
                raise AssertionError(
                    "first TC registration accepted a whitespace-variant duplicate public import"
                )
        finally:
            module.require_file_at_ref = original_require_file_at_ref
            module.git_blob_bytes = original_git_blob_bytes

        module.require_file_at_ref = record_required

        def duplicate_commented_tc_import_blob(
            _repo: Path, _ref: str, path: str
        ) -> bytes:
            if path == module.COMPRESSION_PUBLIC_ROOT:
                return (
                    b"import UEOT.V3.Compression.TheoryCompletion\n"
                    b"import UEOT.V3.Compression.TheoryCompletion -- duplicate\n"
                )
            return original_git_blob_bytes(_repo, _ref, path)

        module.git_blob_bytes = duplicate_commented_tc_import_blob
        try:
            try:
                module.validate_tc_registration_transition(
                    repo, config, candidate, "synthetic-candidate"
                )
            except ValueError as exc:
                if "requires exactly one semantic TheoryCompletion public-root import" not in str(exc):
                    raise AssertionError(
                        f"unexpected commented-duplicate rejection: {exc}"
                    ) from exc
            else:
                raise AssertionError(
                    "first TC registration accepted a comment-variant duplicate public import"
                )
        finally:
            module.require_file_at_ref = original_require_file_at_ref
            module.git_blob_bytes = original_git_blob_bytes

        original_changed_lines = module.changed_lines_for_path_between
        module.changed_lines_for_path_between = (
            lambda *_args, **_kwargs: [
                module.TC_PUBLIC_IMPORT + " -- duplicate"
            ]
        )
        try:
            try:
                module.validate_compression_root_import_change(
                    repo,
                    "synthetic-baseline",
                    "synthetic-candidate",
                    "S",
                    [module.COMPRESSION_PUBLIC_ROOT],
                )
            except ValueError as exc:
                if "Track S may not add/remove the Track TC root import" not in str(exc):
                    raise AssertionError(
                        f"unexpected Track-S commented-import rejection: {exc}"
                    ) from exc
            else:
                raise AssertionError(
                    "Track S accepted a comment-variant duplicate TC root import"
                )
        finally:
            module.changed_lines_for_path_between = original_changed_lines

        module.require_file_at_ref = record_required

        def noncanonical_tc_import_blob(
            _repo: Path, _ref: str, path: str
        ) -> bytes:
            if path == module.COMPRESSION_PUBLIC_ROOT:
                return b"  import UEOT.V3.Compression.TheoryCompletion\n"
            return original_git_blob_bytes(_repo, _ref, path)

        module.git_blob_bytes = noncanonical_tc_import_blob
        try:
            try:
                module.validate_tc_registration_transition(
                    repo, config, candidate, "synthetic-candidate"
                )
            except ValueError as exc:
                if "requires the TheoryCompletion public-root import in canonical format" not in str(exc):
                    raise AssertionError(
                        f"unexpected noncanonical-public-import rejection: {exc}"
                    ) from exc
            else:
                raise AssertionError(
                    "first TC registration accepted a noncanonical public import"
                )
        finally:
            module.require_file_at_ref = original_require_file_at_ref
            module.git_blob_bytes = original_git_blob_bytes

        module.require_file_at_ref = record_required
        module.git_blob_bytes = no_tc_import_blob
        try:
            try:
                module.validate_tc_registration_transition(
                    repo, candidate, candidate, "synthetic-candidate"
                )
            except ValueError as exc:
                if "requires exactly one semantic TheoryCompletion public-root import" not in str(exc):
                    raise AssertionError(
                        f"unexpected registered-TC import-persistence rejection: {exc}"
                    ) from exc
            else:
                raise AssertionError(
                    "registered TC could lose its public import on a later transition"
                )
        finally:
            module.require_file_at_ref = original_require_file_at_ref
            module.git_blob_bytes = original_git_blob_bytes

        removed_tc = copy.deepcopy(candidate)
        del removed_tc["tracks"]["TC"]
        removed_tc["architecture_record_schema"]["track_owners"].remove("TC")
        del removed_tc["architecture_record_schema"]["track_status"]["TC"]
        try:
            module.validate_tc_registration_transition(
                repo, candidate, removed_tc, "synthetic-candidate"
            )
        except ValueError as exc:
            if "persistent and cannot be silently removed" not in str(exc):
                raise AssertionError(
                    f"unexpected TC-removal transition rejection: {exc}"
                ) from exc
        else:
            raise AssertionError("registered TC could be silently removed")
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
    objecthood_track = live_config.get("tracks", {}).get("O")
    objecthood_owned_doc = None
    if objecthood_open:
        if not isinstance(objecthood_track, dict):
            raise AssertionError("open Objecthood gate requires active Track O")
        doc_prefixes = [
            prefix
            for prefix in objecthood_track.get("allowed_path_prefixes", [])
            if prefix.startswith(
                "formalization/ueot-core/docs/compression/objecthood/"
            )
        ]
        if not doc_prefixes:
            raise AssertionError(
                "active Track O requires at least one owned Objecthood docs prefix"
            )
        objecthood_owned_doc = doc_prefixes[0] + "CURRENT_TRACK_OWNED_AUDIT.md"

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
        [objecthood_owned_doc] if objecthood_open else [
            "formalization/ueot-core/docs/compression/objecthood/"
            "CURRENT_TRACK_OWNED_AUDIT.md"
        ],
        objecthood_open,
        "" if objecthood_open else "unclassified compression research branch",
    )
    print("objecthood-live-gate-policy: PASS")

    test_v2_additive_only_guard(repo)
    print("risk-v2-additive-only-existing-surface-guard: PASS")

    test_tc_forward_registration_compatibility(repo)
    print("theory-completion-forward-registration-compatibility: PASS")

    run_case(
        repo,
        "compression/objecthood-self-repair",
        ["formalization/ueot-core/UEOT/V3/Compression.lean"],
        False,
        (
            "outside its owned Objecthood namespace"
            if objecthood_open
            else "unclassified compression research branch"
        ),
    )
    print("objecthood-global-root-rejected: PASS")

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
        "compression/topology-theory-completion-isolation",
        [
            "formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/"
            "Intrusion.lean"
        ],
        False,
        "may not modify cross-owned/protected path",
    )
    print("structural-track-theory-completion-isolation: PASS")

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
            "compression/objecthood-future-task\n"
        )
        cap_file = Path(handle.name)
    try:
        run_case(
            repo,
            "ops/compression-research-governance",
            [],
            True,
            "",
            ["--live-branches-file", str(cap_file)],
        )
    finally:
        cap_file.unlink(missing_ok=True)
    print("four-track-concurrency-v2: PASS")

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

    test_objecthood_root_import_guard(repo)
    print("objecthood-root-additive-import-only: PASS")

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
            "formalization/ueot-core/docs/compression/objecthood/homeostasis/"
            "RH0_RECURRENT_FAULT_SYSTEM_AUDIT.md"
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
