#!/usr/bin/env python3
"""Regression tests for post-FINAL research-track ownership rules."""

from __future__ import annotations

import argparse
import importlib.util
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


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", default=".")
    args = parser.parse_args()
    repo = Path(args.repo_root).resolve()

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


if __name__ == "__main__":
    main()
