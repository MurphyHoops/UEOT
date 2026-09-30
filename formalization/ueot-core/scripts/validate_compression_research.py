#!/usr/bin/env python3
"""Validate post-FINAL Compression research-track governance.

This validator is intentionally independent of the counted compression ledger
validator.  It protects parallel research ownership without granting any new
counted scientific status.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path


TRACKS_REL = Path(
    "formalization/ueot-core/docs/compression/COMPRESSION_RESEARCH_TRACKS.json"
)
LEDGER_REL = Path(
    "formalization/ueot-core/docs/compression/COMPRESSION_LEDGER.yaml"
)


def fail(message: str) -> None:
    print(f"ERROR: {message}", file=sys.stderr)
    raise SystemExit(1)


def git(repo: Path, *args: str) -> str:
    return subprocess.check_output(
        ["git", *args], cwd=repo, text=True, stderr=subprocess.STDOUT
    ).strip()


def load_json(path: Path) -> dict:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        fail(f"could not load JSON-compatible governance file {path}: {exc}")
    if not isinstance(value, dict):
        fail(f"governance file must contain one JSON object: {path}")
    return value


def require_file(repo: Path, rel: str, context: str) -> None:
    if not (repo / rel).is_file():
        fail(f"{context}: referenced file does not exist: {rel}")


def compile_patterns(values: object, context: str) -> list[re.Pattern[str]]:
    if not isinstance(values, list) or not values:
        fail(f"{context}: branch_patterns must be a nonempty list")
    compiled: list[re.Pattern[str]] = []
    for raw in values:
        if not isinstance(raw, str) or not raw:
            fail(f"{context}: branch pattern must be a nonempty string")
        try:
            compiled.append(re.compile(raw))
        except re.error as exc:
            fail(f"{context}: invalid branch regex {raw!r}: {exc}")
    return compiled


def branch_for_run(repo: Path, explicit: str | None) -> str:
    if explicit:
        return explicit
    for key in ("GITHUB_HEAD_REF", "REF_NAME", "GITHUB_REF_NAME"):
        value = os.environ.get(key)
        if value:
            return value
    return git(repo, "branch", "--show-current")


def changed_paths(
    repo: Path, baseline_ref: str | None, changed_path_file: str | None
) -> list[str]:
    if changed_path_file:
        raw = Path(changed_path_file).read_text(encoding="utf-8")
        return sorted({line.strip() for line in raw.splitlines() if line.strip()})
    if not baseline_ref:
        return []
    try:
        raw = git(repo, "diff", "--name-only", f"{baseline_ref}...HEAD")
    except subprocess.CalledProcessError as exc:
        fail(f"could not compute changed paths against {baseline_ref}: {exc}")
    return sorted({line.strip() for line in raw.splitlines() if line.strip()})


def matches_any(branch: str, patterns: list[re.Pattern[str]]) -> bool:
    return any(pattern.fullmatch(branch) for pattern in patterns)


def validate_static(repo: Path, config: dict, ledger: dict) -> dict[str, list[re.Pattern[str]]]:
    if config.get("schema_version") != 1:
        fail("research-track governance schema_version must be 1")
    if config.get("authority_issue") != 146:
        fail("research-track governance authority_issue must remain #146")
    if config.get("counted_core_policy") != "must_match_live_ledger_minimal_core":
        fail("research-track governance must inherit the live ledger minimal core")
    if config.get("max_active_mutating_tracks") != 2:
        fail("post-FINAL governance permits exactly two mutating tracks")
    if config.get("main_only_cross_track_dependencies") is not True:
        fail("cross-track dependencies must remain main-only")
    if config.get("cross_track_integration_gate") not in {"closed", "open"}:
        fail("cross_track_integration_gate must be closed or open")

    for field in (
        "mission_contract",
        "operations_manual",
        "post_final_governance",
        "ledger",
    ):
        value = config.get(field)
        if not isinstance(value, str) or not value:
            fail(f"research-track governance needs nonempty {field}")
        require_file(repo, value, "research-track governance")

    tracks = config.get("tracks")
    if not isinstance(tracks, dict) or set(tracks) != {"S", "H"}:
        fail("research-track governance must define exactly Track S and Track H")

    compiled: dict[str, list[re.Pattern[str]]] = {}
    for track_id in ("S", "H"):
        track = tracks[track_id]
        if not isinstance(track, dict):
            fail(f"Track {track_id} definition must be an object")
        if track.get("status") != "active":
            fail(f"Track {track_id} must remain explicitly active while registered")
        topics = track.get("owned_topics")
        if not isinstance(topics, list) or not topics:
            fail(f"Track {track_id} must declare owned_topics")
        compiled[track_id] = compile_patterns(
            track.get("branch_patterns"), f"Track {track_id}"
        )

    h = tracks["H"]
    if h.get("initial_gate") != "H0-H3":
        fail("Track H must begin at H0-H3")
    if (
        h.get("long_run_stability_work")
        != "blocked_until_cross_track_integration_gate_opens"
    ):
        fail("Track H long-run stability work must remain gated")

    minimal_core = ledger.get("minimal_core")
    if not isinstance(minimal_core, dict):
        fail("compression ledger is missing minimal_core")
    if minimal_core.get("state") != "frozen":
        fail("post-FINAL research governance requires a frozen counted core")
    generator_ids = minimal_core.get("generator_ids")
    if not isinstance(generator_ids, list) or not generator_ids:
        fail("live ledger minimal core has no generator_ids")

    coverage = ledger.get("coverage")
    if not isinstance(coverage, dict):
        fail("compression ledger is missing coverage")
    if coverage.get("counted_generators") != len(generator_ids):
        fail("live ledger counted generator count disagrees with minimal_core")

    return compiled


def validate_track_paths(
    branch: str,
    paths: list[str],
    config: dict,
    compiled: dict[str, list[re.Pattern[str]]],
) -> None:
    matches = [
        track_id
        for track_id in ("S", "H")
        if matches_any(branch, compiled[track_id])
    ]
    if len(matches) > 1:
        fail(f"branch {branch!r} ambiguously matches multiple research tracks")
    if not matches:
        return

    track_id = matches[0]
    track = config["tracks"][track_id]
    forbidden_exact = set(track.get("forbidden_exact_paths", []))
    forbidden_prefixes = tuple(track.get("forbidden_path_prefixes", []))

    for path in paths:
        if path in forbidden_exact or any(
            path.startswith(prefix) for prefix in forbidden_prefixes
        ):
            fail(
                f"Track {track_id} branch {branch!r} may not modify "
                f"cross-owned/protected path {path}"
            )

    if track_id == "H":
        allowed_exact = set(track.get("allowed_exact_paths", []))
        allowed_prefixes = tuple(track.get("allowed_path_prefixes", []))
        for path in paths:
            if path in allowed_exact or any(
                path.startswith(prefix) for prefix in allowed_prefixes
            ):
                continue
            fail(
                f"Track H branch {branch!r} modified {path}, outside its "
                "owned Hierarchy namespace"
            )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", default=".")
    parser.add_argument("--baseline-ref")
    parser.add_argument("--branch-name")
    parser.add_argument("--changed-path-file")
    args = parser.parse_args()

    repo = Path(args.repo_root).resolve()
    config = load_json(repo / TRACKS_REL)
    ledger = load_json(repo / LEDGER_REL)
    compiled = validate_static(repo, config, ledger)
    branch = branch_for_run(repo, args.branch_name)
    paths = changed_paths(repo, args.baseline_ref, args.changed_path_file)
    validate_track_paths(branch, paths, config, compiled)

    print(
        "Compression research-track governance: PASS "
        f"(branch={branch or '<detached>'}, changed_paths={len(paths)})"
    )


if __name__ == "__main__":
    main()
