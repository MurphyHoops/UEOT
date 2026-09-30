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
import urllib.error
import urllib.request
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


def parse_json_object(raw: str, context: str) -> dict:
    try:
        value = json.loads(raw)
    except json.JSONDecodeError as exc:
        fail(f"could not parse JSON-compatible governance data {context}: {exc}")
    if not isinstance(value, dict):
        fail(f"governance data must contain one JSON object: {context}")
    return value


def load_json(path: Path) -> dict:
    try:
        raw = path.read_text(encoding="utf-8")
    except OSError as exc:
        fail(f"could not load governance file {path}: {exc}")
    return parse_json_object(raw, str(path))


def load_json_at_ref(repo: Path, ref: str, rel: Path) -> dict | None:
    completed = subprocess.run(
        ["git", "show", f"{ref}:{rel.as_posix()}"],
        cwd=repo,
        text=True,
        capture_output=True,
        check=False,
    )
    if completed.returncode != 0:
        return None
    return parse_json_object(completed.stdout, f"{ref}:{rel.as_posix()}")


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
    repo: Path,
    baseline_ref: str | None,
    changed_path_file: str | None,
    candidate_ref: str,
) -> list[str]:
    if changed_path_file:
        raw = Path(changed_path_file).read_text(encoding="utf-8")
        return sorted({line.strip() for line in raw.splitlines() if line.strip()})
    if not baseline_ref:
        return []
    try:
        raw = git(
            repo,
            "diff",
            "--name-status",
            "-M",
            f"{baseline_ref}...{candidate_ref}",
        )
    except subprocess.CalledProcessError as exc:
        fail(f"could not compute changed paths against {baseline_ref}: {exc}")
    paths: set[str] = set()
    for line in raw.splitlines():
        if not line.strip():
            continue
        fields = line.split("\t")
        status = fields[0]
        if status.startswith(("R", "C")):
            if len(fields) != 3:
                fail(f"malformed rename/copy diff record: {line!r}")
            paths.add(fields[1])
            paths.add(fields[2])
        else:
            if len(fields) != 2:
                fail(f"malformed changed-path diff record: {line!r}")
            paths.add(fields[1])
    return sorted(paths)


def matches_any(branch: str, patterns: list[re.Pattern[str]]) -> bool:
    return any(pattern.fullmatch(branch) for pattern in patterns)


def string_list(value: object, context: str, *, allow_empty: bool = False) -> list[str]:
    if not isinstance(value, list):
        fail(f"{context} must be a list")
    if not allow_empty and not value:
        fail(f"{context} must be nonempty")
    if not all(isinstance(item, str) and item for item in value):
        fail(f"{context} entries must be nonempty strings")
    return value


def is_governed_path(path: str, config: dict) -> bool:
    exact = set(string_list(config.get("governed_exact_paths"), "governed_exact_paths"))
    prefixes = tuple(
        string_list(config.get("governed_path_prefixes"), "governed_path_prefixes")
    )
    return path in exact or any(path.startswith(prefix) for prefix in prefixes)


def track_owned_path(path: str, track: dict) -> bool:
    exact = set(track.get("allowed_exact_paths", []))
    prefixes = tuple(track.get("allowed_path_prefixes", []))
    return path in exact or any(path.startswith(prefix) for prefix in prefixes)


def repository_slug(repo: Path) -> str:
    env_value = os.environ.get("GITHUB_REPOSITORY")
    if env_value and "/" in env_value:
        return env_value
    remote = git(repo, "remote", "get-url", "origin")
    match = re.search(r"github\.com[/:]([^/]+)/([^/]+?)(?:\.git)?$", remote)
    if not match:
        fail(f"could not infer GitHub repository from origin URL: {remote}")
    return f"{match.group(1)}/{match.group(2)}"


def github_get_json(repo_slug: str, endpoint: str, token: str) -> object:
    request = urllib.request.Request(
        f"https://api.github.com/repos/{repo_slug}{endpoint}",
        headers={
            "Accept": "application/vnd.github+json",
            "Authorization": f"Bearer {token}",
            "X-GitHub-Api-Version": "2022-11-28",
            "User-Agent": "ueot-compression-research-validator",
        },
    )
    try:
        with urllib.request.urlopen(request, timeout=30) as response:
            return json.loads(response.read().decode("utf-8"))
    except (urllib.error.URLError, urllib.error.HTTPError, json.JSONDecodeError) as exc:
        fail(f"GitHub live-state query failed for {endpoint}: {exc}")


def github_branch_names(repo_slug: str, token: str) -> list[str]:
    names: list[str] = []
    page = 1
    while True:
        payload = github_get_json(
            repo_slug, f"/branches?per_page=100&page={page}", token
        )
        if not isinstance(payload, list):
            fail("GitHub branches endpoint returned a non-list payload")
        page_names = [
            item.get("name")
            for item in payload
            if isinstance(item, dict) and isinstance(item.get("name"), str)
        ]
        names.extend(page_names)
        if len(payload) < 100:
            break
        page += 1
    return names


def associated_pr_branch(repo_slug: str, sha: str, token: str) -> str | None:
    payload = github_get_json(repo_slug, f"/commits/{sha}/pulls?per_page=20", token)
    if not isinstance(payload, list):
        fail("GitHub commit/pulls endpoint returned a non-list payload")
    matches: list[str] = []
    for item in payload:
        if not isinstance(item, dict):
            continue
        head = item.get("head")
        if not isinstance(head, dict):
            continue
        ref = head.get("ref")
        if not isinstance(ref, str):
            continue
        if item.get("merge_commit_sha") == sha:
            matches.append(ref)
    unique = sorted(set(matches))
    if len(unique) > 1:
        fail(f"main push commit {sha} is ambiguously associated with PR branches {unique}")
    return unique[0] if unique else None


def validate_live_concurrency(
    branch_names: list[str],
    compiled: dict[str, list[re.Pattern[str]]],
) -> None:
    for branch in branch_names:
        if not branch.startswith("compression/"):
            continue
        matches = [
            track_id
            for track_id in ("S", "H")
            if matches_any(branch, compiled[track_id])
        ]
        if not matches:
            fail(f"unclassified live compression branch is not allowed: {branch}")
        if len(matches) > 1:
            fail(f"live compression branch ambiguously matches tracks: {branch}")

    for track_id in ("S", "H"):
        active = sorted(
            branch
            for branch in branch_names
            if matches_any(branch, compiled[track_id])
        )
        if len(active) > 1:
            fail(
                f"Track {track_id} has {len(active)} active remote branches; "
                f"only one is allowed: {active}"
            )


def changed_lines_for_path(repo: Path, baseline_ref: str, path: str) -> list[str]:
    return changed_lines_for_path_between(repo, baseline_ref, "HEAD", path)


def changed_lines_for_path_between(
    repo: Path, baseline_ref: str, candidate_ref: str, path: str
) -> list[str]:
    try:
        patch = git(
            repo,
            "diff",
            "--unified=0",
            f"{baseline_ref}...{candidate_ref}",
            "--",
            path,
        )
    except subprocess.CalledProcessError as exc:
        fail(f"could not inspect patch for {path}: {exc}")
    changed: list[str] = []
    for line in patch.splitlines():
        if line.startswith(("+++", "---", "@@")):
            continue
        if line.startswith(("+", "-")):
            changed.append(line[1:].strip())
    return changed


def validate_compression_root_import_change(
    repo: Path,
    baseline_ref: str | None,
    candidate_ref: str,
    track_id: str,
    paths: list[str],
) -> None:
    root = "formalization/ueot-core/UEOT/V3/Compression.lean"
    if root not in paths:
        return
    if not baseline_ref:
        fail("Compression.lean ownership validation requires a baseline ref")
    changed = changed_lines_for_path_between(
        repo, baseline_ref, candidate_ref, root
    )
    if track_id == "S":
        for line in changed:
            if not line.startswith("import UEOT.V3.Compression."):
                fail("Track S may change Compression.lean imports only")
            if line == "import UEOT.V3.Compression.Hierarchy":
                fail("Track S may not add/remove the Track H root import")
    elif track_id == "GOVERNANCE":
        if not changed or any(
            line != "import UEOT.V3.Compression.Hierarchy" for line in changed
        ):
            fail(
                "governance may modify Compression.lean only to add/remove the "
                "public Hierarchy root import"
            )
    else:
        fail(f"Track {track_id} may not modify Compression.lean")


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
    string_list(config.get("governed_path_prefixes"), "governed_path_prefixes")
    string_list(config.get("governed_exact_paths"), "governed_exact_paths")

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

    governance = config.get("governance")
    if not isinstance(governance, dict):
        fail("research-track governance must define governance branch ownership")
    compiled["GOVERNANCE"] = compile_patterns(
        governance.get("branch_patterns"), "governance"
    )
    string_list(
        governance.get("allowed_path_prefixes"),
        "governance.allowed_path_prefixes",
        allow_empty=True,
    )
    string_list(
        governance.get("allowed_exact_paths"),
        "governance.allowed_exact_paths",
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
    repo: Path,
    baseline_ref: str | None,
    candidate_ref: str,
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
    governance_match = matches_any(branch, compiled["GOVERNANCE"])
    if len(matches) > 1:
        fail(f"branch {branch!r} ambiguously matches multiple research tracks")
    if matches and governance_match:
        fail(f"branch {branch!r} matches both research and governance patterns")

    governed_changes = [path for path in paths if is_governed_path(path, config)]

    if governance_match:
        governance = config["governance"]
        allowed_exact = set(governance.get("allowed_exact_paths", []))
        allowed_prefixes = tuple(governance.get("allowed_path_prefixes", []))
        for path in paths:
            if path in allowed_exact or any(
                path.startswith(prefix) for prefix in allowed_prefixes
            ):
                continue
            fail(
                f"governance branch {branch!r} modified {path}, outside the "
                "registered governance surface"
            )
        validate_compression_root_import_change(
            repo, baseline_ref, candidate_ref, "GOVERNANCE", paths
        )
        return

    if not matches:
        if branch.startswith("compression/"):
            fail(f"unclassified compression research branch is not allowed: {branch}")
        if governed_changes:
            fail(
                f"unclassified branch {branch!r} modified governed Compression "
                f"paths: {governed_changes}"
            )
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
    elif track_id == "S":
        allowed_prefixes = (
            "formalization/ueot-core/UEOT/V3/Compression/",
            "formalization/ueot-core/docs/compression/",
        )
        allowed_exact = {"formalization/ueot-core/UEOT/V3/Compression.lean"}
        for path in paths:
            if path in allowed_exact or any(
                path.startswith(prefix) for prefix in allowed_prefixes
            ):
                continue
            fail(
                f"Track S branch {branch!r} modified {path}, outside the "
                "post-FINAL Compression research surface"
            )

    validate_compression_root_import_change(
        repo, baseline_ref, candidate_ref, track_id, paths
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", default=".")
    parser.add_argument("--baseline-ref")
    parser.add_argument("--candidate-ref", default="HEAD")
    parser.add_argument("--branch-name")
    parser.add_argument("--head-repo")
    parser.add_argument("--base-repo")
    parser.add_argument("--changed-path-file")
    parser.add_argument("--live-branches-file")
    parser.add_argument("--associated-branch")
    parser.add_argument("--verify-live-state", action="store_true")
    args = parser.parse_args()

    repo = Path(args.repo_root).resolve()
    config = load_json(repo / TRACKS_REL)
    ledger = load_json(repo / LEDGER_REL)
    compiled = validate_static(repo, config, ledger)
    enforcement_config = config
    enforcement_compiled = compiled
    if args.baseline_ref:
        baseline_config = load_json_at_ref(repo, args.baseline_ref, TRACKS_REL)
        if baseline_config is not None:
            enforcement_config = baseline_config
            enforcement_compiled = validate_static(repo, baseline_config, ledger)

    branch = branch_for_run(repo, args.branch_name)
    paths = changed_paths(
        repo, args.baseline_ref, args.changed_path_file, args.candidate_ref
    )
    governed_changes = [
        path for path in paths if is_governed_path(path, enforcement_config)
    ]

    repo_slug: str | None = None
    token: str | None = None
    if args.verify_live_state:
        token = os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN")
        if not token:
            fail("--verify-live-state requires GH_TOKEN or GITHUB_TOKEN")
        repo_slug = repository_slug(repo)

    if branch == "main" and governed_changes:
        associated = args.associated_branch
        if associated is None and args.verify_live_state:
            sha = os.environ.get("GITHUB_SHA") or git(repo, "rev-parse", "HEAD")
            assert repo_slug is not None and token is not None
            associated = associated_pr_branch(repo_slug, sha, token)
        if not associated:
            fail(
                "governed Compression changes on main require an associated "
                "classified PR branch; direct-main research mutation is not allowed"
            )
        branch = associated

    classified_mutating = any(
        matches_any(branch, enforcement_compiled[track_id])
        for track_id in ("S", "H", "GOVERNANCE")
    )
    if classified_mutating and args.head_repo and args.base_repo:
        if args.head_repo != args.base_repo:
            fail(
                "fork-based mutating Compression research/governance branches "
                f"are not allowed: head={args.head_repo}, base={args.base_repo}"
            )

    if args.live_branches_file:
        branch_names = [
            line.strip()
            for line in Path(args.live_branches_file)
            .read_text(encoding="utf-8")
            .splitlines()
            if line.strip()
        ]
        validate_live_concurrency(branch_names, enforcement_compiled)
    elif args.verify_live_state:
        assert repo_slug is not None and token is not None
        validate_live_concurrency(
            github_branch_names(repo_slug, token), enforcement_compiled
        )

    validate_track_paths(
        repo,
        args.baseline_ref,
        args.candidate_ref,
        branch,
        paths,
        enforcement_config,
        enforcement_compiled,
    )

    print(
        "Compression research-track governance: PASS "
        f"(branch={branch or '<detached>'}, changed_paths={len(paths)})"
    )


if __name__ == "__main__":
    main()
