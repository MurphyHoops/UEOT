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
TRACK_IDS = ("S", "H", "X", "O", "TC")
TC_LEAN_PREFIX = "formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/"
TC_DOC_PREFIX = "formalization/ueot-core/docs/compression/theory_completion/"
TC_PUBLIC_ROOT = "formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion.lean"
TC_MODULE = "UEOT.V3.Compression.TheoryCompletion"
TC_PUBLIC_IMPORT = "import UEOT.V3.Compression.TheoryCompletion"
COMPRESSION_PUBLIC_ROOT = "formalization/ueot-core/UEOT/V3/Compression.lean"
TC_BOOTSTRAP_DOCS = {
    f"{TC_DOC_PREFIX}THEORY_COMPLETION_MISSION.md",
    f"{TC_DOC_PREFIX}THEORY_COMPLETION_ROADMAP.md",
    f"{TC_DOC_PREFIX}THEORY_COMPLETION_ARCHITECTURE.md",
    f"{TC_DOC_PREFIX}THEORY_COMPLETION_CLAIM_POLICY.md",
    f"{TC_DOC_PREFIX}THEORY_COMPLETION_STATUS.json",
}
TC_ALLOWED_PATH_PREFIXES = {TC_LEAN_PREFIX, TC_DOC_PREFIX}
TC_ALLOWED_EXACT_PATHS = {TC_PUBLIC_ROOT}
TC_FORBIDDEN_PATH_PREFIXES = {
    "formalization/ueot-core/UEOT/V3/Compression/Hierarchy/",
    "formalization/ueot-core/docs/compression/hierarchy/",
    "formalization/ueot-core/UEOT/V3/Compression/CrossTrack/",
    "formalization/ueot-core/docs/compression/cross_track/",
    "formalization/ueot-core/UEOT/V3/Compression/Objecthood/",
    "formalization/ueot-core/docs/compression/objecthood/",
}
TC_FORBIDDEN_EXACT_PATHS = {
    "formalization/ueot-core/docs/compression/COMPRESSION_LEDGER.yaml",
    "formalization/ueot-core/docs/compression/COMPRESSION_COVERAGE.md",
    "formalization/ueot-core/docs/compression/COMPRESSION_MISSION.md",
    "formalization/ueot-core/docs/compression/COMPRESSION_ABLATION.md",
    "formalization/ueot-core/docs/compression/COMPRESSION_BOOTSTRAP.md",
    "formalization/ueot-core/docs/compression/COMPRESSION_OPERATIONS.md",
    "formalization/ueot-core/docs/compression/POST_FINAL_RESEARCH_GOVERNANCE.md",
    "formalization/ueot-core/docs/compression/COMPRESSION_RESEARCH_TRACKS.json",
    "formalization/ueot-core/scripts/validate_compression.py",
    "formalization/ueot-core/scripts/validate_compression_research.py",
    ".github/workflows/ueot-core-compression.yml",
    ".github/workflows/ueot-compression-research-policy.yml",
    "formalization/ueot-core/UEOT/V3/Compression/Hierarchy.lean",
    "formalization/ueot-core/UEOT/V3/Compression/CrossTrack.lean",
    "formalization/ueot-core/UEOT/V3/Compression/Objecthood.lean",
    "formalization/ueot-core/UEOT/V3/Compression.lean",
}
TC_REQUIRED_S_FORBIDDEN_PREFIXES = TC_ALLOWED_PATH_PREFIXES
TC_REQUIRED_S_FORBIDDEN_EXACT_PATHS = TC_ALLOWED_EXACT_PATHS


def line_imports_module(line: str, module: str) -> bool:
    """Recognize one Lean import command for a module, including trailing comments."""

    return re.match(
        rf"^\s*import\s+{re.escape(module)}(?=$|\s|--|/-)",
        line,
    ) is not None


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


def require_file_at_ref(repo: Path, ref: str, rel: str, context: str) -> None:
    """Require `rel` to be a regular Git blob in `ref` without checking it out."""

    completed = subprocess.run(
        ["git", "cat-file", "-t", f"{ref}:{rel}"],
        cwd=repo,
        text=True,
        capture_output=True,
        check=False,
    )
    if completed.returncode != 0 or completed.stdout.strip() != "blob":
        fail(f"{context}: referenced file does not exist in {ref}: {rel}")


def require_referenced_file(
    repo: Path, rel: str, context: str, *, ref: str | None = None
) -> None:
    """Resolve governance-declared files from one consistent authority tree.

    Normal checked-out validation uses the worktree.  Immutable-base
    `pull_request_target` validation supplies `ref=candidate_ref`, in which case
    every candidate-declared file is required to be a regular blob in the
    candidate Git tree without executing or checking out candidate code.
    """

    if ref is None:
        require_file(repo, rel, context)
    else:
        require_file_at_ref(repo, ref, rel, context)


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
    max_active_mutating_tracks: int,
) -> None:
    registered_tracks = [track_id for track_id in TRACK_IDS if track_id in compiled]
    for branch in branch_names:
        if not branch.startswith("compression/"):
            continue
        matches = [
            track_id
            for track_id in registered_tracks
            if matches_any(branch, compiled[track_id])
        ]
        if not matches:
            fail(f"unclassified live compression branch is not allowed: {branch}")
        if len(matches) > 1:
            fail(f"live compression branch ambiguously matches tracks: {branch}")

    active_tracks = 0
    for track_id in registered_tracks:
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
        if active:
            active_tracks += 1

    if active_tracks > max_active_mutating_tracks:
        fail(
            "post-FINAL mutation cap exceeded: "
            f"{active_tracks} active research tracks > {max_active_mutating_tracks}"
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


def git_blob_bytes(repo: Path, ref: str, path: str) -> bytes:
    """Read one Git blob without universal-newline normalization."""

    completed = subprocess.run(
        ["git", "show", f"{ref}:{path}"],
        cwd=repo,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if completed.returncode != 0:
        fail(f"could not read Git blob {ref}:{path}")
    return completed.stdout


def git_path_exists(repo: Path, ref: str, path: str) -> bool:
    completed = subprocess.run(
        ["git", "cat-file", "-e", f"{ref}:{path}"],
        cwd=repo,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        check=False,
    )
    return completed.returncode == 0


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
        protected_track_roots = {
            "H": "UEOT.V3.Compression.Hierarchy",
            "X": "UEOT.V3.Compression.CrossTrack",
            "O": "UEOT.V3.Compression.Objecthood",
            "TC": TC_MODULE,
        }
        for line in changed:
            if not line.startswith("import UEOT.V3.Compression."):
                fail("Track S may change Compression.lean imports only")
            for owner, module in protected_track_roots.items():
                if line_imports_module(line, module):
                    fail(
                        f"Track S may not add/remove the Track {owner} root import"
                    )
    elif track_id == "X":
        if not changed or any(
            line != "import UEOT.V3.Compression.CrossTrack" for line in changed
        ):
            fail(
                "Track X may modify Compression.lean only to add/remove the "
                "public CrossTrack root import"
            )
    elif track_id == "O":
        if not changed or any(
            line != "import UEOT.V3.Compression.Objecthood" for line in changed
        ):
            fail(
                "Track O may modify Compression.lean only to add/remove the "
                "public Objecthood root import"
            )
    elif track_id == "GOVERNANCE":
        allowed = {
            "import UEOT.V3.Compression.Hierarchy",
            "import UEOT.V3.Compression.TheoryCompletion",
        }
        if not changed or any(line not in allowed for line in changed):
            fail(
                "governance may modify Compression.lean only to add/remove the "
                "public governance-authorized track root imports"
            )
    else:
        fail(f"Track {track_id} may not modify Compression.lean")


def validate_objecthood_root_import_change(
    repo: Path,
    baseline_ref: str | None,
    candidate_ref: str,
    track_id: str,
    paths: list[str],
) -> None:
    """Keep the public Objecthood root immutable except for additive imports.

    Risk-tiered Track O research exposes new additive modules through the already
    public Objecthood.lean root.  The root exception must never become a
    backdoor for rewriting merged imports or adding declarations to the root.
    """

    root = "formalization/ueot-core/UEOT/V3/Compression/Objecthood.lean"
    if root not in paths:
        return
    if track_id != "O":
        fail(f"Track {track_id} may not modify Objecthood.lean")
    if not baseline_ref:
        fail("Objecthood.lean ownership validation requires a baseline ref")

    allowed_import = re.compile(
        r"import UEOT\.V3\.Compression\.Objecthood"
        r"(?:\.[A-Za-z_][A-Za-z0-9_']*)+$"
    )

    baseline_blob = git_blob_bytes(repo, baseline_ref, root)
    candidate_blob = git_blob_bytes(repo, candidate_ref, root)
    if b"\r" in candidate_blob or b"\x00" in candidate_blob:
        fail(
            "Track O Objecthood.lean candidate contains forbidden line-control "
            "or NUL characters"
        )
    try:
        baseline_text = baseline_blob.decode("utf-8")
        candidate_text = candidate_blob.decode("utf-8")
    except UnicodeDecodeError:
        fail("Track O Objecthood.lean must remain valid UTF-8 text")

    baseline_lines = baseline_text.split("\n")
    candidate_lines = candidate_text.split("\n")

    def import_preamble(lines: list[str]) -> tuple[list[str], list[str]]:
        end = 0
        while end < len(lines) and lines[end].startswith("import "):
            end += 1
        return lines[:end], lines[end:]

    baseline_imports, baseline_suffix = import_preamble(baseline_lines)
    candidate_imports, candidate_suffix = import_preamble(candidate_lines)

    # Everything after the import preamble is frozen byte-for-byte (modulo the
    # UTF-8 decode above). This prevents an allowed-looking import from being
    # relocated into the module doc-comment or any later declaration context.
    if candidate_suffix != baseline_suffix:
        fail(
            "Track O may modify Objecthood.lean only by inserting additive "
            "imports inside the existing import preamble"
        )
    if len(set(candidate_imports)) != len(candidate_imports):
        fail("Track O Objecthood.lean import preamble may not contain duplicates")

    # The candidate preamble must preserve every baseline import in its exact
        # original order. Any intervening line is a newly inserted Track-O import and
    # must be one complete allowed command. This is insertion-only: later RH
    # stages cannot delete, move, or rewrite imports exposed by earlier stages.
    baseline_index = 0
    inserted = 0
    for line in candidate_imports:
        if (
            baseline_index < len(baseline_imports)
            and line == baseline_imports[baseline_index]
        ):
            baseline_index += 1
            continue
        if allowed_import.fullmatch(line) is None:
            fail(
                "Track O may insert only complete imports below "
                "UEOT.V3.Compression.Objecthood.*"
            )
        inserted += 1
    if baseline_index != len(baseline_imports):
        fail("Track O may not delete, move, or rewrite existing Objecthood imports")
    if inserted == 0:
        fail("Track O Objecthood.lean change must add a Track-O module import")


def validate_owned_track_root_import_change(
    repo: Path,
    baseline_ref: str | None,
    candidate_ref: str,
    track_id: str,
    paths: list[str],
) -> None:
    roots = {
        "H": (
            "formalization/ueot-core/UEOT/V3/Compression/Hierarchy.lean",
            "UEOT.V3.Compression.Hierarchy",
        ),
        "X": (
            "formalization/ueot-core/UEOT/V3/Compression/CrossTrack.lean",
            "UEOT.V3.Compression.CrossTrack",
        ),
        "TC": (
            "formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion.lean",
            "UEOT.V3.Compression.TheoryCompletion",
        ),
    }
    spec = roots.get(track_id)
    if spec is None:
        return
    root, module_prefix = spec
    if root not in paths:
        return
    if not baseline_ref:
        fail(f"Track {track_id} root ownership validation requires a baseline ref")

    baseline_blob = git_blob_bytes(repo, baseline_ref, root)
    candidate_blob = git_blob_bytes(repo, candidate_ref, root)
    if b"\r" in candidate_blob or b"\x00" in candidate_blob:
        fail(f"Track {track_id} root contains forbidden line-control or NUL characters")
    try:
        baseline_text = baseline_blob.decode("utf-8")
        candidate_text = candidate_blob.decode("utf-8")
    except UnicodeDecodeError:
        fail(f"Track {track_id} root must remain valid UTF-8 text")

    def import_preamble(lines: list[str]) -> tuple[list[str], list[str]]:
        end = 0
        while end < len(lines) and lines[end].startswith("import "):
            end += 1
        return lines[:end], lines[end:]

    baseline_imports, baseline_suffix = import_preamble(baseline_text.split("\n"))
    candidate_imports, candidate_suffix = import_preamble(candidate_text.split("\n"))
    if candidate_suffix != baseline_suffix:
        fail(f"Track {track_id} may modify its public root by additive imports only")
    if len(set(candidate_imports)) != len(candidate_imports):
        fail(f"Track {track_id} root import preamble may not contain duplicates")

    allowed_import = re.compile(
        rf"import {re.escape(module_prefix)}(?:\.[A-Za-z_][A-Za-z0-9_']*)+$"
    )
    baseline_index = 0
    inserted = 0
    for line in candidate_imports:
        if (
            baseline_index < len(baseline_imports)
            and line == baseline_imports[baseline_index]
        ):
            baseline_index += 1
            continue
        if allowed_import.fullmatch(line) is None:
            fail(
                f"Track {track_id} may insert only complete imports below "
                f"{module_prefix}.*"
            )
        inserted += 1
    if baseline_index != len(baseline_imports):
        fail(f"Track {track_id} may not delete, move, or rewrite existing root imports")
    if inserted == 0:
        fail(f"Track {track_id} root change must add an owned module import")


def validate_architecture_records(
    repo: Path,
    config: dict,
    ledger: dict,
    *,
    evidence_ref: str | None = None,
) -> None:
    schema = config.get("architecture_record_schema")
    if not isinstance(schema, dict):
        fail("research governance must define architecture_record_schema")
    if schema.get("schema_version") != 1:
        fail("architecture_record_schema.schema_version must be 1")

    tracks = config.get("tracks")
    tc_registered = isinstance(tracks, dict) and "TC" in tracks
    expected_track_owners = ["CORE", "S", "H", "X", "O"]
    if tc_registered:
        expected_track_owners.append("TC")

    expected_axes = {
        "architecture_roles": ["G0", "G1", "G2", "G3"],
        "lifecycle_statuses": [
            "RESEARCH",
            "MERGED_UNCOUNTED",
            "CANDIDATE",
            "PROMOTION_AUDIT",
            "COUNTED",
            "RETAINED_ADAPTER",
            "RETAINED_BOUNDARY",
            "REJECTED",
        ],
        "track_owners": expected_track_owners,
        "authority_provenance": [
            "FROZEN_CORE_V3",
            "POST_FINAL_MERGED",
            "POST_FINAL_RESEARCH",
            "SYNTHESIS_ONLY",
        ],
        "counted_core_impacts": ["NONE", "PROPOSED", "COUNTED"],
    }
    for field, expected in expected_axes.items():
        actual = string_list(schema.get(field), f"architecture_record_schema.{field}")
        if actual != expected:
            fail(
                f"architecture_record_schema.{field} must remain exactly {expected}"
            )

    gate = config.get("cross_track_integration_gate")
    omega_gate = config.get("objecthood_omega_gate")
    expected_track_status = {
        "CORE": "frozen",
        "S": "active",
        "H": "active",
        "X": "active" if gate == "open" else "closed",
        "O": "active" if omega_gate == "open" else "closed",
    }
    if tc_registered:
        expected_track_status["TC"] = "active"
    track_status = schema.get("track_status")
    if track_status != expected_track_status:
        fail(
            "architecture track_status must keep CORE frozen, S/H active, "
            f"X {'active' if gate == 'open' else 'closed'} with the integration gate, "
            f"O {'active' if omega_gate == 'open' else 'closed'} with the Objecthood gate, "
            f"and TC {'active' if tc_registered else 'absent'}"
        )

    required_fields = string_list(
        schema.get("required_record_fields"),
        "architecture_record_schema.required_record_fields",
    )
    expected_required = {
        "record_id",
        "title",
        "architecture_role",
        "lifecycle_status",
        "track_owner",
        "authority_provenance",
        "counted_core_impact",
        "evidence_paths",
    }
    if set(required_fields) != expected_required:
        fail(
            "architecture_record_schema.required_record_fields must contain the "
            "complete five-axis record contract plus identity/evidence"
        )

    records = config.get("architecture_records")
    if not isinstance(records, list) or not records:
        fail("research governance must contain nonempty architecture_records")

    allowed = {field: set(values) for field, values in expected_axes.items()}
    seen: set[str] = set()
    counted_record_ids: set[str] = set()
    for index, record in enumerate(records):
        context = f"architecture_records[{index}]"
        if not isinstance(record, dict):
            fail(f"{context} must be an object")
        missing = expected_required - set(record)
        if missing:
            fail(f"{context} is missing required fields: {sorted(missing)}")

        record_id = record.get("record_id")
        title = record.get("title")
        if not isinstance(record_id, str) or not record_id:
            fail(f"{context}.record_id must be a nonempty string")
        if record_id in seen:
            fail(f"duplicate architecture record_id: {record_id}")
        seen.add(record_id)
        if not isinstance(title, str) or not title:
            fail(f"{context}.title must be a nonempty string")

        role = record.get("architecture_role")
        lifecycle = record.get("lifecycle_status")
        owner = record.get("track_owner")
        provenance = record.get("authority_provenance")
        impact = record.get("counted_core_impact")
        axis_values = {
            "architecture_roles": role,
            "lifecycle_statuses": lifecycle,
            "track_owners": owner,
            "authority_provenance": provenance,
            "counted_core_impacts": impact,
        }
        for field, value in axis_values.items():
            if value not in allowed[field]:
                fail(f"{context}: invalid {field} value {value!r}")

        evidence = string_list(record.get("evidence_paths"), f"{context}.evidence_paths")
        for path in evidence:
            require_referenced_file(repo, path, context, ref=evidence_ref)

        if lifecycle == "COUNTED" or impact == "COUNTED":
            if not (role == "G0" and lifecycle == "COUNTED" and impact == "COUNTED"):
                fail(f"{context}: only G0 + COUNTED may contribute to the counted core")
            counted_record_ids.add(record_id)
        if role != "G0" and impact != "NONE":
            fail(f"{context}: G1/G2/G3 records cannot propose or claim counted-core impact")
        if impact == "PROPOSED" and lifecycle not in {"CANDIDATE", "PROMOTION_AUDIT"}:
            fail(f"{context}: PROPOSED counted impact requires CANDIDATE or PROMOTION_AUDIT")
        if lifecycle in {"CANDIDATE", "PROMOTION_AUDIT"} and role != "G0":
            fail(f"{context}: primitive promotion lifecycle requires architecture role G0")

        if provenance == "POST_FINAL_RESEARCH" and lifecycle != "RESEARCH":
            fail(f"{context}: POST_FINAL_RESEARCH provenance requires RESEARCH lifecycle")
        if provenance == "POST_FINAL_MERGED" and lifecycle == "RESEARCH":
            fail(f"{context}: POST_FINAL_MERGED provenance cannot retain RESEARCH lifecycle")
        if provenance == "FROZEN_CORE_V3" and owner != "CORE":
            fail(f"{context}: FROZEN_CORE_V3 authority must remain owned by CORE")
        if provenance == "SYNTHESIS_ONLY" and impact != "NONE":
            fail(f"{context}: SYNTHESIS_ONLY records cannot affect counted-core accounting")
        if owner == "X" and config.get("cross_track_integration_gate") == "closed":
            fail(f"{context}: Track X records are forbidden while the integration gate is closed")
        if owner == "O" and config.get("objecthood_omega_gate") == "closed":
            if lifecycle not in {"MERGED_UNCOUNTED", "REJECTED"}:
                fail(
                    f"{context}: closed Objecthood gate permits only historical "
                    "MERGED_UNCOUNTED/REJECTED Track O records"
                )
            if provenance not in {"POST_FINAL_MERGED", "SYNTHESIS_ONLY"}:
                fail(
                    f"{context}: closed Objecthood gate permits only merged/synthesis "
                    "authority for historical Track O records"
                )

    minimal_core = ledger.get("minimal_core")
    if not isinstance(minimal_core, dict):
        fail("compression ledger is missing minimal_core")
    generator_ids = minimal_core.get("generator_ids")
    if not isinstance(generator_ids, list) or not generator_ids:
        fail("live ledger minimal core has no generator_ids")
    if counted_record_ids != set(generator_ids):
        fail(
            "COUNTED architecture records must exactly match the frozen live-ledger "
            f"minimal core: records={sorted(counted_record_ids)}, ledger={sorted(generator_ids)}"
        )


def validate_static(
    repo: Path,
    config: dict,
    ledger: dict,
    *,
    require_architecture_records: bool = True,
    evidence_ref: str | None = None,
) -> dict[str, list[re.Pattern[str]]]:
    if config.get("schema_version") != 1:
        fail("research-track governance schema_version must be 1")
    governance_model = config.get("governance_model", "legacy_v1")
    if governance_model not in {"legacy_v1", "risk_tiered_v2"}:
        fail("governance_model must be legacy_v1 or risk_tiered_v2")
    if governance_model == "risk_tiered_v2":
        tiers = config.get("risk_tiers")
        if not isinstance(tiers, dict) or set(tiers) != {"L0", "L1", "L2", "L3"}:
            fail("risk_tiered_v2 must define exactly L0/L1/L2/L3 risk tiers")
        expected_tier_names = {
            "L0": "read_only_analysis",
            "L1": "additive_uncounted_research",
            "L2": "shared_interface_or_existing_uncounted_surface",
            "L3": "frozen_counted_or_minimal_core_change",
        }
        for tier, name in expected_tier_names.items():
            record = tiers.get(tier)
            if not isinstance(record, dict) or record.get("name") != name:
                fail(f"risk tier {tier} must retain canonical name {name}")
        if tiers["L1"].get("policy") != "new_files_only_inside_owned_namespace":
            fail("L1 must remain additive/new-files-only inside an owned namespace")
        if tiers["L2"].get("policy") != "explicit_governance_exception":
            fail("L2 must require an explicit governance exception")
        if tiers["L3"].get("policy") != "mission_contract_promotion_and_refinalization":
            fail("L3 must retain the Mission Contract promotion/re-finalization lifecycle")
    if config.get("authority_issue") != 146:
        fail("research-track governance authority_issue must remain #146")
    if config.get("counted_core_policy") != "must_match_live_ledger_minimal_core":
        fail("research-track governance must inherit the live ledger minimal core")
    expected_max_tracks = 4 if governance_model == "risk_tiered_v2" else 2
    if config.get("max_active_mutating_tracks") != expected_max_tracks:
        fail(
            "post-FINAL governance permits exactly "
            f"{expected_max_tracks} mutating tracks under {governance_model}"
        )
    if config.get("main_only_cross_track_dependencies") is not True:
        fail("cross-track dependencies must remain main-only")
    if config.get("cross_track_integration_gate") not in {"closed", "open"}:
        fail("cross_track_integration_gate must be closed or open")
    omega_gate = config.get("objecthood_omega_gate")
    if omega_gate is None and not require_architecture_records:
        # Governance PRs are authorized by the already-merged base policy.
        # A pre-Track-O base is therefore a legitimate enforcement baseline.
        omega_gate = "closed"
    elif omega_gate not in {"closed", "open"}:
        fail("objecthood_omega_gate must be closed or open")

    raw_history = config.get("objecthood_completion_history")
    if raw_history is None:
        if require_architecture_records:
            fail("current Objecthood governance requires objecthood_completion_history")
        objecthood_history: list[dict] = []
    else:
        if not isinstance(raw_history, list) or not raw_history:
            fail("objecthood_completion_history must be a nonempty list")
        objecthood_history = []
        seen_issues: set[int] = set()
        seen_gates: set[str] = set()
        for index, checkpoint in enumerate(raw_history):
            context = f"objecthood_completion_history[{index}]"
            if not isinstance(checkpoint, dict):
                fail(f"{context} must be an object")
            if checkpoint.get("tracker_state") != "closed":
                fail(f"{context} must record tracker_state=closed")
            completed_issue = checkpoint.get("tracker_issue")
            if type(completed_issue) is not int or completed_issue <= 0:
                fail(f"{context} needs a positive tracker_issue")
            if completed_issue in seen_issues:
                fail("objecthood completion history cannot reuse a tracker_issue")
            seen_issues.add(completed_issue)
            completed_gate = checkpoint.get("completed_gate")
            if not isinstance(completed_gate, str) or not completed_gate.strip():
                fail(f"{context} needs a nonempty completed_gate")
            if completed_gate != completed_gate.strip():
                fail(f"{context}.completed_gate must not have leading/trailing whitespace")
            if completed_gate in seen_gates:
                fail("objecthood completion history cannot reuse a completed_gate")
            seen_gates.add(completed_gate)
            if checkpoint.get("gate_state") != "closed":
                fail(f"{context} must record gate_state=closed")
            for field in ("reviewed_head", "merge_commit"):
                value = checkpoint.get(field)
                if not isinstance(value, str) or re.fullmatch(r"[0-9a-f]{40}", value) is None:
                    fail(f"{context} needs a 40-hex {field}")
            objecthood_history.append(checkpoint)
    governed_path_prefixes = string_list(
        config.get("governed_path_prefixes"), "governed_path_prefixes"
    )
    governed_exact_paths = string_list(
        config.get("governed_exact_paths"), "governed_exact_paths"
    )

    for field in (
        "mission_contract",
        "operations_manual",
        "post_final_governance",
        "ledger",
    ):
        value = config.get(field)
        if not isinstance(value, str) or not value:
            fail(f"research-track governance needs nonempty {field}")
        require_referenced_file(
            repo,
            value,
            "research-track governance",
            ref=evidence_ref,
        )

    tracks = config.get("tracks")
    gate = config.get("cross_track_integration_gate")
    expected_tracks = {"S", "H"}
    if governance_model == "risk_tiered_v2":
        if gate != "open" or omega_gate != "open":
            fail("risk_tiered_v2 keeps the registered X/O research namespaces statically open")
        expected_tracks.update({"X", "O"})
        if isinstance(tracks, dict) and "TC" in tracks:
            expected_tracks.add("TC")
    else:
        if gate == "open":
            expected_tracks.add("X")
        if omega_gate == "open":
            expected_tracks.add("O")
    if not isinstance(tracks, dict) or set(tracks) != expected_tracks:
        fail(
            "research-track governance must define exactly "
            f"{sorted(expected_tracks)} while the cross-track gate is {gate}"
        )

    compiled: dict[str, list[re.Pattern[str]]] = {}
    for track_id in TRACK_IDS:
        if track_id not in tracks:
            continue
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
        if governance_model == "risk_tiered_v2":
            if track.get("change_policy") != "additive_only_by_default":
                fail(
                    f"Track {track_id} must use additive_only_by_default under risk_tiered_v2"
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
    if governance_model == "legacy_v1" and h.get("initial_gate") != "H0-H3":
        fail("Track H must begin at H0-H3")
    expected_h_stability = (
        "cross_track_only_via_X"
        if gate == "open"
        else "blocked_until_cross_track_integration_gate_opens"
    )
    if h.get("long_run_stability_work") != expected_h_stability:
        fail(
            "Track H long-run stability work must remain routed through the "
            "cross-track gate"
        )

    if gate == "open":
        x = tracks["X"]
        if governance_model == "legacy_v1":
            if x.get("tracker_issue") != 225:
                fail("Track X must be governed by Issue #225")
            if x.get("initial_gate") != "X0-X8":
                fail("Track X must follow the X0-X8 mission sequence")
        if x.get("preferred_branch_prefix") != "compression/cross-track-":
            fail("Track X preferred branch prefix must remain compression/cross-track-")
        if not matches_any("compression/cross-track-parent-semantic", compiled["X"]):
            fail("Track X branch patterns must authorize the governed cross-track prefix")
        if x.get("dependency_rule") != "consume_S_and_H_evidence_from_canonical_main_only":
            fail("Track X must consume S/H evidence from canonical main only")
        if x.get("source_track_reopen_policy") != "forbidden_inside_X":
            fail("Track X must not reopen Track S or Track H inside cross-track work")

    if omega_gate == "open":
        if gate != "open":
            fail("Track O cannot open while Track X integration gate is closed")
        o = tracks["O"]
        if governance_model == "legacy_v1":
            tracker_issue = o.get("tracker_issue")
            stage_plan = o.get("initial_gate")
            if not objecthood_history:
                # Legacy first activation.  This remains accepted when validating
                # an older base policy during the guarded close-transition PR.
                if tracker_issue != 230:
                    fail("initial Track O activation must be governed by Issue #230")
                if stage_plan != "O0-O8":
                    fail("initial Track O activation must follow the O0-O8 mission sequence")
            else:
                if type(tracker_issue) is not int or tracker_issue <= 0:
                    fail("reopened Track O requires a positive fresh tracker_issue")
                completed_issues = {
                    checkpoint["tracker_issue"] for checkpoint in objecthood_history
                }
                if tracker_issue in completed_issues:
                    fail("reopened Track O must use a fresh tracker_issue")
                if not isinstance(stage_plan, str) or not stage_plan.strip():
                    fail("reopened Track O requires a nonempty fresh stage plan")
                if stage_plan != stage_plan.strip():
                    fail("reopened Track O stage plan must not have leading/trailing whitespace")
                completed_gates = {
                    checkpoint["completed_gate"] for checkpoint in objecthood_history
                }
                if stage_plan in completed_gates:
                    fail("reopened Track O must use a fresh stage plan")
        if o.get("preferred_branch_prefix") != "compression/objecthood-":
            fail("Track O preferred branch prefix must remain compression/objecthood-")
        if not matches_any("compression/objecthood-self-repair", compiled["O"]):
            fail("Track O branch patterns must authorize the governed Objecthood prefix")
        if o.get("dependency_rule") != (
            "consume_frozen_core_and_merged_X_evidence_from_canonical_main_only"
        ):
            fail("Track O must consume frozen Core and merged Track-X evidence from canonical main only")
        if o.get("source_track_reopen_policy") != "forbidden_inside_O":
            fail("Track O must not reopen source-track theorem families inside Objecthood work")

    if governance_model == "risk_tiered_v2" and "TC" in tracks:
        tc = tracks["TC"]
        if tc.get("preferred_branch_prefix") != "compression/theory-completion-":
            fail(
                "Track TC preferred branch prefix must remain "
                "compression/theory-completion-"
            )
        if not matches_any(
            "compression/theory-completion-semantic-constitution", compiled["TC"]
        ):
            fail(
                "Track TC branch patterns must authorize the governed "
                "Theory Completion prefix"
            )
        if tc.get("program_tracker_issue") != 265:
            fail("Track TC must remain anchored to Theory Completion program Issue #265")
        if tc.get("dependency_rule") != (
            "consume_S_H_X_O_and_frozen_core_evidence_from_canonical_main_only"
        ):
            fail(
                "Track TC must consume S/H/X/O and frozen Core evidence from "
                "canonical main only"
            )
        if tc.get("source_track_reopen_policy") != "forbidden_inside_TC":
            fail("Track TC must not reopen S/H/X/O source theorem families")

        for tc_prefix in TC_ALLOWED_PATH_PREFIXES:
            if not any(
                tc_prefix.startswith(governed_prefix)
                for governed_prefix in governed_path_prefixes
            ):
                fail(
                    "registered Track TC requires every owned namespace to remain "
                    "inside the top-level governed path surface"
                )
        for tc_exact in TC_ALLOWED_EXACT_PATHS:
            if (
                tc_exact not in governed_exact_paths
                and not any(
                    tc_exact.startswith(governed_prefix)
                    for governed_prefix in governed_path_prefixes
                )
            ):
                fail(
                    "registered Track TC requires every owned exact path to remain "
                    "inside the top-level governed path surface"
                )
        if set(string_list(
            tc.get("allowed_path_prefixes"), "Track TC allowed_path_prefixes"
        )) != TC_ALLOWED_PATH_PREFIXES:
            fail("Track TC allowed_path_prefixes must match the pre-authorized TC scope")
        if set(string_list(
            tc.get("allowed_exact_paths"), "Track TC allowed_exact_paths"
        )) != TC_ALLOWED_EXACT_PATHS:
            fail("Track TC allowed_exact_paths must match the pre-authorized TC scope")
        if set(string_list(
            tc.get("forbidden_path_prefixes"), "Track TC forbidden_path_prefixes"
        )) != TC_FORBIDDEN_PATH_PREFIXES:
            fail("Track TC forbidden_path_prefixes must match the pre-authorized protection set")
        if set(string_list(
            tc.get("forbidden_exact_paths"), "Track TC forbidden_exact_paths"
        )) != TC_FORBIDDEN_EXACT_PATHS:
            fail("Track TC forbidden_exact_paths must match the pre-authorized protection set")

        structural = tracks["S"]
        structural_forbidden_prefixes = set(string_list(
            structural.get("forbidden_path_prefixes"),
            "Track S forbidden_path_prefixes",
        ))
        structural_forbidden_exact = set(string_list(
            structural.get("forbidden_exact_paths"),
            "Track S forbidden_exact_paths",
        ))
        if not TC_REQUIRED_S_FORBIDDEN_PREFIXES.issubset(
            structural_forbidden_prefixes
        ):
            fail(
                "registered Track TC requires reciprocal Track S namespace "
                "exclusions"
            )
        if not TC_REQUIRED_S_FORBIDDEN_EXACT_PATHS.issubset(
            structural_forbidden_exact
        ):
            fail(
                "registered Track TC requires reciprocal Track S public-root "
                "exclusion"
            )

        governance_exact = set(
            string_list(
                governance.get("allowed_exact_paths"),
                "governance.allowed_exact_paths",
            )
        )
        governance_prefixes = set(
            string_list(
                governance.get("allowed_path_prefixes"),
                "governance.allowed_path_prefixes",
                allow_empty=True,
            )
        )
        for path in governance_exact:
            if path in TC_ALLOWED_EXACT_PATHS or any(
                path.startswith(prefix) for prefix in TC_ALLOWED_PATH_PREFIXES
            ):
                fail(
                    "registered Track TC must retire governance exact-path "
                    "access overlapping the Theory Completion scope"
                )
        for governance_prefix in governance_prefixes:
            if any(
                governance_prefix.startswith(tc_prefix)
                or tc_prefix.startswith(governance_prefix)
                for tc_prefix in TC_ALLOWED_PATH_PREFIXES
            ) or any(
                exact.startswith(governance_prefix)
                for exact in TC_ALLOWED_EXACT_PATHS
            ):
                fail(
                    "registered Track TC must not leave a governance prefix "
                    "semantically overlapping the Theory Completion scope"
                )

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

    if require_architecture_records:
        validate_architecture_records(
            repo, config, ledger, evidence_ref=evidence_ref
        )

    return compiled


def validate_objecthood_completion_history_transition(
    baseline_config: dict, candidate_config: dict
) -> None:
    """Keep completed Track-O governance evidence append-only.

    A completion record is an authorization boundary: once it exists, a later
    governance PR may append a newly completed Track-O cycle but may not delete,
    reorder, or rewrite any prior completed tracker/stage entry.
    """

    baseline = baseline_config.get("objecthood_completion_history")
    candidate = candidate_config.get("objecthood_completion_history")

    if candidate_config.get("governance_model") == "risk_tiered_v2":
        if baseline is not None and candidate != baseline:
            fail(
                "risk_tiered_v2 freezes legacy Objecthood completion history; "
                "ordinary research closes in its tracker/merged PR instead"
            )
        return

    # Historical bases before the first Track-O closure have no history.  The
    # first close-transition may establish exactly one record corresponding to
    # the active base tracker/stage.
    if baseline is None:
        if candidate is None:
            return
        if not isinstance(candidate, list) or len(candidate) != 1:
            fail("first Objecthood closure must establish exactly one completion record")
        base_o = baseline_config.get("tracks", {}).get("O")
        if not isinstance(base_o, dict):
            fail("first Objecthood closure requires an active baseline Track O")
        first = candidate[0]
        if (
            first.get("tracker_issue") != base_o.get("tracker_issue")
            or first.get("completed_gate") != base_o.get("initial_gate")
        ):
            fail("first Objecthood completion record must match the active baseline tracker/stage")
        if candidate_config.get("objecthood_omega_gate") != "closed":
            fail("first Objecthood completion record must close the mutation gate")
        return

    if not isinstance(baseline, list) or not baseline:
        fail("baseline objecthood completion history is malformed")
    if not isinstance(candidate, list) or not candidate:
        fail("Objecthood completion history is append-only and cannot be deleted")
    if len(candidate) < len(baseline) or candidate[: len(baseline)] != baseline:
        fail("Objecthood completion history is append-only and prior records are immutable")
    if len(candidate) > len(baseline) + 1:
        fail("Objecthood governance may append at most one completion record per PR")

    baseline_gate = baseline_config.get("objecthood_omega_gate")
    candidate_gate = candidate_config.get("objecthood_omega_gate")
    if baseline_gate == "open" and candidate_gate == "open":
        base_o = baseline_config.get("tracks", {}).get("O")
        candidate_o = candidate_config.get("tracks", {}).get("O")
        if not isinstance(base_o, dict) or not isinstance(candidate_o, dict):
            fail("an open Objecthood cycle requires Track O on both baseline and candidate")
        if candidate_o.get("tracker_issue") != base_o.get("tracker_issue"):
            fail("an active Track O cycle must keep its tracker_issue until closure")
        if candidate_o.get("initial_gate") != base_o.get("initial_gate"):
            fail("an active Track O cycle must keep its stage plan until closure")
    if baseline_gate == "open" and candidate_gate == "closed":
        if len(candidate) != len(baseline) + 1:
            fail(
                "closing an active Track O cycle must append exactly one "
                "completion record"
            )

    if len(candidate) == len(baseline) + 1:
        base_o = baseline_config.get("tracks", {}).get("O")
        if baseline_gate != "open" or not isinstance(base_o, dict):
            fail("new Objecthood completion record requires an active baseline Track O")
        added = candidate[-1]
        if (
            added.get("tracker_issue") != base_o.get("tracker_issue")
            or added.get("completed_gate") != base_o.get("initial_gate")
        ):
            fail("new Objecthood completion record must match the active baseline tracker/stage")
        if candidate_gate != "closed":
            fail("appending an Objecthood completion record must close the mutation gate")


def validate_tc_registration_transition(
    repo: Path,
    baseline_config: dict,
    candidate_config: dict,
    candidate_ref: str,
) -> None:
    """Make first TC registration atomic and later TC registration persistent."""

    baseline_tracks = baseline_config.get("tracks")
    candidate_tracks = candidate_config.get("tracks")
    baseline_has_tc = isinstance(baseline_tracks, dict) and "TC" in baseline_tracks
    candidate_has_tc = isinstance(candidate_tracks, dict) and "TC" in candidate_tracks
    if baseline_has_tc and not candidate_has_tc:
        fail(
            "registered Track TC is persistent and cannot be silently removed "
            "by an ordinary governance transition"
        )
    if candidate_has_tc:
        context = (
            "first Track TC registration"
            if not baseline_has_tc
            else "registered Track TC persistence"
        )
        for path in sorted(TC_BOOTSTRAP_DOCS | {TC_PUBLIC_ROOT}):
            require_file_at_ref(repo, candidate_ref, path, context)

        compression_blob = git_blob_bytes(repo, candidate_ref, COMPRESSION_PUBLIC_ROOT)
        if b"\r" in compression_blob or b"\x00" in compression_blob:
            fail(
                "first Track TC registration requires a valid Compression.lean "
                "public-root import surface"
            )
        try:
            compression_text = compression_blob.decode("utf-8")
        except UnicodeDecodeError:
            fail("first Track TC registration requires UTF-8 Compression.lean")
        semantic_import_lines = [
            line
            for line in compression_text.split("\n")
            if line_imports_module(line, TC_MODULE)
        ]
        if len(semantic_import_lines) != 1:
            fail(
                "registered Track TC requires exactly one semantic "
                "TheoryCompletion public-root import"
            )
        if semantic_import_lines[0] != TC_PUBLIC_IMPORT:
            fail(
                "registered Track TC requires the TheoryCompletion public-root "
                "import in canonical format"
            )


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
        for track_id in TRACK_IDS
        if track_id in compiled
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

    if (
        baseline_ref
        and track.get("change_policy") == "additive_only_by_default"
    ):
        exact_exceptions = set(track.get("allowed_exact_paths", []))
        for path in paths:
            if path in exact_exceptions:
                continue
            if git_path_exists(repo, baseline_ref, path):
                fail(
                    f"Track {track_id} L1 additive research may not modify or delete "
                    f"existing path {path}; use an explicit L2/L3 governance change "
                    "for shared or protected surfaces"
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
    elif track_id == "X":
        allowed_exact = set(track.get("allowed_exact_paths", []))
        allowed_prefixes = tuple(track.get("allowed_path_prefixes", []))
        for path in paths:
            if path in allowed_exact or any(
                path.startswith(prefix) for prefix in allowed_prefixes
            ):
                continue
            fail(
                f"Track X branch {branch!r} modified {path}, outside its "
                "owned CrossTrack namespace"
            )
    elif track_id == "O":
        allowed_exact = set(track.get("allowed_exact_paths", []))
        allowed_prefixes = tuple(track.get("allowed_path_prefixes", []))
        for path in paths:
            if path in allowed_exact or any(
                path.startswith(prefix) for prefix in allowed_prefixes
            ):
                continue
            fail(
                f"Track O branch {branch!r} modified {path}, outside its "
                "owned Objecthood namespace"
            )
    elif track_id == "TC":
        allowed_exact = set(track.get("allowed_exact_paths", []))
        allowed_prefixes = tuple(track.get("allowed_path_prefixes", []))
        for path in paths:
            if path in allowed_exact or any(
                path.startswith(prefix) for prefix in allowed_prefixes
            ):
                continue
            fail(
                f"Track TC branch {branch!r} modified {path}, outside its "
                "owned TheoryCompletion namespace"
            )

    validate_compression_root_import_change(
        repo, baseline_ref, candidate_ref, track_id, paths
    )
    validate_objecthood_root_import_change(
        repo, baseline_ref, candidate_ref, track_id, paths
    )
    validate_owned_track_root_import_change(
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

    # `pull_request_target` intentionally executes this validator from the
    # immutable base checkout.  When a baseline/candidate pair is supplied,
    # policy *authorization* still comes from the base config below, but the
    # candidate registry must be loaded from the candidate Git object rather
    # than from the checked-out base worktree.  Otherwise transition checks
    # such as append-only Objecthood completion history compare base-to-base
    # and silently ignore candidate policy mutations.
    if args.baseline_ref:
        candidate_config = load_json_at_ref(repo, args.candidate_ref, TRACKS_REL)
        if candidate_config is None:
            fail(
                "candidate ref is missing the research-track governance registry: "
                f"{args.candidate_ref}:{TRACKS_REL.as_posix()}"
            )
        config = candidate_config

    compiled = validate_static(
        repo,
        config,
        ledger,
        evidence_ref=args.candidate_ref if args.baseline_ref else None,
    )
    enforcement_config = config
    enforcement_compiled = compiled
    if args.baseline_ref:
        baseline_config = load_json_at_ref(repo, args.baseline_ref, TRACKS_REL)
        if baseline_config is not None:
            enforcement_config = baseline_config
            enforcement_compiled = validate_static(
                repo,
                baseline_config,
                ledger,
                require_architecture_records=False,
            )
            validate_objecthood_completion_history_transition(
                baseline_config, config
            )
            validate_tc_registration_transition(
                repo,
                baseline_config,
                config,
                args.candidate_ref,
            )

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

    # Every registered research/governance lane is mutating.  Derive this from
    # the compiled policy rather than enumerating track IDs so newly activated
    # tracks cannot silently bypass the canonical-repository fork guard.
    classified_mutating = any(
        matches_any(branch, patterns)
        for patterns in enforcement_compiled.values()
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
        validate_live_concurrency(
            branch_names,
            enforcement_compiled,
            enforcement_config["max_active_mutating_tracks"],
        )
    elif args.verify_live_state:
        assert repo_slug is not None and token is not None
        validate_live_concurrency(
            github_branch_names(repo_slug, token),
            enforcement_compiled,
            enforcement_config["max_active_mutating_tracks"],
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
