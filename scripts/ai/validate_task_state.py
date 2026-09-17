#!/usr/bin/env python3
"""Validate UEOT persistent-agent STATE.json files using only Python stdlib."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

STATES = {
    "NEW", "PLANNING", "IMPLEMENTING", "WAITING_CI", "CI_FAILED",
    "REVIEWING", "CHANGES_REQUESTED", "READY_TO_MERGE", "BLOCKED", "DONE",
}
ACTIVE_STATES = STATES - {"DONE"}
SHA_RE = re.compile(r"^[0-9a-f]{40}$")
TASK_RE = re.compile(r"^issue-([0-9]+)$")
REQUIRED = {
    "schema_version", "task_id", "issue", "objective", "status", "iteration",
    "max_iterations", "branch", "base_sha", "checkpoint_sha", "open_pr",
    "required_checks", "latest_ci", "last_event", "retries", "completed",
    "current_problem", "next_action", "guards", "updated_at",
}


def fail(path: Path, message: str, errors: list[str]) -> None:
    errors.append(f"{path}: {message}")


def is_sha(value: object) -> bool:
    return isinstance(value, str) and bool(SHA_RE.fullmatch(value))


def validate(path: Path) -> list[str]:
    errors: list[str] = []
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except Exception as exc:  # noqa: BLE001
        return [f"{path}: invalid JSON: {exc}"]

    if not isinstance(data, dict):
        return [f"{path}: root must be an object"]

    missing = REQUIRED - data.keys()
    extra = data.keys() - REQUIRED
    if missing:
        fail(path, f"missing keys: {sorted(missing)}", errors)
    if extra:
        fail(path, f"unknown keys: {sorted(extra)}", errors)
    if errors:
        return errors

    if data["schema_version"] != 1:
        fail(path, "schema_version must be 1", errors)

    task_match = TASK_RE.fullmatch(str(data["task_id"]))
    if not task_match:
        fail(path, "task_id must be issue-N", errors)
    elif not isinstance(data["issue"], int) or int(task_match.group(1)) != data["issue"]:
        fail(path, "task_id issue number must equal issue", errors)

    status = data["status"]
    if status not in STATES:
        fail(path, f"invalid status {status!r}", errors)

    iteration = data["iteration"]
    maximum = data["max_iterations"]
    if not isinstance(iteration, int) or iteration < 0:
        fail(path, "iteration must be a non-negative integer", errors)
    if not isinstance(maximum, int) or not (1 <= maximum <= 100):
        fail(path, "max_iterations must be in [1,100]", errors)
    if isinstance(iteration, int) and isinstance(maximum, int) and iteration > maximum:
        fail(path, "iteration exceeds max_iterations", errors)

    branch = data["branch"]
    if not isinstance(branch, str) or not branch.strip():
        fail(path, "branch must be non-empty", errors)
    elif status in ACTIVE_STATES and branch == "main":
        fail(path, "active task may not use main as its work branch", errors)

    for key in ("base_sha", "checkpoint_sha"):
        if not is_sha(data[key]):
            fail(path, f"{key} must be a 40-character lowercase git SHA", errors)

    if data["open_pr"] is not None and (not isinstance(data["open_pr"], int) or data["open_pr"] < 1):
        fail(path, "open_pr must be null or a positive integer", errors)

    checks = data["required_checks"]
    if not isinstance(checks, list) or not checks:
        fail(path, "required_checks must be a non-empty string array", errors)
    elif any(not isinstance(x, str) or not x.strip() for x in checks):
        fail(path, "required_checks entries must be non-empty strings", errors)
    elif len(checks) != len(set(checks)):
        fail(path, "required_checks entries must be unique", errors)

    ci = data["latest_ci"]
    if not isinstance(ci, dict) or set(ci) != {"sha", "status", "run_url"}:
        fail(path, "latest_ci must contain exactly sha,status,run_url", errors)
    else:
        if ci["sha"] is not None and not is_sha(ci["sha"]):
            fail(path, "latest_ci.sha must be null or a git SHA", errors)
        if ci["status"] not in {"unknown", "pending", "success", "failure", "cancelled"}:
            fail(path, "latest_ci.status is invalid", errors)

    event = data["last_event"]
    if not isinstance(event, dict) or set(event) != {"key", "type", "sha", "at"}:
        fail(path, "last_event must contain exactly key,type,sha,at", errors)
    elif event["sha"] is not None and not is_sha(event["sha"]):
        fail(path, "last_event.sha must be null or a git SHA", errors)

    retries = data["retries"]
    retry_keys = {"same_failure_count", "consecutive_ci_failures", "max_same_failure", "max_consecutive_ci_failures", "failure_fingerprint"}
    if not isinstance(retries, dict) or set(retries) != retry_keys:
        fail(path, "retries has invalid shape", errors)
    else:
        for key in ("same_failure_count", "consecutive_ci_failures"):
            if not isinstance(retries[key], int) or retries[key] < 0:
                fail(path, f"retries.{key} must be non-negative", errors)
        for key in ("max_same_failure", "max_consecutive_ci_failures"):
            if not isinstance(retries[key], int) or retries[key] < 1:
                fail(path, f"retries.{key} must be positive", errors)
        if retries["same_failure_count"] > retries["max_same_failure"] and status != "BLOCKED":
            fail(path, "same-failure retry budget exceeded without BLOCKED", errors)
        if retries["consecutive_ci_failures"] > retries["max_consecutive_ci_failures"] and status != "BLOCKED":
            fail(path, "CI failure retry budget exceeded without BLOCKED", errors)

    if not isinstance(data["completed"], list) or any(not isinstance(x, str) for x in data["completed"]):
        fail(path, "completed must be a string array", errors)
    if not isinstance(data["objective"], str) or not data["objective"].strip():
        fail(path, "objective must be non-empty", errors)
    if not isinstance(data["next_action"], str) or not data["next_action"].strip():
        fail(path, "next_action must be non-empty", errors)

    guards = data["guards"]
    if guards != {"human_merge_required": True, "builder_may_self_approve": False}:
        fail(path, "guards must require human merge and forbid Builder self-approval", errors)

    if not isinstance(data["updated_at"], str) or not data["updated_at"].endswith("Z"):
        fail(path, "updated_at must be an explicit UTC timestamp ending in Z", errors)

    expected_dir = path.parent.name
    if expected_dir != data["task_id"]:
        fail(path, f"directory {expected_dir!r} must equal task_id {data['task_id']!r}", errors)

    return errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("paths", nargs="*", type=Path)
    args = parser.parse_args()
    paths = args.paths or sorted(Path(".ai/tasks").glob("*/STATE.json"))
    if not paths:
        print("No .ai task states found", file=sys.stderr)
        return 2

    errors: list[str] = []
    for path in paths:
        errors.extend(validate(path))

    if errors:
        print("Persistent-agent state validation FAILED:", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print(f"Persistent-agent state validation passed for {len(paths)} task(s).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
