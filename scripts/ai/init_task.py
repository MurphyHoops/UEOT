#!/usr/bin/env python3
"""Scaffold a persistent UEOT agent task from an already-created GitHub Issue."""

from __future__ import annotations

import argparse
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path

from validate_task_state import validate

SHA_RE = re.compile(r"^[0-9a-f]{40}$")


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--issue", type=int, required=True)
    parser.add_argument("--objective", required=True)
    parser.add_argument("--branch", required=True)
    parser.add_argument("--base-sha", required=True)
    parser.add_argument("--required-check", action="append", dest="required_checks", required=True)
    parser.add_argument("--max-iterations", type=int, default=30)
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()

    if args.issue < 1:
        parser.error("--issue must be positive")
    if not SHA_RE.fullmatch(args.base_sha):
        parser.error("--base-sha must be a 40-character lowercase git SHA")
    if args.branch == "main" or not args.branch.strip():
        parser.error("--branch must be a non-main work branch for the normal audited path")
    if not 1 <= args.max_iterations <= 100:
        parser.error("--max-iterations must be in [1,100]")

    checks = list(dict.fromkeys(x.strip() for x in args.required_checks if x.strip()))
    if not checks:
        parser.error("at least one non-empty --required-check is required")

    task_id = f"issue-{args.issue}"
    task_dir = Path(".ai/tasks") / task_id
    state_path = task_dir / "STATE.json"
    goal_path = task_dir / "GOAL.md"

    if task_dir.exists() and not args.force:
        print(f"Refusing to overwrite existing {task_dir}; use --force only after audit.", file=sys.stderr)
        return 2

    task_dir.mkdir(parents=True, exist_ok=True)
    now = utc_now()
    state = {
        "schema_version": 2,
        "task_id": task_id,
        "issue": args.issue,
        "objective": args.objective.strip(),
        "status": "PLANNING",
        "iteration": 0,
        "max_iterations": args.max_iterations,
        "branch": args.branch.strip(),
        "base_sha": args.base_sha,
        "checkpoint_sha": args.base_sha,
        "open_pr": None,
        "required_checks": checks,
        "latest_ci": {"sha": None, "status": "unknown", "run_url": None},
        "last_event": {"key": None, "type": None, "sha": None, "at": None},
        "retries": {
            "same_failure_count": 0,
            "consecutive_ci_failures": 0,
            "max_same_failure": 3,
            "max_consecutive_ci_failures": 5,
            "failure_fingerprint": None,
        },
        "completed": ["Persistent task state scaffolded from durable GitHub Issue"],
        "current_problem": None,
        "next_action": "Write exact GOAL.md success criteria, reconcile current GitHub state, and plan the first bounded implementation iteration.",
        "guards": {
            "merge_authority": "ai-autonomous",
            "builder_may_self_approve": False,
            "normal_integration_requires_pr": True,
            "direct_main_write_allowed": True,
        },
        "updated_at": now,
    }

    state_path.write_text(json.dumps(state, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    goal_path.write_text(
        f"# Issue #{args.issue} — {args.objective.strip()}\n\n"
        "## Goal\n\nDescribe the durable objective here.\n\n"
        "## Success criteria\n\n1. Replace this placeholder with externally checkable criteria.\n\n"
        "## Non-goals / frozen constraints\n\n- Record constraints that must not be silently weakened.\n",
        encoding="utf-8",
    )

    errors = validate(state_path)
    if errors:
        for error in errors:
            print(error, file=sys.stderr)
        return 1

    print(f"Created {state_path} and {goal_path}")
    print("Next: edit GOAL.md, commit both files on the existing work branch, then open/update one PR.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
