#!/usr/bin/env python3
"""Small stdlib regression tests for persistent-agent state validation."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from validate_task_state import validate

SHA = "a" * 40


def valid_state() -> dict:
    return {
        "schema_version": 2,
        "task_id": "issue-7",
        "issue": 7,
        "objective": "test objective",
        "status": "WAITING_CI",
        "iteration": 1,
        "max_iterations": 3,
        "branch": "ops/test",
        "base_sha": SHA,
        "checkpoint_sha": SHA,
        "open_pr": 8,
        "required_checks": ["validate-state"],
        "latest_ci": {"sha": SHA, "status": "success", "run_url": None},
        "last_event": {"key": None, "type": None, "sha": None, "at": None},
        "retries": {
            "same_failure_count": 0,
            "consecutive_ci_failures": 0,
            "max_same_failure": 3,
            "max_consecutive_ci_failures": 5,
            "failure_fingerprint": None,
        },
        "completed": [],
        "current_problem": None,
        "next_action": "review",
        "guards": {
            "merge_authority": "ai-autonomous",
            "builder_may_self_approve": False,
            "normal_integration_requires_pr": True,
            "direct_main_write_allowed": True,
        },
        "updated_at": "2026-09-17T00:00:00Z",
    }


class ValidatorTests(unittest.TestCase):
    def write_state(self, data: dict) -> Path:
        root = Path(self.temp.name)
        path = root / data.get("task_id", "issue-7") / "STATE.json"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(data), encoding="utf-8")
        return path

    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()

    def tearDown(self) -> None:
        self.temp.cleanup()

    def test_valid_state(self) -> None:
        self.assertEqual(validate(self.write_state(valid_state())), [])

    def test_normal_active_main_is_rejected(self) -> None:
        data = valid_state()
        data["branch"] = "main"
        errors = validate(self.write_state(data))
        self.assertTrue(any("normal active task may not use main" in error for error in errors))

    def test_builder_self_approval_is_rejected(self) -> None:
        data = valid_state()
        data["guards"]["builder_may_self_approve"] = True
        errors = validate(self.write_state(data))
        self.assertTrue(any("AI-autonomous merge authority" in error for error in errors))

    def test_duplicate_required_checks_are_rejected(self) -> None:
        data = valid_state()
        data["required_checks"] = ["validate-state", "validate-state"]
        errors = validate(self.write_state(data))
        self.assertTrue(any("must be unique" in error for error in errors))

    def test_retry_budget_requires_blocked(self) -> None:
        data = valid_state()
        data["retries"]["same_failure_count"] = 4
        errors = validate(self.write_state(data))
        self.assertTrue(any("retry budget exceeded" in error for error in errors))


if __name__ == "__main__":
    unittest.main()
