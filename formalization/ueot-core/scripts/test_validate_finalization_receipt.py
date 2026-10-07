#!/usr/bin/env python3
"""Regression tests for durable FINAL Actions-receipt governance."""

from __future__ import annotations

import contextlib
import copy
import importlib.util
import io
import json
import os
import subprocess
import tempfile
from types import SimpleNamespace
from pathlib import Path


def load_validator(repo: Path):
    path = repo / "formalization/ueot-core/scripts/validate_compression.py"
    spec = importlib.util.spec_from_file_location("ueot_validate_compression", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load validate_compression.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def git(repo: Path, *args: str) -> str:
    return subprocess.check_output(
        ["git", *args], cwd=repo, text=True, stderr=subprocess.STDOUT
    ).strip()


def expect_rejected(name: str, fn, expected: str) -> None:
    stderr = io.StringIO()
    try:
        with contextlib.redirect_stderr(stderr):
            fn()
    except SystemExit as exc:
        output = stderr.getvalue()
        if exc.code == 0 or expected not in output:
            raise AssertionError(f"{name}: wrong rejection\n{output}") from exc
        print(f"{name}: PASS")
        return
    raise AssertionError(f"{name}: expected rejection")


def receipt_dict(module, evidence: dict, runs: dict[str, dict]) -> dict:
    event = module.finalization_event_payload(evidence, runs)
    return {
        "schema_version": module.FINALIZATION_RECEIPT_SCHEMA_VERSION,
        "repository": module.REPO_FULL_NAME,
        "capture_mode": "retrospective_live_reverification",
        "source_status": "ONLINE_VERIFIED_AT_CAPTURE",
        "captured_at": "2026-10-08T00:00:00Z",
        "event": event,
        "event_sha256": module.finalization_event_digest(event),
        "note": "regression fixture",
    }


def run_data(run_id: int, name: str, candidate: str) -> dict:
    return {
        "id": run_id,
        "name": name,
        "event": "push",
        "status": "completed",
        "conclusion": "success",
        "head_sha": candidate,
        "run_attempt": 1,
        "created_at": "2026-09-29T13:55:19Z",
        "updated_at": "2026-09-29T14:03:51Z",
        "html_url": f"https://example.invalid/actions/runs/{run_id}",
    }


def pure_receipt_tests(module) -> None:
    candidate = "a" * 40
    evidence = {
        "candidate_main_sha": candidate,
        "core_lean_run": 101,
        "compression_guard_run": 202,
        "closure_pr": 303,
    }
    runs = {
        "core_lean_run": run_data(101, "UEOT Core Lean", candidate),
        "compression_guard_run": run_data(
            202, "UEOT Core Compression Guard", candidate
        ),
    }
    receipt = receipt_dict(module, evidence, runs)
    module.validate_finalization_receipt_data(receipt, evidence)
    print("valid-receipt-data: PASS")

    fake_run = copy.deepcopy(receipt)
    fake_run["event"]["core_lean_run"]["id"] = 999
    fake_run["event_sha256"] = module.finalization_event_digest(fake_run["event"])
    expect_rejected(
        "fake-run-id",
        lambda: module.validate_finalization_receipt_data(fake_run, evidence),
        "finalization evidence run 101",
    )

    wrong_sha = copy.deepcopy(receipt)
    wrong_sha["event"]["candidate_main_sha"] = "b" * 40
    wrong_sha["event_sha256"] = module.finalization_event_digest(wrong_sha["event"])
    expect_rejected(
        "wrong-candidate-sha",
        lambda: module.validate_finalization_receipt_data(wrong_sha, evidence),
        "candidate_main_sha mismatch",
    )

    wrong_pr = copy.deepcopy(receipt)
    wrong_pr["event"]["closure_pr"] = 304
    wrong_pr["event_sha256"] = module.finalization_event_digest(wrong_pr["event"])
    expect_rejected(
        "mismatched-closure-pr",
        lambda: module.validate_finalization_receipt_data(wrong_pr, evidence),
        "closure_pr mismatch",
    )

    tampered = copy.deepcopy(receipt)
    tampered["event"]["compression_guard_run"]["status"] = "queued"
    expect_rejected(
        "tampered-receipt-digest",
        lambda: module.validate_finalization_receipt_data(tampered, evidence),
        "event digest mismatch",
    )


def transport_retry_tests(module) -> None:
    original_run = module.subprocess.run
    original_sleep = module.time.sleep
    calls = {"count": 0}
    responses = [
        SimpleNamespace(
            returncode=1,
            stdout="",
            stderr='Get "https://api.github.com/example": net/http: TLS handshake timeout',
        ),
        SimpleNamespace(
            returncode=1,
            stdout="",
            stderr='Get "https://api.github.com/example": net/http: TLS handshake timeout',
        ),
        SimpleNamespace(returncode=0, stdout='{"ok": true}', stderr=""),
    ]

    def fake_run(*_args, **_kwargs):
        calls["count"] += 1
        return responses.pop(0)

    try:
        module.subprocess.run = fake_run
        module.time.sleep = lambda _seconds: None
        result = module.gh_api_json(Path("."), "example")
        if result != {"ok": True} or calls["count"] != 3:
            raise AssertionError("transport-retry-success: retry contract mismatch")
        print("transport-retry-success: PASS")

        calls["count"] = 0

        def fake_404(*_args, **_kwargs):
            calls["count"] += 1
            return SimpleNamespace(
                returncode=1,
                stdout='{"message":"Not Found","status":"404"}',
                stderr="gh: Not Found (HTTP 404)",
            )

        module.subprocess.run = fake_404
        try:
            module.gh_api_json(Path("."), "missing")
        except module.GitHubReferenceError as exc:
            if exc.status != 404 or calls["count"] != 1:
                raise AssertionError("explicit-404-no-retry: wrong status/retry count") from exc
            print("explicit-404-no-retry: PASS")
        else:
            raise AssertionError("explicit-404-no-retry: expected failure")
    finally:
        module.subprocess.run = original_run
        module.time.sleep = original_sleep


def commit_file(repo: Path, rel: str, content: str, message: str) -> str:
    path = repo / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")
    git(repo, "add", rel)
    git(repo, "commit", "-m", message)
    return git(repo, "rev-parse", "HEAD")


def fallback_tests(module) -> None:
    inherited_validation_env = {
        key: os.environ.pop(key, None)
        for key in ("COMPRESSION_VALIDATION_SHA", "GITHUB_SHA")
    }
    try:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            git(repo, "init", "-b", "main")
            git(repo, "config", "user.name", "UEOT Receipt Test")
            git(repo, "config", "user.email", "receipt-test@example.invalid")

            candidate = commit_file(repo, "seed.txt", "candidate\n", "candidate main")
            evidence = {
                "candidate_main_sha": candidate,
                "core_lean_run": 101,
                "compression_guard_run": 202,
                "closure_pr": 303,
            }
            runs = {
                "core_lean_run": run_data(101, "UEOT Core Lean", candidate),
                "compression_guard_run": run_data(
                    202, "UEOT Core Compression Guard", candidate
                ),
            }

            git(repo, "switch", "-c", "closure")
            closure_head = commit_file(repo, "closure.txt", "closure\n", "closure head")
            git(repo, "switch", "main")
            git(repo, "merge", "--no-ff", "closure", "-m", "merge closure")
            closure_merge = git(repo, "rev-parse", "HEAD")
            missing_receipt_baseline = closure_merge

            receipt_path = module.write_finalization_receipt(
                repo, evidence, runs, "retrospective_live_reverification"
            )
            git(repo, "add", str(receipt_path.relative_to(repo)))
            git(repo, "commit", "-m", "archive finalization receipt")
            baseline = git(repo, "rev-parse", "HEAD")
            git(repo, "update-ref", "refs/remotes/origin/main", baseline)
            commit_file(repo, "later.txt", "later\n", "later unrelated change")

            pr = {
                "number": 303,
                "state": "closed",
                "merged_at": "2026-09-29T14:37:59Z",
                "base": {"ref": "main", "sha": candidate},
                "head": {"ref": "closure", "sha": closure_head},
                "merge_commit_sha": closure_merge,
            }

            original_fetcher = module.gh_api_json

            def retained_run_404(_repo: Path, endpoint: str) -> dict:
                if "/actions/runs/" in endpoint:
                    raise module.GitHubReferenceError("Not Found (HTTP 404)", status=404)
                if endpoint.endswith("/pulls/303"):
                    return pr
                raise AssertionError(f"unexpected endpoint {endpoint}")

            def transient_network_failure(_repo: Path, endpoint: str) -> dict:
                if "/actions/runs/" in endpoint:
                    raise module.GitHubReferenceError("TLS handshake timeout")
                if endpoint.endswith("/pulls/303"):
                    return pr
                raise AssertionError(f"unexpected endpoint {endpoint}")

            try:
                module.gh_api_json = retained_run_404
                module.verify_finalization_references(
                    repo, evidence, baseline_ref=baseline
                )
                print("retained-run-404-with-baseline-receipt: PASS")

                expect_rejected(
                    "deleted-run-without-baseline-receipt",
                    lambda: module.verify_finalization_references(
                        repo, evidence, baseline_ref=missing_receipt_baseline
                    ),
                    "no immutable baseline finalization receipt exists",
                )

                module.gh_api_json = transient_network_failure
                expect_rejected(
                    "network-timeout-does-not-fallback",
                    lambda: module.verify_finalization_references(
                        repo, evidence, baseline_ref=baseline
                    ),
                    "TLS handshake timeout",
                )

                module.gh_api_json = retained_run_404
                original_bytes = receipt_path.read_bytes()
                receipt_path.write_text(
                    json.dumps({"tampered": True}) + "\n", encoding="utf-8"
                )
                expect_rejected(
                    "baseline-receipt-candidate-tamper",
                    lambda: module.verify_finalization_references(
                        repo, evidence, baseline_ref=baseline
                    ),
                    "immutable baseline finalization receipt was modified",
                )
                receipt_path.write_bytes(original_bytes)
            finally:
                module.gh_api_json = original_fetcher
    finally:
        for key, value in inherited_validation_env.items():
            if value is not None:
                os.environ[key] = value


def main() -> None:
    repo = Path(__file__).resolve().parents[3]
    module = load_validator(repo)
    pure_receipt_tests(module)
    transport_retry_tests(module)
    fallback_tests(module)
    print("finalization-receipt-regressions: PASS")


if __name__ == "__main__":
    main()
