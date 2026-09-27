#!/usr/bin/env python3
"""Regression tests for compression-governance completion gates.

The tests mutate only the checked-out ledger, invoke the production validator,
and restore the original bytes in a finally block. CI workspaces are ephemeral,
but restoration also keeps local runs safe.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path


def validator(repo: Path) -> list[str]:
    return [
        sys.executable,
        str(repo / "formalization/ueot-core/scripts/validate_compression.py"),
        "--repo-root",
        str(repo),
    ]


def expect_rejected(
    repo: Path,
    ledger_path: Path,
    original: str,
    name: str,
    mutate,
    expected: str,
) -> None:
    data = json.loads(original)
    mutate(data)
    ledger_path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    completed = subprocess.run(
        validator(repo),
        text=True,
        capture_output=True,
        check=False,
    )
    output = completed.stdout + completed.stderr
    if completed.returncode == 0 or expected not in output:
        raise AssertionError(
            f"{name}: validator did not reject as expected\n{output}"
        )
    print(f"{name}: PASS")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", default=".")
    args = parser.parse_args()

    repo = Path(args.repo_root).resolve()
    ledger_path = (
        repo
        / "formalization/ueot-core/docs/compression/COMPRESSION_LEDGER.yaml"
    )
    original = ledger_path.read_text(encoding="utf-8")

    try:
        expect_rejected(
            repo,
            ledger_path,
            original,
            "premature-finalization",
            lambda d: d["mission_contract"].update(
                state="ready_for_finalization"
            ),
            "mission finalization gate failed",
        )

        expect_rejected(
            repo,
            ledger_path,
            original,
            "forged-disposition-count",
            lambda d: d["coverage"].update(
                final_disposition_pids=1, unresolved_pids=105
            ),
            "final_disposition_pids disagrees",
        )
        def fake_generated(data: dict) -> None:
            data["final_dispositions"] = {
                "P-API-01": {
                    "status": "generated",
                    "generator_ids": ["M-TC-01"],
                }
            }
            data["coverage"].update(
                final_disposition_pids=1,
                generated_pids=1,
                unresolved_pids=105,
            )

        expect_rejected(
            repo,
            ledger_path,
            original,
            "uncounted-generated-mapping",
            fake_generated,
            "generated disposition needs a counted exact mapping",
        )

        def fake_frozen_core(data: dict) -> None:
            data["minimal_core"].update(
                state="frozen",
                generator_ids=["M-TC-01"],
                ablation_state="complete",
                minimality_claim=(
                    "nonredundant_under_declared_derivation_system"
                ),
            )

        expect_rejected(
            repo,
            ledger_path,
            original,
            "uncounted-frozen-core",
            fake_frozen_core,
            "final minimal-core generator must be counted",
        )
    finally:
        ledger_path.write_text(original, encoding="utf-8")

    completed = subprocess.run(
        validator(repo),
        text=True,
        capture_output=True,
        check=False,
    )
    if completed.returncode != 0:
        raise AssertionError(
            "restored ledger failed positive validation\n"
            + completed.stdout
            + completed.stderr
        )
    print("restored-positive-validation: PASS")


if __name__ == "__main__":
    main()
