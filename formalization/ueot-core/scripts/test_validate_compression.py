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
        "--verify-finalization-refs",
    ]


def normalized_active_fixture(original: str) -> dict:
    """Return a stable pre-counting fixture independent of real mission progress."""
    data = json.loads(original)
    data["mission_contract"]["state"] = "active"
    data["final_dispositions"] = {}
    data["minimal_core"] = {
        "state": "open",
        "generator_ids": [],
        "ablation_state": "not_started",
        "minimality_claim": "not_established",
    }
    data["finalization_evidence"] = {}

    for generator in data["generators"].values():
        if generator.get("state") == "counted_generator":
            generator["state"] = "cross_family_green"
            generator.pop("promotion", None)
        for mapping in generator.get("mappings", {}).values():
            if mapping.get("state") == "counted":
                mapping["state"] = "lean_rederived"
                mapping.pop("promotion", None)

    data["coverage"].update(
        counted_compressed_pids=0,
        counted_generators=0,
        final_disposition_pids=0,
        generated_pids=0,
        retained_adapter_pids=0,
        retained_boundary_pids=0,
        unresolved_pids=106,
    )
    return data


def expect_rejected(
    repo: Path,
    ledger_path: Path,
    original: str,
    name: str,
    mutate,
    expected: str,
) -> None:
    data = normalized_active_fixture(original)
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


def expect_index_rejected(
    repo: Path,
    index_path: Path,
    original_index: str,
) -> None:
    index_path.write_text(
        original_index.replace("P-MET-01,1,", "P-MET-01,99,", 1),
        encoding="utf-8",
    )
    completed = subprocess.run(
        validator(repo),
        text=True,
        capture_output=True,
        check=False,
    )
    output = completed.stdout + completed.stderr
    if (
        completed.returncode == 0
        or "compression theorem index digest drifted" not in output
    ):
        raise AssertionError(
            "theorem-index-digest-drift: validator did not reject as expected\n"
            + output
        )
    print("theorem-index-digest-drift: PASS")
    index_path.write_text(original_index, encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", default=".")
    args = parser.parse_args()

    repo = Path(args.repo_root).resolve()
    ledger_path = (
        repo
        / "formalization/ueot-core/docs/compression/COMPRESSION_LEDGER.yaml"
    )
    index_path = (
        repo
        / "formalization/ueot-core/docs/CORE_COMPRESSION_THEOREM_INDEX.csv"
    )
    original = ledger_path.read_text(encoding="utf-8")
    original_index = index_path.read_text(encoding="utf-8")

    try:
        expect_index_rejected(repo, index_path, original_index)

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

        expect_rejected(
            repo,
            ledger_path,
            original,
            "forged-audit-summary",
            lambda d: d["coverage"].update(
                analyzed_pids=4, schema_classified_pids=4
            ),
            "analyzed_pids disagrees with explicit per-P-ID audit records",
        )

        def fake_generated(data: dict) -> None:
            data["generators"]["M-TC-01"]["state"] = "cross_family_green"
            data["generators"]["M-TC-01"]["mappings"]["P-API-01"][
                "state"
            ] = "lean_rederived"
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
            "every generated dependency must be a counted generator",
        )

        def stronger_assumption(data: dict) -> None:
            data["generators"]["M-TC-01"]["mappings"]["P-API-01"][
                "assumption_relation"
            ] = "stronger"

        expect_rejected(
            repo,
            ledger_path,
            original,
            "stronger-assumption-full-mapping",
            stronger_assumption,
            "full rederivation cannot strengthen",
        )

        def retained_without_evidence(data: dict) -> None:
            data["final_dispositions"] = {
                "P-DYN-01": {
                    "status": "retained_adapter",
                    "rationale": (
                        "Measurable-kernel descent remains a distinct "
                        "domain-specific obligation."
                    ),
                }
            }
            data["coverage"].update(
                final_disposition_pids=1,
                retained_adapter_pids=1,
                unresolved_pids=105,
            )

        expect_rejected(
            repo,
            ledger_path,
            original,
            "retained-without-audit-evidence",
            retained_without_evidence,
            "needs nonempty audit_evidence references",
        )

        def malformed_retained_evidence(data: dict) -> None:
            retained_without_evidence(data)
            data["final_dispositions"]["P-DYN-01"]["audit_evidence"] = [None]

        expect_rejected(
            repo,
            ledger_path,
            original,
            "malformed-retained-audit-evidence",
            malformed_retained_evidence,
            "audit_evidence entries must be nonempty strings",
        )

        def fragment_retained_evidence(data: dict) -> None:
            retained_without_evidence(data)
            data["final_dispositions"]["P-DYN-01"]["audit_evidence"] = [
                (
                    "doc:formalization/ueot-core/docs/compression/"
                    "COMPRESSION_MISSION.md#definitely-no-such-heading"
                )
            ]

        expect_rejected(
            repo,
            ledger_path,
            original,
            "doc-fragment-audit-evidence",
            fragment_retained_evidence,
            "doc audit fragments are not supported",
        )

        def unrelated_ablation_loss(data: dict) -> None:
            generator = data["generators"]["M-TC-01"]
            generator["state"] = "counted_generator"
            generator["promotion"] = {"test": True}
            for pid in ("P-API-01", "P-ID-01"):
                mapping = generator["mappings"][pid]
                mapping["state"] = "counted"
                mapping["promotion"] = {"test": True}
            generator["ablation"] = {
                "result": "nonredundant_under_declared_derivation_system",
                "broken_pids": ["P-DYN-01"],
                "rationale": (
                    "This deliberately names an unrelated P-ID and must be "
                    "rejected by the ablation dependency check."
                ),
            }
            data["coverage"].update(
                counted_compressed_pids=2,
                counted_generators=1,
                final_disposition_pids=2,
                generated_pids=2,
                unresolved_pids=104,
            )
            data["final_dispositions"] = {
                "P-API-01": {
                    "status": "generated",
                    "generator_ids": ["M-TC-01"],
                },
                "P-ID-01": {
                    "status": "generated",
                    "generator_ids": ["M-TC-01"],
                },
            }
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
            "unrelated-ablation-loss",
            unrelated_ablation_loss,
            "ablation broken_pids must be final generated mappings",
        )

        def frozen_core_omits_used_generator(data: dict) -> None:
            tc = data["generators"]["M-TC-01"]
            tc["state"] = "counted_generator"
            tc["promotion"] = {"test": True}
            for pid in ("P-API-01", "P-ID-01"):
                mapping = tc["mappings"][pid]
                mapping["state"] = "counted"
                mapping["promotion"] = {"test": True}

            spare = json.loads(json.dumps(tc))
            spare["title"] = "Synthetic regression-only spare generator"
            spare["state"] = "counted_generator"
            spare["promotion"] = {"test": True}
            data["generators"]["M-TX-99"] = spare

            data["coverage"].update(
                counted_compressed_pids=2,
                counted_generators=2,
                final_disposition_pids=2,
                generated_pids=2,
                unresolved_pids=104,
            )
            data["final_dispositions"] = {
                "P-API-01": {
                    "status": "generated",
                    "generator_ids": ["M-TC-01"],
                },
                "P-ID-01": {
                    "status": "generated",
                    "generator_ids": ["M-TC-01"],
                },
            }
            data["minimal_core"].update(
                state="frozen",
                generator_ids=["M-TX-99"],
                ablation_state="complete",
                minimality_claim=(
                    "nonredundant_under_declared_derivation_system"
                ),
            )

        expect_rejected(
            repo,
            ledger_path,
            original,
            "frozen-core-omits-used-generator",
            frozen_core_omits_used_generator,
            "frozen minimal core must exactly match generators used",
        )

        def missing_remaining_core_derivability(data: dict) -> None:
            tc = data["generators"]["M-TC-01"]
            tc["state"] = "counted_generator"
            tc["promotion"] = {"test": True}
            for pid in ("P-API-01", "P-ID-01"):
                mapping = tc["mappings"][pid]
                mapping["state"] = "counted"
                mapping["promotion"] = {"test": True}
            tc["ablation"] = {
                "result": "nonredundant_under_declared_derivation_system",
                "broken_pids": ["P-API-01"],
                "rationale": (
                    "Removing this generator breaks a recorded generated "
                    "mapping in this regression fixture."
                ),
            }
            data["coverage"].update(
                counted_compressed_pids=2,
                counted_generators=1,
                final_disposition_pids=2,
                generated_pids=2,
                unresolved_pids=104,
            )
            data["final_dispositions"] = {
                "P-API-01": {
                    "status": "generated",
                    "generator_ids": ["M-TC-01"],
                },
                "P-ID-01": {
                    "status": "generated",
                    "generator_ids": ["M-TC-01"],
                },
            }
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
            "missing-remaining-core-derivability",
            missing_remaining_core_derivability,
            "final ablation needs remaining_core_derivability",
        )
    finally:
        ledger_path.write_text(original, encoding="utf-8")
        index_path.write_text(original_index, encoding="utf-8")

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
