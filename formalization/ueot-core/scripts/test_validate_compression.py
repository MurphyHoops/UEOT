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
import tempfile
from pathlib import Path


def validator(repo: Path) -> list[str]:
    return [
        sys.executable,
        str(repo / "formalization/ueot-core/scripts/validate_compression.py"),
        "--repo-root",
        str(repo),
        "--baseline-ref",
        "origin/main",
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


def run_lean_witness_controls(repo: Path) -> None:
    """Exercise the production emitter against real kernel axiom dependencies."""
    from validate_compression import compression_source_modules, render_lean_witness_audit

    core = repo / "formalization/ueot-core"
    expected_source_modules = compression_source_modules(core)
    good = "UEOT.V3.Compression.TransportCertificate.weighted_chain_bound"
    missing = "UEOT.MissingWitnessForAuditControl"
    leak = "AuditControl.leak"
    fixtures = {
        "standard-axioms": (good, "", True, "LEDGER_AXIOM_ALLOWLIST_PASS"),
        "missing-witness": (missing, "", False, "Unknown"),
        "custom-axiom": (
            leak, "namespace AuditControl\naxiom external : False\n"
            "theorem leak : False := external\nend AuditControl\n",
            False, "LEDGER_NONSTANDARD_AXIOM AuditControl.leak: #[AuditControl.external]",
        ),
        "incomplete-proof": (
            leak, "namespace AuditControl\ntheorem leak : False := by sorry\n"
            "end AuditControl\n", False,
            "LEDGER_NONSTANDARD_AXIOM AuditControl.leak: #[sorryAx]",
        ),
    }
    with tempfile.TemporaryDirectory(prefix="ueot-ledger-axiom-controls-") as tmp:
        for label, (name, prelude, should_pass, marker) in fixtures.items():
            source = render_lean_witness_audit(
                {name}, expected_source_modules=expected_source_modules)
            source = source.replace(f"#check {name}", prelude + f"#check {name}", 1)
            path = Path(tmp) / (label + ".lean")
            path.write_text(source, encoding="utf-8")
            result = subprocess.run(
                ["lake", "env", "lean", str(path)],
                cwd=repo / "formalization/ueot-core",
                text=True, capture_output=True, check=False,
            )
            output = result.stdout + result.stderr
            if (result.returncode == 0) != should_pass or marker not in output:
                raise AssertionError(f"{label}: unexpected Lean audit result\n{output}")
            print(f"ledger-axiom-control-{label}: PASS")

        # An imported private theorem can be outside the logical namespace
        # while still belonging to a Compression source module. The compiler's
        # module provenance, not an FQN string prefix, defines this coverage.
        lean_path = subprocess.check_output(
            ["lake", "env", "printenv", "LEAN_PATH"], cwd=core, text=True).strip()
        command = ["lake", "env", "env", f"LEAN_PATH={tmp}:{lean_path}", "lean"]
        for label, conclusion, proof, should_pass in (
            ("imported-private-standard", "True", "True.intro", True),
            ("imported-private-custom-axiom", "False", "external", False),
        ):
            suffix = "PrivateStandard" if should_pass else "PrivateCustom"
            module = "UEOT.V3.Compression.AuditControl" + suffix
            fixture = Path(tmp).joinpath(*module.split(".")).with_suffix(".lean")
            fixture.parent.mkdir(parents=True, exist_ok=True)
            prelude = "" if should_pass else "axiom external : False\n"
            fixture.write_text(
                "namespace AuditOutsideCompression\n" + prelude +
                "theorem anchor : True := True.intro\n" +
                f"private theorem certificate : {conclusion} := {proof}\n" +
                "end AuditOutsideCompression\n", encoding="utf-8")
            compiled = subprocess.run(
                command + ["-R", tmp, "-o", str(fixture.with_suffix(".olean")), str(fixture)],
                cwd=core, text=True, capture_output=True, check=False)
            if compiled.returncode != 0:
                raise AssertionError(f"{label}: fixture compilation failed\n" +
                                     compiled.stdout + compiled.stderr)
            # Isolate the imported module to avoid shadowing the real UEOT
            # package root with this temporary UEOT fixture directory.
            source = render_lean_witness_audit(
                {"AuditOutsideCompression.anchor"}, expected_source_modules={module})
            source = source.replace("import UEOT.V3.Compression\n",
                                    f"import {module}\n", 1)
            path = Path(tmp) / (label + ".lean")
            path.write_text(source, encoding="utf-8")
            result = subprocess.run(command + [str(path)], cwd=core,
                                    text=True, capture_output=True, check=False)
            output = result.stdout + result.stderr
            marker = ("COMPRESSION_NATIVE_AXIOM_PASS" if should_pass
                      else "COMPRESSION_NONSTANDARD_AXIOM")
            if (result.returncode == 0) != should_pass or marker not in output:
                raise AssertionError(f"{label}: unexpected source-module audit result\n{output}")
            print(f"ledger-axiom-control-{label}: PASS")

        # A compilable source can exist outside the umbrella's import closure.
        # Use the production filesystem census, not a manually invented name.
        fixture_core = Path(tmp) / "source-census"
        fixture_command = [
            "lake", "env", "env", f"LEAN_PATH={fixture_core}:{lean_path}", "lean"]

        def compile_module(module: str, source: str) -> None:
            path = fixture_core.joinpath(*module.split(".")).with_suffix(".lean")
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source, encoding="utf-8")
            result = subprocess.run(
                fixture_command + ["-R", str(fixture_core), "-o",
                                   str(path.with_suffix(".olean")), str(path)],
                cwd=core, text=True, capture_output=True, check=False)
            if result.returncode != 0:
                raise AssertionError(f"source-census fixture {module} failed\n" +
                                     result.stdout + result.stderr)

        anchor = "AuditSourceCensus.anchor"
        imported = "UEOT.V3.Compression.AuditSourceImported"
        orphan = "UEOT.V3.Compression.AuditSourceOrphan"
        compile_module(
            imported, "namespace AuditSourceCensus\n"
            "theorem anchor : True := True.intro\nend AuditSourceCensus\n")
        compile_module("UEOT.V3.Compression", f"import {imported}\n")
        before = compression_source_modules(fixture_core)
        if before != {"UEOT.V3.Compression", imported}:
            raise AssertionError(f"unexpected initial source census: {before}")
        stale_audit = render_lean_witness_audit(
            {anchor}, expected_source_modules=before)

        # The nonstandard axiom is outside Compression; the unimported private
        # theorem is inside it. Neither is visible through the umbrella alone.
        compile_module(
            "AuditSourceExternal", "namespace AuditSourceExternal\n"
            "axiom external : False\nend AuditSourceExternal\n")
        compile_module(
            orphan, "import AuditSourceExternal\nnamespace AuditSourceCensus\n"
            "private theorem orphan : False := AuditSourceExternal.external\n"
            "end AuditSourceCensus\n")
        after = compression_source_modules(fixture_core)
        if after != before | {orphan}:
            raise AssertionError(f"unimported physical source was not inventoried: {after}")
        for label, source, should_pass, marker in (
            ("umbrella-does-not-see-orphan", stale_audit, True,
             "COMPRESSION_NATIVE_AXIOM_PASS"),
            ("unimported-source-module", render_lean_witness_audit(
                {anchor}, expected_source_modules=after), False,
             f"COMPRESSION_SOURCE_MODULE_NOT_IMPORTED {orphan}"),
        ):
            path = fixture_core / (label + ".lean")
            path.write_text(source, encoding="utf-8")
            result = subprocess.run(
                fixture_command + [str(path)], cwd=core,
                text=True, capture_output=True, check=False)
            output = result.stdout + result.stderr
            if (result.returncode == 0) != should_pass or marker not in output:
                raise AssertionError(f"{label}: unexpected census audit result\n{output}")
            print(f"ledger-axiom-control-{label}: PASS")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", default=".")
    parser.add_argument("--lean-witness-controls-only", action="store_true")
    args = parser.parse_args()

    repo = Path(args.repo_root).resolve()
    if args.lean_witness_controls_only:
        run_lean_witness_controls(repo)
        return
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
