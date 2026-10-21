#!/usr/bin/env python3
"""Prepare a temporary, reviewable overlay only from two observed Lean successes.

The repository consumer and all existing ledgers remain untouched. The finalizer
rechecks real process/log/build/source bindings and compares complete native JSON
objects before promoting the three *evidence clauses* in a temporary candidate.
Typed reuse review and outer registration remain separate required work.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
import tempfile

import prepare_registered_interfaces_export as export_helper
import prepare_registered_interfaces_fixed_certificate as fixed_helper
import run_native_registered_interfaces_pipeline as pipeline

PREFIX = fixed_helper.PREFIX
OVERLAY_NAME = "REGISTERED_INTERFACES_REUSE_OVERLAY_V1.json"


def finalize(args) -> dict:
    repo, observed, output = args.repo.resolve(), args.observed.resolve(), args.output.resolve()
    if output.is_relative_to(repo) or output == observed:
        raise RuntimeError("USE_A_SEPARATE_TEMPORARY_FINAL_OUTPUT_DIRECTORY")
    if output.exists() and any(output.iterdir()):
        raise RuntimeError("FINAL_OUTPUT_DIRECTORY_MUST_BE_EMPTY")
    status = pipeline.read_json(observed / pipeline.STATUS_NAME)
    if status.get("state") != "pass":
        raise RuntimeError("ACTUAL_NATIVE_PIPELINE_NOT_SUCCESSFUL")
    results = status.get("results", [])
    if [row.get("label") for row in results] != list(pipeline.RUN_LABELS):
        raise RuntimeError("ACTUAL_NATIVE_EXECUTION_SEQUENCE_MISMATCH")
    for row in results:
        if type(row.get("returncode")) is not int or row["returncode"] != 0:
            raise RuntimeError("ACTUAL_NATIVE_EXECUTION_NOT_EXIT_ZERO")
        if pipeline.sha(observed / (row["label"] + ".log")) != row.get("log_sha256"):
            raise RuntimeError("ACTUAL_NATIVE_PROCESS_LOG_DRIFT: " + row["label"])
    build = pipeline.validate_build_inputs(repo, args.build_status, args.build_manifest,
                                            args.build_log_dir, args.focused_label, args.full_label)
    if status.get("build_binding") != build:
        raise RuntimeError("NATIVE_PIPELINE_AND_FINAL_BUILD_BINDINGS_DIFFER")
    if args.base_ref and pipeline.resolve_commit(repo, args.base_ref) != build["baseline_ref"]:
        raise RuntimeError("FINALIZER_BASE_REF_DIFFERS_FROM_ACTUAL_BUILD_PREDECESSOR")

    # Reparse both actual Lean logs; equality of census summaries is insufficient.
    first = pipeline.native_json(observed / "native_export.log")
    fixed = pipeline.native_json(observed / "fixed_verifier.log")
    canonical = pipeline.read_json(observed / pipeline.NATIVE_NAME)
    saved_first = pipeline.read_json(observed / "observed_first_native.json")
    saved_fixed = pipeline.read_json(observed / "observed_fixed_native.json")
    if not first == fixed == canonical == saved_first == saved_fixed:
        raise RuntimeError("COMPLETE_NATIVE_JSON_BINDING_FAILED")
    comparison = pipeline.read_json(observed / "native_fixed_comparison_status.json")
    if comparison != status.get("binding") or comparison.get("status") != "EXACT_JSON_OBJECT_MATCH":
        raise RuntimeError("RECORDED_FULL_NATIVE_OUTPUT_BINDING_FAILED")
    for key, filename in (("first_sha256", "observed_first_native.json"),
                          ("fixed_sha256", "observed_fixed_native.json")):
        if comparison.get(key) != pipeline.sha(observed / filename):
            raise RuntimeError("OBSERVED_NATIVE_JSON_FILE_DRIFT: " + filename)
    native_sha = pipeline.sha(observed / pipeline.NATIVE_NAME)
    if native_sha != comparison["fixed_sha256"]:
        raise RuntimeError("CANONICAL_NATIVE_ARTIFACT_IS_NOT_FIXED_VERIFIER_OUTPUT")
    pre = pipeline.read_json(observed / pipeline.PREFLIGHT_NAME)
    overlay = pipeline.read_json(observed / "overlay_candidate.json")
    if pre.get("baseline_ref") != build["baseline_ref"]:
        raise RuntimeError("NATIVE_PREFLIGHT_BASE_REF_MISMATCH")
    verifier_sha = pipeline.sha(observed / pipeline.VERIFIER_NAME)
    if verifier_sha != overlay.get("pending_verifier_sha256"):
        raise RuntimeError("OBSERVED_FIXED_VERIFIER_DRIFT")

    # Reproduce the pending source/exporter/fixed candidate using the same frozen
    # sources and compiler output. This also revalidates all prior pinned overlays,
    # every new native constant, axiom closure, ownership and exact proof edges.
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="registered-interfaces-recheck-", dir=output.parent) as temporary:
        staging = Path(temporary)
        regenerated = export_helper.prepare(repo, staging, build["baseline_ref"])
        if regenerated != pre:
            raise RuntimeError("REGENERATED_SOURCE_PREFLIGHT_DIFFERS_FROM_OBSERVED")
        if (staging / pipeline.EXPORTER_NAME).read_bytes() != (observed / pipeline.EXPORTER_NAME).read_bytes():
            raise RuntimeError("OBSERVED_EXPORTER_IS_NOT_CURRENT_PROTOCOL_ON_FROZEN_SOURCE")
        fixed_helper.prepare(repo, observed / pipeline.PREFLIGHT_NAME,
                             observed / pipeline.NATIVE_NAME, observed / pipeline.EXPORTER_NAME,
                             staging)
        if pipeline.read_json(staging / "overlay_candidate.json") != overlay:
            raise RuntimeError("REGENERATED_PENDING_CANDIDATE_DIFFERS_FROM_OBSERVED")
        if (staging / pipeline.VERIFIER_NAME).read_bytes() != (observed / pipeline.VERIFIER_NAME).read_bytes():
            raise RuntimeError("FIXED_VERIFIER_IS_NOT_EXACT_REGENERATED_PROTOCOL")

    core = repo / export_helper.CORE_PREFIX
    knowledge = core / "docs/compression/theory_completion/knowledge"
    sys.path.insert(0, str(knowledge))
    fkrg = export_helper.import_file("registered_interfaces_final_fkrg", knowledge / "fkrg.py")
    parser = export_helper.import_file("registered_interfaces_final_preflight", knowledge / "reuse/pr_preflight.py")
    base_ref = build["baseline_ref"]
    base_sources = parser.corpus(repo, base_ref)
    head_sources = {path.relative_to(repo).as_posix(): path.read_text() for path in fkrg.sources().values()}
    if len(base_sources) != 659 or len(head_sources) != 659 + len(export_helper.STEMS):
        raise RuntimeError("IMMUTABLE_BASE_AND_CURRENT_SOURCE_MODULE_CENSUS_MISMATCH")
    baseline = [decl for path, source in base_sources.items() for decl in parser.declarations(path, source)]
    current = [decl for path, source in head_sources.items() for decl in parser.declarations(path, source)]
    prior_names = parser.validate_unique(baseline, "IMMUTABLE_PREDECESSOR")
    current_names = parser.validate_unique(current, "FROZEN_REGISTERED_INTERFACES_WORKTREE")
    added = [row for row in current if row["symbol"] not in prior_names]
    new_native_names = {row["name"] for row in fixed["public_source_theorems"]
                        if row["registration_kind"] == "new_source_public"}
    historical_native_names = {row["name"] for row in fixed["public_source_theorems"]
                               if row["registration_kind"] == "historical_public_repair"}
    if {row["symbol"] for row in added} != new_native_names:
        raise RuntimeError("NATIVE_AND_PR_LEXICAL_ADDED_SOURCE_SETS_DIFFER")
    historical = pre["historical_public_repairs"]
    if historical_native_names != {row["name"] for row in historical}:
        raise RuntimeError("NATIVE_HISTORICAL_PUBLIC_REPAIR_SET_MISMATCH")
    base_by_name = {row["symbol"]: row for row in baseline}
    for row in historical:
        if (row["name"] not in prior_names or row["name"] not in current_names or
                base_by_name[row["name"]]["path"] != row["path"] or
                pipeline.sha(repo / row["path"]) != row["content_sha256"]):
            raise RuntimeError("HISTORICAL_PUBLIC_REPAIR_IS_NOT_UNCHANGED_BASE_DECLARATION")
    source_sha = fkrg.fingerprint(fkrg.sources())
    if source_sha != pre["source_tree_sha256"]:
        raise RuntimeError("FROZEN_SOURCE_TREE_DRIFT")
    hints = [{**row, "reuse_candidates": parser.candidate_hints(row, baseline)} for row in added]
    hinted = sum(bool(row["reuse_candidates"]) for row in hints)
    prior_count = export_helper.HISTORICAL_THEOREMS
    lexical = {
        "baseline_ref": base_ref, "candidate_ref": None,
        "candidate_scope": "Current frozen worktree bytes; an immutable Git-object PR preflight is separately required after commit.",
        "base_lean_module_count": len(base_sources), "candidate_lean_module_count": len(head_sources),
        "base_public_lexical_theorem_count": len(baseline),
        "candidate_public_lexical_theorem_count": len(current),
        "new_public_source_theorem_count": len(added),
        "historical_public_repair_count": len(historical),
        "overlay_public_registration_count": len(fixed["public_source_theorems"]),
        "new_theorems_with_lexical_reuse_candidates": hinted,
        "candidate_source_tree_sha256": source_sha,
        "registered_prior_public_source_theorem_count": prior_count,
        "candidate_registered_public_source_theorem_count": prior_count + len(fixed["public_source_theorems"]),
        "note": "Actual-base PR parser and name hints identify 52 new declarations. One exact unchanged base declaration is repaired additively after native confirmation; it is not a new mathematical proof. The frozen fkrg.py trailing-word-boundary parser is unchanged. Name hints and raw stored-type isDefEq do not replace semantic review.",
    }
    for key in ("type_distinctness", "proof_dependency_certification", "native_axiom_census",
                "historical_public_repair_certification", "existing_proof_dependency_repair_certification"):
        if overlay[key]["status"] != "PENDING_FIXED_CERTIFICATE_COMPILATION":
            raise RuntimeError("UNEXPECTED_PENDING_CANDIDATE_STATE")
        overlay[key]["status"] = "PASS"
    del overlay["pending_verifier_sha256"]
    overlay["source_tree_sha256"] = source_sha
    overlay["lexical_pr_preflight"] = lexical
    scope = fixed["all_native_theorem_constants"]
    overlay["native_export_evidence"] = {
        "path": PREFIX + pipeline.NATIVE_NAME, "sha256": native_sha,
        "scope": f"Actual fixed-verifier output for all {len(scope)} theorem constants in seven new source modules and one unchanged historical repair module: types, stored universe parameters, all direct constants, theorem constants, ownership and axiom closure. The {len(added)} new declarations and {len(historical)} historical repair have registered proof edges. A separate actual scan of all 4094 previous registered proofs records every direct caller of the exact repair name; fixed replay checks each prior edge set and its additive delta.",
    }
    native_rows = {row["label"]: row for row in results}
    overlay["native_execution"] = {
        "toolchain": (core / "lean-toolchain").read_text().strip(),
        "observed_builds": build["builds"],
        "build_status_sha256": build["build_status_sha256"],
        "source_manifest_sha256": build["source_manifest_sha256"],
        "native_export_exit_code": native_rows["native_export"]["returncode"],
        "fixed_certificate_exit_code": native_rows["fixed_verifier"]["returncode"],
        "fixed_certificate_sha256": verifier_sha,
        "fixed_export_equals_initial_native_export": first == fixed,
        "native_log_sha256": native_rows["native_export"]["log_sha256"],
        "fixed_verifier_log_sha256": native_rows["fixed_verifier"]["log_sha256"],
        "pipeline_status_sha256": pipeline.sha(observed / pipeline.STATUS_NAME),
        "source_binding": "The actual successful build receipt pins all 666 production source modules, all nine dependency checkouts, three build environment files and actual Lean/Lake executables. The smaller new-module/root list is supplemental. Complete identities and real logs are rechecked before/after execution and at finalization; both complete Lean JSON objects, including the historical incoming-edge scan, match exactly.",
    }
    review = {
        "status": "PENDING_TYPED_REUSE_REVIEW" if hinted else "PENDING_OUTER_REGISTRATION_REVIEW",
        "lexical_hint_groups": hinted,
        "scope": "Only the native type/edge/axiom evidence clauses have observed PASS. This temporary packet is unregistered; semantic typed-reuse review and Git-object publication gates are not claimed complete.",
    }
    output.mkdir(parents=True, exist_ok=True)
    for filename in (pipeline.VERIFIER_NAME, pipeline.NATIVE_NAME):
        (output / filename).write_bytes((observed / filename).read_bytes())
    pipeline.write_json(output / OVERLAY_NAME, overlay)
    pipeline.write_json(output / "development_lexical_reuse_hints.json", hints)
    pipeline.write_json(output / "review_status.json", review)
    summary = {"state": "OBSERVED_NATIVE_EVIDENCE_BOUND_PENDING_OUTER_REVIEW",
               "overlay_sha256": pipeline.sha(output / OVERLAY_NAME),
               "verifier_sha256": verifier_sha, "native_sha256": native_sha,
               "lexical": lexical, "review": review,
               "registered_edges": overlay["proof_dependency_certification"]["registered_direct_edges"],
               "existing_registered_edge_repairs": overlay["existing_proof_dependency_repair_certification"]["added_registered_direct_edges"]}
    pipeline.write_json(output / "finalization_summary.json", summary)
    return summary


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("repo", "observed", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    pipeline.add_build_arguments(parser)
    args = parser.parse_args()
    result = finalize(args)
    print(json.dumps(result, ensure_ascii=False, indent=2))
