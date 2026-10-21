#!/usr/bin/env python3
"""Read-only FKRG theorem reuse navigator over pinned Lean audit evidence.

The immutable 2026-10-10 633-module snapshot remains the historical base.
Governed additive overlays extend the live source census without rewriting that
history. Exact-type groups remain kernel-verified; every overlay carries its
own source hashes and a Lean type-distinctness certificate.
"""
from __future__ import annotations

import argparse
import csv
from hashlib import sha256
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
AUDIT = HERE.parent / "audits" / "2026-10-10"
REPO = HERE.parents[6]
SCHEMA = "FKRG_REUSE_NAVIGATOR_V2"
SOURCE_BASELINE = "48b582beabec2ebae61ab0d51081b83356fcb3e1"
OVERLAY_PATHS = [
    HERE / "MINCORE_REUSE_OVERLAY_V1.json",
    HERE / "CALIBRATED_DEFECT_REUSE_OVERLAY_V1.json",
    HERE / "DEFECT_GAUGE_REUSE_OVERLAY_V1.json",
    HERE / "FINITE_HORIZON_RISK_REUSE_OVERLAY_V1.json",
    HERE / "STATISTICAL_RISK_REUSE_OVERLAY_V1.json",
    HERE / "DEPLOYMENT_JOINT_REUSE_OVERLAY_V1.json",
    HERE / "SUPPORT_VIABILITY_REUSE_OVERLAY_V1.json",
    HERE / "REGISTERED_INTERFACES_REUSE_OVERLAY_V1.json",
    HERE / "LONGTERM_CONTROL_STATISTICS_REUSE_OVERLAY_V1.json",
]
OVERLAY_TYPE_CHECKS = [
    HERE / "VERIFY_MINCORE_OVERLAY_TYPES.lean",
    HERE / "VERIFY_CALIBRATED_DEFECT_OVERLAY_TYPES.lean",
    HERE / "VERIFY_DEFECT_GAUGE_OVERLAY_TYPES.lean",
    HERE / "VERIFY_FINITE_HORIZON_RISK_OVERLAY_TYPES.lean",
    HERE / "VERIFY_STATISTICAL_RISK_OVERLAY_TYPES.lean",
    HERE / "VERIFY_DEPLOYMENT_JOINT_OVERLAY_TYPES.lean",
    HERE / "VERIFY_SUPPORT_VIABILITY_OVERLAY_TYPES.lean",
    HERE / "VERIFY_REGISTERED_INTERFACES_OVERLAY_TYPES.lean",
    HERE / "VERIFY_LONGTERM_CONTROL_STATISTICS_OVERLAY_TYPES.lean",
]
OVERLAY_SHA256S = [
    "90df2d97cca4383032d9f4729b6698252b985d657583275c6755c3cfafad84d8",
    "b48607f7b68bfcd8aef0d2417d0111d66e374001114fd38048602b4557f8adc2",
    "182efa3fc030cac3ba2082fc13df461a8e165411b58582b5a85cb05343c263b9",
    "c7e4f561e438f6f3eef3112ecf7ceeea59e1cb98c10b5b20c65490eb7919d480",
    "f0d0ea91584773c24eeed59f8f1915102b92c318bf864f3b08a4c7093552c755",
    "72fd346f3ab3adca4cb29de1f5c19cc6742555e3003fc32efa345eabbda850f2",
    "2af284000d6a6c25f67e9356a236817b22334dbfba777ca2eaf37e8060a3a45e",
    "6667bf7a908d713394e5daae5291c3a82f1ff7b3da144e2addf3da5959d0e781",
    "cb5792eff95b2a1386a7c0832eeeedc5a283f212b462f2c6c6d3342dd5e1bb06",
]
OVERLAY_TYPE_CHECK_SHA256S = [
    "23112dd2df1e1233c664a98e3d3118275cac1053e0ed8f3d08feb4061cfcb550",
    "c75a3af6508d2ec1ba0214d833ae17783d7f2e410c6f0226534e278fb83cecc2",
    "058a7a228d13a8063408053e4b9006ab30309324a03ccffbbd89e9982246f061",
    "8624de79f7bde2b2af5b1cafc65342d925b3ea4a753ba3f62f86207dcd5e37de",
    "5615a23f94b3ba53f9faec51b72d021f204e539fc73448f793752cc78727438d",
    "48e310eb767413092a0e02fff53bc00b22c87808b4abc838be1ec2279c35b873",
    "26fd18e77dd6b7db550c6c5e1105376ef7f494db03bbab646e8d8fa42313a118",
    "0d3eb26c9471e1701a28652f308c9dd1e1ccac72c0b9ef36eec27c1bc3165d32",
    "0643f8dfca2daec2ce6b4638f712f6abcacf8f91f31669a37120f397d6c27213",
]

# Independent immutable digests calculated from main after merged PR #314.
# Changing a CSV and its claimed source hash together must fail closed.
EVIDENCE_SHA = {
    "EVERY_FILE_633_DETAILED_METRICS.csv": "3abeba50709ab1dd06e5245e81615ecee604995976a28ae945c5430de2343162",
    "EVERY_DECLARATION_5553_COMPACT.csv": "8baa41ef67a8cba4560f1ed22c510e212af728dcb88c921c17345f052e4e6ac9",
    "all_3793_theorem_direct_reuse_graph.csv": "1a52b06b9bae3efd92aea18b64ccc2c29ff314fe7571420d334bcc1b43d9d6a3",
    "ALL_binder_normalized_equal_type_clusters.json": "4b6f83592ae9002b3bd88e669d7ab3a0527f5915acd60cbb89b4907f17482f03",
    "NEAR_TYPE_15_DISTINCT_HEURISTIC_PAIRS.json": "3b6878de62b336e361c7d658edce00c2925c10f8d11a7cbd73ee29e7cd19721b",
    "SOURCE_PROVENANCE_BREAKDOWN.json": "968f4b8e16fe743c1a7e54d1fbe3c086585cd2c858c97b1490c08bc595c41079",
    "FOCUSED_14_REUSE_TRIAGE.md": "26e8ebb25049f65a81a6e5990b91ec2befad30b2a2d7f3f49836427b45241946",
}
# Triage labels are evidence classifications, not proof of unique scientific
# minimality. Only ledger-counted M-TC/M-OI source-facing mappings use that label.
ROLES = {
    "UEOT.V3.Compression.OccupationLimitInvariance.p_goa_01_via_occupationLimit": "COUNTED_GENERATOR_FAMILY_REDERIVATION",
    "UEOT.V3.Compression.OccupationLimitInvariance.feller_invariant_of_occupation_tendsto": "COUNTED_GENERATOR_FAMILY_SUPPORT_LEMMA",
    "UEOT.V3.Compression.OccupationLimitInvariance.p_per_02_via_occupationLimit": "COUNTED_GENERATOR_FAMILY_REDERIVATION",
    "UEOT.V3.Compression.TransportCertificate.processInterface_approx_via_twoStage": "COUNTED_GENERATOR_FAMILY_REDERIVATION",
    "UEOT.V3.Compression.TransportCertificate.processInterface_exact_source_via_twoStage": "COUNTED_GENERATOR_FAMILY_REDERIVATION",
    "UEOT.V3.Compression.TransportCertificate.dynamicsCrossScale_approx_via_twoStage": "COUNTED_GENERATOR_FAMILY_REDERIVATION",
    "UEOT.V3.Compression.TransportCertificate.dynamicsCrossScale_exact_via_factor": "COUNTED_GENERATOR_FAMILY_REDERIVATION",
    "UEOT.V3.Compression.TransportCertificate.p_dyn_03_via_multiplicative_chain": "COUNTED_GENERATOR_FAMILY_REDERIVATION",
    "UEOT.V3.Compression.ValueAlignment.p_ali_02_core_via_mva": "UNCOUNTED_RETAINED_ADAPTER_EXPERIMENT",
    "UEOT.V3.Compression.ValueAlignment.p_ali_02_via_mva": "UNCOUNTED_RETAINED_ADAPTER_EXPERIMENT",
    "UEOT.V3.Compression.ContractiveFixedPoint.bellman_valueError_le_residual_via_mcf": "UNCOUNTED_RETAINED_ADAPTER_EXPERIMENT",
    "UEOT.V3.Compression.ContractiveFixedPoint.bellman_fixedPoint_unique_via_mcf": "UNCOUNTED_RETAINED_ADAPTER_EXPERIMENT",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.flip_physical_seed_cannot_select_two_programs": "SAME_NO_GO_INTERFACE_ALIAS",
}
CANONICAL_TV_HELPER = "UEOT.V3.InformationPacking.tvDist_symm"
DUPLICATED_TV_HELPER = "UEOT.V3.StatisticalDefect.tvDist_symm"


CLONE_SHA256 = "e369d3eee8fe5383532bf68c18ed08ec961d9710b4d600da3edc11a243ebc064"
LEDGER = REPO / "formalization/ueot-core/docs/compression/COMPRESSION_LEDGER.yaml"
LEDGER_SHA256 = "621da1e3c2a9b87aab0a07ca0624fe192fe15cc9bcd1c5aa6f5e669526a4d948"
# Compiled theorem proof graph and Meta.isDefEq certificates are only valid
# under the exact pinned Lean compiler/configuration/dependency manifest.
BUILD_ENVIRONMENT_SHA256 = {
    "lean-toolchain": "3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71",
    "lakefile.lean": "7f083f896c58e521092721637c067a9bd892c4b2d5185bdd1b99fd5391f25986",
    "lake-manifest.json": "84542dad0540d0595b67e5b83d6b2d7bf96b4ca4aee9051f557ed73b0cb012d1",
}



def read_csv(path: Path) -> list[dict]:
    with path.open(newline="", encoding="utf-8") as stream:
        return list(csv.DictReader(stream))


def source_area(path: str) -> str:
    """Derive the physical source area; logical namespaces need not match it."""
    prefix = Path("formalization/ueot-core/UEOT")
    candidate = Path(path)
    if candidate.is_absolute() or ".." in candidate.parts:
        raise RuntimeError("INVALID_OVERLAY_SOURCE_PATH")
    try:
        relative = candidate.relative_to(prefix)
    except ValueError as exc:
        raise RuntimeError("INVALID_OVERLAY_SOURCE_PATH") from exc
    if relative.suffix != ".lean":
        raise RuntimeError("INVALID_OVERLAY_SOURCE_PATH")
    return relative.parent.as_posix()


def load_overlays() -> list[dict]:
    if not (len(OVERLAY_PATHS) == len(OVERLAY_TYPE_CHECKS) ==
            len(OVERLAY_SHA256S) == len(OVERLAY_TYPE_CHECK_SHA256S)):
        raise RuntimeError("OVERLAY_REGISTRY_LENGTH_MISMATCH")
    overlays = []
    expected_base_modules = 633
    for index, path in enumerate(OVERLAY_PATHS):
        overlay = json.loads(path.read_text())
        if overlay.get("schema") != "FKRG_REUSE_OVERLAY_V1":
            raise RuntimeError("UNSUPPORTED_REUSE_OVERLAY_SCHEMA")
        if overlay.get("base_snapshot_modules") != expected_base_modules:
            raise RuntimeError("OVERLAY_BASE_MODULE_COUNT_MISMATCH")
        if index:
            prior = overlay.get("prior_overlay", {})
            expected_prior_path = OVERLAY_PATHS[index - 1].relative_to(REPO).as_posix()
            if (prior.get("path") != expected_prior_path or
                    prior.get("sha256") != OVERLAY_SHA256S[index - 1]):
                raise RuntimeError("OVERLAY_PRIOR_CHAIN_MISMATCH")
        if overlay.get("type_distinctness", {}).get("status") != "PASS":
            raise RuntimeError("OVERLAY_TYPE_DISTINCTNESS_NOT_CERTIFIED")
        if overlay.get("type_distinctness", {}).get("definitionally_equal_matches") != 0:
            raise RuntimeError("OVERLAY_TYPE_COLLISION_RECORDED")
        cert = overlay.get("proof_dependency_certification", {})
        if cert.get("status") != "PASS":
            raise RuntimeError("OVERLAY_PROOF_DEPENDENCIES_NOT_CERTIFIED")
        actual_edges = sum(len(x.get("source_theorem_deps", []))
                           for x in overlay.get("public_theorems", []))
        if cert.get("registered_direct_edges") != actual_edges:
            raise RuntimeError("OVERLAY_PROOF_EDGE_COUNT_MISMATCH")
        overlays.append(overlay)
        expected_base_modules += len(overlay.get("added_modules", []))
    return overlays


def apply_existing_proof_dependency_repairs(proof_rows, overlay, prior_names,
                                            prior_modules, *, repo):
    """Apply native-certified additive repairs in memory; never rewrite history.

    prior_modules contains the effective source hashes before this overlay.
    All validation completes before any existing proof row is changed.
    """
    if not any(key in overlay for key in
               ("historical_public_repairs", "existing_proof_dependency_repairs")):
        return

    def names(value, label):
        if (not isinstance(value, list) or not all(isinstance(x, str) and x for x in value)
                or len(value) != len(set(value))):
            raise RuntimeError("OVERLAY_REPAIR_INVALID_NAME_LIST: " + label)
        return set(value)

    for key in ("type_distinctness", "proof_dependency_certification", "native_axiom_census",
                "historical_public_repair_certification", "existing_proof_dependency_repair_certification"):
        if overlay.get(key, {}).get("status") != "PASS":
            raise RuntimeError("OVERLAY_REPAIR_NOT_CERTIFIED: " + key)
    if overlay["type_distinctness"].get("definitionally_equal_matches") != 0:
        raise RuntimeError("OVERLAY_REPAIR_TYPE_COLLISION")
    historical = overlay.get("historical_public_repairs", [])
    repairs = overlay.get("existing_proof_dependency_repairs", [])
    if not isinstance(historical, list) or not historical or not isinstance(repairs, list):
        raise RuntimeError("OVERLAY_REPAIR_MISSING_EXPLICIT_SCOPE")
    targets = names([row["name"] for row in historical], "historical targets")
    by_name = {row["name"]: row for row in proof_rows}
    if len(by_name) != len(proof_rows):
        raise RuntimeError("OVERLAY_REPAIR_DUPLICATED_GRAPH_NAME")
    registered = set(by_name)
    public = {row["name"]: row for row in overlay["public_theorems"]}
    if len(public) != len(overlay["public_theorems"]) or not targets <= set(public) & registered:
        raise RuntimeError("OVERLAY_REPAIR_UNREGISTERED_TARGET")
    if targets & prior_names:
        raise RuntimeError("OVERLAY_REPAIR_TARGET_WAS_ALREADY_REGISTERED")
    if overlay["proof_dependency_certification"].get("registered_direct_edges") != sum(
            len(row.get("source_theorem_deps", [])) for row in public.values()):
        raise RuntimeError("OVERLAY_REPAIR_NEW_NODE_EDGE_COUNT_MISMATCH")

    evidence = overlay.get("native_export_evidence", {})
    artifact = (repo / evidence.get("path", "")).resolve()
    reuse_root = (repo / "formalization/ueot-core/docs/compression/theory_completion/knowledge/reuse").resolve()
    if not artifact.is_relative_to(reuse_root) or not artifact.is_file():
        raise RuntimeError("OVERLAY_REPAIR_INVALID_NATIVE_PATH")
    if sha256(artifact.read_bytes()).hexdigest() != evidence.get("sha256"):
        raise RuntimeError("OVERLAY_REPAIR_NATIVE_EVIDENCE_DRIFT")
    native = json.loads(artifact.read_text())
    if native.get("schema") != "REGISTERED_INTERFACES_NATIVE_EXPORT_V1" or native.get("collisions") != []:
        raise RuntimeError("OVERLAY_REPAIR_INVALID_NATIVE_EXPORT")
    scan = native.get("historical_repair_incoming_scan", {})
    hcert = overlay["historical_public_repair_certification"]
    cert = overlay["existing_proof_dependency_repair_certification"]
    if (native.get("registered_prior_theorems") != len(prior_names) or
            scan.get("registered_theorems_scanned") != len(prior_names) or
            cert.get("registered_theorems_scanned") != len(prior_names) or
            hcert.get("historical_registered_base") != len(prior_names) or
            hcert.get("historical_public_repairs") != len(targets) or
            hcert.get("new_source_public_theorems") != len(public) - len(targets)):
        raise RuntimeError("OVERLAY_REPAIR_PRIOR_SCOPE_MISMATCH")
    if (names(scan.get("historical_public_repair_targets"), "native targets") != targets or
            names(cert.get("historical_public_repair_targets"), "certified targets") != targets):
        raise RuntimeError("OVERLAY_REPAIR_TARGET_SCOPE_MISMATCH")
    native_public = {row["name"]: row for row in native.get("public_source_theorems", [])}
    native_scope = {row["name"]: row for row in native.get("all_native_theorem_constants", [])}
    if (set(native_public) != set(public) or
            len(native_public) != len(native.get("public_source_theorems", [])) or
            len(native_scope) != len(native.get("all_native_theorem_constants", []))):
        raise RuntimeError("OVERLAY_REPAIR_NATIVE_PUBLIC_SET_MISMATCH")

    def source_hash(path, expected):
        source_area(path)
        source = (repo / path).resolve()
        if (path not in prior_modules or not source.is_relative_to(repo.resolve()) or
                expected != prior_modules[path]["content_sha256"] or
                not source.is_file() or sha256(source.read_bytes()).hexdigest() != expected):
            raise RuntimeError("OVERLAY_REPAIR_SOURCE_HASH_MISMATCH: " + path)

    for row in historical:
        name, path = row["name"], row["path"]
        source_hash(path, row["content_sha256"])
        owner = prior_modules[path]["module"]
        if (row.get("module") != owner or public[name]["path"] != path or
                public[name].get("registration_kind") != "historical_public_repair" or
                native_public[name].get("registration_kind") != "historical_public_repair" or
                native_public[name].get("source_module") != owner or
                native_scope.get(name, {}).get("source_module") != owner or
                native_scope.get(name, {}).get("is_private") is not False):
            raise RuntimeError("OVERLAY_REPAIR_HISTORICAL_OWNER_MISMATCH")

    repair_names = names([row["name"] for row in repairs], "existing callers")
    incoming = scan.get("incoming_rows", [])
    actual_names = names([row["name"] for row in incoming], "native callers")
    if repair_names != actual_names or cert.get("repaired_existing_nodes") != len(repairs):
        raise RuntimeError("OVERLAY_REPAIR_INCOMING_CALLER_SET_MISMATCH")
    actual_by_name = {row["name"]: row for row in incoming}
    planned = []
    for repair in repairs:
        name = repair["name"]
        if name not in prior_names or name not in by_name:
            raise RuntimeError("OVERLAY_REPAIR_CALLER_NOT_PREVIOUSLY_REGISTERED")
        old, actual = by_name[name], actual_by_name[name]
        path = old["path"]
        if repair["path"] != path or int(repair["line"]) != int(old["line"]):
            raise RuntimeError("OVERLAY_REPAIR_CALLER_LOCATION_MISMATCH")
        source_hash(path, repair["content_sha256"])
        owner = prior_modules[path]["module"]
        if repair.get("source_module") != owner or actual.get("source_module") != owner:
            raise RuntimeError("OVERLAY_REPAIR_CALLER_OWNER_MISMATCH")
        prior = names(repair.get("prior_source_theorem_deps"), "prior edges")
        if prior != names(json.loads(old["source_theorem_deps_json"]), "existing graph edges"):
            raise RuntimeError("OVERLAY_REPAIR_PRIOR_EDGE_MISMATCH")
        if not prior <= prior_names:
            raise RuntimeError("OVERLAY_REPAIR_UNREGISTERED_PRIOR_EDGE")
        delta = names(repair.get("added_source_theorem_deps"), "added edges")
        constants = names(actual.get("direct_constants"), "native direct constants")
        if (not delta or not delta <= targets or prior & delta or
                delta != constants & targets or
                delta != names(actual.get("historical_repair_deps"), "native repair hits")):
            raise RuntimeError("OVERLAY_REPAIR_FALSE_OR_NONADDITIVE_DELTA")
        expected = prior | delta
        if (names(repair.get("actual_source_theorem_deps"), "repaired edges") != expected or
                names(actual.get("actual_source_theorem_deps"), "native registered edges") != expected or
                (constants & registered) - {name} != expected):
            raise RuntimeError("OVERLAY_REPAIR_ACTUAL_PROOF_EDGE_MISMATCH")
        if name in native_scope:
            if (native_scope[name].get("source_module") != owner or
                    names(native_scope[name].get("direct_constants"), "full native constants") != constants):
                raise RuntimeError("OVERLAY_REPAIR_NARROW_AND_FULL_NATIVE_DISAGREE")
        planned.append((old, repair, sorted(expected)))
    if cert.get("added_registered_direct_edges") != sum(
            len(row["added_source_theorem_deps"]) for row in repairs):
        raise RuntimeError("OVERLAY_REPAIR_EXISTING_EDGE_COUNT_MISMATCH")
    for old, repair, deps in planned:
        old.setdefault("additive_dependency_repair_provenance", []).append({
            "overlay_id": overlay["overlay_id"],
            "prior_source_theorem_deps": repair["prior_source_theorem_deps"],
            "added_source_theorem_deps": repair["added_source_theorem_deps"],
        })
        old["source_theorem_deps_json"] = json.dumps(deps)
        old["direct_existing_source_theorem_deps"] = str(len(deps))


def _parse_data() -> dict:
    modules = read_csv(AUDIT / "EVERY_FILE_633_DETAILED_METRICS.csv")
    declarations = read_csv(AUDIT / "EVERY_DECLARATION_5553_COMPACT.csv")
    proof_rows = read_csv(AUDIT / "all_3793_theorem_direct_reuse_graph.csv")
    groups = json.loads((AUDIT / "ALL_binder_normalized_equal_type_clusters.json").read_text())
    near = json.loads((AUDIT / "NEAR_TYPE_15_DISTINCT_HEURISTIC_PAIRS.json").read_text())
    clones = json.loads((HERE / "CLONE_CANDIDATES_68.json").read_text())
    if (len(modules), len(declarations), len(proof_rows), len(groups), len(near), len(clones)) != (
        633, 5553, 3793, 37, 15, 68
    ):
        raise RuntimeError("AUDIT_ROW_COUNT_MISMATCH")
    overlays = load_overlays()
    source_overrides = {}
    for overlay in overlays:
        prior_names = {row["name"] for row in proof_rows}
        prior_modules = {row["path"]: {**row, "content_sha256": source_overrides.get(
            row["path"], row["content_sha256"])} for row in modules}
        for item in overlay["added_modules"]:
            modules.append(dict(item))
        for item in overlay["public_theorems"]:
            deps = item.get("source_theorem_deps", [])
            proof_rows.append({
                "name": item["name"],
                "path": item["path"],
                "line": str(item["line"]),
                "area": source_area(item["path"]),
                "all_direct_project_scoped_constants": "",
                "direct_existing_source_theorem_deps": str(len(deps)),
                "source_theorem_deps_json": json.dumps(deps),
                "source_origin": item.get("source_origin", "UEOT_MAINTAINED"),
                "overlay_scientific_role": (
                    "HISTORICAL_PUBLIC_DECLARATION_REPAIR_UNCOUNTED"
                    if item.get("registration_kind") == "historical_public_repair"
                    else overlay.get("scientific_role")),
            })
        apply_existing_proof_dependency_repairs(
            proof_rows, overlay, prior_names, prior_modules, repo=REPO)
        source_overrides.update(overlay.get("source_hash_overrides", {}))
    graph = {}
    incoming: dict[str, list[str]] = {}
    for row in proof_rows:
        name = row["name"]
        if name in graph:
            raise RuntimeError("DUPLICATED_THEOREM_NAME: " + name)
        graph[name] = row
        for dep in json.loads(row["source_theorem_deps_json"]):
            incoming.setdefault(dep, []).append(name)
    duplicate_members: dict[str, dict] = {}
    for group in groups:
        for entry in group["group_member_declarations"]:
            name = entry["name"]
            if name in duplicate_members:
                raise RuntimeError("OVERLAPPING_DUPLICATE_TYPE_GROUP: " + name)
            duplicate_members[name] = group
    if len(duplicate_members) != 77:
        raise RuntimeError("AUDIT_TYPE_GROUP_MEMBER_COUNT_MISMATCH")
    return {
        "modules": modules, "declarations": declarations, "graph": graph,
        "incoming": incoming, "groups": groups, "duplicates": duplicate_members,
        "near": near, "clones": clones, "overlays": overlays,
        "overlay": overlays[-1]
    }


def verify_evidence_files():
    for path, expected in zip(OVERLAY_PATHS, OVERLAY_SHA256S):
        if sha256(path.read_bytes()).hexdigest() != expected:
            raise RuntimeError("REUSE_OVERLAY_EVIDENCE_DRIFT")
    for path, expected in zip(OVERLAY_TYPE_CHECKS, OVERLAY_TYPE_CHECK_SHA256S):
        if sha256(path.read_bytes()).hexdigest() != expected:
            raise RuntimeError("REUSE_OVERLAY_TYPE_CHECK_DRIFT")
    # A pinned overlay may retain its structured native export as supporting
    # evidence. This supplements the registered public-source graph; it does
    # not redefine the historical snapshot or become another counted ledger.
    for path in OVERLAY_PATHS:
        native = json.loads(path.read_text()).get("native_export_evidence")
        if native:
            artifact = REPO / native["path"]
            if not artifact.resolve().is_relative_to(HERE.resolve()):
                raise RuntimeError("INVALID_NATIVE_OVERLAY_EVIDENCE_PATH")
            if sha256(artifact.read_bytes()).hexdigest() != native["sha256"]:
                raise RuntimeError("NATIVE_OVERLAY_EVIDENCE_DRIFT")
    for name, pinned_hash in BUILD_ENVIRONMENT_SHA256.items():
        path = REPO / "formalization/ueot-core" / name
        actual = sha256(path.read_bytes()).hexdigest()
        if actual != pinned_hash:
            raise RuntimeError(
                f"STALE_LEAN_BUILD_ENVIRONMENT: {name}: {actual} != {pinned_hash}"
            )
    if sha256(LEDGER.read_bytes()).hexdigest() != LEDGER_SHA256:
        raise RuntimeError("CANONICAL_COMPRESSION_LEDGER_CHANGED_RECLASSIFY_FIRST")
    if sha256((HERE / "CLONE_CANDIDATES_68.json").read_bytes()).hexdigest() != CLONE_SHA256:
        raise RuntimeError("AUDIT_CLONE_EVIDENCE_DRIFT")
    for name, expected in EVIDENCE_SHA.items():
        actual = sha256((AUDIT / name).read_bytes()).hexdigest()
        if actual != expected:
            raise RuntimeError(f"AUDIT_EVIDENCE_DRIFT: {name}: {actual} != {expected}")


def live_source_paths() -> set[str]:
    core = REPO / "formalization/ueot-core"
    # Match the FKRG v1 and compiled-census source universe exactly:
    # public root + every recursively present UEOT package module.
    all_files = [core / "UEOT.lean", *(core / "UEOT").rglob("*.lean")]
    return {p.relative_to(REPO).as_posix() for p in all_files if p.is_file()}


def verify_sources(modules: list[dict]):
    overlays = load_overlays()
    overrides = {}
    for overlay in overlays:
        overrides.update(overlay.get("source_hash_overrides", {}))
    recorded = {row["path"] for row in modules}
    current = live_source_paths()
    if len(recorded) != len(modules) or recorded != current:
        added = sorted(current - recorded)
        removed = sorted(recorded - current)
        raise RuntimeError(
            "STALE_AUDIT_SOURCE_SET: " +
            json.dumps({"new_live_modules": added[:16],
                        "missing_archived_modules": removed[:16]})
        )
    mismatches = []
    for row in modules:
        p = REPO / row["path"]
        expected = overrides.get(row["path"], row["content_sha256"])
        if not p.is_file():
            mismatches.append({"path": row["path"], "reason": "MISSING"})
        elif sha256(p.read_bytes()).hexdigest() != expected:
            mismatches.append({"path": row["path"], "reason": "SOURCE_CHANGED"})
    if mismatches:
        raise RuntimeError("STALE_AUDIT_SOURCE: "+json.dumps(mismatches[:12]))
    return len(modules)


def load(*, verify_source=True):
    verify_evidence_files()
    data = _parse_data()
    if verify_source:
        verify_sources(data["modules"])
    return data


def role(name: str):
    if name.startswith("UEOT.V3.Compression.TheoryCompletion.MinCore."):
        return "UNCOUNTED_MINCORE_BOUNDARY"
    if name == DUPLICATED_TV_HELPER:
        return "LOW_RISK_DUPLICATE_HELPER_IMPLEMENTATION"
    if name == CANONICAL_TV_HELPER:
        return "PREFERRED_TV_HELPER_IMPLEMENTATION"
    return ROLES.get(name, "NO_TRIAGE_CLASSIFICATION")


def explain(data: dict, name: str) -> dict:
    row = data["graph"].get(name)
    if not row:
        raise RuntimeError(
            "UNKNOWN_PUBLIC_SOURCE_THEOREM: no exact fully-qualified match; "
            "use FKRG v1 find/show and confirm in Lean"
        )
    group = data["duplicates"].get(name)
    peers = []
    direct_group_edges = []
    if group:
        peers = [x for x in group["group_member_declarations"] if x["name"] != name]
        direct_group_edges = group["verified_direct_proof_dep_edges"]
    dependents = data["incoming"].get(name, [])
    near = [x for x in data["near"] if name in (x["a"], x["b"])]
    return {
        "symbol": name, "origin": row["source_origin"],
        "file": row["path"], "line": int(row["line"]), "area": row["area"],
        "role": (row.get("overlay_scientific_role") or role(name))
                if role(name) == "NO_TRIAGE_CLASSIFICATION" else role(name),
        "direct_existing_source_theorem_uses": json.loads(row["source_theorem_deps_json"]),
        "direct_source_theorem_user_count": len(dependents),
        "direct_source_theorem_users": sorted(dependents)[:50],
        "type_relation": "LEANTYPE_DEF_EQ_VERIFIED_SNAPSHOT_40_PAIRS" if group else "NO_TYPE_EQUIVALENCE_CERTIFICATE",
        "definitionally_equal_type_peers": peers,
        "equal_type_group_direct_proof_edges": direct_group_edges,
        "near_type_heuristic_candidates_not_defeq": [
            {"other": x["b"] if x["a"] == name else x["a"],
             "score": x["score"]} for x in near
        ],
        "caution": "Lean type identity is a 40/40 pinned compilation result; "
                   "API relevance, hypotheses of unrelated results and "
                   "scientific independence require additional review."
    }


def search(data: dict, query: str, limit: int):
    parts = [x.lower() for x in re.findall(r"[A-Za-z0-9_]+", query) if len(x) > 1]
    if not parts:
        raise RuntimeError("EMPTY_SEARCH_QUERY")
    scores = []
    for name, row in data["graph"].items():
        hay = (name + " " + row["path"]).lower()
        base = name.rsplit(".", 1)[-1].lower()
        score = sum((12 if part == base else 5 if part in base else 2 if part in hay else 0)
                    for part in parts)
        if score:
            scores.append((score, name))
    scores.sort(key=lambda item: (-item[0], item[1]))
    return [{"score": score, "symbol": n, "file": data["graph"][n]["path"],
             "role": (data["graph"][n].get("overlay_scientific_role") or role(n))
                     if role(n) == "NO_TRIAGE_CLASSIFICATION" else role(n),
             "has_equal_type_peers": n in data["duplicates"]}
            for score, n in scores[:limit]]


def clone_candidates(data: dict, threshold: int):
    rows = [x for x in data["clones"] if int(x["equal_nonblank_code_lines"]) >= threshold]
    return {
        "count": len(rows),
        "threshold_nonblank_code_lines": threshold,
        "entries": rows,
        "not_a_proof": "Equal source spans do not imply identical theorem type or safe refactoring"
    }


def status(data: dict):
    overlays = data["overlays"]
    return {
        "schema": SCHEMA,
        "base_snapshot_source_commit": SOURCE_BASELINE,
        "overlay_source_checkpoints": [x["source_checkpoint"] for x in overlays],
        "latest_overlay_source_checkpoint": overlays[-1]["source_checkpoint"],
        "overlay_count": len(overlays),
        "module_source_hashes_verified": len(data["modules"]),
        "bundled_modules": len(data["modules"]),
        "ueot_maintained_modules": sum(row["source_origin"] == "UEOT_MAINTAINED"
                                       for row in data["modules"]),
        "vendor_modules": sum(row["source_origin"] == "VENDORED_ADAPTED_UPSTREAM"
                              for row in data["modules"]),
        "public_source_theorems_with_direct_proof_graph": len(data["graph"]),
        "overlay_public_theorems": sum(len(x["public_theorems"]) for x in overlays),
        "overlay_registered_direct_edges": sum(
            x["proof_dependency_certification"]["registered_direct_edges"] for x in overlays),
        "overlay_historical_public_repairs": sum(
            len(x.get("historical_public_repairs", [])) for x in overlays),
        "overlay_existing_registered_direct_edge_repairs": sum(
            x.get("existing_proof_dependency_repair_certification", {}).get(
                "added_registered_direct_edges", 0) for x in overlays),
        "verified_equal_type_groups": len(data["groups"]),
        "equal_type_statement_names": len(data["duplicates"]),
        "overlay_cross_snapshot_defeq_matches": sum(
            x["type_distinctness"]["definitionally_equal_matches"] for x in overlays),
        "near_type_not_defeq_candidate_pairs": len(data["near"]),
        "overlay_lexical_reuse_candidates": sum(
            x["lexical_pr_preflight"]["new_theorems_with_lexical_reuse_candidates"]
            for x in overlays),
        "crossfile_exact_code_clone_candidates": len(data["clones"]),
        "source_of_truth": "immutable 2026-10-10 Lean proof snapshot plus governed pinned MINCORE, calibrated-defect, defect-gauge, finite-horizon-risk, statistical-risk, deployment-joint, support-viability, registered-interfaces and longterm-control-statistics overlays, Lean kernel, and canonical Core/Compression ledgers",
        "scientific_closure": "NOT_ESTABLISHED"
    }


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--json", action="store_true", help="machine-readable output")
    sub = cli.add_subparsers(dest="command", required=True)
    sub.add_parser("status")
    p = sub.add_parser("show"); p.add_argument("symbol")
    p = sub.add_parser("search"); p.add_argument("words"); p.add_argument("--limit", type=int, default=15)
    p = sub.add_parser("clones"); p.add_argument("--min-lines", type=int, default=15)
    options = cli.parse_args()
    if options.command == "search" and not (1 <= options.limit <= 100):
        raise RuntimeError("INVALID_SEARCH_LIMIT")
    if options.command == "clones" and options.min_lines < 8:
        raise RuntimeError("CLONE_MIN_LINES_AT_LEAST_8")
    data = load()
    if options.command == "status":
        result = status(data)
    elif options.command == "show":
        result = explain(data, options.symbol)
    elif options.command == "search":
        result = search(data, options.words, options.limit)
    else:
        result = clone_candidates(data, options.min_lines)
    if options.json:
        print(json.dumps(result, ensure_ascii=False, indent=2))
    elif options.command == "search":
        for item in result:
            print(f"{item['score']:2d} {item['symbol']} "
                  f"[{item['role']}] {item['file']}")
        print(f"MATCHES {len(result)}: SOURCE_DISCOVERY_NOT_PROOF_EQUIVALENCE")
    elif options.command == "clones":
        for row in result["entries"]:
            print(f"{row['equal_nonblank_code_lines']} code lines"
                  f" {row['file_a']}:{row['start_line_a']}"
                  f" <-> {row['file_b']}:{row['start_line_b']}")
        print(f"CLONES {result['count']}: NOT_PROOF_EQUIVALENCE")
    else:
        print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError, ValueError, KeyError, json.JSONDecodeError) as exc:
        print("FKRG_REUSE_ERROR", exc, file=sys.stderr)
        sys.exit(2)
