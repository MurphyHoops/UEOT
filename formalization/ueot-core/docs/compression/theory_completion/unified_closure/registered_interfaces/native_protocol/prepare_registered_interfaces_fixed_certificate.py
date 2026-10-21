#!/usr/bin/env python3
"""One-off scratch preparation after an observed exit-zero native export.

Writes an unregistered candidate and a fixed-edge verifier, never a PASS ledger.
The caller retains the real exporter process status/log and must compile the
fixed verifier before the candidate can be registered by the existing navigator.
"""
from __future__ import annotations

import argparse
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

import prepare_registered_interfaces_export as export_helper

PREFIX = "formalization/ueot-core/docs/compression/theory_completion/knowledge/reuse/"
VERIFIER = "VERIFY_REGISTERED_INTERFACES_OVERLAY_TYPES.lean"


def existing_reuse(repo):
    path = repo / PREFIX / "fkrg_reuse.py"
    spec = importlib.util.spec_from_file_location("registered_interfaces_fixed_existing", path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module, module.load(verify_source=False)


def existing_dependency_repairs(previous, native, registered, native_by_name, repo):
    """Validate the actual narrow scan against the immutable previous graph.

    The scan determines the complete list of callers; this function does not
    fabricate a singleton p_ref_03 result. Prior edges are exact graph inputs.
    """
    repair_names = {row["name"] for row in export_helper.HISTORICAL_PUBLIC_REPAIRS}
    scan = native.get("historical_repair_incoming_scan", {})
    targets = scan.get("historical_public_repair_targets")
    if (scan.get("registered_theorems_scanned") != len(previous["graph"]) or
            not isinstance(targets, list) or len(targets) != len(set(targets)) or
            set(targets) != repair_names):
        raise RuntimeError("HISTORICAL_REPAIR_NARROW_SCAN_SCOPE_MISMATCH")
    rows = scan.get("incoming_rows")
    if not isinstance(rows, list):
        raise RuntimeError("MISSING_HISTORICAL_REPAIR_INCOMING_ROWS")
    modules = {row["path"]: row for row in previous["modules"]}
    seen, repairs = set(), []
    for row in rows:
        name = row.get("name")
        if name not in previous["graph"] or name in seen:
            raise RuntimeError("INVALID_EXISTING_DEPENDENCY_REPAIR_SOURCE")
        seen.add(name)
        old = previous["graph"][name]
        prior = json.loads(old["source_theorem_deps_json"])
        constants = row.get("direct_constants")
        hits = row.get("historical_repair_deps")
        actual = row.get("actual_source_theorem_deps")
        for values in (prior, constants, hits, actual):
            if (not isinstance(values, list) or not all(isinstance(x, str) for x in values)
                    or len(values) != len(set(values))):
                raise RuntimeError("INVALID_EXISTING_DEPENDENCY_REPAIR_NAME_LIST")
        if (not hits or set(hits) != set(constants) & repair_names or
                set(prior) & set(hits) or not set(prior) <= set(previous["graph"])):
            raise RuntimeError("INVALID_HISTORICAL_REPAIR_DIRECT_HITS")
        if (set(actual) != (set(constants) & registered) - {name} or
                set(actual) != set(prior) | set(hits)):
            raise RuntimeError("EXISTING_PROOF_DEPENDENCY_REPAIR_IS_NOT_EXACT_ADDITIVE_DELTA")
        path = old["path"]
        if path not in modules or row.get("source_module") != modules[path]["module"]:
            raise RuntimeError("EXISTING_PROOF_DEPENDENCY_REPAIR_OWNER_MISMATCH")
        if name in native_by_name:
            for key in ("source_module", "direct_constants"):
                if row[key] != native_by_name[name][key]:
                    raise RuntimeError("NARROW_SCAN_AND_FULL_NATIVE_RECORD_DISAGREE")
        repairs.append({
            "name": name, "path": path, "line": int(old["line"]),
            "source_module": row["source_module"],
            "content_sha256": sha256((repo / path).read_bytes()).hexdigest(),
            "prior_source_theorem_deps": sorted(prior),
            "added_source_theorem_deps": sorted(hits),
            "actual_source_theorem_deps": sorted(actual),
            "evidence_kind": "ACTUAL_REGISTERED_PROOF_VALUE_DIRECT_CONSTANT_NARROW_SCAN",
        })
    if "UEOT.V3.FreeInformationValue.p_ref_03" not in seen:
        raise RuntimeError("KNOWN_HISTORICAL_HELPER_USE_NOT_OBSERVED_IN_NATIVE_PROOF")
    return sorted(repairs, key=lambda row: row["name"])


def prepare(repo, preflight_path, native_path, exporter_path, output):
    repo, output = repo.resolve(), output.resolve()
    if output.is_relative_to(repo):
        raise RuntimeError("TEMPORARY_OUTPUT_MUST_BE_OUTSIDE_REPOSITORY")
    preflight = json.loads(preflight_path.read_text())
    native = json.loads(native_path.read_text())
    reuse, previous = existing_reuse(repo)
    if len(previous["modules"]) != 659 or len(previous["graph"]) != 4094:
        raise RuntimeError("EXPECTED_UNREGISTERED_659_MODULE_BASE")
    if len(previous["overlays"]) != 7 or preflight.get("prior_overlay_count") != 7:
        raise RuntimeError("EXPECTED_SEVEN_PRIOR_OVERLAYS")
    if preflight.get("status") != "PENDING_NATIVE_COMPILATION":
        raise RuntimeError("UNEXPECTED_SOURCE_PREFLIGHT_STATE")
    if preflight.get("build_environment_sha256") != reuse.BUILD_ENVIRONMENT_SHA256:
        raise RuntimeError("BUILD_ENVIRONMENT_PREFLIGHT_MISMATCH")
    added_modules = preflight["added_modules"]
    native_modules = preflight["native_audit_modules"]
    historical = preflight["historical_public_repairs"]
    if (len(added_modules) != 7 or len(native_modules) != 8 or
            historical != list(export_helper.HISTORICAL_PUBLIC_REPAIRS)):
        raise RuntimeError("EXPLICIT_HISTORICAL_REPAIR_OR_MODULE_SCOPE_MISMATCH")
    expected_audit_modules = {row["module"] for row in added_modules} | {
        row["module"] for row in historical}
    if ({row["module"] for row in native_modules} != expected_audit_modules or
            len({row["path"] for row in native_modules}) != 8):
        raise RuntimeError("NATIVE_AUDIT_MODULE_SET_MISMATCH")
    for row in native_modules:
        if sha256((repo / row["path"]).read_bytes()).hexdigest() != row["content_sha256"]:
            raise RuntimeError("SOURCE_DRIFT_SINCE_NATIVE_PREFLIGHT: " + row["path"])
    for path, expected in preflight["source_hash_overrides"].items():
        if sha256((repo / path).read_bytes()).hexdigest() != expected:
            raise RuntimeError("ROOT_IMPORT_DRIFT_SINCE_NATIVE_PREFLIGHT")
    if sha256(exporter_path.read_bytes()).hexdigest() != preflight["exporter_sha256"]:
        raise RuntimeError("EXPORTER_DRIFT_SINCE_PREFLIGHT")
    if native.get("schema") != "REGISTERED_INTERFACES_NATIVE_EXPORT_V1":
        raise RuntimeError("UNEXPECTED_NATIVE_SCHEMA")
    candidates = {row["name"]: row for row in preflight["public_source_candidates"]}
    new_names = {row["name"] for row in preflight["new_public_source_candidates"]}
    repair_names = {row["name"] for row in historical}
    if (len(new_names) != 52 or len(repair_names) != 1 or new_names & repair_names or
            set(candidates) != new_names | repair_names or
            len(preflight["public_source_candidates"]) != 53):
        raise RuntimeError("EXPECTED_52_NEW_AND_ONE_HISTORICAL_PUBLIC_REGISTRATION")
    rows = native.get("public_source_theorems", [])
    names = [row["name"] for row in rows]
    if len(names) != len(set(names)) or set(names) != set(candidates):
        raise RuntimeError("NATIVE_PUBLIC_CANDIDATE_SET_MISMATCH")
    n, prior_count = len(rows), len(previous["graph"])
    expected_counts = {"registered_prior_theorems": prior_count,
                       "new_source_public_theorem_count": len(new_names),
                       "historical_public_repair_count": len(repair_names),
                       "overlay_public_registration_count": n,
                       "cross_isDefEq_comparisons": n * prior_count,
                       "new_source_to_registered_isDefEq_comparisons": len(new_names) * prior_count,
                       "historical_repair_to_registered_isDefEq_comparisons": len(repair_names) * prior_count,
                       "internal_isDefEq_comparisons": n * (n - 1) // 2,
                       "new_source_internal_isDefEq_comparisons": len(new_names) * (len(new_names) - 1) // 2,
                       "new_source_to_historical_repair_isDefEq_comparisons": len(new_names) * len(repair_names),
                       "historical_repair_internal_isDefEq_comparisons": len(repair_names) * (len(repair_names) - 1) // 2}
    if any(native.get(key) != value for key, value in expected_counts.items()):
        raise RuntimeError("NATIVE_COMPARISON_COUNT_MISMATCH")
    if native.get("collisions") != []:
        raise RuntimeError("NATIVE_TYPE_COLLISIONS_REQUIRE_REVIEW")
    registered = set(previous["graph"]) | set(names)
    modules = {row["module"] for row in native_modules}
    if native.get("native_audit_modules") != [row["module"] for row in native_modules]:
        raise RuntimeError("EXPECTED_SEVEN_NEW_PLUS_ONE_EXISTING_NATIVE_MODULE")
    scope = native.get("all_native_theorem_constants", [])
    scope_names = set()
    private_count = 0
    for row in scope:
        name = row.get("name")
        if not isinstance(name, str) or not name or name in scope_names:
            raise RuntimeError("INVALID_NATIVE_SCOPE_NAME")
        scope_names.add(name)
        if row.get("source_module") not in modules or type(row.get("is_private")) is not bool:
            raise RuntimeError("INVALID_NATIVE_MODULE_SCOPE")
        axioms = row.get("axioms")
        if not isinstance(axioms, list) or not set(axioms) <= {"propext", "Classical.choice", "Quot.sound"}:
            raise RuntimeError("INVALID_NATIVE_AXIOM_SCOPE")
        if not isinstance(row.get("type"), str) or not isinstance(row.get("level_parameters"), list):
            raise RuntimeError("INVALID_ALL_NATIVE_TYPE_PRESENTATION")
        if not row["type"] or not all(isinstance(level, str) for level in row["level_parameters"]):
            raise RuntimeError("INVALID_ALL_NATIVE_LEVEL_PARAMETERS")
        constants = row.get("direct_constants")
        theorem_constants = row.get("direct_theorem_constants")
        if (not isinstance(constants, list) or not isinstance(theorem_constants, list)
                or len(constants) != len(set(constants))
                or len(theorem_constants) != len(set(theorem_constants))
                or not all(isinstance(name, str) for name in constants + theorem_constants)
                or not set(theorem_constants) <= set(constants)):
            raise RuntimeError("INVALID_ALL_NATIVE_DIRECT_CONSTANTS")
        private_count += row["is_private"]
    if not set(names) <= scope_names:
        raise RuntimeError("PUBLIC_THEOREM_MISSING_FROM_NATIVE_AXIOM_SCOPE")
    if {row["source_module"] for row in scope} != modules:
        raise RuntimeError("EMPTY_SOURCE_MODULE_NATIVE_SCOPE")
    public = []
    for row in rows:
        candidate = candidates[row["name"]]
        expected_kind = "historical_public_repair" if row["name"] in repair_names else "new_source_public"
        if row.get("registration_kind") != expected_kind or candidate.get("registration_kind") != expected_kind:
            raise RuntimeError("PUBLIC_REGISTRATION_KIND_MISMATCH")
        if row["source_module"] != candidate["module"]:
            raise RuntimeError("NATIVE_OWNER_MISMATCH")
        constants = row["direct_constants"]
        deps = row["source_theorem_deps"]
        if (not isinstance(constants, list) or len(constants) != len(set(constants))
                or len(deps) != len(set(deps))
                or set(deps) != (set(constants) & registered) - {row["name"]}):
            raise RuntimeError("INVALID_NATIVE_REGISTERED_EDGE_FILTER")
        if not isinstance(row.get("type"), str) or not isinstance(row.get("level_parameters"), list):
            raise RuntimeError("INVALID_NATIVE_TYPE_PRESENTATION")
        public.append({"name": row["name"], "path": candidate["path"],
                       "line": candidate["line"], "source_origin": "UEOT_MAINTAINED",
                       "registration_kind": expected_kind,
                       "source_module": row["source_module"],
                       "source_theorem_deps": sorted(deps)})
    native_by_name = {row["name"]: row for row in scope}
    if any(native_by_name[name]["is_private"] for name in names):
        raise RuntimeError("PUBLIC_CANDIDATE_IS_NATIVE_PRIVATE")
    for row in rows:
        all_native = native_by_name[row["name"]]
        for field in ("source_module", "type", "level_parameters", "direct_constants"):
            if row[field] != all_native[field]:
                raise RuntimeError("PUBLIC_AND_ALL_NATIVE_RECORD_DISAGREE: " + row["name"])
    repairs = existing_dependency_repairs(previous, native, registered, native_by_name, repo)
    entries = []
    for row in public:
        deps = ", ".join("`" + name for name in row["source_theorem_deps"])
        entries.append(f"    (`{row['name']}, [{deps}]),")
    fixed = exporter_path.read_text()
    anchor = "  let mut nativeScope : Array Json := #[]"
    if fixed.count(anchor) != 1:
        raise RuntimeError("UNRECOGNIZED_NATIVE_EXPORTER_INSERTION_POINT")
    fixed = fixed.replace(anchor,
        "  let expectedEdges : Array (Name × List Name) := #[\n" +
        "\n".join(entries) + "\n  ]\n" + anchor)
    anchor = "    let deps := constants.filter fun dep => dep != name && allRegistered.contains dep"
    if fixed.count(anchor) != 1:
        raise RuntimeError("UNRECOGNIZED_NATIVE_DEPENDENCY_POINT")
    fixed = fixed.replace(anchor, anchor + "\n" +
        "    let some (_, expected) := expectedEdges.find? (fun pair => pair.1 == name)\n" +
        '      | throwError s!"REGISTERED_INTERFACES_EXPECTED_EDGES_MISSING {name}"\n' +
        "    unless deps.length == expected.length && expected.all (fun dep => deps.contains dep) do\n" +
        '      throwError s!"REGISTERED_INTERFACES_FIXED_PROOF_DEPENDENCIES_MISMATCH {name}: actual={deps} expected={expected}"')
    anchor = "  let mut cross := 0"
    fixed = fixed.replace(anchor,
        f"  unless nativeScope.size == {len(scope)} do\n" +
        '    throwError s!"REGISTERED_INTERFACES_NATIVE_THEOREM_SCOPE_DRIFT {nativeScope.size}"\n' + anchor)
    # Replay the whole narrow scan, requiring precisely the observed callers,
    # prior edge lists plus the exact additive repair, without replacing old CSV.
    repair_entries = []
    for row in repairs:
        prior = ", ".join("`" + name for name in row["prior_source_theorem_deps"])
        added = ", ".join("`" + name for name in row["added_source_theorem_deps"])
        repair_entries.append(f"    (`{row['name']}, [{prior}], [{added}]),")
    anchor = "  let mut registeredScanned := 0"
    if fixed.count(anchor) != 1:
        raise RuntimeError("UNRECOGNIZED_HISTORICAL_SCAN_INSERTION_POINT")
    fixed = fixed.replace(anchor,
        "  let expectedExistingRepairs : Array (Name × List Name × List Name) := #[\n" +
        "\n".join(repair_entries) + "\n  ]\n" + anchor)
    anchor = "      let actualDeps := constants.filter fun dep => dep != name && allRegistered.contains dep"
    if fixed.count(anchor) != 1:
        raise RuntimeError("UNRECOGNIZED_HISTORICAL_REPAIR_EDGE_POINT")
    fixed = fixed.replace(anchor, anchor + "\n" +
        "      let some (_, prior, added) := expectedExistingRepairs.find? (fun entry => entry.1 == name)\n" +
        '        | throwError s!"UNEXPECTED_HISTORICAL_REPAIR_CALLER {name}"\n' +
        "      unless hits.length == added.length && added.all (fun dep => hits.contains dep) do\n" +
        '        throwError s!"HISTORICAL_REPAIR_DIRECT_HITS_DRIFT {name}"\n' +
        "      let expectedDeps := prior ++ added\n" +
        "      unless actualDeps.length == expectedDeps.length && expectedDeps.all (fun dep => actualDeps.contains dep) do\n" +
        '        throwError s!"HISTORICAL_REPAIR_PRIOR_PLUS_DELTA_DRIFT {name}"')
    anchor = "  let historicalScan := Json.mkObj ["
    if fixed.count(anchor) != 1:
        raise RuntimeError("UNRECOGNIZED_HISTORICAL_SCAN_COMPLETION_POINT")
    fixed = fixed.replace(anchor,
        "  unless registeredScanned == 4094 && historicalIncoming.size == expectedExistingRepairs.size do\n" +
        '    throwError "HISTORICAL_REPAIR_COMPLETE_NARROW_SCAN_DRIFT"\n' + anchor)
    output.mkdir(parents=True, exist_ok=True)
    (output / VERIFIER).write_text(fixed)
    certificate_sha = sha256(fixed.encode()).hexdigest()
    edges = [{"source": row["name"], "target": dep} for row in public
             for dep in row["source_theorem_deps"]]
    candidate = {
        "schema": "FKRG_REUSE_OVERLAY_V1", "overlay_id": "REGISTERED_INTERFACES_REUSE_OVERLAY_V1",
        "source_checkpoint": "worktree-sha256:" + preflight["source_tree_sha256"],
        "source_checkpoint_kind": "FROZEN_SOURCE_CONTENT_BEFORE_GIT_COMMIT",
        "baseline_ref": preflight["baseline_ref"],
        "base_snapshot_modules": 659, "prior_overlay": preflight["prior_overlay"],
        "source_hash_overrides": preflight["source_hash_overrides"],
        "added_modules": preflight["added_modules"], "public_theorems": public,
        "native_audit_modules": native_modules,
        "historical_public_repairs": historical,
        "existing_proof_dependency_repairs": repairs,
        "type_distinctness": {"verifier": PREFIX + VERIFIER, "new_theorems": n,
                              **expected_counts, "definitionally_equal_matches": 0,
                              "counting_note": "new_theorems counts newly registered nodes: 52 new source declarations and one unchanged historical repair, not 53 new mathematical proofs.",
                              "protocol": "Meta.isDefEq on raw stored compiled types, with each comparison in fresh liftTermElabM; universe parameters retain their stored names",
                              "status": "PENDING_FIXED_CERTIFICATE_COMPILATION"},
        "proof_dependency_certification": {"verifier": PREFIX + VERIFIER,
            "measure": "Lean .thmInfo.value.getUsedConstants restricted to immutable base, seven prior overlays and this overlay's public source theorem nodes",
            "registered_direct_edges": len(edges), "edges": edges,
            "status": "PENDING_FIXED_CERTIFICATE_COMPILATION"},
        "existing_proof_dependency_repair_certification": {
            "verifier": PREFIX + VERIFIER,
            "status": "PENDING_FIXED_CERTIFICATE_COMPILATION",
            "registered_theorems_scanned": prior_count,
            "historical_public_repair_targets": sorted(repair_names),
            "repaired_existing_nodes": len(repairs),
            "added_registered_direct_edges": sum(len(row["added_source_theorem_deps"]) for row in repairs),
            "measure": "Every prior registered proof.value is scanned only for the historical target. Every positive caller is exported; fixed replay verifies exact prior edges plus observed additive delta. Frozen graph files remain unchanged.",
        },
        "historical_public_repair_certification": {
            "verifier": PREFIX + VERIFIER,
            "status": "PENDING_FIXED_CERTIFICATE_COMPILATION",
            "historical_registered_base": prior_count,
            "new_source_public_theorems": len(new_names),
            "historical_public_repairs": len(repair_names),
            "frozen_source_parser_modified": False,
            "historical_csv_modified": False,
            "measure": "Explicit exact name, unchanged source hash at actual base and candidate, native public theorem ownership/type/axiom confirmation, 4094 historical comparisons and 52 new-versus-repair comparisons.",
        },
        "native_axiom_census": {"physical_source_modules": len(modules),
            "new_physical_source_modules": len(added_modules),
            "historical_physical_source_modules": len(modules) - len(added_modules),
            "theorem_constants": len(scope), "private_theorem_constants": private_count,
            "confirmed_public_source_candidates": n,
            "other_native_public_constants": len(scope) - private_count - n,
            "scope": "Every theorem constant owned by seven new modules and the unchanged historical repair module, including private and generated constants. Other native public constants include existing registered declarations and are not automatically generated declarations.",
            "standard_axioms": ["propext", "Classical.choice", "Quot.sound"],
            "status": "PENDING_FIXED_CERTIFICATE_COMPILATION"},
        "scientific_role": "UNCOUNTED_REGISTERED_JOINT_AND_FINITE_CARRIER_BRIDGES",
        "counted_core_impact": "NONE", "scientific_closure": "NOT_ESTABLISHED",
        "pending_verifier_sha256": certificate_sha,
    }
    (output / "overlay_candidate.json").write_text(json.dumps(candidate, ensure_ascii=False, indent=2) + "\n")
    (output / "REGISTERED_INTERFACES_NATIVE_V1.json").write_text(json.dumps(native, ensure_ascii=False, indent=2) + "\n")
    return {"status": "PENDING_FIXED_CERTIFICATE_COMPILATION", "public_theorems": n,
            "new_source_public_theorems": len(new_names), "historical_public_repairs": len(repair_names),
            "existing_proof_dependency_repairs": len(repairs),
            "registered_direct_edges": len(edges), "native_theorem_constants": len(scope),
            "private_theorem_constants": private_count, "verifier_sha256": certificate_sha}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("repo", "preflight", "native", "exporter", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(prepare(args.repo.resolve(), args.preflight, args.native,
                             args.exporter, args.output), indent=2))
