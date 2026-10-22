#!/usr/bin/env python3
"""Read-only checks of imported actual path-realization build/native evidence.

This does not run Lean, Lake, native protocol entrypoints, or registration.
It rederives identities, complete exports, fixed proof-edge source, and protocol
archive bytes from immutable source and the actual supplied raw records.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys
import types

if not __debug__:
    raise RuntimeError("Assertions are required")

CORE = "formalization/ueot-core/"
PACKET = CORE + "docs/compression/theory_completion/unified_closure/"
REUSE = CORE + "docs/compression/theory_completion/knowledge/reuse/"
OLD = PACKET + "longterm_control_statistics_v1/native_protocol/"
NEW = PACKET + "path_realization_v1/native_protocol/"
NAME = "PATH_REALIZATION"


def digest(data):
    return sha256(data).hexdigest()


def unique(rows, key):
    result = {row[key]: row for row in rows}
    assert len(result) == len(rows), ("duplicate", key)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for key in ("repo", "manifest", "build", "native", "output"):
        parser.add_argument("--" + key, type=Path, required=True)
    parser.add_argument("--expected-manifest-sha256", required=True)
    args = parser.parse_args()
    manifest_sha = args.expected_manifest_sha256
    assert re.fullmatch("[0-9a-f]{64}", manifest_sha)
    repo, manifest, build_dir, native_dir, output = (
        args.repo.resolve(), args.manifest.resolve(), args.build.resolve(),
        args.native.resolve(), args.output.resolve())
    assert not output.exists(), "Preserve previous audit attempts"
    reads, checks = {}, []

    def read(path):
        path = Path(path)
        assert path.is_file() and not path.is_symlink(), ("missing/symlink", str(path))
        if path not in reads:
            reads[path] = path.read_bytes()
        return reads[path]

    def obj(path):
        return json.loads(read(path))

    def git(*arguments):
        return subprocess.check_output(["git", *arguments], cwd=repo)

    def module(name, path):
        read(path)
        spec = importlib.util.spec_from_file_location(name, path)
        imported = importlib.util.module_from_spec(spec)
        sys.modules[name] = imported
        spec.loader.exec_module(imported)
        return imported

    def passed(label):
        checks.append(label)

    frozen = obj(manifest)
    public_count, hint_count = frozen["new_public"], frozen["lexical_hinted"]
    assert type(public_count) is int and public_count > 0
    assert type(hint_count) is int and 0 <= hint_count <= public_count
    assert digest(read(manifest)) == manifest_sha
    assert frozen["state"] == "FROZEN_SOURCE_ONLY_ACTUAL_BUILD_AND_NATIVE_PENDING"
    base = frozen["baseline_ref"]
    assert git("rev-parse", "--verify", base + "^{commit}").decode().strip() == base
    assert (frozen["prior_modules"], frozen["prior_registered_public"],
            frozen["prior_overlays"], frozen["complete_modules"],
            frozen["new_public"], frozen["lexical_hinted"]) == (684, 4272, 10, 691, public_count, hint_count)
    for row in frozen["protocol_files"] + frozen["immutable_drivers"]:
        assert digest(read(repo / row["path"])) == row["sha256"]
    for row in frozen["immutable_drivers"]:
        assert read(repo / row["path"]) == git("show", base + ":" + row["path"])
    core = repo / CORE
    paths = [core / "UEOT.lean", *(core / "UEOT").rglob("*.lean")]
    by_module = {p.relative_to(core).with_suffix("").as_posix().replace("/", "."): p
                 for p in paths if p.is_file()}
    assert len(by_module) == len(paths) == 691
    fingerprint, source_records = sha256(), []
    for name, path in sorted(by_module.items()):
        content = read(path)
        fingerprint.update(name.encode() + b"\0" + content + b"\0")
        source_records.append({"module": name, "path": path.relative_to(repo).as_posix(),
                               "bytes": len(content), "sha256": digest(content)})
    assert fingerprint.hexdigest() == frozen["source_tree_sha256"]
    passed("Frozen manifest, exact base, protocol hashes, complete current source bytes")

    build_path = build_dir / "FULL_BUILD_RECEIPT.json"
    build = obj(build_path)
    assert (build["schema"], build["state"], build["baseline_ref"]) == (
        "PATH_REALIZATION_ACTUAL_FULL_BUILD_V1", "PASS", base)
    identity = build["identity"]
    assert identity["module_count"] == 691
    assert identity["source_tree_sha256"] == frozen["source_tree_sha256"]
    assert identity["source_files"] == source_records
    identity_path = repo / PACKET / "registered_interfaces/native_protocol/build_identity.py"
    assert read(identity_path) == git("show", base + ":" + identity_path.relative_to(repo).as_posix())
    assert build["identity_helper_sha256"] == digest(read(identity_path))
    identity_code = module("independent_identity_constants", identity_path)
    assert identity["toolchain"] == identity_code.TOOLCHAIN
    assert identity["environment_files"] == [
        {"path": CORE + key, "sha256": expected}
        for key, expected in sorted(identity_code.ENVIRONMENT_SHA256.items())]
    for row in identity["environment_files"]:
        assert digest(read(repo / row["path"])) == row["sha256"]
    assert identity["dependencies"] == [
        {"name": key, "manifest_rev": revision, "actual_head": revision,
         "clean": True, "status_porcelain": ""}
        for key, revision in sorted(identity_code.DEPENDENCY_REVISIONS.items())]
    tools = identity["runtime_tools"]
    assert set(tools) == {"lake", "lean"}
    assert Path(tools["lake"]["executable"]).parent == Path(tools["lean"]["executable"]).parent
    for name, row in tools.items():
        assert Path(row["executable"]).name == name and re.fullmatch("[0-9a-f]{64}", row["sha256"])
        assert "4.33.1" in row["version"]
    build_log = read(build_dir / "full-build.log")
    assert build["full_build"]["exit_code"] == 0
    assert build["full_build"]["command"] == [tools["lake"]["executable"], "build", "UEOT"]
    assert build["full_build"]["log_name"] == "full-build.log"
    assert digest(build_log) == build["full_build"]["log_sha256"]
    assert b"Build completed successfully" in build_log
    assert build["driver_sha256"] == digest(read(repo / NEW / "full_build.py"))
    passed("Actual full-build command, exit, raw log, pinned source/environment/runtime receipt")

    def check_protocol(kind, location):
        context = obj(location / "PROTOCOL_ADAPTATION.json")
        assert context["schema"] == "PATH_REALIZATION_PROTOCOL_ADAPTATION_V1"
        assert context["kind"] == kind and context["baseline_ref"] == base
        assert context["frozen_inputs_sha256"] == manifest_sha
        assert context["source_tree_sha256"] == frozen["source_tree_sha256"]
        assert read(location / "FROZEN_INPUTS.json") == read(manifest)
        assert read(location / "protocol_adapter.py") == read(repo / NEW / "protocol_adapter.py")
        assert digest(read(location / "protocol_adapter.py")) == context["adapter_sha256"]
        wrapper = NEW + kind + ".py"
        original = OLD + kind + ".py"
        assert context["wrapper"] == {"path": wrapper, "sha256": digest(read(repo / wrapper))}
        assert context["immutable_driver"] == {"path": original, "sha256": digest(read(repo / original))}
        assert read(location / (kind + ".py")) == read(repo / wrapper)
        immutable = read(location / ("immutable_" + kind + ".py"))
        assert immutable == read(repo / original) == git("show", base + ":" + original)
        replacements = [('"LONGTERM_ACTUAL_FULL_BUILD_V1"', '"PATH_REALIZATION_ACTUAL_FULL_BUILD_V1"')]
        if kind == "integration_native":
            replacements.extend([
                ('NAME = "LONGTERM_CONTROL_STATISTICS"', 'NAME = "PATH_REALIZATION"'),
                ('PRIOR_MODULES, PRIOR_THEOREMS, PRIOR_OVERLAYS = 666, 4147, 8',
                 'PRIOR_MODULES, PRIOR_THEOREMS, PRIOR_OVERLAYS = 684, 4272, 10'),
                ('"UNCOUNTED_SAME_SOURCE_LONGTERM_POLICY_AND_ROWWISE_SISC"',
                 '"UNCOUNTED_SAME_SOURCE_PATH_REALIZATION"')])
        assert context["substitutions"] == [
            {"old": old, "new": new, "occurrences": 1} for old, new in replacements]
        adapted = immutable.decode()
        for old, new in replacements:
            assert adapted.count(old) == 1
            adapted = adapted.replace(old, new)
        executed = read(location / ("executed_" + kind + ".py"))
        assert executed == adapted.encode()
        assert digest(executed) == context["executed_source_sha256"]

    check_protocol("full_build", build_dir)
    check_protocol("integration_native", native_dir)
    passed("Exact original, wrapper, adapter, frozen manifest and adapted executed protocol archives")

    pre = obj(native_dir / "SOURCE_PREFLIGHT.json")
    status = obj(native_dir / "STATUS.json")
    native = obj(native_dir / (NAME + "_NATIVE_V1.json"))
    first = obj(native_dir / "observed_first_native.json")
    overlay = obj(native_dir / (NAME + "_REUSE_OVERLAY_V1.json"))
    assert pre["status"] == "PENDING_ACTUAL_NATIVE_EXECUTION"
    assert status["state"] == "PASS_PENDING_INDEPENDENT_REVIEW_AND_REGISTRATION"
    assert pre["baseline_ref"] == status["baseline_ref"] == overlay["baseline_ref"] == base
    assert pre["source_tree_sha256"] == frozen["source_tree_sha256"]
    assert (pre["base_snapshot_modules"], pre["complete_source_modules"],
            pre["registered_prior_theorems"], pre["prior_overlay_count"]) == (684, 691, 4272, 10)
    assert pre["integration_driver_sha256"] == digest(read(repo / NEW / "integration_native.py"))
    assert status["build_receipt_sha256"] == digest(read(build_path))
    for row in pre["immutable_protocol_helpers"]:
        assert digest(read(repo / row["path"])) == row["sha256"]
        assert read(repo / row["path"]) == git("show", base + ":" + row["path"])

    declaration_parser = module("independent_base_declaration_parser", repo / REUSE / "pr_preflight.py")
    baseline = declaration_parser.corpus(repo, base)
    assert len(baseline) == 684
    current = {row["path"]: read(repo / row["path"]).decode() for row in source_records}
    assert set(baseline) <= set(current)
    root = CORE + "UEOT/V3/Compression/TheoryCompletion.lean"
    assert {path for path in baseline if current[path] != baseline[path]} == {root}
    old_lines, new_lines = baseline[root].splitlines(), current[root].splitlines()
    assert [line for line in new_lines if line in old_lines] == old_lines
    assert all(line.startswith("import UEOT.V3.Compression.TheoryCompletion.")
               for line in new_lines if line not in old_lines)
    added_paths = sorted(set(current) - set(baseline))
    new_modules = [path[len(CORE):-5].replace("/", ".") for path in added_paths]
    assert new_modules == frozen["modules"]
    expected_modules = [
        {"module": path[len(CORE):-5].replace("/", "."), "path": path,
         "content_sha256": digest(read(repo / path)), "source_origin": "UEOT_MAINTAINED"}
        for path in added_paths]
    assert pre["added_modules"] == expected_modules
    baseline_declarations = [row for path, content in baseline.items()
                             for row in declaration_parser.declarations(path, content)]
    declarations = [row for path in added_paths
                    for row in declaration_parser.declarations(path, current[path])]
    declaration_parser.validate_unique(baseline_declarations, "BASE")
    declaration_parser.validate_unique(declarations, "NEW")
    assert sorted(row["symbol"] for row in declarations) == frozen["public_source_names"]
    public = [{"name": row["symbol"], "module": row["path"][len(CORE):-5].replace("/", "."),
               "path": row["path"], "line": row["line"], "source_origin": "UEOT_MAINTAINED",
               "registration_kind": "new_source_public"} for row in declarations]
    assert pre["public_source_candidates"] == public
    hints = [{**row, "reuse_candidates": declaration_parser.candidate_hints(row, baseline_declarations)}
             for row in declarations]
    assert hints == pre["lexical_reuse_hints"] == obj(native_dir / "development_lexical_reuse_hints.json")
    assert sum(bool(row["reuse_candidates"]) for row in hints) == hint_count
    assert pre["source_hash_overrides"] == {root: digest(read(repo / root))}
    passed("Original PENDING preflight, source candidates, unchanged old source, exact seven imports/modules, hints")

    base_consumer_path = REUSE + "fkrg_reuse.py"
    consumer_bytes = git("show", base + ":" + base_consumer_path)
    assert digest(consumer_bytes) == frozen["baseline_consumer_sha256"]
    assert pre["baseline_reuse_consumer"] == {"path": base_consumer_path, "sha256": digest(consumer_bytes)}
    consumer = types.ModuleType("independent_actual_base_registry")
    consumer.__file__ = str(repo / base_consumer_path)
    sys.modules[consumer.__name__] = consumer
    exec(compile(consumer_bytes, consumer.__file__, "exec"), consumer.__dict__)
    previous = consumer.load(verify_source=False)
    assert (len(previous["modules"]), len(previous["graph"]), len(previous["overlays"])) == (684, 4272, 10)
    assert {row["symbol"] for row in baseline_declarations} == set(previous["graph"])
    assert pre["prior_overlay"] == {"path": consumer.OVERLAY_PATHS[-1].relative_to(repo).as_posix(),
                                    "sha256": consumer.OVERLAY_SHA256S[-1]}
    assert digest(read(repo / pre["prior_overlay"]["path"])) == pre["prior_overlay"]["sha256"]
    helper_path = repo / PACKET / "registered_interfaces/native_protocol/prepare_registered_interfaces_export.py"
    helper = module("independent_export_renderer", helper_path)
    assert pre["reused_export_protocol"] == {"path": helper_path.relative_to(repo).as_posix(),
                                            "sha256": digest(read(helper_path))}
    prior_names = [row["name"] for item in previous["overlays"] for row in item["public_theorems"]]
    exporter = helper.render_export(prior_names, public, expected_modules, [])
    exporter = exporter.replace("REGISTERED_INTERFACES", NAME)
    assert exporter.count("registered.length == 4094") == 1
    exporter = exporter.replace("registered.length == 4094", "registered.length == 4272")
    anchor = "newNames.size == 53 && historicalRepairNames.size == 1 && sourceModules.size == 8"
    assert exporter.count(anchor) == 1
    exporter = exporter.replace(anchor, f"newNames.size == {public_count} && historicalRepairNames.size == 0 && sourceModules.size == 7")
    exporter_path = native_dir / (NAME + "_NATIVE_EXPORT.lean")
    assert read(exporter_path) == exporter.encode()
    assert pre["exporter_sha256"] == digest(read(exporter_path))
    passed("Exact immutable predecessor registry and independently regenerated actual Lean exporter")

    results = unique(status["results"], "label")
    assert set(results) == {"native_export", "fixed_verifier"}
    assert native == first
    for label, source_name in (("native_export", NAME + "_NATIVE_EXPORT.lean"),
                               ("fixed_verifier", "VERIFY_" + NAME + "_OVERLAY_TYPES.lean")):
        result, log = results[label], read(native_dir / (label + ".log"))
        assert result["exit_code"] == 0 and result["seconds"] >= 0
        assert result["log_sha256"] == digest(log)
        command = result["command"]
        assert len(command) == 4 and command[:3] == [tools["lake"]["executable"], "env", tools["lean"]["executable"]]
        assert Path(command[3]).name == source_name
        marker = NAME + "_NATIVE_JSON "
        records = [line[len(marker):] for line in log.decode().splitlines() if line.startswith(marker)]
        assert len(records) == 1 and json.loads(records[0]) == native
    assert native["schema"] == NAME + "_NATIVE_EXPORT_V1"
    assert native["native_audit_modules"] == new_modules
    expected_counts = {"registered_prior_theorems": 4272, "new_source_public_theorem_count": public_count,
                       "historical_public_repair_count": 0, "overlay_public_registration_count": public_count,
                       "cross_isDefEq_comparisons": 4272 * public_count,
                       "new_source_to_registered_isDefEq_comparisons": 4272 * public_count,
                       "historical_repair_to_registered_isDefEq_comparisons": 0,
                       "internal_isDefEq_comparisons": public_count * (public_count - 1) // 2,
                       "new_source_internal_isDefEq_comparisons": public_count * (public_count - 1) // 2,
                       "new_source_to_historical_repair_isDefEq_comparisons": 0,
                       "historical_repair_internal_isDefEq_comparisons": 0}
    for key, value in expected_counts.items():
        assert native[key] == value, key
    assert native["collisions"] == []
    assert native["historical_repair_incoming_scan"] == {
        "registered_theorems_scanned": 4272, "historical_public_repair_targets": [], "incoming_rows": []}
    scope = unique(native["all_native_theorem_constants"], "name")
    public_native = unique(native["public_source_theorems"], "name")
    public_by_name = unique(public, "name")
    assert set(public_native) == set(public_by_name) <= set(scope)
    assert {row["source_module"] for row in scope.values()} == set(new_modules)
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    for row in scope.values():
        assert isinstance(row["is_private"], bool) and row["type"]
        assert isinstance(row["level_parameters"], list)
        assert set(row["axioms"]) <= allowed
        assert len(row["direct_constants"]) == len(set(row["direct_constants"]))
        assert set(row["direct_theorem_constants"]) <= set(row["direct_constants"])
    registered_names = set(previous["graph"]) | set(public_native)
    for name, row in public_native.items():
        assert row["source_module"] == public_by_name[name]["module"]
        assert row["registration_kind"] == "new_source_public" and not scope[name]["is_private"]
        for field in ("source_module", "type", "level_parameters", "direct_constants"):
            assert row[field] == scope[name][field]
        assert set(row["source_theorem_deps"]) == (set(row["direct_constants"]) & registered_names) - {name}
        assert len(row["source_theorem_deps"]) == len(set(row["source_theorem_deps"]))
    passed("Both actual native commands/logs, complete JSON equality, all frozen public types, all owners and axioms")

    witness_module = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMemorySafetyWitness"
    witness_endpoint = witness_module + ".physical_safety_premises_independent"
    witness_helpers = ["safe_source_all_times_mass_one", "unsafe_transition_time_one_mass_zero",
                       "unsafe_transition_all_times_mass_zero", "unsafe_initial_time_zero_mass_zero",
                       "unsafe_initial_all_times_mass_zero"]
    private_helper_bindings = []
    assert witness_endpoint in public_native
    endpoint = public_native[witness_endpoint]
    for short_name in witness_helpers:
        matches = [row for row in scope.values()
                   if row["source_module"] == witness_module and row["name"].endswith("." + short_name)]
        assert len(matches) == 1
        row = matches[0]
        assert row["is_private"] is True and row["name"] not in public_native
        assert witness_module + "." + short_name not in public_native
        assert row["name"] in endpoint["direct_constants"]
        assert row["name"] in scope[witness_endpoint]["direct_theorem_constants"]
        assert set(row["axioms"]) <= allowed
        private_helper_bindings.append({"source_name": short_name, "native_name": row["name"],
                                        "is_private": True, "axioms": row["axioms"],
                                        "directly_used_by_public_endpoint": True})
    passed("Revised public safety independence endpoint directly uses all five retained native private mass theorems")

    rows = native["public_source_theorems"]
    entries = ["    (`" + row["name"] + ", [" + ", ".join("`" + d for d in sorted(row["source_theorem_deps"])) + "]),"
               for row in rows]
    anchor = "  let mut nativeScope : Array Json := #[]"
    assert exporter.count(anchor) == 1
    fixed = exporter.replace(anchor, "  let expectedEdges : Array (Name × List Name) := #[\n" +
                             "\n".join(entries) + "\n  ]\n" + anchor)
    anchor = "    let deps := constants.filter fun dep => dep != name && allRegistered.contains dep"
    assert fixed.count(anchor) == 1
    fixed = fixed.replace(anchor, anchor + "\n" +
        "    let some (_, expected) := expectedEdges.find? (fun pair => pair.1 == name)\n" +
        '      | throwError "LONGTERM_EXPECTED_EDGES_MISSING"\n' +
        "    unless deps.length == expected.length && expected.all (fun dep => deps.contains dep) do\n" +
        '      throwError s!"LONGTERM_FIXED_PROOF_DEPENDENCIES_MISMATCH {name}"')
    assert fixed.count("  let mut cross := 0") == 1
    fixed = fixed.replace("  let mut cross := 0", f"  unless nativeScope.size == {len(scope)} do\n" +
                          '    throwError "LONGTERM_NATIVE_CENSUS_DRIFT"\n  let mut cross := 0')
    verifier_path = native_dir / ("VERIFY_" + NAME + "_OVERLAY_TYPES.lean")
    assert read(verifier_path) == fixed.encode()
    passed("Independent reconstruction of fixed-edge second Lean source from first observed proof bodies")

    expected_public = [{**{k: v for k, v in public_by_name[row["name"]].items() if k != "module"},
                        "source_module": row["source_module"],
                        "source_theorem_deps": sorted(row["source_theorem_deps"])} for row in rows]
    assert overlay["public_theorems"] == expected_public
    assert not {"registration_provenance", "lexical_pr_preflight"}.intersection(overlay)
    assert overlay["schema"] == "FKRG_REUSE_OVERLAY_V1"
    assert overlay["overlay_id"] == NAME + "_REUSE_OVERLAY_V1"
    assert overlay["source_checkpoint"] == "worktree-sha256:" + frozen["source_tree_sha256"]
    assert overlay["source_checkpoint_kind"] == "FROZEN_SOURCE_CONTENT_BEFORE_GIT_COMMIT"
    for key in ("base_snapshot_modules", "prior_overlay", "source_hash_overrides", "added_modules"):
        assert overlay[key] == pre[key]
    edges = [{"source": row["name"], "target": target}
             for row in expected_public for target in row["source_theorem_deps"]]
    dependencies = overlay["proof_dependency_certification"]
    assert dependencies["status"] == "PASS" and dependencies["edges"] == edges
    assert dependencies["registered_direct_edges"] == len(edges)
    distinct = overlay["type_distinctness"]
    assert distinct["status"] == "PASS" and distinct["new_theorems"] == public_count
    assert distinct["registered_prior_theorems"] == 4272
    assert distinct["cross_isDefEq_comparisons"] == 4272 * public_count
    assert distinct["internal_isDefEq_comparisons"] == public_count * (public_count - 1) // 2
    assert distinct["definitionally_equal_matches"] == 0
    assert distinct["verifier"] == dependencies["verifier"] == REUSE + verifier_path.name
    private = sum(row["is_private"] for row in scope.values())
    census = overlay["native_axiom_census"]
    for key, value in {"status": "PASS", "physical_source_modules": 7, "theorem_constants": len(scope),
                       "private_theorem_constants": private, "confirmed_public_source_candidates": public_count,
                       "other_native_public_constants": len(scope) - private - public_count,
                       "standard_axioms": ["propext", "Classical.choice", "Quot.sound"]}.items():
        assert census[key] == value
    assert overlay["native_export_evidence"] == {
        "path": REUSE + NAME + "_NATIVE_V1.json",
        "sha256": digest(read(native_dir / (NAME + "_NATIVE_V1.json")))}
    execution = overlay["native_execution"]
    assert execution["build_receipt_sha256"] == digest(read(build_path))
    assert execution["source_tree_sha256"] == frozen["source_tree_sha256"]
    assert execution["native_export_exit_code"] == execution["fixed_certificate_exit_code"] == 0
    assert execution["fixed_certificate_sha256"] == digest(read(verifier_path))
    assert execution["fixed_export_equals_initial_native_export"] is True
    assert execution["results"] == status["results"]
    assert status["summary"] == {
        "modules": 7, "public_source_theorems": public_count, "native_constants": len(scope),
        "registered_edges": len(edges),
        "overlay_sha256": digest(read(native_dir / (NAME + "_REUSE_OVERLAY_V1.json"))),
        "verifier_sha256": digest(read(verifier_path)),
        "native_sha256": digest(read(native_dir / (NAME + "_NATIVE_V1.json")))}
    assert overlay["scientific_role"] == "UNCOUNTED_SAME_SOURCE_PATH_REALIZATION"
    assert overlay["counted_core_impact"] == "NONE" and overlay["scientific_closure"] == "NOT_ESTABLISHED"
    passed("Raw candidate overlay, all actual dependency edges, public census and scientific boundaries")

    for path, data in reads.items():
        assert path.read_bytes() == data, ("Input changed during read-only audit", str(path))
    assert {p for p in [core / "UEOT.lean", *(core / "UEOT").rglob("*.lean")] if p.is_file()} == set(paths)
    passed("Every directly audited input remained byte-identical during review")
    result = {
        "schema": "PATH_REALIZATION_INDEPENDENT_EXECUTION_BYTE_AUDIT_V1",
        "state": "READ_ONLY_EXECUTION_ARTIFACT_CHECKS_PASS_REVIEW_REPORT_PENDING",
        "reviewer": "/root/finite_window_source", "created_utc": datetime.now(timezone.utc).isoformat(),
        "manifest_sha256": manifest_sha, "baseline_ref": base,
        "source_tree_sha256": frozen["source_tree_sha256"],
        "module_count": 691, "new_modules": 7, "public_source_theorems": public_count,
        "native_constants": len(scope), "private_native_constants": private,
        "other_native_public_constants": len(scope) - private - public_count,
        "native_module_counts": dict(Counter(row["source_module"] for row in scope.values())),
        "public_module_counts": dict(Counter(row["source_module"] for row in public_native.values())),
        "observed_axioms": sorted({a for row in scope.values() for a in row["axioms"]}),
        "registered_direct_edges": len(edges), "type_comparisons": expected_counts,
        "revised_safety_endpoint": witness_endpoint,
        "private_mass_helpers": private_helper_bindings,
        "lexical_hint_groups": hint_count, "lexical_hint_pairs": sum(len(row["reuse_candidates"]) for row in hints),
        "build": build["full_build"], "native_executions": status["results"],
        "checks_passed": checks,
        "auditor_did_not_execute": ["Mac tools", "Lean", "Lake", "native protocol entrypoints", "registration"],
        "cache_qualification": "Actual full lake build and native import executions under retained identity; not a clean-room no-cache rebuild. Earlier focused attempts are separate historical evidence.",
        "artifacts": [{"path": str(path), "bytes": len(data), "sha256": digest(data)}
                      for path, data in sorted(reads.items(), key=lambda item: str(item[0]))],
        "auditor_script_sha256": digest(Path(__file__).read_bytes())}
    with output.open("xb") as stream:
        stream.write((json.dumps(result, ensure_ascii=False, indent=2) + "\n").encode())
    print(json.dumps({k: result[k] for k in ("state", "module_count", "public_source_theorems",
          "native_constants", "private_native_constants", "other_native_public_constants",
          "registered_direct_edges", "observed_axioms")}, indent=2))


if __name__ == "__main__":
    main()
