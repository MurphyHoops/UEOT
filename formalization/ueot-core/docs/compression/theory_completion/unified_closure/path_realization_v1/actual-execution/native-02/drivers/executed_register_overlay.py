#!/usr/bin/env python3
"""Register metadata around actual native evidence without rewriting that evidence.

Requires explicit successful native output and its exact full-build receipt.
Adds only lexical_pr_preflight and registration_provenance to the raw candidate.
Copies immutable evidence and the registered overlay; never edits the consumer,
runs Lean, performs a Git-object PR preflight, or upgrades scientific status.
All checks precede writes. Existing destinations must have identical bytes.
--check-only validates the planned metadata/copies without writing any file.
"""
from __future__ import annotations

import argparse
from hashlib import sha256
import json
from pathlib import Path, PurePosixPath
import re
import subprocess

if not __debug__:
    raise RuntimeError("OPTIMIZED_PYTHON_NOT_ALLOWED")

CORE = "formalization/ueot-core/"
REUSE = CORE + "docs/compression/theory_completion/knowledge/reuse/"
PACKET = CORE + "docs/compression/theory_completion/unified_closure/"
PROTOCOL = PACKET + "path_realization_v1/native_protocol/"
NAME = "PATH_REALIZATION"
OVERLAY = NAME + "_REUSE_OVERLAY_V1.json"
NATIVE = NAME + "_NATIVE_V1.json"
EXPORTER = NAME + "_NATIVE_EXPORT.lean"
VERIFIER = "VERIFY_" + NAME + "_OVERLAY_TYPES.lean"
ADDED_KEYS = {"lexical_pr_preflight", "registration_provenance"}
EXPECTED_SOURCE = 'de7c7e287bd1b351ed3f790de58bfd71edf18df4013f7e5aaf2af55a6b3f6379'
PRIOR_MODULES, MODULES, PRIOR_PUBLIC, NEW_PUBLIC = 684, 691, 4272, 73
RAW_FILES = ("SOURCE_PREFLIGHT.json", "STATUS.json", EXPORTER, VERIFIER,
             "native_export.log", "fixed_verifier.log", "observed_first_native.json",
             NATIVE, OVERLAY, "development_lexical_reuse_hints.json", 'PROTOCOL_ADAPTATION.json', 'FROZEN_INPUTS.json', 'protocol_adapter.py', 'integration_native.py', 'immutable_integration_native.py', 'executed_integration_native.py')


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(data):
    return sha256(data).hexdigest()


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()


def unique(rows, key, label):
    result = {row[key]: row for row in rows}
    require(len(result) == len(rows), "DUPLICATE_" + label)
    return result


def run(repo, native_output, archive_relative, build_receipt, check_only=False):
    repo, native_output = Path(repo).resolve(strict=True), Path(native_output).resolve(strict=True)
    build_receipt = Path(build_receipt).resolve(strict=True)
    reads, writes, inputs = {}, {}, []

    def destination(relative):
        relative = PurePosixPath(relative)
        require(not relative.is_absolute() and ".." not in relative.parts and str(relative) != ".",
                "INVALID_REPOSITORY_RELATIVE_PATH")
        path = repo.joinpath(*relative.parts)
        require(path.resolve().is_relative_to(repo) and not path.is_symlink(), "OUTPUT_PATH_ESCAPE")
        return path

    archive = destination(archive_relative)
    require(archive.is_relative_to(repo / PACKET / "path_realization_v1"),
            "ARCHIVE_OUTSIDE_INCREMENT")
    require(build_receipt.name == "FULL_BUILD_RECEIPT.json" and
            build_receipt.parent.name.startswith("full-build-"), "EXPLICIT_FULL_BUILD_RECEIPT_REQUIRED")

    def read(path):
        path = Path(path)
        require(path.is_file() and not path.is_symlink(), "MISSING_OR_SYMLINK_INPUT: " + str(path))
        if path not in reads:
            reads[path] = path.read_bytes()
        return reads[path]

    def record(role, source, target, data=None):
        data = read(source) if data is None else data
        target = destination(target)
        require(target not in writes or writes[target] == data, "PLANNED_OUTPUT_CONFLICT")
        writes[target] = data
        entry = {"role": role, "input_path": str(source),
                 "path": target.relative_to(repo).as_posix(), "sha256": digest(data)}
        inputs.append(entry)
        return entry

    def raw(name):
        return json.loads(read(native_output / name))

    def git(*args):
        return subprocess.check_output(["git", *args], cwd=repo)

    status, pre, candidate = raw("STATUS.json"), raw("SOURCE_PREFLIGHT.json"), raw(OVERLAY)
    native, first = raw(NATIVE), raw("observed_first_native.json")
    build = json.loads(read(build_receipt))
    require(status["state"] == "PASS_PENDING_INDEPENDENT_REVIEW_AND_REGISTRATION", "NATIVE_NOT_PASSED")
    require(pre["status"] == "PENDING_ACTUAL_NATIVE_EXECUTION", "PREFLIGHT_HISTORY_WAS_REWRITTEN")
    require(not ADDED_KEYS.intersection(candidate), "RAW_CANDIDATE_ALREADY_AUGMENTED")
    require(candidate["schema"] == "FKRG_REUSE_OVERLAY_V1" and
            candidate["overlay_id"] == NAME + "_REUSE_OVERLAY_V1", "WRONG_RAW_OVERLAY")
    base = pre["baseline_ref"]
    require(re.fullmatch(r"[0-9a-f]{40}", base) is not None, "BASE_MUST_BE_EXACT_COMMIT")
    require(git("rev-parse", "--verify", base + "^{commit}").decode().strip() == base, "BASE_NOT_ACTUAL_COMMIT")
    require(status["baseline_ref"] == candidate["baseline_ref"] == build["baseline_ref"] == base,
            "BASE_IDENTITY_MISMATCH")
    require((pre["base_snapshot_modules"], pre["complete_source_modules"],
             pre["registered_prior_theorems"], pre["prior_overlay_count"]) ==
            (PRIOR_MODULES, MODULES, PRIOR_PUBLIC, 10), "WRONG_PREFLIGHT_COUNTS")
    identity = build["identity"]
    require(build["schema"] == "PATH_REALIZATION_ACTUAL_FULL_BUILD_V1" and build["state"] == "PASS" and
            build["full_build"]["exit_code"] == 0, "FULL_BUILD_NOT_PASSED")
    require(pre["source_tree_sha256"] == candidate["native_execution"]["source_tree_sha256"] ==
            identity["source_tree_sha256"] == EXPECTED_SOURCE, "SOURCE_IDENTITY_MISMATCH")
    require(candidate["source_checkpoint"] == "worktree-sha256:" + EXPECTED_SOURCE and
            candidate["source_checkpoint_kind"] == "FROZEN_SOURCE_CONTENT_BEFORE_GIT_COMMIT",
            "WRONG_SOURCE_CHECKPOINT_KIND")
    require(identity["module_count"] == MODULES, "FULL_BUILD_MODULE_COUNT_MISMATCH")
    build_sha = digest(read(build_receipt))
    require(status["build_receipt_sha256"] == candidate["native_execution"]["build_receipt_sha256"] ==
            build_sha, "FULL_BUILD_RECEIPT_HASH_MISMATCH")
    full_log = read(build_receipt.parent / "full-build.log")
    require(build["full_build"]["log_name"] == "full-build.log" and
            digest(full_log) == build["full_build"]["log_sha256"] and
            b"Build completed successfully" in full_log, "FULL_BUILD_LOG_MISMATCH")
    tools = identity["runtime_tools"]
    require(build["full_build"]["command"] == [tools["lake"]["executable"], "build", "UEOT"],
            "WRONG_FULL_BUILD_COMMAND")

    def source_identity():
        paths = [repo / CORE / "UEOT.lean", *(repo / CORE / "UEOT").rglob("*.lean")]
        by_module = {p.relative_to(repo / CORE).with_suffix("").as_posix().replace("/", "."): p
                     for p in paths if p.is_file()}
        h, records = sha256(), []
        for module, path in sorted(by_module.items()):
            data = path.read_bytes()
            h.update(module.encode() + b"\0" + data + b"\0")
            records.append({"module": module, "path": path.relative_to(repo).as_posix(),
                            "bytes": len(data), "sha256": digest(data)})
        require(len(by_module) == MODULES and h.hexdigest() == EXPECTED_SOURCE and
                records == identity["source_files"], "CURRENT_FULL_SOURCE_DRIFT")
        return {r["path"]: r for r in records}

    current = source_identity()
    base_paths = {p for p in git("ls-tree", "-r", "--name-only", base).decode().splitlines()
                  if p == CORE + "UEOT.lean" or (p.startswith(CORE + "UEOT/") and p.endswith(".lean"))}
    require(len(base_paths) == PRIOR_MODULES and base_paths <= set(current), "BASE_SOURCE_CENSUS_MISMATCH")
    modules = unique(pre["added_modules"], "path", "ADDED_MODULE")
    require(set(modules) == set(current) - base_paths and len(modules) == MODULES - PRIOR_MODULES,
            "ADDED_MODULE_SET_MISMATCH")
    for path, row in modules.items():
        require(row["module"] == current[path]["module"] and
                row["content_sha256"] == current[path]["sha256"] and
                row["source_origin"] == "UEOT_MAINTAINED", "ADDED_MODULE_BINDING_MISMATCH")
    for field in ("base_snapshot_modules", "prior_overlay", "source_hash_overrides", "added_modules"):
        require(candidate[field] == pre[field], "RAW_PREFLIGHT_MISMATCH: " + field)
    require(set(pre["source_hash_overrides"]) == {CORE + "UEOT/V3/Compression/TheoryCompletion.lean"},
            "UNEXPECTED_SOURCE_OVERRIDE")
    for path, expected in pre["source_hash_overrides"].items():
        require(current[path]["sha256"] == expected, "SOURCE_OVERRIDE_HASH_MISMATCH")

    public = unique(pre["public_source_candidates"], "name", "SOURCE_CANDIDATE")
    native_public = unique(native["public_source_theorems"], "name", "NATIVE_PUBLIC")
    registered_public = unique(candidate["public_theorems"], "name", "RAW_PUBLIC")
    require(len(public) == NEW_PUBLIC and set(public) == set(native_public) == set(registered_public),
            "PUBLIC_CANDIDATE_SET_MISMATCH")
    require(native == first and native["schema"] == NAME + "_NATIVE_EXPORT_V1", "NATIVE_JSON_MISMATCH")
    require((native["registered_prior_theorems"], native["new_source_public_theorem_count"],
             native["historical_public_repair_count"], native["cross_isDefEq_comparisons"],
             native["internal_isDefEq_comparisons"], native["collisions"]) ==
            (PRIOR_PUBLIC, NEW_PUBLIC, 0, NEW_PUBLIC * PRIOR_PUBLIC, NEW_PUBLIC * (NEW_PUBLIC - 1) // 2, []),
            "NATIVE_TYPE_SCOPE_MISMATCH")
    require(native["native_audit_modules"] == [m["module"] for m in pre["added_modules"]],
            "NATIVE_MODULE_SCOPE_MISMATCH")
    scope = unique(native["all_native_theorem_constants"], "name", "NATIVE_CONSTANT")
    require(set(public) <= set(scope) and {r["source_module"] for r in scope.values()} ==
            set(native["native_audit_modules"]), "NATIVE_OWNERSHIP_SCOPE_MISMATCH")
    for name, row in public.items():
        observed = native_public[name]
        require(row["path"] in modules and row["module"] == modules[row["path"]]["module"] and
                observed["source_module"] == row["module"] and not scope[name]["is_private"] and
                row["registration_kind"] == observed["registration_kind"] == "new_source_public",
                "PUBLIC_SOURCE_OWNER_MISMATCH")
        expected = {**{k: v for k, v in row.items() if k != "module"},
                    "source_module": observed["source_module"],
                    "source_theorem_deps": sorted(observed["source_theorem_deps"])}
        require(registered_public[name] == expected, "RAW_PUBLIC_METADATA_MISMATCH")
        for field in ("source_module", "type", "level_parameters", "direct_constants"):
            require(observed[field] == scope[name][field], "PUBLIC_NATIVE_CENSUS_MISMATCH")
    edges = [{"source": r["name"], "target": d} for r in candidate["public_theorems"]
             for d in r["source_theorem_deps"]]
    types, deps = candidate["type_distinctness"], candidate["proof_dependency_certification"]
    require(types["status"] == deps["status"] == candidate["native_axiom_census"]["status"] == "PASS",
            "RAW_CERTIFICATION_NOT_PASSED")
    require(types["verifier"] == deps["verifier"] == REUSE + VERIFIER and
            types["definitionally_equal_matches"] == 0 and types["new_theorems"] == NEW_PUBLIC and
            types["registered_prior_theorems"] == PRIOR_PUBLIC and
            types["cross_isDefEq_comparisons"] == NEW_PUBLIC * PRIOR_PUBLIC and
            types["internal_isDefEq_comparisons"] == NEW_PUBLIC * (NEW_PUBLIC - 1) // 2 and
            deps["edges"] == edges and deps["registered_direct_edges"] == len(edges), "RAW_CERTIFICATE_MISMATCH")
    require(candidate["native_export_evidence"] == {"path": REUSE + NATIVE,
            "sha256": digest(read(native_output / NATIVE))}, "RAW_NATIVE_ARTIFACT_MISMATCH")
    execution = candidate["native_execution"]
    require(execution["native_export_exit_code"] == execution["fixed_certificate_exit_code"] == 0 and
            execution["fixed_export_equals_initial_native_export"] is True and
            execution["fixed_certificate_sha256"] == digest(read(native_output / VERIFIER)) and
            status["results"] == execution["results"], "RAW_EXECUTION_MISMATCH")
    results = unique(status["results"], "label", "EXECUTION_LABEL")
    require(set(results) == {"native_export", "fixed_verifier"}, "WRONG_EXECUTION_LABELS")
    for label, source in (("native_export", EXPORTER), ("fixed_verifier", VERIFIER)):
        result, log = results[label], read(native_output / (label + ".log"))
        require(result["exit_code"] == 0 and result["log_sha256"] == digest(log) and
                result["command"][:3] == [tools["lake"]["executable"], "env", tools["lean"]["executable"]] and
                len(result["command"]) == 4 and Path(result["command"][-1]).name == source,
                "ACTUAL_NATIVE_EXECUTION_LOG_MISMATCH")
        marked = [line[len(NAME + "_NATIVE_JSON "):] for line in log.decode().splitlines()
                  if line.startswith(NAME + "_NATIVE_JSON ")]
        require(len(marked) == 1 and json.loads(marked[0]) == native, "FIXED_FIRST_LOG_JSON_MISMATCH")
    require(status["summary"] == {"modules": len(modules), "public_source_theorems": NEW_PUBLIC,
            "native_constants": len(scope), "registered_edges": len(edges),
            "overlay_sha256": digest(read(native_output / OVERLAY)),
            "verifier_sha256": digest(read(native_output / VERIFIER)),
            "native_sha256": digest(read(native_output / NATIVE))}, "STATUS_SUMMARY_MISMATCH")
    require(pre["exporter_sha256"] == digest(read(native_output / EXPORTER)), "EXPORTER_HASH_MISMATCH")

    hints = pre["lexical_reuse_hints"]
    require(raw("development_lexical_reuse_hints.json") == hints, "LEXICAL_HINT_ARTIFACT_MISMATCH")
    hint_map = unique(hints, "symbol", "LEXICAL_HINT")
    require(set(hint_map) == set(public), "LEXICAL_PUBLIC_SET_MISMATCH")
    for name, row in hint_map.items():
        require((row["path"], row["line"]) == (public[name]["path"], public[name]["line"]) and
                isinstance(row["reuse_candidates"], list), "LEXICAL_SOURCE_LOCATION_MISMATCH")
    hinted = sum(bool(row["reuse_candidates"]) for row in hints)
    require(hinted == 25, "OBSERVED_HINT_COUNT_DIFFERS_FROM_INDEPENDENT_RECOMPUTATION")
    lexical = {"baseline_ref": base, "candidate_ref": None,
        "candidate_scope": "Current frozen worktree bytes; an immutable Git-object PR preflight is separately required after commit.",
        "base_lean_module_count": PRIOR_MODULES, "candidate_lean_module_count": MODULES,
        "base_public_lexical_theorem_count": PRIOR_PUBLIC,
        "candidate_public_lexical_theorem_count": PRIOR_PUBLIC + NEW_PUBLIC,
        "new_public_source_theorem_count": NEW_PUBLIC, "historical_public_repair_count": 0,
        "overlay_public_registration_count": NEW_PUBLIC,
        "new_theorems_with_lexical_reuse_candidates": hinted,
        "candidate_source_tree_sha256": EXPECTED_SOURCE,
        "registered_prior_public_source_theorem_count": PRIOR_PUBLIC,
        "candidate_registered_public_source_theorem_count": PRIOR_PUBLIC + NEW_PUBLIC,
        "note": "Counts and H use the actual SOURCE_PREFLIGHT declaration/name hints. This is not a Git-object PR preflight; name hints and raw stored-type isDefEq do not replace independent semantic review."}

    # Select the ten actual driver outputs, so an in-place archive remains
    # re-entrant after this script adds its own metadata and provenance copies.
    raw_files = [native_output / name for name in sorted(RAW_FILES)]
    for path in raw_files:
        record("actual_native_output", path, (archive / path.relative_to(native_output)).relative_to(repo))
    full_archive = archive.parent / build_receipt.parent.name
    for name in ("FULL_BUILD_RECEIPT.json", "full-build.log", 'PROTOCOL_ADAPTATION.json', 'FROZEN_INPUTS.json', 'protocol_adapter.py', 'full_build.py', 'immutable_full_build.py', 'executed_full_build.py'):
        record("actual_full_build", build_receipt.parent / name, (full_archive / name).relative_to(repo))
    for relative, expected in ((PROTOCOL + "integration_native.py", pre["integration_driver_sha256"]),
                               (PROTOCOL + "full_build.py", build["driver_sha256"])):
        data = read(destination(relative))
        require(digest(data) == expected, "ACTUAL_DRIVER_HASH_MISMATCH")
        record("executed_driver", repo / relative, (archive / "drivers" / Path(relative).name).relative_to(repo), data)
    for helper in pre["immutable_protocol_helpers"]:
        data = read(destination(helper["path"]))
        require(digest(data) == helper["sha256"] and git("show", base + ":" + helper["path"]) == data,
                "IMMUTABLE_PROTOCOL_HELPER_MISMATCH")
        record("immutable_protocol_helper", repo / helper["path"],
               (archive / "protocol-inputs" / helper["path"]).relative_to(repo), data)
    identity_path = PACKET + "registered_interfaces/native_protocol/build_identity.py"
    require(digest(read(destination(identity_path))) == build["identity_helper_sha256"], "BUILD_IDENTITY_HELPER_MISMATCH")
    prior = pre["prior_overlay"]
    require(digest(read(destination(prior["path"]))) == prior["sha256"], "PRIOR_OVERLAY_HASH_MISMATCH")
    record("prior_overlay", repo / prior["path"], (archive / "protocol-inputs" / Path(prior["path"]).name).relative_to(repo))
    consumer = pre["baseline_reuse_consumer"]
    require(consumer["path"] == REUSE + "fkrg_reuse.py", "WRONG_BASE_CONSUMER_PATH")
    base_code = git("show", base + ":" + consumer["path"])
    require(digest(base_code) == consumer["sha256"], "BASE_CONSUMER_HASH_MISMATCH")
    record("immutable_base_consumer", base + ":" + consumer["path"],
           (archive / "drivers/baseline_fkrg_reuse.py").relative_to(repo), base_code)
    record("registration_driver", Path(__file__).resolve(),
           (archive / "drivers/register_overlay.py").relative_to(repo))
    for name, content in ADAPTED_REGISTRATION_INPUTS.items():
        record("executed_registration_protocol", "executed-memory:" + name,
               (archive / "drivers" / name).relative_to(repo), content)
    provenance = {"schema": NAME + "_REGISTRATION_PROVENANCE_V1", "inputs": inputs,
        "baseline_ref": base, "source_tree_sha256": EXPECTED_SOURCE,
        "metadata_additions_only": sorted(ADDED_KEYS), "raw_evidence_bytes_preserved": True,
        "git_object_pr_preflight": "NOT_PERFORMED_SEPARATE_GATE",
        "consumer_registry_modified": False, "independent_review": "SEPARATE_GATE"}
    registered = {**candidate, "lexical_pr_preflight": lexical, "registration_provenance": provenance}
    require(set(registered) - set(candidate) == ADDED_KEYS and
            {k: v for k, v in registered.items() if k not in ADDED_KEYS} == candidate,
            "REGISTRATION_CHANGED_RAW_PAYLOAD")
    registered_bytes = encoded(registered)
    for path, data in ((destination(REUSE + OVERLAY), registered_bytes),
                       (destination((archive / "REGISTERED_OVERLAY.json").relative_to(repo)), registered_bytes),
                       (destination(REUSE + NATIVE), read(native_output / NATIVE)),
                       (destination(REUSE + VERIFIER), read(native_output / VERIFIER))):
        require(path not in writes or writes[path] == data, "PLANNED_REGISTRATION_CONFLICT")
        writes[path] = data
    receipt = {"schema": NAME + "_REGISTRATION_RECEIPT_V1", "state": "PASS_METADATA_ONLY_CONSUMER_UNCHANGED",
        "baseline_ref": base, "source_tree_sha256": EXPECTED_SOURCE, "input_files": inputs,
        "registered_overlay": {"path": REUSE + OVERLAY, "sha256": digest(registered_bytes)},
        "raw_overlay_sha256": digest(read(native_output / OVERLAY)),
        "added_top_level_keys": sorted(ADDED_KEYS), "stripped_registered_json_equals_raw": True,
        "lexical_hinted_count": hinted, "candidate_ref": None,
        "git_object_pr_preflight": "NOT_PERFORMED_SEPARATE_GATE"}
    receipt_path = destination((archive / "REGISTRATION_RECEIPT.json").relative_to(repo))
    writes[receipt_path] = encoded(receipt)
    source_identity()
    for path, data in reads.items():
        require(path.read_bytes() == data, "INPUT_CHANGED_DURING_REGISTRATION: " + str(path))
    for path, data in writes.items():
        require(not path.exists() or (path.is_file() and path.read_bytes() == data),
                "EXISTING_OUTPUT_DIFFERS: " + str(path))
    summary = {"state": receipt["state"], "registered_overlay": receipt["registered_overlay"],
               "receipt": receipt_path.relative_to(repo).as_posix(),
               "receipt_sha256": digest(encoded(receipt)), "lexical_hinted_count": hinted}
    if check_only:
        return {**summary, "state": "CHECKED_NO_FILES_WRITTEN", "planned_output_files": len(writes)}
    for path, data in writes.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        try:
            with path.open("xb") as stream:
                stream.write(data)
        except FileExistsError:
            require(path.read_bytes() == data, "CONCURRENT_OUTPUT_CONFLICT: " + str(path))
    return summary


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("repo", "native-output", "archive-relative", "build-receipt"):
        parser.add_argument("--" + name, required=True)
    parser.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    print(json.dumps(run(args.repo, args.native_output, args.archive_relative, args.build_receipt,
                         check_only=args.check_only), indent=2))
