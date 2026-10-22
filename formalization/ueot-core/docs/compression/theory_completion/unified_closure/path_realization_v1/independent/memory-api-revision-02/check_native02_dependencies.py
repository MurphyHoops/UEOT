#!/usr/bin/env python3
"""Read the actual native02 archive and verify the revised witness dependencies."""
from argparse import ArgumentParser
from hashlib import sha256
import json
from pathlib import Path


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--execution", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    native_dir = args.execution / "native-02"
    read = lambda name: json.loads((native_dir / name).read_text())
    native = read("PATH_REALIZATION_NATIVE_V1.json")
    first = read("observed_first_native.json")
    overlay = read("PATH_REALIZATION_REUSE_OVERLAY_V1.json")
    status = read("STATUS.json")
    frozen = read("FROZEN_INPUTS.json")
    preflight = read("SOURCE_PREFLIGHT.json")
    build_path = args.execution / "full-build-02/FULL_BUILD_RECEIPT.json"
    build = json.loads(build_path.read_text())
    base = "d503586107974c56e0773b4ea106b41a7d144b43"
    source_sha = "de7c7e287bd1b351ed3f790de58bfd71edf18df4013f7e5aaf2af55a6b3f6379"
    witness_sha = "08060447a92c3b129351b95615ed2e1b3214e12e9ded21c638d0c6554c400c88"
    assert build["state"] == "PASS"
    assert status["state"] == "PASS_PENDING_INDEPENDENT_REVIEW_AND_REGISTRATION"
    assert all(row["baseline_ref"] == base for row in [status, frozen, preflight, build, overlay])
    assert frozen["source_tree_sha256"] == preflight["source_tree_sha256"] == source_sha
    assert overlay["source_checkpoint"] == "worktree-sha256:" + source_sha
    assert status["build_receipt_sha256"] == digest(build_path)
    assert digest(native_dir / "PATH_REALIZATION_NATIVE_V1.json") == status["summary"]["native_sha256"]
    assert digest(native_dir / "PATH_REALIZATION_REUSE_OVERLAY_V1.json") == status["summary"]["overlay_sha256"]
    assert digest(native_dir / "VERIFY_PATH_REALIZATION_OVERLAY_TYPES.lean") == status["summary"]["verifier_sha256"]
    runs = {row["label"]: row for row in status["results"]}
    logs = []
    for label in ["native_export", "fixed_verifier"]:
        log_path = native_dir / (label + ".log")
        raw = log_path.read_bytes()
        assert runs[label]["exit_code"] == 0
        assert digest(log_path) == runs[label]["log_sha256"]
        assert raw.startswith(b"PATH_REALIZATION_NATIVE_JSON ")
        assert json.loads(raw[len(b"PATH_REALIZATION_NATIVE_JSON "):]) == native
        logs.append(raw)
    assert logs[0] == logs[1]
    assert first == native
    assert native["collisions"] == []
    assert native["registered_prior_theorems"] == 4272
    assert native["cross_isDefEq_comparisons"] == 311856
    assert native["internal_isDefEq_comparisons"] == 2628
    public = native["public_source_theorems"]
    scope = native["all_native_theorem_constants"]
    owners = {row["module"] for row in overlay["added_modules"]}
    by_name = {row["name"]: row for row in scope}
    public_by_name = {row["name"]: row for row in public}
    assert len(owners) == 7 and len(scope) == len(by_name) == 249
    assert len(public) == len(public_by_name) == 73
    assert sum(row["is_private"] for row in scope) == 51
    assert {row["source_module"] for row in scope} == owners
    assert set(public_by_name) == {row["name"] for row in overlay["public_theorems"]}
    assert sum(len(row["source_theorem_deps"]) for row in public) == 114
    standard = {"propext", "Classical.choice", "Quot.sound"}
    for row in scope:
        assert set(row["axioms"]) <= standard
        assert set(row["direct_theorem_constants"]) <= set(row["direct_constants"])
    for row in public:
        compiled = by_name[row["name"]]
        assert not compiled["is_private"]
        for field in ["source_module", "level_parameters", "type", "direct_constants"]:
            assert row[field] == compiled[field]
        assert set(row["source_theorem_deps"]) <= set(compiled["direct_theorem_constants"])
    module = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMemorySafetyWitness"
    source_row = next(row for row in overlay["added_modules"] if row["module"] == module)
    assert source_row["content_sha256"] == witness_sha
    assert digest(args.repo / source_row["path"]) == witness_sha
    endpoint = module + ".physical_safety_premises_independent"
    public_row = public_by_name[endpoint]
    owned_row = by_name[endpoint]
    old_public = [module + "." + name for name in [
        "safe_is_proper_nonempty", "all_rows_zero_uncovered", "initial_false_safe",
        "source_false_preserves_safe",
    ]]
    assert public_row["source_theorem_deps"] == old_public
    helper_names = [
        "safe_source_all_times_mass_one",
        "unsafe_transition_time_one_mass_zero",
        "unsafe_transition_all_times_mass_zero",
        "unsafe_initial_time_zero_mass_zero",
        "unsafe_initial_all_times_mass_zero",
    ]
    helpers = []
    for short_name in helper_names:
        matches = [row for row in scope if row["source_module"] == module
                   and row["name"].endswith("." + short_name)]
        assert len(matches) == 1
        row = matches[0]
        assert row["is_private"] and row["name"].startswith("_private.")
        assert set(row["axioms"]) == standard
        assert row["name"] not in public_by_name
        assert public_row["direct_constants"].count(row["name"]) == 1
        assert owned_row["direct_theorem_constants"].count(row["name"]) == 1
        helpers.append({
            "short_name": short_name,
            "compiled_name": row["name"],
            "source_module": row["source_module"],
            "is_private": row["is_private"],
            "level_parameters": row["level_parameters"],
            "stored_type_sha256": sha256(row["type"].encode()).hexdigest(),
            "axioms": row["axioms"],
            "public_proof_direct_reference": True,
            "ueot_direct_theorem_constants": [name for name in row["direct_theorem_constants"]
                                               if name.startswith(("UEOT.", "_private.UEOT."))],
        })
    assert any(name.endswith(".controller_all_times_physical_safe")
               for name in helpers[0]["ueot_direct_theorem_constants"])
    assert helpers[1]["compiled_name"] in helpers[2]["ueot_direct_theorem_constants"]
    assert helpers[3]["compiled_name"] in helpers[4]["ueot_direct_theorem_constants"]
    witness_scope = [row for row in scope if row["source_module"] == module]
    assert len(witness_scope) == 16 and sum(row["is_private"] for row in witness_scope) == 8
    evidence = [{"path": "native-02/" + name, "sha256": digest(native_dir / name)} for name in [
        "PATH_REALIZATION_NATIVE_V1.json", "observed_first_native.json",
        "PATH_REALIZATION_REUSE_OVERLAY_V1.json", "VERIFY_PATH_REALIZATION_OVERLAY_TYPES.lean",
        "native_export.log", "fixed_verifier.log", "STATUS.json", "FROZEN_INPUTS.json",
        "SOURCE_PREFLIGHT.json",
    ]]
    evidence.append({"path": "full-build-02/FULL_BUILD_RECEIPT.json", "sha256": digest(build_path)})
    result = {
        "schema": "PATH_REALIZATION_MEMORY_REVISION_02_NATIVE_DEPENDENCY_REVIEW",
        "status": "ACTUAL_NATIVE_DEPENDENCIES_CLEAR_REGISTRATION_PENDING",
        "reviewer": "/root/c3_executable_search",
        "baseline_ref": base, "complete_source_fingerprint": source_sha,
        "reviewed_witness_sha256": witness_sha,
        "execution_import_root": str(args.execution),
        "check_script_sha256": digest(Path(__file__)),
        "evidence": evidence, "actual_runs": status["results"],
        "scope_counts": {"public_candidates": 73, "owned_constants": 249,
                         "private_constants": 51, "other_public_generated_constants": 125,
                         "registered_direct_edges": 114,
                         "witness_owned_constants": 16, "witness_private_constants": 8},
        "actual_public_comparisons": {"cross": 311856, "internal": 2628, "collisions": []},
        "initial_and_fixed_raw_bytes_equal": True,
        "both_raw_logs_decode_to_the_actual_native_artifact": True,
        "endpoint": endpoint,
        "endpoint_stored_type_sha256": sha256(public_row["type"].encode()).hexdigest(),
        "endpoint_registered_direct_edges": old_public,
        "private_helpers": helpers,
        "review_scope": "Actual native ownership, private dependencies, standard axiom closure and exact initial/fixed byte bindings; complete protocol/archive execution review is separately authored.",
        "scope_limitation": "The five private helpers are compiler-audited proof ingredients and direct public consequences; they are not individual members of the new public pairwise comparison domain. The interrupted native01 remains an incomplete historical run.",
        "registration_and_live_consumer_gates": "PENDING_SEPARATE_ACTUAL_RECEIPTS",
    }
    with args.output.open("x") as stream:
        json.dump(result, stream, ensure_ascii=False, indent=2)
        stream.write("\n")
    print(json.dumps({"status": result["status"], "private_helpers": len(helpers),
                      "receipt_sha256": digest(args.output)}))


if __name__ == "__main__":
    main()
