#!/usr/bin/env python3
"""Read-only registration audit; writes only this reviewer's JSON evidence."""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess

BASE = "d503586107974c56e0773b4ea106b41a7d144b43"
SOURCE = "de7c7e287bd1b351ed3f790de58bfd71edf18df4013f7e5aaf2af55a6b3f6379"
CORE = "formalization/ueot-core/"
PACKET = CORE + "docs/compression/theory_completion/unified_closure/path_realization_v1/"
REUSE = CORE + "docs/compression/theory_completion/knowledge/reuse/"
NAME = "PATH_REALIZATION"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--execution-receipt", type=Path, required=True)
    args = parser.parse_args()
    repo = args.repo.resolve(strict=True)
    observed = {}
    checks = []

    def digest(data):
        return hashlib.sha256(data).hexdigest()

    def read(path):
        path = Path(path)
        assert path.is_file() and not path.is_symlink(), str(path)
        value = path.read_bytes()
        if path in observed:
            assert observed[path] == value, "INPUT_CHANGED_DURING_REVIEW"
        observed[path] = value
        return value

    def obj(path):
        return json.loads(read(path))

    def check(name, condition):
        assert condition, name
        checks.append(name)

    def git_blob(spec):
        return subprocess.check_output(["git", "show", spec], cwd=repo)

    packet = repo / PACKET
    actual = packet / "actual-execution"
    native_dir = actual / "native-02"
    drivers = native_dir / "drivers"
    review_path = packet / "independent/ACTUAL_EXECUTION_REVIEW.json"
    review = obj(review_path)
    check("signed_execution_review_exact_binding",
          digest(read(review_path)) == "89697625b9aa110791da53332ba02714191c30b5accf239f5380242076529fbf"
          and review["state"] == "CLEAR" and review["binding"]["baseline_ref"] == BASE
          and review["binding"]["source_tree_sha256"] == SOURCE)

    receipt_path = native_dir / "REGISTRATION_RECEIPT.json"
    receipt = obj(receipt_path)
    check("registration_receipt_exact_bytes_and_state",
          digest(read(receipt_path)) == "1f72a7a063bab710241b7ea11fe643835019da7e06aad155ffbd9439c26c5d51"
          and receipt["state"] == "PASS_METADATA_ONLY_CONSUMER_UNCHANGED"
          and receipt["baseline_ref"] == BASE and receipt["source_tree_sha256"] == SOURCE)
    raw_path = native_dir / (NAME + "_REUSE_OVERLAY_V1.json")
    live_path = repo / REUSE / (NAME + "_REUSE_OVERLAY_V1.json")
    raw, live = obj(raw_path), obj(live_path)
    additions = {"lexical_pr_preflight", "registration_provenance"}
    check("exact_two_metadata_additions_and_full_payload_preserved",
          not additions.intersection(raw) and set(live) - set(raw) == additions
          and {k: v for k, v in live.items() if k not in additions} == raw
          and receipt["added_top_level_keys"] == sorted(additions)
          and receipt["stripped_registered_json_equals_raw"] is True)
    check("raw_and_registered_hashes_and_archived_registered_bytes",
          digest(read(raw_path)) == receipt["raw_overlay_sha256"] ==
          "e87a8b9a921e4f9014d59f761ed73c8432c869f354e3b498542d99133a84239a"
          and digest(read(live_path)) == receipt["registered_overlay"]["sha256"] ==
          "8e72781498acf49496733ace5dfbf80257830ff3a6d85e1b02e66474f936ec3b"
          and read(live_path) == read(native_dir / "REGISTERED_OVERLAY.json"))
    check("registered_encoding_is_exact_metadata_augmented_object",
          read(live_path) == (json.dumps(live, ensure_ascii=False, indent=2) + "\n").encode())

    for filename in (NAME + "_NATIVE_V1.json", "VERIFY_" + NAME + "_OVERLAY_TYPES.lean"):
        check("live_artifact_byte_identity:" + filename,
              read(repo / REUSE / filename) == read(native_dir / filename))

    pre = obj(native_dir / "SOURCE_PREFLIGHT.json")
    status = obj(native_dir / "STATUS.json")
    build = obj(actual / "full-build-02/FULL_BUILD_RECEIPT.json")
    frozen = obj(actual / "FROZEN_INPUTS_FINAL_02.json")
    hints = obj(native_dir / "development_lexical_reuse_hints.json")
    check("original_pending_and_actual_pass_records_preserved",
          pre["status"] == "PENDING_ACTUAL_NATIVE_EXECUTION"
          and status["state"] == "PASS_PENDING_INDEPENDENT_REVIEW_AND_REGISTRATION"
          and build["state"] == "PASS" and build["full_build"]["exit_code"] == 0)
    check("actual_source_identity_agrees_across_bound_inputs",
          all(v == SOURCE for v in (pre["source_tree_sha256"], frozen["source_tree_sha256"],
              build["identity"]["source_tree_sha256"], raw["native_execution"]["source_tree_sha256"]))
          and all(v == BASE for v in (pre["baseline_ref"], frozen["baseline_ref"],
              build["baseline_ref"], raw["baseline_ref"], status["baseline_ref"])))

    lexical = live["lexical_pr_preflight"]
    hinted = sum(bool(r["reuse_candidates"]) for r in hints)
    check("lexical_metadata_derived_from_actual_source_hints",
          hints == pre["lexical_reuse_hints"] and len(hints) == 73 and hinted == 25
          and len({r["symbol"] for r in hints}) == 73
          and {r["symbol"] for r in hints} == {r["name"] for r in pre["public_source_candidates"]}
          and lexical["baseline_ref"] == BASE and lexical["candidate_ref"] is None
          and lexical["candidate_source_tree_sha256"] == SOURCE
          and lexical["base_lean_module_count"] == 684
          and lexical["candidate_lean_module_count"] == 691
          and lexical["base_public_lexical_theorem_count"] == 4272
          and lexical["candidate_public_lexical_theorem_count"] == 4345
          and lexical["new_public_source_theorem_count"] == 73
          and lexical["historical_public_repair_count"] == 0
          and lexical["overlay_public_registration_count"] == 73
          and lexical["new_theorems_with_lexical_reuse_candidates"] == hinted
          and lexical["registered_prior_public_source_theorem_count"] == 4272
          and lexical["candidate_registered_public_source_theorem_count"] == 4345)

    adaptation = obj(drivers / "PROTOCOL_ADAPTATION.json")
    immutable = read(drivers / "immutable_register_overlay.py")
    check("immutable_registration_driver_is_exact_accepted_git_blob",
          immutable == git_blob(BASE + ":" + adaptation["immutable_driver"]["path"])
          and digest(immutable) == adaptation["immutable_driver"]["sha256"])
    reconstructed = immutable.decode()
    for substitution in adaptation["substitutions"]:
        check("exact_literal_anchor:" + substitution["old"],
              reconstructed.count(substitution["old"]) == substitution["occurrences"] == 1)
        reconstructed = reconstructed.replace(substitution["old"], substitution["new"])
    check("all_11_substitutions_reconstruct_executed_registration_bytes",
          len(adaptation["substitutions"]) == 11
          and reconstructed.encode() == read(drivers / "executed_register_overlay.py")
          and digest(reconstructed.encode()) == adaptation["executed_source_sha256"])
    check("registration_adaptation_pinned_to_frozen_reviewed_protocol",
          adaptation["baseline_ref"] == BASE and adaptation["source_tree_sha256"] == SOURCE
          and adaptation["frozen_inputs_sha256"] == digest(read(actual / "FROZEN_INPUTS_FINAL_02.json"))
          and adaptation["wrapper"]["sha256"] == digest(read(repo / adaptation["wrapper"]["path"])) ==
          "71f810000fdafa39c1cc28e0e5a219521e0e385fd7ae30fa0febfcbcfb3357bf"
          and adaptation["adapter_sha256"] == digest(read(packet / "native_protocol/protocol_adapter.py")) ==
          "8afada91c504c3f97f18cf20b519ac2f701b13fa2211e748bbbc4ddca6bead4f")

    memory_inputs = {
        "PROTOCOL_ADAPTATION.json": read(drivers / "PROTOCOL_ADAPTATION.json"),
        "FROZEN_INPUTS.json": read(actual / "FROZEN_INPUTS_FINAL_02.json"),
        "protocol_adapter.py": read(packet / "native_protocol/protocol_adapter.py"),
        "register_overlay.py": read(packet / "native_protocol/register_overlay.py"),
        "immutable_register_overlay.py": immutable,
        "executed_register_overlay.py": reconstructed.encode(),
    }
    input_checks = []
    for entry in receipt["input_files"]:
        target = repo / entry["path"]
        actual_bytes = read(target)
        origin = entry["input_path"]
        if origin.startswith("executed-memory:"):
            origin_bytes = memory_inputs[origin.split(":", 1)[1]]
        elif origin.startswith(BASE + ":"):
            origin_bytes = git_blob(origin)
        else:
            origin_bytes = read(Path(origin))
        check("archived_input_preserved:" + entry["role"] + ":" + entry["path"],
              actual_bytes == origin_bytes and digest(actual_bytes) == entry["sha256"])
        input_checks.append({**entry, "bytes": len(actual_bytes), "origin_bytes_equal": True})
    provenance = live["registration_provenance"]
    check("complete_39_record_registration_provenance",
          len(input_checks) == 39 and provenance["inputs"] == receipt["input_files"]
          and provenance["baseline_ref"] == BASE and provenance["source_tree_sha256"] == SOURCE
          and provenance["metadata_additions_only"] == sorted(additions)
          and provenance["raw_evidence_bytes_preserved"] is True
          and provenance["consumer_registry_modified"] is False
          and provenance["git_object_pr_preflight"] == receipt["git_object_pr_preflight"] ==
          "NOT_PERFORMED_SEPARATE_GATE" and provenance["independent_review"] == "SEPARATE_GATE")

    source_hash = hashlib.sha256()
    source_records = []
    core = repo / CORE
    source_paths = [core / "UEOT.lean", *(core / "UEOT").rglob("*.lean")]
    for module, path in sorted((p.relative_to(core).with_suffix("").as_posix().replace("/", "."), p)
                               for p in source_paths if p.is_file()):
        data = read(path)
        source_hash.update(module.encode() + b"\0" + data + b"\0")
        source_records.append({"module": module, "path": path.relative_to(repo).as_posix(),
                               "bytes": len(data), "sha256": digest(data)})
    check("full_current_source_unchanged_after_registration",
          len(source_records) == 691 and source_hash.hexdigest() == SOURCE
          and source_records == build["identity"]["source_files"])

    execution = obj(args.execution_receipt)
    execution_log = read(args.execution_receipt.parent / "run.log")
    check("actual_registration_command_and_result_bound",
          execution["state"] == "PASS" and execution["exit_code"] == 0
          and execution["mode"] == "REGISTER_METADATA"
          and "--check-only" not in execution["command"]
          and digest(execution_log) == execution["log_sha256"]
          and json.loads(execution_log) == execution["result"]
          and execution["result"]["receipt_sha256"] == digest(read(receipt_path))
          and execution["result"]["registered_overlay"] == receipt["registered_overlay"])
    for entry in review["key_actual_artifacts"]:
        check("reviewed_actual_artifact_still_exact:" + entry["path"],
              digest(read(repo / entry["path"])) == entry["sha256"])
    check("all_read_input_bytes_stable_during_review",
          all(path.read_bytes() == data for path, data in observed.items()))
    result = {
        "schema": "PATH_REALIZATION_INDEPENDENT_REGISTRATION_REVIEW_V1",
        "state": "CLEAR_METADATA_ONLY_REGISTRATION_AND_EXACT_BYTE_PRESERVATION",
        "reviewed_at_utc": datetime.now(timezone.utc).isoformat(),
        "reviewer": "/root/finite_memory_realization",
        "independence": {
            "registration_executor": "/root",
            "consumer_author": "/root/c3_executable_search",
            "protocol_static_reviewer": "/root/c3_executable_search",
            "disclosure": "Reviewer authored the frozen adapter and three Lean modules, but did not execute registration or author the six consumers. This independently checks the actual metadata/byte result and binds the separate protocol and execution reviews; it is not a self-signed independent protocol or mathematics review. No Lean/Mac/Git write or production artifact mutation was performed."
        },
        "baseline_ref": BASE, "source_tree_sha256": SOURCE,
        "registered_overlay_sha256": digest(read(live_path)),
        "raw_overlay_sha256": digest(read(raw_path)),
        "registration_receipt_sha256": digest(read(receipt_path)),
        "execution_review_sha256": digest(read(review_path)),
        "actual_registration_execution": {"receipt_path": str(args.execution_receipt),
            "receipt_sha256": digest(read(args.execution_receipt)),
            "seconds": execution["seconds"], "exit_code": execution["exit_code"],
            "mode": execution["mode"], "log_sha256": execution["log_sha256"]},
        "metadata_additions": sorted(additions),
        "raw_payload_deep_equality": True, "raw_archived_bytes_preserved": True,
        "live_native_and_verifier_exact_archived_bytes": True,
        "archived_input_records": input_checks,
        "archived_input_roles": dict(Counter(x["role"] for x in input_checks)),
        "lexical_source_counts": {"modules": 691, "prior_public": 4272,
            "new_public": 73, "registered_candidate_public": 4345, "hinted_groups": 25},
        "checks_passed": checks,
        "check_script_sha256": digest(Path(__file__).read_bytes()),
        "remaining": ["Independent six-consumer and DAG review", "Actual consumer/clone/canonical gates",
            "Git-object preflight and publication/resulting-main checks"],
        "raw_statuses_rewritten": False,
        "global_mathematical_closure": "NOT_ESTABLISHED",
    }
    output = Path(__file__).parent / "REGISTRATION_REVIEW.json"
    output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({"state": result["state"], "checks": len(checks),
        "input_records": len(input_checks), "output": str(output),
        "sha256": digest(output.read_bytes())}, indent=2))


if __name__ == "__main__":
    main()
