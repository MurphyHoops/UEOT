#!/usr/bin/env python3
"""Execute the two real Lean checks against observed, source-bound local builds.

This temporary runner never changes the repository or registers an overlay.
Every successful status is derived from subprocess exit codes and real files.
"""
from __future__ import annotations

import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import traceback

import prepare_registered_interfaces_export as export_helper
import build_identity

CORE_PREFIX = export_helper.CORE_PREFIX
NATIVE_PREFIX = "REGISTERED_INTERFACES_NATIVE_JSON "
STATUS_NAME = "registered-interfaces-native-pipeline-status.json"
EXPORTER_NAME = "REGISTERED_INTERFACES_NATIVE_EXPORT.lean"
VERIFIER_NAME = "VERIFY_REGISTERED_INTERFACES_OVERLAY_TYPES.lean"
NATIVE_NAME = "REGISTERED_INTERFACES_NATIVE_V1.json"
PREFLIGHT_NAME = "registered_interfaces_source_preflight.json"
RUN_LABELS = ("prepare_export", "native_export", "prepare_fixed", "fixed_verifier")
ROOT_IMPORT = CORE_PREFIX + "UEOT/V3/Compression/TheoryCompletion.lean"
NEW_PATHS = {
    CORE_PREFIX + (export_helper.SCOPE + "." + stem).replace(".", "/") + ".lean"
    for stem in export_helper.STEMS
}


def sha(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def read_json(path: Path):
    return json.loads(path.read_text())


def write_json(path: Path, value) -> None:
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n")


def native_json(logfile: Path):
    rows = [line[len(NATIVE_PREFIX):] for line in logfile.read_text().splitlines()
            if line.startswith(NATIVE_PREFIX)]
    if len(rows) != 1:
        raise RuntimeError("MISSING_OR_MULTIPLE_NATIVE_RECORDS: " + str(logfile))
    value = json.loads(rows[0])
    if not isinstance(value, dict) or value.get("schema") != "REGISTERED_INTERFACES_NATIVE_EXPORT_V1":
        raise RuntimeError("UNEXPECTED_NATIVE_JSON_SCHEMA")
    return value


def resolve_commit(repo: Path, ref: str) -> str:
    value = subprocess.check_output(
        ["git", "rev-parse", "--verify", ref + "^{commit}"], cwd=repo, text=True).strip()
    if not re.fullmatch(r"[0-9a-f]{40}", value):
        raise RuntimeError("EXPECTED_ACTUAL_GIT_COMMIT_ID")
    return value


def validate_build_inputs(repo: Path, status_path: Path, manifest_path: Path,
                          log_dir: Path, focused_label: str, full_label: str) -> dict:
    """Read actual receipt plus its real logs and recheck every frozen source."""
    raw = read_json(status_path)
    receipt = raw.get("status", raw)
    if not isinstance(receipt, dict) or str(receipt.get("state", "")).lower() != "pass":
        raise RuntimeError("FINAL_NEW_MODULE_AND_FULL_BUILD_NOT_OBSERVED")
    rows = receipt.get("results", [])
    if not isinstance(rows, list) or not rows:
        raise RuntimeError("MISSING_ACTUAL_BUILD_RESULTS")
    labels = [row.get("label") for row in rows]
    if len(labels) != len(set(labels)) or set(labels) != {focused_label, full_label}:
        raise RuntimeError("REQUIRED_BUILD_RESULT_SET_MISMATCH")
    manifest = read_json(manifest_path)
    manifest_sha = sha(manifest_path)
    if receipt.get("source_manifest_sha256") != manifest_sha:
        raise RuntimeError("BUILD_RECEIPT_MUST_BIND_THE_SAME_SOURCE_MANIFEST")
    files = manifest.get("files", [])
    paths = [row.get("path") for row in files]
    if len(paths) != len(set(paths)) or set(paths) != NEW_PATHS | {ROOT_IMPORT}:
        raise RuntimeError("EXPECTED_FINAL_NEW_SOURCES_AND_PUBLIC_ROOT_IN_BUILD_MANIFEST")
    for row in files:
        if sha(repo / row["path"]) != row.get("sha256"):
            raise RuntimeError("SOURCE_DIFFERS_FROM_ACTUAL_BUILD_MANIFEST: " + row["path"])
    identity = manifest.get("build_identity")
    if not isinstance(identity, dict):
        raise RuntimeError("ACTUAL_BUILD_MUST_BIND_COMPLETE_SOURCE_AND_RUNTIME_IDENTITY")
    observed_identity = build_identity.capture(
        repo,
        lake=identity["runtime_tools"]["lake"]["executable"],
        lean=identity["runtime_tools"]["lean"]["executable"],
        expected=identity,
        expected_module_count=export_helper.HISTORICAL_MODULES + len(export_helper.STEMS),
    )
    predecessor = resolve_commit(repo, manifest["predecessor_head"])
    builds = []
    for row in rows:
        code = row.get("exit_code", row.get("returncode"))
        if type(code) is not int or code != 0:
            raise RuntimeError("ACTUAL_BUILD_EXIT_NOT_ZERO: " + str(row.get("label")))
        label = row["label"]
        if not isinstance(label, str) or not re.fullmatch(r"[a-zA-Z0-9_-]+", label):
            raise RuntimeError("INVALID_BUILD_LOG_LABEL")
        logfile = log_dir / (label + ".log")
        actual_sha = sha(logfile)
        if actual_sha != row.get("log_sha256"):
            raise RuntimeError("ACTUAL_BUILD_LOG_HASH_MISMATCH: " + label)
        record = {"label": label, "exit_code": code,
                  "log": logfile.name, "log_sha256": actual_sha}
        if "elapsed_seconds" in row:
            record["elapsed_seconds"] = row["elapsed_seconds"]
        if "command" in row:
            record["command"] = row["command"]
        counts = re.findall(r"Build completed successfully \((\d+) jobs\)", logfile.read_text())
        if len(counts) == 1:
            record["observed_build_jobs"] = int(counts[0])
        builds.append(record)
    return {
        "build_status_sha256": sha(status_path),
        "source_manifest_sha256": manifest_sha,
        "baseline_ref": predecessor,
        "source_files": files,
        "build_identity": observed_identity,
        "focused_label": focused_label,
        "full_label": full_label,
        "builds": builds,
        "source_binding": "The successful build receipt pins the complete production source tree, exact dependency checkouts, three environment files and actual Lean/Lake executables, in addition to the new-source manifest and both actual build-log hashes. All identities are rechecked before and after native execution.",
    }


def run_pipeline(args) -> dict:
    repo, output = args.repo.resolve(), args.output.resolve()
    if output.is_relative_to(repo):
        raise RuntimeError("TEMPORARY_OUTPUT_MUST_BE_OUTSIDE_REPOSITORY")
    if output.exists() and any(output.iterdir()):
        raise RuntimeError("USE_A_FRESH_EMPTY_OUTPUT_DIRECTORY_FOR_ACTUAL_EXECUTION")
    output.mkdir(parents=True, exist_ok=True)
    core = repo / CORE_PREFIX
    helpers = Path(__file__).resolve().parent
    results = []
    status_path = output / STATUS_NAME
    binding = None
    env = os.environ.copy()
    env["PATH"] = str(Path.home() / ".elan/bin") + ":/opt/homebrew/bin:" + env.get("PATH", "")
    env["PYTHONDONTWRITEBYTECODE"] = "1"

    def report(state, **extra):
        write_json(status_path, {"state": state, "results": results,
                                "build_binding": binding, **extra})

    def run(label, command):
        report("running", active=label)
        logfile = output / (label + ".log")
        with logfile.open("w") as stream:
            completed = subprocess.run(command, cwd=core, env=env, stdout=stream,
                                       stderr=subprocess.STDOUT)
        results.append({"label": label, "returncode": completed.returncode,
                        "command": command, "log_sha256": sha(logfile)})
        report("running", last_completed=label)
        if completed.returncode:
            # A collision is a real failed run. Preserve its actually printed
            # raw JSON as well as the original log; never manufacture PASS.
            if label in ("native_export", "fixed_verifier"):
                try:
                    failed_native = native_json(logfile)
                except (RuntimeError, ValueError):
                    failed_native = None
                if failed_native is not None:
                    name = "observed_failed_" + label + ".json"
                    write_json(output / name, failed_native)
                    results[-1]["failed_native_artifact"] = name
                    results[-1]["failed_native_sha256"] = sha(output / name)
            raise RuntimeError(label + "_ACTUAL_EXECUTION_FAILED")
        return logfile

    try:
        binding = validate_build_inputs(repo, args.build_status, args.build_manifest,
                                        args.build_log_dir, args.focused_label, args.full_label)
        resolved_lake = shutil.which(args.lake)
        runtime = binding["build_identity"]["runtime_tools"]
        if not resolved_lake or str(Path(resolved_lake).resolve()) != runtime["lake"]["executable"]:
            raise RuntimeError("NATIVE_LAKE_DIFFERS_FROM_ACTUAL_BUILD_RUNTIME")
        actual_lean = runtime["lean"]["executable"]
        base_ref = binding["baseline_ref"]
        if args.base_ref and resolve_commit(repo, args.base_ref) != base_ref:
            raise RuntimeError("BASE_REF_DIFFERS_FROM_BUILD_MANIFEST_PREDECESSOR")
        run("prepare_export", [sys.executable, "-B", str(helpers / "prepare_registered_interfaces_export.py"),
                               "--repo", str(repo), "--output", str(output), "--base-ref", base_ref])
        first_log = run("native_export", [args.lake, "env", actual_lean, str(output / EXPORTER_NAME)])
        first = native_json(first_log)
        write_json(output / "observed_first_native.json", first)
        run("prepare_fixed", [sys.executable, "-B", str(helpers / "prepare_registered_interfaces_fixed_certificate.py"),
                              "--repo", str(repo), "--preflight", str(output / PREFLIGHT_NAME),
                              "--native", str(output / "observed_first_native.json"),
                              "--exporter", str(output / EXPORTER_NAME), "--output", str(output)])
        fixed_log = run("fixed_verifier", [args.lake, "env", actual_lean, str(output / VERIFIER_NAME)])
        fixed = native_json(fixed_log)
        write_json(output / "observed_fixed_native.json", fixed)
        match = first == fixed
        comparison = {
            "status": "EXACT_JSON_OBJECT_MATCH" if match else "MISMATCH",
            "first_sha256": sha(output / "observed_first_native.json"),
            "fixed_sha256": sha(output / "observed_fixed_native.json"),
            "scope": "Every JSON field: all native constants in seven new and one historical module, private/generated names, types, universe parameters, owners, axioms, full direct constants, public registered edges, 52-new/1-historical comparison partitions, and the complete 4094-proof narrow incoming-edge scan.",
        }
        write_json(output / "native_fixed_comparison_status.json", comparison)
        if not match:
            raise RuntimeError("FIRST_AND_FIXED_FULL_NATIVE_JSON_OBJECTS_DIFFER")
        repeated_binding = validate_build_inputs(repo, args.build_status, args.build_manifest,
                                                 args.build_log_dir, args.focused_label, args.full_label)
        if repeated_binding != binding:
            raise RuntimeError("BUILD_BINDING_DRIFT_DURING_NATIVE_EXECUTION")
        knowledge = core / "docs/compression/theory_completion/knowledge"
        extractor = export_helper.import_file("registered_interfaces_post_native_fkrg", knowledge / "fkrg.py")
        preflight = read_json(output / PREFLIGHT_NAME)
        if extractor.fingerprint(extractor.sources()) != preflight["source_tree_sha256"]:
            raise RuntimeError("FULL_LEAN_SOURCE_TREE_DRIFT_DURING_NATIVE_EXECUTION")
        # The canonical artifact is literally the actually executed fixed-verifier output.
        (output / NATIVE_NAME).write_bytes((output / "observed_fixed_native.json").read_bytes())
        scope = fixed["all_native_theorem_constants"]
        report("pass", public_theorems=len(fixed["public_source_theorems"]),
               new_source_public_theorems=fixed["new_source_public_theorem_count"],
               historical_public_repairs=fixed["historical_public_repair_count"],
               historical_registered_proofs_scanned=fixed["historical_repair_incoming_scan"]["registered_theorems_scanned"],
               existing_proof_dependency_repair_nodes=len(fixed["historical_repair_incoming_scan"]["incoming_rows"]),
               native_theorems=len(scope), private_theorems=sum(row["is_private"] for row in scope),
               cross_comparisons=fixed["cross_isDefEq_comparisons"],
               internal_comparisons=fixed["internal_isDefEq_comparisons"],
               collisions=fixed["collisions"], binding=comparison,
               overlay_status="PENDING_OUTER_TYPED_REUSE_REVIEW_AND_REGISTRATION")
        return read_json(status_path)
    except Exception as error:
        report("fail", error=str(error), traceback=traceback.format_exc())
        raise


def add_build_arguments(parser):
    parser.add_argument("--build-status", type=Path, required=True)
    parser.add_argument("--build-manifest", type=Path, required=True)
    parser.add_argument("--build-log-dir", type=Path, required=True)
    parser.add_argument("--focused-label", default="new_modules")
    parser.add_argument("--full-label", default="full_ueot")
    parser.add_argument("--base-ref", help="Optional extra check against the build manifest predecessor.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lake", default="lake")
    add_build_arguments(parser)
    args = parser.parse_args()
    result = run_pipeline(args)
    print(json.dumps({"state": result["state"], "public_theorems": result["public_theorems"],
                      "native_theorems": result["native_theorems"],
                      "overlay_status": result["overlay_status"]}))
