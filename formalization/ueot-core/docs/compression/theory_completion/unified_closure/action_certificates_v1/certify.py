#!/usr/bin/env python3
"""Certify exact finite candidates only after their generated Lean proof passes.

Usage: certify.py --registered --output NEW_DIRECTORY
       certify.py INPUT.json --output NEW_DIRECTORY
The output directory retains source tables, candidates, generated proof, commands,
logs and hashes. Search failure and any Lean/build failure remain UNKNOWN.
"""
from __future__ import annotations

import argparse
from hashlib import sha256
import json
from pathlib import Path
import shutil
import subprocess
import sys

from emit_lean_witness import emit
from exact_certificates import Source, registered_cases, run

CORE = Path(__file__).resolve().parents[5]
SOURCE_MODULE = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RationalConditionedSource"


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def snapshot(path, text):
    """Hash the intended bytes, rather than trusting a subsequent file read."""
    data = text.encode()
    path.write_bytes(data)
    return sha256(data).hexdigest()


def source_identity():
    """Bind the proof run to its actual Core sources and pinned toolchain."""
    paths = sorted((CORE / "UEOT").rglob("*.lean"))
    paths += [p for p in (CORE / "lean-toolchain", CORE / "lake-manifest.json",
                          CORE / "lakefile.toml", CORE / "lakefile.lean", CORE / "UEOT.lean") if p.is_file()]
    return {str(p.relative_to(CORE)): digest(p) for p in paths}


def execute(command, log):
    with log.open("w") as stream:
        try:
            code = subprocess.run(command, cwd=CORE, stdout=stream, stderr=subprocess.STDOUT,
                                  check=False).returncode
        except OSError as error:
            stream.write(str(error) + "\n")
            code = 127
    return {"command": command, "cwd": str(CORE), "exit_code": code,
            "log": str(log), "log_sha256": digest(log)}


def certified_status(candidate):
    if not candidate.get("target", {}).get("Z"):
        return "CONDITIONING_UNDEFINED"
    cert = candidate.get("certificate", {})
    if "weights" in cert:
        return "CERTIFIED_REALIZABLE"
    if cert or "initial_TV_lower_bound" in candidate:
        return "CERTIFIED_UNREALIZABLE"
    return "UNKNOWN"


def certify(cases, output):
    output = output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    # Detach caller-owned mutable data, then normalize valid rational sources.
    cases = json.loads(json.dumps(cases, default=str))
    candidates = {name: run(raw) for name, raw in cases.items()}
    cases = {name: Source.read(raw).__dict__ if candidates[name]["status"] != "INVALID_INPUT" else raw
             for name, raw in cases.items()}
    source = output / "source.json"
    source_sha = snapshot(source, json.dumps(cases, sort_keys=True, indent=2, default=str) + "\n")
    candidate_file = output / "candidates.json"
    candidate_sha = snapshot(candidate_file, json.dumps(candidates, sort_keys=True, indent=2,
                                                       default=str) + "\n")
    valid = {name: raw for name, raw in cases.items()
             if candidates[name]["status"] != "INVALID_INPUT"}
    driver_paths = [Path(__file__), Path(__file__).with_name("emit_lean_witness.py"),
                    Path(__file__).with_name("exact_certificates.py")]
    drivers = {str(p): digest(p) for p in driver_paths}
    evidence = {"schema": "UEOT/EXACT_ACTION_CERTIFICATION/V1", "driver_sources": drivers,
                "source": str(source),
                "source_sha256": source_sha, "candidates": str(candidate_file),
                "candidates_sha256": candidate_sha, "cases": {}, "verification": []}
    verified = False
    if valid:
        proof = output / "Certificate.lean"
        proof_sha = snapshot(proof, emit(valid, candidates=candidates))
        evidence.update(lean_source=str(proof), lean_source_sha256=proof_sha)
        lake = shutil.which("lake")
        if lake is None:
            evidence["failure"] = "lake executable unavailable"
        else:
            before = source_identity()
            source_manifest = output / "core-source-identity.json"
            manifest_sha = snapshot(source_manifest, json.dumps(before, sort_keys=True, indent=2) + "\n")
            evidence.update(core_source_identity=str(source_manifest), core_source_identity_sha256=manifest_sha)
            bound = {str(source): source_sha, str(candidate_file): candidate_sha,
                     str(proof): proof_sha, str(source_manifest): manifest_sha}
            evidence.update(bound_artifacts=bound, binding_checks=[])

            def matches(stage):
                # Exclusive new output directory, with no other intended writer.
                # Endpoint checks do not claim to defeat change-and-restore races.
                check = {"stage": stage, "artifacts_match": False, "sources_match": False}
                try:
                    check["artifacts_match"] = all(digest(Path(p)) == sha for p, sha in bound.items())
                    check["sources_match"] = before == source_identity() and drivers == {
                        str(p): digest(p) for p in driver_paths}
                except OSError as error:
                    check["error"] = str(error)
                evidence["binding_checks"].append(check)
                stable = all(c["sources_match"] for c in evidence["binding_checks"])
                evidence["sources_unchanged_during_build_and_proof"] = stable
                evidence["core_sources_unchanged_during_proof"] = stable
                evidence["artifacts_unchanged_during_build_and_proof"] = all(
                    c["artifacts_match"] for c in evidence["binding_checks"])
                if not check["artifacts_match"] or not check["sources_match"]:
                    evidence["failure"] = "Bound input, candidate, proof, identity manifest, source or driver changed or missing"
                    return False
                return True

            if matches("before_build"):
                build = execute([lake, "build", SOURCE_MODULE], output / "build.log")
                evidence["verification"].append(build)
                if matches("after_build") and build["exit_code"] == 0 and matches("before_proof"):
                    checked = execute([lake, "env", "lean", str(proof)], output / "lean.log")
                    evidence["verification"].append(checked)
                    verified = matches("after_proof") and checked["exit_code"] == 0
            if not verified and "failure" not in evidence:
                evidence["failure"] = "Lean build or proof rejected the generated obligations"
    for name, candidate in candidates.items():
        if candidate["status"] == "INVALID_INPUT":
            result = {"status": "INVALID_INPUT", "reason": candidate["reason"]}
        elif verified:
            result = {"status": certified_status(candidate), "proof_namespace": f"case_{list(valid).index(name)}"}
        else:
            result = {"status": "UNKNOWN", "reason": evidence.get("failure", "No Lean proof executed")}
        evidence["cases"][name] = result
    manifest = output / "result.json"
    manifest.write_text(json.dumps(evidence, sort_keys=True, indent=2) + "\n")
    return evidence, manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", nargs="?", type=Path)
    parser.add_argument("--registered", action="store_true")
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    if args.registered == bool(args.input):
        parser.error("supply exactly one of INPUT.json and --registered")
    try:
        cases = registered_cases() if args.registered else {"input": json.loads(args.input.read_text())}
        result, manifest = certify(cases, args.output)
    except (OSError, ValueError) as error:
        parser.error(str(error))
    print(json.dumps({"cases": result["cases"], "receipt": str(manifest),
                      "receipt_sha256": digest(manifest)}, sort_keys=True, indent=2))
    return 0 if all(c["status"] != "UNKNOWN" for c in result["cases"].values()) else 1


if __name__ == "__main__":
    sys.exit(main())
