#!/usr/bin/env python3
"""Inspect archived CI proof evidence against an already fetched Git commit.

This is a read-only identity/audit check. It does not compile Lean, expand the
formalized scope, or turn an expected failed elaboration into an accepted proof.
Artifact IDs and the expected ZIP digest come from the observed GitHub API.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import zipfile


ROOT = Path(__file__).resolve().parents[4]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    for name in ["zip", "sha256", "head", "output"]:
        parser.add_argument("--" + name, required=True)
    parser.add_argument("--run", required=True, type=int)
    parser.add_argument("--artifact", required=True, type=int)
    args = parser.parse_args()
    archive_bytes = Path(args.zip).read_bytes()
    assert digest(archive_bytes) == args.sha256
    archive = zipfile.ZipFile(args.zip)
    prefix = next(name.removesuffix("source-manifest.json")
                  for name in archive.namelist()
                  if name.endswith("formalization/ueot-qm/source-manifest.json"))

    def read_json(name):
        return json.loads(archive.read(name))

    def at_commit(path):
        return subprocess.check_output(["git", "show", args.head + ":" + path], cwd=ROOT)

    def archive_path(path):
        marker = "/home/runner/work/"
        assert path.startswith(marker), path
        return path.removeprefix(marker)

    manifest = read_json(prefix + "source-manifest.json")
    assert manifest["observed_checkout_commit"] == args.head
    assert len(manifest["sources"]) == manifest["source_count"]
    for item in manifest["sources"]:
        data = at_commit(item["path"])
        assert digest(data) == item["sha256"] and len(data) == item["bytes"]
    identity_log = archive.read(prefix + "source-identity.log").decode()
    assert identity_log.splitlines()[0] == args.head
    build_log = archive.read(prefix + "lean-build.log").decode()
    assert "Built UEOTQM.OperationalEquivalence" in build_log
    assert "Build completed successfully" in build_log

    audit = read_json(prefix + "proof-axioms.json")
    assert audit["status"] == "PASS" and set(audit["allowed_foundation"]) == ALLOWED
    declarations = audit["declarations"]
    assert len(declarations) == audit["declaration_count"] == 1365
    assert all(set(found) <= ALLOWED for found in declarations.values())
    requests = re.findall(r"(?m)^#print axioms (\S+)\s*$",
                          at_commit("formalization/ueot-qm/scripts/AxiomAudit.lean").decode())
    assert len(requests) == len(set(requests)) == len(declarations)
    assert set(requests) == set(declarations)
    audit_text = archive.read(prefix + "axiom-audit.log").decode()
    parsed = {}
    for name, names in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",
                                  audit_text, re.S):
        assert name not in parsed
        parsed[name] = {part.strip() for part in names.split(",") if part.strip()}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", audit_text):
        assert name not in parsed
        parsed[name] = set()
    assert parsed == {name: set(found) for name, found in declarations.items()}
    operational = [name for name in declarations
                   if name.startswith("UEOTQM.OperationalEquivalence.")]
    assert len(operational) == 80

    exports = read_json("_temp/ueot-qm-lean-exports/verification.json")
    assert exports["status"] == "PASS" and not exports["problems"]
    assert set(exports["allowed_axioms"]) == ALLOWED
    assert len(exports["positive_cases"]) == 6 and len(exports["negative_cases"]) == 4

    def check_execution(execution, accepted):
        assert not execution["timed_out"] and not execution["launch_error"]
        assert (execution["exit_code"] == 0) == accepted
        assert digest(archive.read(archive_path(execution["log_path"]))) == execution["log_sha256"]

    for case in exports["positive_cases"]:
        assert case["status"] == "PASS" and not case["problems"]
        check_execution(case["execution"], True)
        assert digest(archive.read(archive_path(case["source_path"]))) == case["source_sha256"]
        assert all(set(found) <= ALLOWED for found in case["actual_axioms"].values())
    for case in exports["negative_cases"]:
        assert case["status"] == "PASS" and not case["problems"]
        assert case["data_prefixes_identical_after_both_compilations"]
        check_execution(case["true_claim_rejection"]["execution"], False)
        check_execution(case["false_witness"]["execution"], True)
        # Failed elaborations can report sorryAx placeholders. Those failed
        # candidates are preserved and never counted as accepted proof terms.
        assert all(set(found) <= ALLOWED
                   for found in case["false_witness"]["actual_axioms"].values())

    finite = read_json("_temp/ueot-qm-finite-witnesses/verification.json")
    assert finite["status"] == "PASS" and not finite["errors"]
    assert finite["selection_is_complete"] and finite["all_inputs_unchanged"]
    assert len(finite["checks"]) == 13
    repo_prefix = "/home/runner/work/UEOT/UEOT/"
    module_sources = finite["inputs_before"]["general_modules"]
    for module in module_sources.values():
        item = module["source"]
        assert item["path"].startswith(repo_prefix)
        assert digest(at_commit(item["path"].removeprefix(repo_prefix))) == item["sha256"]
    for case in finite["checks"]:
        assert case["status"] == "PASS" and case["exit_code"] == 0
        assert case["inputs_unchanged"] and case["audit"]["complete_unique"]
        assert case["audit"]["status"] == "PASS" and not case["audit"]["unreviewed_axioms"]
        assert digest(archive.read(archive_path(case["log"]["path"]))) == case["log"]["sha256"]
        source = case["source"]
        assert digest(at_commit(source["path"].removeprefix(repo_prefix))) == source["sha256"]

    receipt = {
        "schema": "ueot-qm.remote-lean-inspection/1", "status": "PASS",
        "observed_at_utc": datetime.now(timezone.utc).isoformat(),
        "checker_sha256": digest(Path(__file__).read_bytes()), "command": sys.argv,
        "run_id": args.run, "artifact_id": args.artifact,
        "workflow_url": "https://github.com/MurphyHoops/UEOT/actions/runs/" + str(args.run),
        "scientific_head": args.head, "artifact_sha256": args.sha256,
        "public_source_manifest_count": manifest["source_count"],
        "public_source_set_sha256": manifest["source_set_sha256"],
        "recursive_module_sources_matched": len(module_sources),
        "axiom_requests_and_actual_reports": len(declarations),
        "new_operational_namespace_constants": len(operational),
        "allowed_foundations": sorted(ALLOWED),
        "positive_export_cases": 6, "false_certificate_rejections_and_false_witnesses": 4,
        "retained_finite_witnesses": 13,
        "logs": {name: digest(archive.read(prefix + name)) for name in
                 ["source-identity.log", "lean-build.log", "axiom-audit.log", "lean-install.log"]},
        "scope": "Actual public build/audit and archived finite witnesses; source manifests with different scopes retain their distinct identities",
        "not_proved_by_this_check": ["whole OPT formalization", "trace-class paper statements",
                                     "device validity", "empirical closure"],
    }
    Path(args.output).write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt))


if __name__ == "__main__":
    main()
