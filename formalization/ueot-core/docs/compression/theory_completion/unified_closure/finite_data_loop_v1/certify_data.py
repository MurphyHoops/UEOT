#!/usr/bin/env python3
"""Promote data-only candidates only after their bound literal Lean proof passes.

No private truth or observed Good value is read. The positive/negative theorem
quantifies over every true Box parameter satisfying Good. The byte parser and
sampling-source interface remain explicit preconditions of statistical use.
"""
from __future__ import annotations

import argparse
from hashlib import sha256
import json
from pathlib import Path
import shutil
import sys

import selector
from selector import encoded, select
from emit_data import emit
# selector adds the existing certificate directory to the import path.
import certify as exact_runner
from certify import execute, snapshot, source_identity, digest
import emit_data
import exact_certificates

PREFIX = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."


def certify(record, horizon, output):
    record, output = Path(record).resolve(), Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    proposal = select(record, horizon)
    candidate_file = output / "candidate.json"
    candidate_sha = snapshot(candidate_file, encoded(proposal).decode())
    result = {"schema": "UEOT/FINITE_DATA_STATISTICAL_CERTIFICATE/V1", "status": "UNKNOWN",
              "record": str(record), "horizon": horizon, "candidate": str(candidate_file),
              "candidate_sha256": candidate_sha, "verification": [], "binding_checks": [],
              "meaning": "Universal Box(theta) and Good(theta,estimate,1/250) conditional conclusion; Good and truth are not selector inputs.",
              "host_boundary": "Counts are recomputed from every bound raw bit; byte parsing is not a native per-bit Lean proof."}
    accepted = proposal["status"] in ("CANDIDATE_STATISTICAL_APPROX", "CANDIDATE_STATISTICAL_NO_GO")
    verified = False
    if not accepted:
        result.update(status="INVALID_INPUT" if proposal["status"] == "INVALID_INPUT" else "UNKNOWN",
                      reason=proposal.get("reason", "No positive-horizon statistical candidate"))
    else:
        try:
            identity = proposal["data_identity"]
            training = record / "training.json"
            training_bytes = training.read_bytes()
            public = record.parent.parent / "FREEZE.json"
            freeze = json.loads(public.read_bytes())
            numerical = record.parent.parent / "NUMERICAL_PROOF.json"
            bound = {str(candidate_file): candidate_sha, str(training): identity["training_sha256"],
                     str(public): identity["freeze_sha256"], str(numerical): freeze["numerical_receipt_sha256"]}
            bound.update({str(record / name): sha for name, sha in identity["raw_probe_sha256"].items()})
            batch = record.parent.parent
            decision = batch / "decisions" / f"{identity['record_id']}-T{horizon}.json"
            deployment = batch / "deployments" / decision.name
            sample_result = batch / "SAMPLE_RESULT.json"
            if decision.exists() or deployment.exists() or sample_result.exists() or (batch / "SAMPLE_STARTED.json").exists():
                saved = decision.read_bytes()
                if saved != encoded(proposal):
                    raise ValueError("Saved decision differs from the data-recomputed literal candidate")
                decision_sha = sha256(saved).hexdigest()
                trace_bytes = deployment.read_bytes()
                trace = json.loads(trace_bytes)
                if not isinstance(trace, dict) or trace.get("decision_sha256") != decision_sha or trace.get("training_sha256") != identity["training_sha256"] or trace.get("T") != horizon:
                    raise ValueError("Deployment trace does not bind this training record and saved decision")
                sample_bytes = sample_result.read_bytes()
                sampling = json.loads(sample_bytes)
                if not isinstance(sampling, dict) or sampling.get("schema") != "UEOT/FINITE_DATA_SAMPLE_RESULT/V1" or sampling.get("freeze_sha256") != identity["freeze_sha256"]:
                    raise ValueError("Saved sampler provenance has the wrong frozen batch")
                matches_record = [r for r in sampling["records"] if isinstance(r, dict) and r.get("record") == identity["record_id"]]
                if len(matches_record) != 1 or matches_record[0].get("state") != "COMPLETE":
                    raise ValueError("Missing unique completed sampled record")
                rows = [r for r in matches_record[0]["decisions"] if isinstance(r, dict) and r.get("T") == horizon]
                if len(rows) != 1 or rows[0].get("decision_sha256") != decision_sha or rows[0].get("deployment_sha256") != sha256(trace_bytes).hexdigest():
                    raise ValueError("Saved decision or deployment trace changed since sampling")
                bound.update({str(decision): decision_sha, str(deployment): sha256(trace_bytes).hexdigest(),
                              str(sample_result): sha256(sample_bytes).hexdigest()})
                result["saved_decision"] = {"path": str(decision), "sha256": decision_sha}
                result["saved_deployment"] = {"path": str(deployment), "sha256": sha256(trace_bytes).hexdigest(),
                                               "state": trace["status"]}
            else:
                result["deployment_binding"] = "No saved deployment; universal literal-policy implication only"

            training_copy = output / "training.json"
            bound[str(training_copy)] = snapshot(training_copy, training_bytes.decode())
            proof = output / "Certificate.lean"
            bound[str(proof)] = snapshot(proof, emit(proposal))
            result.update(lean_source=str(proof), lean_source_sha256=bound[str(proof)],
                          training_source=str(training_copy), training_source_sha256=bound[str(training_copy)])
            before = source_identity()
            core_manifest = output / "core-source-identity.json"
            bound[str(core_manifest)] = snapshot(core_manifest, encoded(before).decode())
            drivers = [Path(__file__), Path(selector.__file__), Path(emit_data.__file__),
                       Path(exact_runner.__file__), Path(exact_certificates.__file__),
                       Path(exact_runner.__file__).with_name("emit_lean_witness.py")]
            driver_hashes = {str(p): digest(p) for p in drivers}
            result.update(bound_artifacts=bound, driver_sources=driver_hashes,
                          core_source_identity=str(core_manifest), core_source_identity_sha256=bound[str(core_manifest)])

            def matches(stage):
                row = {"stage": stage, "match": False}
                try:
                    row["match"] = all(digest(Path(p)) == sha for p, sha in bound.items()) and before == source_identity() and all(
                        digest(Path(p)) == sha for p, sha in driver_hashes.items())
                except OSError as error:
                    row["error"] = str(error)
                result["binding_checks"].append(row)
                if not row["match"]:
                    result["reason"] = "Input/raw data, proof, manifest, source or driver changed or missing"
                return row["match"]

            lake = shutil.which("lake")
            if lake is None:
                result["reason"] = "lake executable unavailable"
            elif matches("before_build"):
                built = execute([lake, "build", PREFIX + "FiniteDataCertifiedConsumer", PREFIX + "FiniteDataJoint"], output / "build.log")
                result["verification"].append(built)
                if matches("after_build") and built["exit_code"] == 0 and matches("before_proof"):
                    checked = execute([lake, "env", "lean", str(proof)], output / "lean.log")
                    result["verification"].append(checked)
                    verified = matches("after_proof") and checked["exit_code"] == 0
            if verified:
                result["status"] = ("CONDITIONAL_STATISTICAL_APPROX" if proposal["decision"] == "ACCEPT"
                                    else "STATISTICAL_NO_GO")
                result["returned_preparation"] = proposal["preparation"]
                result["returned_weights"] = proposal["weights"]
                result["beta_prep"] = proposal["beta_prep"]
                if proposal["decision"] == "ACCEPT":
                    result["proven_reference_prepared"] = proposal["reference_prepared"]
                    result["proven_reference_initial_residual"] = proposal["reference_initial_residual"]
                    result["proven_reference_row_residuals"] = proposal["reference_row_residuals"]
                    result["proven_reference_path_bound"] = proposal["reference_path_bound"]
                result["statistical_failure_lower"] = proposal["failure_probability_lower"]
                result["joint_event_risk_upper"] = proposal["accepted_joint_risk_upper"]
                result["joint_risk_scope"] = "Ideal registered product-training/selection/deployment Accept∩Fail, not P(Fail|Accept) and not a three-deployment union bound."
            elif "reason" not in result:
                result["reason"] = "Lean rejected the build or bound generated proof"
        except (OSError, ValueError, KeyError, TypeError) as error:
            result["reason"] = str(error)
    receipt = output / "result.json"
    receipt.write_bytes(encoded(result))
    return result, receipt


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("record", type=Path)
    parser.add_argument("--horizon", required=True, type=int)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    result, receipt = certify(args.record, args.horizon, args.output)
    print(json.dumps({"status": result["status"], "receipt": str(receipt), "receipt_sha256": digest(receipt)}))
    raise SystemExit(0 if result["status"] in ("CONDITIONAL_STATISTICAL_APPROX", "STATISTICAL_NO_GO") else 1)
