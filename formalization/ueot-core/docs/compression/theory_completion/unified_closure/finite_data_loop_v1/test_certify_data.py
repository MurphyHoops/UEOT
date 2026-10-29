#!/usr/bin/env python3
"""Binding faults and actual Lean on handcrafted counts; no registered sampling."""
from copy import deepcopy
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

import certify_data as runner
from batch import realization
from selector import N, encoded, digest
from test_runtime import fixture


def saved_execution(record):
    """Handcrafted unit trajectory, never a registered draw or freeze."""
    proposal = runner.select(record, 2)
    identity = proposal["data_identity"]
    root = record.parent.parent
    decision = root / "decisions" / f"{identity['record_id']}-T2.json"
    deployment = root / "deployments" / decision.name
    decision.parent.mkdir()
    deployment.parent.mkdir()
    decision.write_bytes(encoded(proposal))
    trace = realization(["3/4", "1/4", "1/200", "1/200"], proposal, "00")
    assert trace["operation_count"] == 3 and len(trace["operations"]) == 3
    trace.update(decision_sha256=digest(decision.read_bytes()),
                 training_sha256=identity["training_sha256"], T=2)
    deployment.write_bytes(encoded(trace))
    sample_result = root / "SAMPLE_RESULT.json"
    sample_result.write_bytes(encoded({"schema": "UEOT/FINITE_DATA_SAMPLE_RESULT/V1",
        "freeze_sha256": identity["freeze_sha256"], "records": [{"record": identity["record_id"],
        "state": "COMPLETE", "decisions": [{"T": 2,
        "decision_sha256": digest(decision.read_bytes()),
        "deployment_sha256": digest(deployment.read_bytes())}]}]}))
    return decision, deployment, sample_result


def check():
    low = [3*N//4, N//4, N//200, N//200]
    with TemporaryDirectory() as temp:
        root = Path(temp)
        record, _ = fixture(root / "synthetic", low)
        with patch.object(runner, "source_identity", return_value=runner.source_identity()):
            for filename in ("candidate.json", "Certificate.lean", "core-source-identity.json", "RAW"):
                def alter(command, log):
                    target = record / "risk0_safe.bin" if filename == "RAW" else log.parent / filename
                    if filename == "core-source-identity.json":
                        target.unlink()
                    else:
                        target.write_bytes(b"-- replaced\n" if filename.endswith(".lean") else b"\x00")
                    return {"exit_code": 0}
                raw = (record / "risk0_safe.bin").read_bytes()
                with patch.object(runner, "execute", side_effect=alter) as execute:
                    failed, _ = runner.certify(record, 2, root / (filename + "-failure"))
                (record / "risk0_safe.bin").write_bytes(raw)
                assert failed["status"] == "UNKNOWN", filename
                assert execute.call_count == 1
                assert not failed["binding_checks"][-1]["match"]
            with patch.object(runner, "execute", side_effect=AssertionError("invalid input invoked Lean")):
                invalid, _ = runner.certify(root / "missing-record", 2, root / "invalid")
            assert invalid["status"] == "INVALID_INPUT"
        # Genuine source snapshots and actual Lean for the data-only universal
        # implication. The fixture is not claimed to be a product-law sample.
        positive, receipt = runner.certify(record, 2, root / "actual-positive")
        assert positive["status"] == "CONDITIONAL_STATISTICAL_APPROX", receipt.read_text()
        assert all(row["exit_code"] == 0 for row in positive["verification"])
        assert all(row["match"] for row in positive["binding_checks"])
        assert positive["proven_reference_path_bound"] > 0
        forged = deepcopy(runner.select(record, 2))
        forged["reference_path_bound"] = 0
        with patch.object(runner, "select", return_value=forged):
            bad_residual, receipt = runner.certify(record, 2, root / "actual-forged-fine-bound")
        assert bad_residual["status"] == "UNKNOWN", receipt.read_text()
        assert [row["exit_code"] for row in bad_residual["verification"]] == [0, 1]
        negative_record, _ = fixture(root / "negative-synthetic", [3*N//4, N//4, N//20, N//20])
        negative, receipt = runner.certify(negative_record, 10, root / "actual-negative")
        assert negative["status"] == "STATISTICAL_NO_GO", receipt.read_text()
        assert all(row["exit_code"] == 0 for row in negative["verification"])
        saved_record, _ = fixture(root / "saved-execution-unit", low)
        decision, deployment, sample_result = saved_execution(saved_record)
        original = {p: p.read_bytes() for p in (decision, deployment, sample_result)}
        # Actual Lean certifies the same saved table used in a complete trace.
        saved, receipt = runner.certify(saved_record, 2, root / "actual-saved-execution")
        assert saved["status"] == "CONDITIONAL_STATISTICAL_APPROX", receipt.read_text()
        assert saved["saved_decision"]["sha256"] == digest(original[decision])
        assert saved["saved_deployment"]["sha256"] == digest(original[deployment])
        for p in original:
            p.write_bytes(b"{}")
            with patch.object(runner, "execute", side_effect=AssertionError("tampered saved execution invoked Lean")):
                tampered, _ = runner.certify(saved_record, 2, root / (p.parent.name + "-tampered"))
            assert tampered["status"] == "UNKNOWN"
            p.write_bytes(original[p])
        decision.unlink()
        deployment.unlink()
        with patch.object(runner, "execute", side_effect=AssertionError("missing saved execution invoked Lean")):
            missing_trace, _ = runner.certify(saved_record, 2, root / "saved-execution-deleted")
        assert missing_trace["status"] == "UNKNOWN"
        decision.write_bytes(original[decision])
        deployment.write_bytes(original[deployment])
        def alter_trace(command, log):
            if "env" in command:
                deployment.write_bytes(b"{}")
            return {"exit_code": 0}
        with patch.object(runner, "execute", side_effect=alter_trace), patch.object(
                runner, "source_identity", return_value=runner.source_identity()):
            changed_trace, _ = runner.certify(saved_record, 2, root / "trace-changed-during-proof")
        assert changed_trace["status"] == "UNKNOWN"
        assert changed_trace["binding_checks"][-1] == {"stage": "after_proof", "match": False}
    print("data certificate raw/proof/candidate/manifest/saved-decision/trace binding and actual universal Lean positive/negative PASS; no registered sampling")


if __name__ == "__main__":
    check()
