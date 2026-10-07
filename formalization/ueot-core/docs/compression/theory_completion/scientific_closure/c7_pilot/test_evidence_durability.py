#!/usr/bin/env python3
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
RUNNER = ROOT / "run_pilot.py"
VERIFIER = ROOT / "verify_evidence.py"


def load_runner():
    spec = importlib.util.spec_from_file_location("c7_run_pilot", RUNNER)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def load_verifier():
    spec = importlib.util.spec_from_file_location("c7_verify_evidence", VERIFIER)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def main():
    runner = load_runner()
    verifier = load_verifier()
    assert not verifier.observed_schema_complete({
        "timestamp_utc": runner.utc_now(),
        "run_id": "cert-n1-read-r1",
        "split": "certification",
        "protocol": "P_READ",
        "matches_expected": True,
        "record_status": "OBSERVED",
        # Missing `query` must be treated as unresolved data, not a rejection
        # and not a verifier exception.
    })
    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        raw = tmp / "raw_fault_injection.jsonl"

        with runner.DurableJsonlWriter(raw) as writer:
            ok = runner.execute_attempt(
                writer,
                run_id="cert-n1-read-r1",
                split="certification",
                protocol="P_READ",
                candidate_ids=["W1"],
                thunk=lambda: {
                    "timestamp_utc": runner.utc_now(),
                    "run_id": "cert-n1-read-r1",
                    "split": "certification",
                    "protocol": "P_READ",
                    "candidate_ids": ["W1"],
                    "query": {"service_output": "OK"},
                    "matches_expected": True,
                },
            )
            assert ok["record_status"] == "OBSERVED"

            try:
                runner.execute_attempt(
                    writer,
                    run_id="cert-n1-single-r1",
                    split="certification",
                    protocol="P_SINGLE_FAULT",
                    candidate_ids=["W1"],
                    thunk=lambda: (_ for _ in ()).throw(RuntimeError("injected durable failure")),
                )
            except RuntimeError as exc:
                assert "injected durable failure" in str(exc)
            else:
                raise AssertionError("fault injection did not raise")

        rows = [json.loads(line) for line in raw.read_text().splitlines() if line.strip()]
        assert len(rows) == 2
        assert rows[0]["run_id"] == "cert-n1-read-r1"
        assert rows[0]["record_status"] == "OBSERVED"
        assert rows[1]["run_id"] == "cert-n1-single-r1"
        assert rows[1]["record_status"] == "EXECUTION_ERROR"
        assert rows[1]["matches_expected"] is False

        # The same label/path is permanently occupied after a partial run.
        try:
            runner.DurableJsonlWriter(raw)
        except FileExistsError:
            pass
        else:
            raise AssertionError("existing partial raw evidence was overwriteable")

        # The hardened verifier must classify the interrupted collection as
        # unresolved rather than accepting the successful prefix.
        out = tmp / "recomputed.json"
        proc = subprocess.run(
            [sys.executable, str(VERIFIER), str(raw), "--out", str(out)],
            text=True,
            capture_output=True,
        )
        assert proc.returncode != 0
        result = json.loads(out.read_text())
        assert result["all_checks_pass"] is False
        assert result["checks"]["no_execution_errors"] is False
        assert result["claim_verdicts"] == {
            "C7-LOCAL-FORM-01": "UNRESOLVED",
            "C7-LOCAL-FBT-01": "UNRESOLVED",
            "C7-LOCAL-NEG-01": "UNRESOLVED",
        }

        # Model an uncatchable hard stop after one fsynced observation: there
        # is no EXECUTION_ERROR row, but the reserved partial raw file still
        # makes the registered run-ID set incomplete and therefore unresolved.
        hard_stop_raw = tmp / "raw_hard_stop.jsonl"
        with runner.DurableJsonlWriter(hard_stop_raw) as writer:
            writer.append({
                "timestamp_utc": runner.utc_now(),
                "run_id": "cert-n1-read-r1",
                "split": "certification",
                "protocol": "P_READ",
                "candidate_ids": ["W1"],
                "query": {"service_output": "OK"},
                "matches_expected": True,
                "record_status": "OBSERVED",
            })
        hard_stop_out = tmp / "hard_stop_recomputed.json"
        hard_stop_proc = subprocess.run(
            [sys.executable, str(VERIFIER), str(hard_stop_raw), "--out", str(hard_stop_out)],
            text=True,
            capture_output=True,
        )
        assert hard_stop_proc.returncode != 0
        hard_stop_result = json.loads(hard_stop_out.read_text())
        assert hard_stop_result["checks"]["no_execution_errors"] is True
        assert hard_stop_result["checks"]["registered_run_ids_complete"] is False
        assert hard_stop_result["claim_verdicts"]["C7-LOCAL-FORM-01"] == "UNRESOLVED"

        # Exercise the actual main-loop ordering as well.  Redirect evidence
        # output to the temp directory while retaining the real worker binary.
        integration_root = tmp / "integration"
        integration_root.mkdir()
        old_root, old_worker, old_argv = runner.ROOT, runner.WORKER, sys.argv[:]
        runner.ROOT = integration_root
        runner.WORKER = old_worker
        try:
            sys.argv = [
                str(RUNNER),
                "--label", "fault_integration",
                "--inject-failure-run-id", "cert-n1-single-r1",
            ]
            try:
                runner.main()
            except RuntimeError as exc:
                assert "cert-n1-single-r1" in str(exc)
            else:
                raise AssertionError("main-loop fault injection did not raise")

            integration_raw = integration_root / "raw_fault_integration.jsonl"
            integration_summary = integration_root / "summary_fault_integration.json"
            integration_rows = [
                json.loads(line)
                for line in integration_raw.read_text().splitlines()
                if line.strip()
            ]
            assert [r["record_status"] for r in integration_rows] == [
                "OBSERVED", "EXECUTION_ERROR"
            ]
            assert integration_rows[1]["run_id"] == "cert-n1-single-r1"
            assert not integration_summary.exists()

            # A second invocation with the same label is refused before any
            # new collection can overwrite/censor the failed attempt.
            sys.argv = [str(RUNNER), "--label", "fault_integration"]
            try:
                runner.main()
            except SystemExit as exc:
                assert "refusing to overwrite existing evidence" in str(exc)
            else:
                raise AssertionError("same-label rerun was not refused")
        finally:
            runner.ROOT, runner.WORKER, sys.argv = old_root, old_worker, old_argv

    print("C7 durable evidence regression: PASS")


if __name__ == "__main__":
    main()
