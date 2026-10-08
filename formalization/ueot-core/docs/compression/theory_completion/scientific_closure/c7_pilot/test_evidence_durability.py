#!/usr/bin/env python3
import contextlib
import importlib.util
import io
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

            # Build one complete hardened collection, then mutate copies to
            # exercise the exact verifier-confusion cases found in review.
            full_root = tmp / "full"
            full_root.mkdir()
            runner.ROOT = full_root
            runner.WORKER = old_worker
            sys.argv = [str(RUNNER), "--label", "registry_attacks"]
            with contextlib.redirect_stdout(io.StringIO()):
                runner.main()
            full_raw = full_root / "raw_registry_attacks.jsonl"
            full_rows = [
                json.loads(line) for line in full_raw.read_text().splitlines() if line.strip()
            ]
            assert len(full_rows) == 45

            def verify_rows(name, rows):
                path = full_root / f"raw_{name}.jsonl"
                out_path = full_root / f"verify_{name}.json"
                path.write_text(
                    "".join(json.dumps(row, sort_keys=True) + "\n" for row in rows),
                    encoding="utf-8",
                )
                process = subprocess.run(
                    [sys.executable, str(VERIFIER), str(path), "--out", str(out_path)],
                    text=True,
                    capture_output=True,
                )
                return process, json.loads(out_path.read_text())

            # The pristine hardened collection is the positive control.  The
            # regression must prove that the verifier accepts the unmodified
            # 45-row run before relying on any mutation-rejection checks.
            pristine_out = full_root / "verify_pristine.json"
            pristine_proc = subprocess.run(
                [sys.executable, str(VERIFIER), str(full_raw), "--out", str(pristine_out)],
                text=True,
                capture_output=True,
            )
            assert pristine_proc.returncode == 0, pristine_proc.stderr or pristine_proc.stdout
            pristine_result = json.loads(pristine_out.read_text())
            assert pristine_result["all_checks_pass"] is True
            assert pristine_result["checks"]["registered_intervention_match"] is True
            assert pristine_result["claim_verdicts"] == {
                "C7-LOCAL-FORM-01": "SUPPORTED_LOCAL",
                "C7-LOCAL-FBT-01": "SUPPORTED_LOCAL",
                "C7-LOCAL-NEG-01": "SUPPORTED_LOCAL",
            }
            produced_summary = full_root / "summary_registry_attacks.json"
            assert produced_summary.exists()
            summary = json.loads(produced_summary.read_text())
            assert summary["claim_verdicts"] == pristine_result["claim_verdicts"]

            # A run ID uniquely determines protocol, split and candidate set.
            metadata_mutations = [
                ("protocol", lambda row: row.__setitem__("protocol", "P_READ")),
                ("split", lambda row: row.__setitem__("split", "holdout")),
                ("candidate", lambda row: row.__setitem__("candidate_ids", ["W1", "W2"])),
            ]
            for name, mutate in metadata_mutations:
                rows = json.loads(json.dumps(full_rows))
                target = next(r for r in rows if r["run_id"] == "cert-n3-single-r1")
                mutate(target)
                process, result = verify_rows(f"metadata_{name}", rows)
                assert process.returncode != 0
                assert result["checks"]["registered_metadata_match"] is False
                assert set(result["claim_verdicts"].values()) == {"UNRESOLVED"}

            # Fault protocols are evidence about interventions, not merely
            # service outputs.  Missing/wrong actions or replies inconsistent
            # with the registered terminated workers must make the collection
            # unresolved even when the output bit is unchanged.
            intervention_mutations = [
                (
                    "single_missing_action",
                    "cert-n3-single-r1",
                    lambda row: row.pop("action"),
                ),
                (
                    "single_wrong_victim",
                    "cert-n3-single-r1",
                    lambda row: row["action"].__setitem__("terminated", "W1"),
                ),
                (
                    "single_victim_replied",
                    "cert-n3-single-r1",
                    lambda row: row["query"]["worker_replies"].append({
                        "worker_id": "W3",
                        "pid": row["action"]["pid"],
                        "status": "OK",
                    }),
                ),
                (
                    "double_missing_action",
                    "neg-double-r1",
                    lambda row: row["action"].pop(),
                ),
                (
                    "single_zero_returncode",
                    "cert-n3-single-r1",
                    lambda row: row["action"].__setitem__("returncode", 0),
                ),
                (
                    "replacement_wrong_new_pid",
                    "holdout-replace-r1",
                    lambda row: row["replacement"].__setitem__(
                        "new_pid", row["replacement"]["new_pid"] + 100000
                    ),
                ),
                (
                    "replacement_replayed_read_token",
                    "holdout-replace-r1",
                    lambda row: row["single_fault_query"]["worker_replies"][0].__setitem__(
                        "token", row["read_query"]["worker_replies"][0]["token"]
                    ),
                ),
            ]
            for name, run_id, mutate in intervention_mutations:
                rows = json.loads(json.dumps(full_rows))
                target = next(r for r in rows if r["run_id"] == run_id)
                mutate(target)
                process, result = verify_rows(name, rows)
                assert process.returncode != 0
                assert result["checks"]["registered_intervention_match"] is False
                assert set(result["claim_verdicts"].values()) == {"UNRESOLVED"}

            # Never trust the producer's `matches_expected` bit.  The raw
            # observed service output is compared with the registration table.
            rows = json.loads(json.dumps(full_rows))
            target = next(r for r in rows if r["run_id"] == "cert-n1-read-r1")
            target["query"]["worker_replies"][0]["status"] = "NO_REPLY"
            target["query"]["ok_replies"] = 0
            target["query"]["service_output"] = "UNAVAILABLE"
            target["matches_expected"] = True
            process, result = verify_rows("lying_match_flag", rows)
            assert process.returncode != 0
            assert result["checks"]["registered_metadata_match"] is True
            assert result["checks"]["all_registered_outcomes_match"] is False
            assert result["checks"]["producer_match_flag_consistent"] is False
            assert result["claim_verdicts"]["C7-LOCAL-FORM-01"] == "REJECTED_LOCAL"

            # DEAD is a producer-defined coherent observation when a process
            # exits after service_query's alive() filter but before Worker.ping
            # performs its own liveness check. It is scientific evidence of a
            # failed read, not collection corruption. Preserve collection
            # integrity and classify the contradictory outcome locally.
            rows = json.loads(json.dumps(full_rows))
            target = next(r for r in rows if r["run_id"] == "cert-n1-read-r1")
            reply = target["query"]["worker_replies"][0]
            reply["status"] = "DEAD"
            reply.pop("token", None)
            reply["latency_ns"] = None
            target["query"]["ok_replies"] = 0
            target["query"]["service_output"] = "UNAVAILABLE"
            target["matches_expected"] = False
            process, result = verify_rows("coherent_dead_observation", rows)
            assert process.returncode != 0
            assert result["checks"]["registered_intervention_match"] is True
            assert result["checks"]["all_registered_outcomes_match"] is False
            assert result["checks"]["producer_match_flag_consistent"] is True
            assert result["claim_verdicts"]["C7-LOCAL-FORM-01"] == "REJECTED_LOCAL"

            # Missing/non-string run IDs are integrity failures that still
            # produce a machine-readable UNRESOLVED result instead of crashing.
            for name, bad_id in [("missing_run_id", None), ("nonstr_run_id", 17)]:
                rows = json.loads(json.dumps(full_rows))
                if bad_id is None:
                    rows[0].pop("run_id")
                else:
                    rows[0]["run_id"] = bad_id
                process, result = verify_rows(name, rows)
                assert process.returncode != 0
                assert result["checks"]["registered_run_ids_complete"] is False
                assert result["malformed_run_id_count"] == 1
                assert set(result["claim_verdicts"].values()) == {"UNRESOLVED"}
        finally:
            runner.ROOT, runner.WORKER, sys.argv = old_root, old_worker, old_argv

    print("C7 durable evidence regression: PASS")


if __name__ == "__main__":
    main()
