#!/usr/bin/env python3
"""The trusted handoff must pass Lean, fail closed, and handle another map."""
import json
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

from certify import certify, digest, execute, snapshot, source_identity


SOURCE = dict(P=[[[1, 0], [0, 1]], [[1, 0], [0, 1]]], q=[0, 1],
              base=[[1, 0], [0, 1]], p0=["1/2", "1/2"], deployed=["1/2", "1/2"],
              safe=[True, True], T=1)


def check():
    with TemporaryDirectory() as temp:
        root = Path(temp)
        with patch("certify.execute", return_value={"exit_code": 1}):
            failed, _ = certify({"arbitrary": SOURCE}, root / "failed")
        assert failed["cases"]["arbitrary"]["status"] == "UNKNOWN"
        assert "Lean" in failed["failure"]
        with patch("certify.execute", side_effect=[{"exit_code": 0}, {"exit_code": 1}]):
            rejected, _ = certify({"arbitrary": SOURCE}, root / "rejected")
        assert rejected["cases"]["arbitrary"]["status"] == "UNKNOWN"
        assert len(rejected["verification"]) == 2
        identity = {"source": "before build"}
        def mutate_during_build(*_):
            identity["source"] = "after build mutation"
            return {"exit_code": 0}
        with patch("certify.source_identity", side_effect=lambda: dict(identity)), \
             patch("certify.execute", side_effect=mutate_during_build):
            changed, _ = certify({"arbitrary": SOURCE}, root / "changed-during-build")
        assert changed["cases"]["arbitrary"]["status"] == "UNKNOWN"
        assert not changed["sources_unchanged_during_build_and_proof"]
        with patch("certify.execute", side_effect=AssertionError("invalid input invoked Lean")):
            invalid, _ = certify({"invalid": {**SOURCE, "p0": [0.5, 0.5]}}, root / "invalid")
        assert invalid["cases"]["invalid"]["status"] == "INVALID_INPUT"

        # These fault tests isolate artifact binding from parallel source edits.
        # Actual source-identity mutation is covered separately above.
        with patch("certify.source_identity", return_value=source_identity()):
            for filename in ("source.json", "candidates.json", "Certificate.lean", "core-source-identity.json"):
                for phase in ("build", "proof"):
                    for missing in (False, True):
                        def alter(command, log):
                            if (command[1] == "build") == (phase == "build"):
                                artifact = log.parent / filename
                                if missing:
                                    artifact.unlink()
                                else:
                                    artifact.write_text("-- replaced obligations\n" if filename.endswith(".lean") else "{}\n")
                            return {"exit_code": 0}
                        with patch("certify.execute", side_effect=alter) as called:
                            altered, _ = certify({"arbitrary": SOURCE}, root / f"{filename}-{phase}-{missing}")
                        assert altered["cases"]["arbitrary"]["status"] == "UNKNOWN", (filename, phase, missing)
                        assert not altered["artifacts_unchanged_during_build_and_proof"]
                        assert called.call_count == (1 if phase == "build" else 2)

            # A replacement before the first check must not become the baseline.
            def replace_snapshot(path, text):
                intended = snapshot(path, text)
                if path.name == "Certificate.lean":
                    path.write_text("-- replaced immediately after writing\n")
                return intended
            with patch("certify.snapshot", side_effect=replace_snapshot), \
                 patch("certify.execute", side_effect=AssertionError("changed initial snapshot invoked Lean")):
                replaced, _ = certify({"arbitrary": SOURCE}, root / "changed-before-build")
            assert replaced["cases"]["arbitrary"]["status"] == "UNKNOWN"

            # Real build and real Lean, with substitution after the final preproof
            # check: Lean accepts the comment file, but the runner must reject it.
            def real_empty_proof(command, log):
                if command[1] == "env":
                    Path(command[-1]).write_text("-- REAL LEAN REGRESSION: generated obligations removed.\n")
                return execute(command, log)
            with patch("certify.execute", side_effect=real_empty_proof):
                emptied, _ = certify({"arbitrary": SOURCE}, root / "real-empty-proof")
            assert [r["exit_code"] for r in emptied["verification"]] == [0, 0]
            assert emptied["cases"]["arbitrary"]["status"] == "UNKNOWN"
            assert emptied["lean_source_sha256"] != digest(Path(emptied["lean_source"]))
            assert emptied["binding_checks"][-1]["stage"] == "after_proof"
            print("actual Lean comment-proof replacement: build 0, Lean 0, runner UNKNOWN")

        verified, receipt = certify({"arbitrary": SOURCE}, root / "verified")
        assert verified["cases"]["arbitrary"]["status"] == "CERTIFIED_REALIZABLE", receipt.read_text()
        assert all(run["exit_code"] == 0 for run in verified["verification"])
        assert verified["core_sources_unchanged_during_proof"]
        assert verified["artifacts_unchanged_during_build_and_proof"]
        assert [c["stage"] for c in verified["binding_checks"]] == [
            "before_build", "after_build", "before_proof", "after_proof"]
        for path, expected in verified["bound_artifacts"].items():
            assert digest(Path(path)) == expected
        saved = json.loads(Path(verified["source"]).read_text())["arbitrary"]
        assert saved["p0"] == ["1/2", "1/2"]
        assert saved["P"][0][0] == ["1", "0"]
    print("trusted runner: artifact binding, Lean positive, source identity and invalid input PASS")


if __name__ == "__main__":
    check()
