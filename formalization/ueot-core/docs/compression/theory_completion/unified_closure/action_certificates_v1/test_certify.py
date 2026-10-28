#!/usr/bin/env python3
"""The trusted handoff must pass Lean, fail closed, and handle another map."""
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

from certify import certify


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
        verified, receipt = certify({"arbitrary": SOURCE}, root / "verified")
        assert verified["cases"]["arbitrary"]["status"] == "CERTIFIED_REALIZABLE", receipt.read_text()
        assert all(run["exit_code"] == 0 for run in verified["verification"])
        assert verified["core_sources_unchanged_during_proof"]
    print("trusted runner: Lean positive, nonconstant observation, build/proof failure and invalid input PASS")


if __name__ == "__main__":
    check()
