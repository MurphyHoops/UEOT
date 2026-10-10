#!/usr/bin/env python3
"""Non-destructive Lean proof replacement: two local TV lemmas, one proof.

Checks immutable baseline SHA-256 for BOTH source modules before ANY build,
then copies the target module to a disposable temp file and compiles it after
replacing only the existing duplicated PMF TV proof with the source theorem.

Do not interpret this as permission to edit frozen P-GOA-03/P-GOA-04 modules.
"""
from hashlib import sha256
from pathlib import Path
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[7]
CORE = ROOT / "formalization/ueot-core"
SOURCE = CORE / "UEOT/V3"
FIRST = "FiniteRecurrentDecompositionStability.lean"
SECOND = "SymmetricKilledSpectralStability.lean"
PINNED_SHA = {
    FIRST: "2f8aa0e5a98f1091bba8a3d8f7556fcaa8fb68ebdee193187dbc2935362997ee",
    SECOND: "c27d79e0ec7d46b0ea23d2ecbc0a6a69819a70b2b4f224348f9e62163820953a",
}
THEOREM = (
    "UEOT.V3.FiniteRecurrentDecompositionStability.pmf_tv_eq_half_sum_abs"
)
AFTER = "variable {ι : Type*}"


def run(compilation=subprocess.run):
    seen = {}
    for filename, expected in PINNED_SHA.items():
        content = (SOURCE / filename).read_bytes()
        actual = sha256(content).hexdigest()
        if actual != expected:
            raise RuntimeError(f"STALE_ORIGINAL_SOURCE: {filename}: {actual}")
        seen[filename] = content
    if len(seen) != 2:
        raise RuntimeError("SOURCE_PREFLIGHT_INCOMPLETE")
    old = seen[SECOND].decode("utf-8")
    assertion = r"(^lemma pmf_tv_eq_half_sum_abs\b[\s\S]*?:=)\s*by[\s\S]*?(?=^" + re.escape(AFTER) + r")"
    matches = list(re.finditer(assertion, old, re.MULTILINE))
    if len(matches) != 1:
        raise RuntimeError(f"REPLACEMENT_PROOF_BOUNDARY_UNKNOWN {len(matches)}")
    match = matches[0]
    original_lines = match.group(0).count("\n") + 1
    new = old[:match.start()] + match.group(1) + (
        f" by\n  exact {THEOREM} p q\n\n"
    ) + old[match.end():]
    new = "import UEOT.V3.FiniteRecurrentDecompositionStability\n" + new
    with tempfile.TemporaryDirectory(prefix="ueot-pmf-tv-source-bridge-") as d:
        sample = Path(d) / "SymmetricKilledSpectralStabilityBridge.lean"
        sample.write_text(new)
        result = compilation(
            ["lake", "lean", str(sample)], cwd=CORE,
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            timeout=180
        )
        if result.returncode != 0:
            raise RuntimeError("LEAN_PROOF_BRIDGE_FAIL: " + result.stdout[-6000:])
    return {
        "status": "PASS",
        "pinned_source_kind": "Core proof copies; no source files edited",
        "source_source_theorem": THEOREM,
        "target_theorem": "UEOT.V3.SymmetricKilledSpectralStability.pmf_tv_eq_half_sum_abs",
        "original_target_proof_lines": original_lines,
        "replacement": "by exact <source theorem> p q",
        "lean_check": "lake lean temporary whole source module PASS",
        "type_identity": "NOT_definitional_equal_as_closed_Expr",
        "implication": "REUSE_WORKS_UNDER_THE_TARGETS_IMPLICIT_ARGUMENT_AND_INSTANCE_CONTEXT",
        "not_a_claim": "This is not a safe-to-merge Core source modification; frozen Core governance still applies",
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
