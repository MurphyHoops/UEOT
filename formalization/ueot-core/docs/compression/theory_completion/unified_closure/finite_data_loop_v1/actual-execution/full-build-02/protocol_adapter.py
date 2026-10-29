#!/usr/bin/env python3
"""Reuse the pinned exact-certificate native gates with only new-layer scope.

The unchanged longterm drivers still execute full source/owner/type/axiom/edge
checks and fixed replay. Every adapted byte and its immutable origins are
archived; this adapter adds no sampling, statistical or scientific verdict.
"""
from pathlib import Path
from hashlib import sha256
import json

_ADAPTER_PREDECESSOR = Path(__file__).resolve().parents[2] / "action_certificates_v1/native_protocol/protocol_adapter.py"
_ADAPTER_BYTES = _ADAPTER_PREDECESSOR.read_bytes()
_ADAPTER_SHA = "05a2a9e8732a1c7f5cc0cc556fe31913f4e35c9d1231a6141ac32e8a7ccb0501"
if sha256(_ADAPTER_BYTES).hexdigest() != _ADAPTER_SHA:
    raise RuntimeError("IMMUTABLE_ADAPTER_PREDECESSOR_DRIFT")
_ADAPTER_SOURCE = _ADAPTER_BYTES.decode()
_ADAPTER_SUBSTITUTIONS = []


def _scope(old, new, expected=1):
    global _ADAPTER_SOURCE
    count = _ADAPTER_SOURCE.count(old)
    if count != expected:
        raise RuntimeError("ADAPTER_SCOPE_ANCHOR_DRIFT: " + old)
    _ADAPTER_SOURCE = _ADAPTER_SOURCE.replace(old, new)
    _ADAPTER_SUBSTITUTIONS.append({"old": old, "new": new, "occurrences": count})


_scope("action_certificates", "finite_data_loop", 7)
_scope("ACTION_CERTIFICATES", "FINITE_DATA_LOOP", 7)
_scope('"FinitePolicyPath", "FiniteActionCertificate",\n    "RationalConditionedSource", "FiniteActionCertificateWitness"',
       '"FiniteDataSource", "FiniteDataPathBounds", "FiniteDataConditioned",\n'
       '    "FiniteDataNumericalBounds", "FiniteDataControl", "FiniteDataCalibration",\n'
       '    "FiniteDataObstacles", "FiniteDataCertificate", "FiniteDataGeneralRoute",\n'
       '    "FiniteDataJoint", "FiniteDataLiteral", "FiniteDataCertifiedConsumer"')
_scope("PRIOR_MODULES, PRIOR_PUBLIC, PRIOR_OVERLAYS = 708, 4504, 17",
       "PRIOR_MODULES, PRIOR_PUBLIC, PRIOR_OVERLAYS = 712, 4542, 18")
_scope("(708, 4504, 17, 712)", "(712, 4542, 18, 724)")
_scope("PRIOR_MODULES, PRIOR_THEOREMS, PRIOR_OVERLAYS = 708, 4504, 17",
       "PRIOR_MODULES, PRIOR_THEOREMS, PRIOR_OVERLAYS = 712, 4542, 18")
_scope("PRIOR_MODULES, MODULES, PRIOR_PUBLIC, NEW_PUBLIC = 708, 712, 4504,",
       "PRIOR_MODULES, MODULES, PRIOR_PUBLIC, NEW_PUBLIC = 712, 724, 4542,")
_scope('"(PRIOR_MODULES, MODULES, PRIOR_PUBLIC, 17)"',
       '"(PRIOR_MODULES, MODULES, PRIOR_PUBLIC, 18)"')
_scope("UNCOUNTED_FINITE_SOURCE_FINITE_DATA_LOOP", "UNCOUNTED_FINITE_DATA_PATH_RISK")
_scope("EXACT_FOUR_MODULE_SCOPE_REQUIRED", "EXACT_TWELVE_MODULE_SCOPE_REQUIRED")
_scope("four new modules", "twelve new modules")
exec(compile(_ADAPTER_SOURCE, __file__ + "::adapted_pinned_adapter", "exec"), globals())

# Registration must archive the additional adapter provenance with native/full
# evidence. The old strict archive verifier reconstructs these exact bytes.
ARCHIVE_FILES += ("adapter_predecessor.py", "ADAPTER_SCOPE_SUBSTITUTIONS.json")
_base_adapted_driver = adapted_driver


def adapted_driver(kind, repo, manifest_path, base):
    driver, archive = _base_adapted_driver(kind, repo, manifest_path, base)
    metadata = json.loads(archive["PROTOCOL_ADAPTATION.json"])
    metadata["adapter_predecessor"] = {"path": str(_ADAPTER_PREDECESSOR), "sha256": _ADAPTER_SHA}
    metadata["adapter_scope_substitutions"] = _ADAPTER_SUBSTITUTIONS
    archive["PROTOCOL_ADAPTATION.json"] = encoded(metadata)
    archive["adapter_predecessor.py"] = _ADAPTER_BYTES
    archive["ADAPTER_SCOPE_SUBSTITUTIONS.json"] = encoded(_ADAPTER_SUBSTITUTIONS)
    if kind == "register_overlay":
        driver.ADAPTED_REGISTRATION_INPUTS = archive
    return driver, archive
