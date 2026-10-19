"""Source generation, exact index semantics, and rejection controls.

These tests do not invoke Lean or turn a source export into a build receipt.
The emitted positive instances and post-generation corruption controls are
compiled separately against ExactCertificate for proof-assistant evidence.
"""

from copy import deepcopy
from dataclasses import FrozenInstanceError
from fractions import Fraction as F
from hashlib import sha256
import json
import re
import unittest
from unittest.mock import patch

from ueot_qm import (
    Matrix, QComplex, identity, diagonal, KrausTerm, Instrument,
    InstrumentLibrary, PredictiveModel,
)
from ueot_qm.algebra import matrix_payload, zeros
from ueot_qm.lean_export import (
    LeanExportError, LeanRepresentationExport, export_lean_representation,
)
from ueot_qm.representation_certificate import (
    SCHEMA, PROTOCOL_CLASS, SCALAR_DOMAIN, export_representation_certificate,
)


I2 = identity(2)
P0 = diagonal([1, 0])
P1 = diagonal([0, 1])
Z = Instrument({"0": [KrausTerm(P0)], "1": [KrausTerm(P1)]})
H = Instrument({"ok": [KrausTerm(Matrix([[1, 1], [1, -1]]), F(1, 2))]})
S = Instrument({"ok": [KrausTerm(diagonal([1, QComplex(0, 1)]))]})


def _hash(value):
    return sha256(json.dumps(value, sort_keys=True, ensure_ascii=True,
                             separators=(",", ":")).encode()).hexdigest()


def hand_z_certificate():
    """Closed I,P0 presentation with hand-computed coefficient rows."""
    library = InstrumentLibrary({"Z": Z})
    basis = [matrix_payload(I2), matrix_payload(P0)]
    certificate = {
        "schema": SCHEMA,
        "protocol_class": PROTOCOL_CLASS,
        "scalar_domain": SCALAR_DOMAIN,
        "normalization": "first-coordinate-is-trace",
        "hilbert_dimension": 2,
        "response_dimension": 2,
        "library_fingerprint": library.fingerprint,
        "context_fingerprint": _hash({
            "schema": "ueot_qm.predictive_model.v1",
            "library_fingerprint": library.fingerprint,
            "normalization": "first-coordinate-is-trace", "basis": basis,
        }),
        "library": {"schema": "ueot_qm.instrument_library.v1",
                    "protocol_class": "all-finite-causal-combinations",
                    "actions": [["Z", {"dimension": 2, "outcomes": [
                        ["0", [[1, 1, matrix_payload(P0)]]],
                        ["1", [[1, 1, matrix_payload(P1)]]],
                    ]}]]},
        "basis": [{"effect": basis[0], "word": []},
                  {"effect": basis[1], "word": [["Z", "0"]]}],
        "pullbacks": [
            {"action": "Z", "outcome": "0", "matrix": matrix_payload(Matrix([[0, 1], [0, 1]]))},
            {"action": "Z", "outcome": "1", "matrix": matrix_payload(Matrix([[1, -1], [0, 0]]))},
        ],
    }
    return library, certificate


def example_libraries():
    """Independent positive shapes used by tests and actual Lean fixtures."""
    p4 = diagonal([1, 0, 0, 0])
    coarse = Instrument({"done": [KrausTerm(P0), KrausTerm(P1)]})
    zzero = Instrument({"0": [KrausTerm(P0)], "1": [KrausTerm(P1)], "impossible": []})
    return {
        "z": InstrumentLibrary({"Z": Z}),
        "hz": InstrumentLibrary({"H": H, "Z": Z}),
        "hsz": InstrumentLibrary({"H": H, "S": S, "Z": Z}),
        "ragged": InstrumentLibrary({"coarse": coarse, "H": H, "Z": zzero}),
        "d1": InstrumentLibrary({"phase": Instrument({
            "ok": [KrausTerm(Matrix([[QComplex(1, 1)]]), F(1, 2))], "zero": [],
        })}),
        "d4": InstrumentLibrary({"project": Instrument({
            "hit": [KrausTerm(p4)], "miss": [KrausTerm(identity(4) - p4)],
        })}),
    }


def decode_matrix(payload):
    return Matrix([[QComplex(F(entry[0], entry[1]), F(entry[2], entry[3]))
                    for entry in row] for row in payload])


def decode_terms(branch):
    return tuple(KrausTerm(decode_matrix(term["operator"]), F(*term["weight"]))
                 for term in branch["terms"])


def explicit_pullback(terms, effect):
    result = zeros(effect.nrows)
    for term in terms:
        result += (term.operator.adjoint() @ effect @ term.operator) * term.weight
    return result


class LeanExportTests(unittest.TestCase):
    def test_hand_certificate_needs_no_predictive_search(self):
        library, certificate = hand_z_certificate()
        with patch("ueot_qm.predictive.PredictiveModel.__init__", side_effect=AssertionError("no search")):
            result = export_lean_representation(certificate, library)
        self.assertIsInstance(result, LeanRepresentationExport)
        self.assertIn("ExactCertificate.Data 2 1 2 1 2", result.lean_source)
        self.assertIn("ExactCertificate.check data = true", result.lean_source)
        self.assertIn("ExactCertificate.presentation data checked", result.lean_source)
        self.assertNotIn("native_decide", result.lean_source)
        self.assertEqual(result.to_dict()["status"], "LEAN_SOURCE_EXPORTED_NOT_COMPILED")

    def test_data_have_exact_numeric_semantics_for_all_positive_shapes(self):
        for name, library in example_libraries().items():
            with self.subTest(name=name):
                model = PredictiveModel(library)
                certificate = export_representation_certificate(model)
                result = export_lean_representation(certificate, library,
                    expected_context_fingerprint=model.context_fingerprint)
                manifest = result.to_dict()
                layout = manifest["index_layout"]
                dims = layout["dimensions"]
                self.assertEqual((dims["hilbert"], dims["coordinates"]),
                                 (library.dimension, model.dimension))
                numeric = {}
                for action in layout["actions"]:
                    total = zeros(library.dimension)
                    for branch in action["outcomes"]:
                        terms = decode_terms(branch)
                        numeric[action["index"], branch["index"]] = terms
                        pulled_i = explicit_pullback(terms, identity(library.dimension))
                        total += pulled_i
                        if not branch["padding"]:
                            self.assertEqual(pulled_i, library.adjoint(identity(library.dimension),
                                action["label"], branch["label"]))
                        else:
                            self.assertEqual(pulled_i, zeros(library.dimension))
                        coeff = decode_matrix(branch["pullback"])
                        for j, basis in enumerate(model.basis):
                            actual = explicit_pullback(terms, basis)
                            claimed = sum((model.basis[q] * coeff[j, q]
                                           for q in range(model.dimension)), zeros(library.dimension))
                            self.assertEqual(actual, claimed)
                    self.assertEqual(total, identity(library.dimension))
                for word, basis in zip(layout["words"], model.basis):
                    effect = identity(library.dimension)
                    for letter in reversed(word):
                        effect = explicit_pullback(numeric[tuple(letter)], effect)
                    self.assertEqual(effect, basis)

    def test_hsz_real_imaginary_parts_and_word_direction_survive(self):
        library = example_libraries()["hsz"]
        model = PredictiveModel(library)
        certificate = export_representation_certificate(model)
        result = export_lean_representation(certificate, library)
        manifest = result.to_dict()
        self.assertEqual(manifest["index_layout"]["dimensions"]["coordinates"], 4)
        # Sorted action indices are H=0, S=1, Z=2. Word order is chronological.
        self.assertIn([[1, 0], [0, 0], [2, 0]], manifest["index_layout"]["words"])
        imaginary = [entry[2] for basis in manifest["certificate"]["basis"]
                     for row in basis["effect"] for entry in row]
        self.assertTrue(any(value > 0 for value in imaginary))
        self.assertTrue(any(value < 0 for value in imaginary))
        self.assertIn("!![", result.lean_source)
        self.assertIn("(-1 : ℚ)", result.lean_source)
        self.assertIn("(⟨2, by decide⟩ : Action)", result.lean_source)

    def test_ragged_and_explicit_impossible_outcomes_remain_distinct(self):
        library = example_libraries()["ragged"]
        result = export_lean_representation(export_representation_certificate(PredictiveModel(library)), library)
        layout = result.to_dict()["index_layout"]
        self.assertEqual((layout["dimensions"]["outcomes"], layout["dimensions"]["kraus"]), (3, 2))
        zaction = next(a for a in layout["actions"] if a["label"] == "Z")
        impossible = next(b for b in zaction["outcomes"] if b["label"] == "impossible")
        self.assertFalse(impossible["padding"])
        self.assertEqual(impossible["original_kraus_count"], 0)
        self.assertTrue(all(term["padding"] for term in impossible["terms"]))
        haction = next(a for a in layout["actions"] if a["label"] == "H")
        self.assertEqual([b["padding"] for b in haction["outcomes"]], [False, True, True])
        self.assertTrue(all(b["label"] is None for b in haction["outcomes"][1:]))

    def test_zero_weight_original_term_is_not_rewritten_as_padding(self):
        unused = diagonal([1, -1])
        library = InstrumentLibrary({"stay": Instrument({
            "ok": [KrausTerm(I2), KrausTerm(unused, F(0))],
        })})
        result = export_lean_representation(export_representation_certificate(PredictiveModel(library)), library)
        term = result.to_dict()["index_layout"]["actions"][0]["outcomes"][0]["terms"][1]
        self.assertFalse(term["padding"])
        self.assertEqual(term["original_index"], 1)
        self.assertEqual(term["weight"], [0, 1])
        self.assertEqual(decode_matrix(term["operator"]), unused)

    def test_labels_cannot_supply_lean_tokens_or_paths(self):
        action = '../bad\nend UEOTQM\naxiom injected_false : False\n/-'
        outcome = '"\\\x00\n-/ #eval IO.println "payload" /-'
        library = InstrumentLibrary({action: Instrument({outcome: [KrausTerm(I2)]})})
        result = export_lean_representation(export_representation_certificate(PredictiveModel(library)), library)
        self.assertRegex(result.module_name, r"\AUEOTQM\.Generated\.Certificate_[0-9a-f]{64}\Z")
        self.assertNotIn(action, result.lean_source)
        self.assertNotIn(outcome, result.lean_source)
        self.assertNotIn("injected_false", result.lean_source)
        self.assertNotIn("..", result.relative_source_path)
        self.assertNotIn("\\", result.relative_source_path)
        layout = result.to_dict()["index_layout"]
        self.assertEqual(layout["actions"][0]["label"], action)
        self.assertEqual(layout["actions"][0]["outcomes"][0]["label"], outcome)

    def test_repeated_export_is_deterministic_and_bound_to_exact_source(self):
        library, certificate = hand_z_certificate()
        first = export_lean_representation(certificate, library)
        reordered = json.loads(json.dumps(certificate, sort_keys=True))
        second = export_lean_representation(reordered, library)
        self.assertEqual(first, second)
        self.assertEqual(first.source_sha256, first.to_dict()["source_sha256"])
        self.assertEqual(first.to_dict()["certificate_fingerprint"], _hash(certificate))
        self.assertEqual(first.relative_source_path, first.module_name.replace(".", "/") + ".lean")
        self.assertEqual(len(first.to_dict()["audit_targets"]), 7)

    def test_no_mutable_alias_to_certificate_or_manifest(self):
        library, certificate = hand_z_certificate()
        result = export_lean_representation(certificate, library)
        snapshot = result.canonical_manifest
        certificate["basis"][1]["word"].clear()
        external = result.to_dict()
        external["certificate"].clear()
        external["index_layout"]["actions"].clear()
        self.assertEqual(result.canonical_manifest, snapshot)
        self.assertTrue(result.to_dict()["certificate"]["basis"][1]["word"])
        with self.assertRaises(FrozenInstanceError):
            result.lean_source = "altered"

    def test_wrong_word_is_rejected_before_source_generation(self):
        library = example_libraries()["hz"]
        certificate = export_representation_certificate(PredictiveModel(library))
        next(row for row in certificate["basis"] if len(row["word"]) == 2)["word"].reverse()
        with self.assertRaisesRegex(LeanExportError, "chronological"):
            export_lean_representation(certificate, library)

    def test_wrong_pullback_and_missing_branch_are_rejected(self):
        library, good = hand_z_certificate()
        for mutation in ("wrong", "missing", "duplicate"):
            with self.subTest(mutation=mutation):
                certificate = deepcopy(good)
                if mutation == "wrong":
                    certificate["pullbacks"][0]["matrix"][0][1] = [0, 1, 0, 1]
                elif mutation == "missing":
                    certificate["pullbacks"].pop()
                else:
                    certificate["pullbacks"][1] = deepcopy(certificate["pullbacks"][0])
                with self.assertRaises(LeanExportError):
                    export_lean_representation(certificate, library)

    def test_wrong_kraus_data_and_library_anchor_are_rejected(self):
        library, good = hand_z_certificate()
        certificate = deepcopy(good)
        certificate["library"]["actions"][0][1]["outcomes"][0][1][0][2][0][0] = [2, 1, 0, 1]
        with self.assertRaisesRegex(LeanExportError, "serialized Kraus"):
            export_lean_representation(certificate, library)
        with self.assertRaisesRegex(LeanExportError, "different library"):
            export_lean_representation(good, InstrumentLibrary({"H": H, "Z": Z}))
        with self.assertRaisesRegex(LeanExportError, "intended model context"):
            export_lean_representation(good, library, expected_context_fingerprint="0" * 64)

    def test_noncanonical_and_non_json_numeric_inputs_are_not_coerced(self):
        library, good = hand_z_certificate()
        for invalid in ([True, 1, 0, 1], [1.0, 1, 0, 1], ["1", 1, 0, 1],
                        [2, 2, 0, 1], [1, -1, 0, 1], [0, 2, 0, 1]):
            with self.subTest(invalid=invalid):
                certificate = deepcopy(good)
                certificate["basis"][0]["effect"][0][0] = invalid
                with self.assertRaises(LeanExportError):
                    export_lean_representation(certificate, library)
        certificate = deepcopy(good)
        certificate["basis"] = tuple(certificate["basis"])
        with self.assertRaisesRegex(LeanExportError, "plain exact JSON"):
            export_lean_representation(certificate, library)
        certificate = deepcopy(good)
        certificate[7] = "nonstring key"
        with self.assertRaisesRegex(LeanExportError, "plain strings"):
            export_lean_representation(certificate, library)

    def test_cycles_and_oversized_literal_are_rejected_explicitly(self):
        library, good = hand_z_certificate()
        cyclic = deepcopy(good)
        cyclic["cycle"] = cyclic
        with self.assertRaisesRegex(LeanExportError, "nesting"):
            export_lean_representation(cyclic, library)
        big = deepcopy(good)
        big["basis"][0]["effect"][0][0][0] = 1 << 4096
        with self.assertRaisesRegex(LeanExportError, "4096-bit"):
            export_lean_representation(big, library)

    def test_padded_resource_budget_is_enforced_without_partial_output(self):
        library, certificate = hand_z_certificate()
        with patch("ueot_qm.lean_export.MAX_PADDED_SCALARS", 1):
            with self.assertRaisesRegex(LeanExportError, "scalar export limit"):
                export_lean_representation(certificate, library)
        with patch("ueot_qm.lean_export.MAX_SOURCE_BYTES", 1):
            with self.assertRaisesRegex(LeanExportError, "source exceeds"):
                export_lean_representation(certificate, library)

    def test_changed_contract_and_unknown_fields_are_rejected(self):
        library, good = hand_z_certificate()
        for key, value in (("schema", "something-else"),
                           ("protocol_class", "only-words-up-to-depth-2"),
                           ("hilbert_dimension", 5), ("unsafe_lean", "axiom x : False")):
            with self.subTest(key=key):
                certificate = deepcopy(good)
                certificate[key] = value
                with self.assertRaises(LeanExportError):
                    export_lean_representation(certificate, library)


if __name__ == "__main__":
    unittest.main()
