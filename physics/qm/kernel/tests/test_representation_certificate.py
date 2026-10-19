"""Exact representation witnesses and deliberate false-certificate controls.

The hand-written Z certificate is an oracle independent of PredictiveModel.
Other tests corrupt mathematically essential fields rather than merely
round-tripping a serializer.  No test is evidence of Python-to-Lean refinement.
"""

from copy import deepcopy
from fractions import Fraction as F
from hashlib import sha256
import json
import unittest
from unittest.mock import patch

from ueot_qm import Matrix, QComplex, identity, diagonal, KrausTerm, Instrument, InstrumentLibrary, PredictiveModel
from ueot_qm.algebra import matrix_payload
from ueot_qm.representation_certificate import (
    SCHEMA, PROTOCOL_CLASS, SCALAR_DOMAIN, RepresentationCertificateError,
    export_representation_certificate, verify_representation_certificate,
)


J = QComplex(0, 1)
P0 = diagonal([1, 0])
P1 = diagonal([0, 1])
Z = Instrument({"0": [KrausTerm(P0)], "1": [KrausTerm(P1)]})
H = Instrument({"ok": [KrausTerm(Matrix([[1, 1], [1, -1]]), F(1, 2))]})
S = Instrument({"ok": [KrausTerm(diagonal([1, J]))]})


def exact_hash(payload):
    return sha256(json.dumps(payload, ensure_ascii=True, separators=(",", ":"), sort_keys=True).encode()).hexdigest()


def pin_basis(certificate):
    """Recompute a claimed hash, so negative tests cannot pass on hash checks alone."""
    certificate["context_fingerprint"] = exact_hash({
        "schema": "ueot_qm.predictive_model.v1",
        "library_fingerprint": certificate["library_fingerprint"],
        "normalization": "first-coordinate-is-trace",
        "basis": [entry["effect"] for entry in certificate["basis"]],
    })


def z_certificate():
    """I, |0><0| is a hand-computed generated closed basis for a Z measurement."""
    library = InstrumentLibrary({"Z": Z})
    certificate = {
        "schema": SCHEMA,
        "protocol_class": PROTOCOL_CLASS,
        "scalar_domain": SCALAR_DOMAIN,
        "normalization": "first-coordinate-is-trace",
        "hilbert_dimension": 2,
        "response_dimension": 2,
        "library_fingerprint": library.fingerprint,
        "library": {
            "schema": "ueot_qm.instrument_library.v1",
            "protocol_class": "all-finite-causal-combinations",
            "actions": [["Z", {"dimension": 2, "outcomes": [
                ["0", [[1, 1, matrix_payload(P0)]]],
                ["1", [[1, 1, matrix_payload(P1)]]],
            ]}]],
        },
        "basis": [
            {"effect": matrix_payload(identity(2)), "word": []},
            {"effect": matrix_payload(P0), "word": [["Z", "0"]]},
        ],
        "pullbacks": [
            {"action": "Z", "outcome": "0", "matrix": matrix_payload(Matrix([[0, 1], [0, 1]]))},
            {"action": "Z", "outcome": "1", "matrix": matrix_payload(Matrix([[1, -1], [0, 0]]))},
        ],
    }
    pin_basis(certificate)
    return library, certificate


class RepresentationCertificateTests(unittest.TestCase):
    def test_hand_computed_z_representation(self):
        library, certificate = z_certificate()
        result = verify_representation_certificate(certificate, library)
        self.assertEqual(result.response_dimension, 2)
        self.assertEqual(result.gram_determinant, 1)
        self.assertEqual(result.checked_word_count, 2)
        self.assertEqual(result.checked_pullback_identity_count, 4)
        self.assertEqual(result.certificate_fingerprint, exact_hash(certificate))

    def test_z_hz_hsz_exports_have_expected_ranks_and_chronological_words(self):
        for actions, rank in (({"Z": Z}, 2), ({"H": H, "Z": Z}, 3), ({"H": H, "S": S, "Z": Z}, 4)):
            with self.subTest(actions=tuple(actions)):
                model = PredictiveModel(InstrumentLibrary(actions))
                certificate = json.loads(json.dumps(export_representation_certificate(model)))
                result = verify_representation_certificate(
                    certificate, model.library, expected_context_fingerprint=model.fingerprint,
                )
                self.assertEqual(result.response_dimension, rank)
                self.assertGreater(result.gram_determinant, 0)
                words = [entry["word"] for entry in certificate["basis"]]
                if "H" in actions:
                    self.assertIn([["H", "ok"], ["Z", "0"]], words)
                if "S" in actions:
                    self.assertIn([["S", "ok"], ["H", "ok"], ["Z", "0"]], words)

    def test_checker_does_not_call_model_search_solver_or_adjoint(self):
        library, certificate = z_certificate()
        forbidden = AssertionError("a certificate checker must not rerun the producer")
        with patch("ueot_qm.predictive.PredictiveModel.__init__", side_effect=forbidden), \
             patch("ueot_qm.predictive.linear_coordinates", side_effect=forbidden), \
             patch("ueot_qm.algebra.linear_coordinates", side_effect=forbidden), \
             patch.object(InstrumentLibrary, "adjoint", side_effect=forbidden), \
             patch.object(Instrument, "adjoint", side_effect=forbidden):
            self.assertEqual(verify_representation_certificate(certificate, library).gram_determinant, 1)

    def test_reversed_witness_is_rejected_even_with_correct_effect_hash(self):
        library = InstrumentLibrary({"H": H, "Z": Z})
        certificate = export_representation_certificate(PredictiveModel(library))
        entry = next(item for item in certificate["basis"] if len(item["word"]) == 2)
        entry["word"].reverse()
        with self.assertRaisesRegex(RepresentationCertificateError, "chronological"):
            verify_representation_certificate(certificate, library)

    def test_origin_requires_identity_and_empty_word(self):
        library, good = z_certificate()
        for field, value in (("effect", matrix_payload(P0)), ("word", [["Z", "0"]])):
            with self.subTest(field=field):
                certificate = deepcopy(good)
                certificate["basis"][0][field] = value
                pin_basis(certificate)
                with self.assertRaisesRegex(RepresentationCertificateError, "basis\\[0\\]"):
                    verify_representation_certificate(certificate, library)

    def test_dependent_actual_word_basis_is_rejected(self):
        library, certificate = z_certificate()
        certificate["basis"][1] = deepcopy(certificate["basis"][0])
        pin_basis(certificate)
        with self.assertRaisesRegex(RepresentationCertificateError, "linearly independent"):
            verify_representation_certificate(certificate, library)

    def test_generated_but_nonclosed_subspace_is_rejected(self):
        library, certificate = z_certificate()
        certificate["response_dimension"] = 1
        certificate["basis"] = certificate["basis"][:1]
        for item in certificate["pullbacks"]:
            item["matrix"] = matrix_payload(Matrix([[F(1, 2)]]))
        pin_basis(certificate)
        with self.assertRaisesRegex(RepresentationCertificateError, "local pullback identity"):
            verify_representation_certificate(certificate, library)

    def test_an_ungenerated_distinguishing_direction_is_rejected(self):
        library, certificate = z_certificate()
        certificate["basis"][1]["effect"] = matrix_payload(Matrix([[1, 1], [1, 1]]) / 2)
        pin_basis(certificate)
        with self.assertRaisesRegex(RepresentationCertificateError, "chronological"):
            verify_representation_certificate(certificate, library)

    def test_missing_duplicate_and_unknown_branch_claims_are_rejected(self):
        library, good = z_certificate()
        for change in ("missing", "duplicate", "unknown"):
            with self.subTest(change=change):
                certificate = deepcopy(good)
                if change == "missing":
                    certificate["pullbacks"].pop()
                elif change == "duplicate":
                    certificate["pullbacks"][1] = deepcopy(certificate["pullbacks"][0])
                else:
                    certificate["pullbacks"][1]["outcome"] = "not-declared"
                with self.assertRaises(RepresentationCertificateError):
                    verify_representation_certificate(certificate, library)

    def test_wrong_pullback_orientation_and_coefficients_are_rejected(self):
        library, good = z_certificate()
        for bad in (Matrix([[0, 0], [1, 1]]), Matrix([[0, 1], [0, 0]])):
            with self.subTest(matrix=bad):
                certificate = deepcopy(good)
                certificate["pullbacks"][0]["matrix"] = matrix_payload(bad)
                with self.assertRaisesRegex(RepresentationCertificateError, "local pullback identity"):
                    verify_representation_certificate(certificate, library)

    def test_complex_coefficient_and_nonhermitian_effect_are_rejected(self):
        library, good = z_certificate()
        certificate = deepcopy(good)
        certificate["pullbacks"][0]["matrix"][0][0] = [0, 1, 1, 1]
        with self.assertRaisesRegex(RepresentationCertificateError, "real rationals"):
            verify_representation_certificate(certificate, library)
        certificate = deepcopy(good)
        certificate["basis"][1]["effect"][0][1] = [1, 1, 0, 1]
        with self.assertRaisesRegex(RepresentationCertificateError, "Hermitian"):
            verify_representation_certificate(certificate, library)

    def test_noncanonical_and_inexact_scalar_payloads_are_rejected(self):
        library, good = z_certificate()
        for scalar in ([True, 1, 0, 1], [1.0, 1, 0, 1], ["1", 1, 0, 1],
                       [2, 2, 0, 1], [1, -1, 0, 1], [0, 0, 0, 1], [1, 1, 0, 2]):
            with self.subTest(scalar=scalar):
                certificate = deepcopy(good)
                certificate["basis"][0]["effect"][0][0] = scalar
                with self.assertRaises(RepresentationCertificateError):
                    verify_representation_certificate(certificate, library)

    def test_context_and_serialized_library_tampering_are_rejected(self):
        library, good = z_certificate()
        for mutation in ("library_hash", "basis_hash", "payload", "boolean_payload", "duplicate_outcome"):
            with self.subTest(mutation=mutation):
                certificate = deepcopy(good)
                if mutation == "library_hash":
                    certificate["library_fingerprint"] = "0" * 64
                elif mutation == "basis_hash":
                    certificate["context_fingerprint"] = "0" * 64
                elif mutation == "payload":
                    certificate["library"]["actions"][0][1]["outcomes"][0][1][0][0] = 2
                elif mutation == "boolean_payload":
                    certificate["library"]["actions"][0][1]["outcomes"][0][1][0][0] = True
                else:
                    certificate["library"]["actions"][0][1]["outcomes"][1][0] = "0"
                with self.assertRaises(RepresentationCertificateError):
                    verify_representation_certificate(certificate, library)

    def test_alternative_valid_basis_allowed_only_under_its_own_context(self):
        model = PredictiveModel(InstrumentLibrary({"H": H, "Z": Z}))
        certificate = export_representation_certificate(model)
        permutation = [0, 2, 1]
        certificate["basis"] = [certificate["basis"][index] for index in permutation]
        for branch in certificate["pullbacks"]:
            old = branch["matrix"]
            branch["matrix"] = [[old[i][j] for j in permutation] for i in permutation]
        pin_basis(certificate)
        result = verify_representation_certificate(certificate, model.library)
        self.assertNotEqual(result.context_fingerprint, model.fingerprint)
        self.assertEqual(result.response_dimension, 3)
        with self.assertRaisesRegex(RepresentationCertificateError, "intended model"):
            verify_representation_certificate(certificate, model.library, expected_context_fingerprint=model.fingerprint)

    def test_impossible_outcome_still_requires_its_zero_pullback(self):
        library = InstrumentLibrary({"I": Instrument({"ok": [KrausTerm(identity(2))], "never": []})})
        certificate = export_representation_certificate(PredictiveModel(library))
        result = verify_representation_certificate(certificate, library)
        self.assertEqual(result.response_dimension, 1)
        zero = next(item for item in certificate["pullbacks"] if item["outcome"] == "never")
        self.assertEqual(zero["matrix"], matrix_payload(Matrix([[0]])))
        zero["matrix"] = matrix_payload(Matrix([[1]]))
        with self.assertRaisesRegex(RepresentationCertificateError, "local pullback identity"):
            verify_representation_certificate(certificate, library)

    def test_dimension_one_and_four_have_exact_certificates(self):
        one = InstrumentLibrary({"I": Instrument({"ok": [KrausTerm(identity(1))]})})
        four = InstrumentLibrary({"Z0": Instrument({
            "0": [KrausTerm(diagonal([1, 1, 0, 0]))],
            "1": [KrausTerm(diagonal([0, 0, 1, 1]))],
        })})
        for library, rank, determinant in ((one, 1, 1), (four, 2, 4)):
            with self.subTest(dimension=library.dimension):
                result = verify_representation_certificate(export_representation_certificate(PredictiveModel(library)), library)
                self.assertEqual(result.response_dimension, rank)
                self.assertEqual(result.gram_determinant, determinant)

    def test_protocol_schema_dimensions_and_witness_resource_limits(self):
        library, good = z_certificate()
        for field, value in (("hilbert_dimension", True), ("hilbert_dimension", 5),
                             ("response_dimension", 0), ("response_dimension", 5),
                             ("protocol_class", "time-dependent-controls"),
                             ("scalar_domain", "floating-point"),
                             ("normalization", "second-coordinate"),
                             ("schema", "unregistered-schema"), ("undeclared_claim", True)):
            with self.subTest(field=field, value=value):
                certificate = deepcopy(good)
                certificate[field] = value
                with self.assertRaises(RepresentationCertificateError):
                    verify_representation_certificate(certificate, library)
        certificate = deepcopy(good)
        certificate["basis"][1]["word"] = [["Z", "0"]] * 4
        with self.assertRaisesRegex(RepresentationCertificateError, "generation-depth"):
            verify_representation_certificate(certificate, library)
        certificate["basis"][1]["word"] = [["Z", "undeclared"]]
        with self.assertRaisesRegex(RepresentationCertificateError, "undeclared action/outcome"):
            verify_representation_certificate(certificate, library)

    def test_expected_library_is_rechecked_and_not_inferred_from_the_claim(self):
        library, certificate = z_certificate()
        other = InstrumentLibrary({"Z": Instrument({
            "0": [KrausTerm(P0, F(1, 2)), KrausTerm(P0, F(1, 2))],
            "1": [KrausTerm(P1)],
        })})
        # This is the same physical channel with another exact Kraus listing.
        with self.assertRaisesRegex(RepresentationCertificateError, "different library"):
            verify_representation_certificate(certificate, other)
        corrupted = deepcopy(library)
        object.__setattr__(corrupted, "fingerprint", "0" * 64)
        with self.assertRaisesRegex(RepresentationCertificateError, "stored fingerprint"):
            verify_representation_certificate(certificate, corrupted)
        corrupted = deepcopy(library)
        first = corrupted.entries[0][1].branches[0][1][0]
        object.__setattr__(first, "weight", F(2))
        with self.assertRaisesRegex(RepresentationCertificateError, "completeness"):
            verify_representation_certificate(certificate, corrupted)


if __name__ == "__main__":
    unittest.main()
