"""Independent physical examples, negative controls, and exact certificates.

Closed-form probabilities are primary oracles. Dense/coordinate agreement is
an additional implementation cross-check, never described as a Lean proof.
"""

from fractions import Fraction as F
import unittest

from ueot_qm import (QComplex, Matrix, identity, diagonal, outer, zeros,
                     KrausTerm, Instrument, InstrumentLibrary, ProtocolNode,
                     PredictiveModel, EncodedState, validate_density)
from ueot_qm.certificates import (tv_distance, compare_finite_protocols,
                                  TransportStep, transport_budget,
                                  verify_transport_trace, certify_postselection)


J = QComplex(0, 1)
R0 = diagonal([1, 0])
R1 = diagonal([0, 1])
RP = Matrix([[1, 1], [1, 1]]) / 2
RM = Matrix([[1, -1], [-1, 1]]) / 2
RY = Matrix([[1, -J], [J, 1]]) / 2
RYM = Matrix([[1, J], [-J, 1]]) / 2
MIX = identity(2) / 2
H0 = Matrix([[1, 1], [1, -1]])
S = diagonal([1, J])
X = Matrix([[0, 1], [1, 0]])
Z = Instrument({"0": [KrausTerm(R0)], "1": [KrausTerm(R1)]})
H = Instrument({"ok": [KrausTerm(H0, F(1, 2))]})
PHASE = Instrument({"ok": [KrausTerm(S)]})


def library(*actions):
    choices = {"Z": Z, "H": H, "S": PHASE}
    return InstrumentLibrary({a: choices[a] for a in actions})


def tensor(left, right):
    """Test oracle for the lexicographic tensor product."""
    return Matrix([
        left[i // right.nrows, j // right.ncols] * right[i % right.nrows, j % right.ncols]
        for j in range(left.ncols * right.ncols)]
        for i in range(left.nrows * right.nrows))


def terminal_z():
    return ProtocolNode("Z", {"0": None, "1": None})


class ExactQuantumTests(unittest.TestCase):
    def test_complex_phase_arithmetic(self):
        self.assertEqual(J * J, -1)
        self.assertEqual(QComplex(1, 1) / QComplex(1, -1), J)
        self.assertEqual(S.adjoint() @ S, identity(2))
        self.assertEqual((S @ RP @ S.adjoint()), RY)

    def test_inexact_inputs_rejected(self):
        for value in (0.5, "1/2", complex(0, 1)):
            with self.subTest(value=value), self.assertRaises(TypeError):
                QComplex(value)
        with self.assertRaises(TypeError):
            Matrix([[0.5, 0], [0, 0.5]])
        with self.assertRaises(TypeError):
            KrausTerm(H0, 0.5)

    def test_density_positive_and_negative_controls(self):
        for rho in (R0, R1, RP, RM, RY, RYM, MIX):
            with self.subTest(rho=rho):
                self.assertTrue(rho.is_density())
        # Hermitian and trace one alone do not imply a physical state.
        bad = diagonal([F(3, 2), F(-1, 2)])
        self.assertTrue(bad.is_hermitian())
        self.assertEqual(bad.trace(), 1)
        self.assertFalse(bad.is_density())
        with self.assertRaises(ValueError):
            Z.probability(bad, "0")
        self.assertFalse(Matrix([[1, 1], [0, 0]]).is_density())

    def test_all_principal_minors_are_needed(self):
        # Checking only leading minors would wrongly accept this matrix.
        hidden_negative = diagonal([0, -1, 2])
        self.assertEqual(hidden_negative.trace(), 1)
        self.assertEqual(hidden_negative.determinant(), 0)
        self.assertFalse(hidden_negative.is_psd())

    def test_bell_partial_transpose_is_not_positive(self):
        bell = outer([1, 0, 0, 1]) / 2
        self.assertTrue(bell.is_density())
        partial_transpose = Matrix([[1, 0, 0, 0], [0, 0, 1, 0],
                                    [0, 1, 0, 0], [0, 0, 0, 1]]) / 2
        self.assertEqual(partial_transpose.trace(), 1)
        self.assertEqual(partial_transpose.determinant(), F(-1, 16))
        self.assertFalse(partial_transpose.is_psd())
        with self.assertRaises(ValueError):
            validate_density(partial_transpose)

    def test_dimension_and_completeness_rejections(self):
        with self.assertRaises(ValueError):
            (identity(5) / 5).is_density()
        with self.assertRaises(ValueError):
            KrausTerm(identity(5))
        with self.assertRaises(ValueError):
            Instrument({"only": [KrausTerm(R0)]})
        with self.assertRaises(ValueError):
            KrausTerm(identity(2), -1)
        with self.assertRaises(ValueError):
            Instrument({"a": [KrausTerm(identity(2))], "b": [KrausTerm(identity(3))]})
        with self.assertRaises(ValueError):
            Z.probability(identity(3) / 3, "0")

    def test_hadamard_interference_has_exact_probabilities(self):
        lib = library("H", "Z")
        self.assertEqual(lib.word_law(R0, ["H", "Z"]),
                         {("ok", "0"): F(1, 2), ("ok", "1"): F(1, 2)})
        self.assertEqual(lib.word_law(R0, ["H", "H", "Z"]),
                         {("ok", "ok", "0"): F(1), ("ok", "ok", "1"): F(0)})
        self.assertEqual(H.completeness(), identity(2))

    def test_complex_y_phase_is_observable(self):
        lib = library("H", "S", "Z")
        expected = {("ok", "ok", "0"): F(0), ("ok", "ok", "1"): F(1)}
        self.assertEqual(lib.word_law(RY, ["S", "H", "Z"]), expected)
        self.assertEqual(PredictiveModel(lib).word_law(RY, ["S", "H", "Z"]), expected)

    def test_zero_branch_has_no_posterior(self):
        self.assertIsNone(Z.posterior(R0, "1"))
        self.assertEqual(Z.branch(R0, "1"), zeros(2))
        self.assertEqual(Z.posterior(R0, "0"), R0)
        impossible = Instrument({"ok": [KrausTerm(identity(2))], "never": []})
        self.assertEqual(impossible.probability(RY, "never"), 0)
        self.assertIsNone(impossible.posterior(RY, "never"))

    def test_damping_with_multiple_weighted_kraus_terms(self):
        k0 = diagonal([1, F(1, 2)])
        k1 = Matrix([[0, 1], [0, 0]])
        damping = Instrument({"survive": [KrausTerm(k0)],
                              "jump": [KrausTerm(k1, F(3, 4))]})
        self.assertEqual(damping.probability(R1, "jump"), F(3, 4))
        self.assertEqual(damping.probability(R1, "survive"), F(1, 4))
        self.assertEqual(damping.posterior(R1, "jump"), R0)
        self.assertEqual(damping.posterior(R1, "survive"), R1)
        channel = Instrument({"ok": [KrausTerm(k0), KrausTerm(k1, F(3, 4))]})
        expected = Matrix([[F(7, 8), F(1, 4)], [F(1, 4), F(1, 8)]])
        self.assertEqual(channel.branch(RP, "ok"), expected)
        self.assertTrue(expected.is_density())

    def test_damping_on_entangled_input(self):
        k0 = tensor(diagonal([1, F(1, 2)]), identity(2))
        k1 = tensor(Matrix([[0, 1], [0, 0]]), identity(2))
        joint = Instrument({"ok": [KrausTerm(k0), KrausTerm(k1, F(3, 4))]})
        bell = outer([1, 0, 0, 1]) / 2
        expected = Matrix([[F(1, 2), 0, 0, F(1, 4)],
                           [0, F(3, 8), 0, 0], [0, 0, 0, 0],
                           [F(1, 4), 0, 0, F(1, 8)]])
        self.assertEqual(joint.branch(bell, "ok"), expected)
        self.assertTrue(expected.is_density())

    def test_adjoint_trace_duality_with_complex_inputs(self):
        # Noncommuting Y density and off-diagonal effect catch conjugation errors.
        for op in (H, PHASE, Z):
            for outcome in op.outcomes:
                self.assertEqual((op.branch(RY, outcome) @ RP).trace(),
                                 (RY @ op.adjoint(RP, outcome)).trace())


class PredictiveQuotientTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.z = PredictiveModel(library("Z"))
        cls.hz = PredictiveModel(library("H", "Z"))
        cls.hsz = PredictiveModel(library("H", "S", "Z"))

    def test_observable_dimensions_and_terminal_stability(self):
        self.assertEqual([m.dimension for m in (self.z, self.hz, self.hsz)], [2, 3, 4])
        for model in (self.z, self.hz, self.hsz):
            self.assertEqual(model.dimension_history[-1], model.dimension_history[-2])
            self.assertLessEqual(len(model.dimension_history) - 2, model.hilbert_dimension ** 2 - 1)
            self.assertEqual(model.basis[0], identity(2))

    def test_protocol_relative_equivalence(self):
        self.assertTrue(self.z.equivalent(RP, RM))
        self.assertFalse(self.hz.equivalent(RP, RM))
        self.assertTrue(self.hz.equivalent(RY, RYM))
        self.assertFalse(self.hsz.equivalent(RY, RYM))
        self.assertFalse(self.z.equivalent(R0, R1))

    def test_recursive_branch_matches_closed_form(self):
        encoded = self.hsz.encode(RY)
        encoded = self.hsz.update(encoded, "S", "ok")
        self.assertEqual(encoded, self.hsz.encode(RM))
        encoded = self.hsz.update(encoded, "H", "ok")
        self.assertEqual(encoded, self.hsz.encode(R1))
        self.assertIsNone(self.hsz.update(encoded, "Z", "0"))
        self.assertEqual(self.hsz.update(encoded, "Z", "1"), self.hsz.encode(R1))

    def test_pullbacks_close_every_basis_effect(self):
        for model in (self.z, self.hz, self.hsz):
            for action in model.library.actions:
                for outcome in model.library.outcomes(action):
                    coefficients = model.pullback_matrix(action, outcome)
                    for j, effect in enumerate(model.basis):
                        expansion = zeros(model.hilbert_dimension)
                        for coefficient, basis_effect in zip(coefficients[j], model.basis):
                            self.assertEqual(coefficient.imag, 0)
                            expansion += basis_effect * coefficient.real
                        self.assertEqual(expansion, model.library.adjoint(effect, action, outcome))

    def test_coordinate_only_record_laws_match_dense_oracle(self):
        words = [[], ["Z", "Z"], ["H", "Z", "H", "Z"],
                 ["S", "H", "Z", "S", "H", "Z"]]
        for rho in (R0, RP, RM, RY, RYM, MIX):
            for word in words:
                with self.subTest(rho=rho, word=word):
                    direct = self.hsz.library.word_law(rho, word)
                    encoded = self.hsz.word_law(self.hsz.encode(rho), word)
                    self.assertEqual(encoded, direct)
                    self.assertEqual(sum(encoded.values()), 1)
                    self.assertTrue(all(isinstance(p, F) and p >= 0 for p in encoded.values()))

    def test_all_positive_branches_are_physical(self):
        for rho in (R0, RP, RM, RY, MIX):
            for action in self.hsz.library.actions:
                for outcome in self.hsz.library.outcomes(action):
                    dense = self.hsz.library.posterior(rho, action, outcome)
                    encoded = self.hsz.update(self.hsz.encode(rho), action, outcome)
                    if dense is None:
                        self.assertIsNone(encoded)
                    else:
                        self.assertTrue(dense.is_density())
                        self.assertEqual(encoded, self.hsz.encode(dense))

    def test_context_change_requires_reencoding(self):
        old = self.z.encode(RP)
        with self.assertRaises(ValueError):
            self.hz.update(old, "H", "ok")
        with self.assertRaises(ValueError):
            self.hz.word_law(old, ["Z"])
        with self.assertRaises(TypeError):
            EncodedState(self.z.context_fingerprint, [1, 0])
        self.assertEqual(PredictiveModel(library("Z")).encode(RP), old)

    def test_fingerprint_is_representation_sensitive(self):
        original = InstrumentLibrary({"U": Instrument({"ok": [KrausTerm(X)]})})
        phased = InstrumentLibrary({"U": Instrument({"ok": [KrausTerm(X * J)]})})
        self.assertNotEqual(original.fingerprint, phased.fingerprint)
        self.assertEqual(original.branch(RY, "U", "ok"), phased.branch(RY, "U", "ok"))

    def test_invalid_record_is_rejected_even_after_zero_probability(self):
        for engine in (self.hz, self.hz.library):
            with self.assertRaises(KeyError):
                engine.record_probability(R0, [("Z", "1"), ("unknown", "x")])


class ProtocolAndMemoryTests(unittest.TestCase):
    def test_adaptive_controller_complete_law(self):
        lib = library("H", "Z")
        tree = ProtocolNode("Z", {"0": ProtocolNode("H", {"ok": terminal_z()}),
                                  "1": terminal_z()})
        expected = {
            (("Z", "0"), ("H", "ok"), ("Z", "0")): F(1, 4),
            (("Z", "0"), ("H", "ok"), ("Z", "1")): F(1, 4),
            (("Z", "1"), ("Z", "0")): F(0),
            (("Z", "1"), ("Z", "1")): F(1, 2),
        }
        self.assertEqual(lib.protocol_law(MIX, tree), expected)
        self.assertEqual(PredictiveModel(lib).protocol_law(MIX, tree), expected)

    def test_protocol_validation_includes_impossible_continuations(self):
        lib = library("Z")
        with self.assertRaises(ValueError):
            lib.protocol_law(R0, ProtocolNode("Z", {"0": None}))
        unreachable_bad = ProtocolNode("Z", {
            "0": None, "1": ProtocolNode("unknown", {"x": None})})
        for engine in (lib, PredictiveModel(lib)):
            with self.assertRaises(KeyError):
                engine.protocol_law(R0, unreachable_bad)
        self.assertEqual(lib.protocol_law(RY, None), {(): F(1)})

    def test_same_system_and_environment_marginals_do_not_fix_memory(self):
        # Correlated and anticorrelated classical joint states have the same
        # marginals I/2; an environment-controlled CNOT reveals opposite futures.
        correlated = diagonal([F(1, 2), 0, 0, F(1, 2)])
        anticorrelated = diagonal([0, F(1, 2), F(1, 2), 0])
        for rho in (correlated, anticorrelated):
            sys = Matrix([[sum(rho[2*i+e, 2*j+e] for e in range(2))
                           for j in range(2)] for i in range(2)])
            env = Matrix([[sum(rho[2*s+i, 2*s+j] for s in range(2))
                           for j in range(2)] for i in range(2)])
            self.assertEqual(sys, MIX)
            self.assertEqual(env, MIX)
        cnot = Matrix([[1, 0, 0, 0], [0, 0, 0, 1],
                       [0, 0, 1, 0], [0, 1, 0, 0]])
        lib = InstrumentLibrary({
            "couple": Instrument({"ok": [KrausTerm(cnot)]}),
            "Z": Instrument({"0": [KrausTerm(diagonal([1, 1, 0, 0]))],
                              "1": [KrausTerm(diagonal([0, 0, 1, 1]))]}),
        })
        self.assertEqual(lib.word_law(correlated, ["Z"]), lib.word_law(anticorrelated, ["Z"]))
        self.assertEqual(lib.word_law(correlated, ["couple", "Z"]),
                         {("ok", "0"): F(1), ("ok", "1"): F(0)})
        self.assertEqual(lib.word_law(anticorrelated, ["couple", "Z"]),
                         {("ok", "0"): F(0), ("ok", "1"): F(1)})
        joint_model = PredictiveModel(lib)
        self.assertFalse(joint_model.equivalent(correlated, anticorrelated))


class CertificateTests(unittest.TestCase):
    def test_deep_finite_protocol_certificate_uses_no_recursive_serialization(self):
        lib = InstrumentLibrary({"I": Instrument({"ok": [KrausTerm(identity(1))]})})
        tree = None
        for _ in range(1100):
            tree = ProtocolNode("I", {"ok": tree})
        receipt = compare_finite_protocols(lib, lib, {"same": (identity(1), identity(1))},
                                           {"long": tree})
        self.assertEqual(receipt.maximum_tv, 0)
        self.assertEqual(receipt.protocol_count, 1)

    def test_tv_support_alignment_and_normalization(self):
        self.assertEqual(tv_distance({"a": 1}, {"b": 1}), 1)
        self.assertEqual(tv_distance({"a": F(1, 2), "b": F(1, 2)}, {"a": 1}), F(1, 2))
        for bad in ({}, {"a": F(1, 2)}, {"a": 2, "b": -1}):
            with self.assertRaises(ValueError):
                tv_distance(bad, {"a": 1})
        with self.assertRaises(TypeError):
            tv_distance({"a": 1.0}, {"a": 1})

    def test_finite_coverage_cannot_be_promoted_to_all_protocols(self):
        lib = library("H", "Z")
        pair = {"plus-minus": (RP, RM)}
        narrow = compare_finite_protocols(lib, lib, pair, {"Z": terminal_z()})
        wider = compare_finite_protocols(lib, lib, pair, {
            "Z": terminal_z(), "HZ": ProtocolNode("H", {"ok": terminal_z()})})
        self.assertEqual(narrow.maximum_tv, 0)
        self.assertEqual(wider.maximum_tv, 1)
        self.assertEqual(wider.protocol_count, 2)
        self.assertNotEqual(narrow.scope_fingerprint, wider.scope_fingerprint)
        self.assertEqual(narrow.scope, "declared-finite-preparation-pairs-and-causal-trees")
        self.assertNotEqual(compare_finite_protocols(lib, lib, {"plus-minus": (RP, RP)},
                                                     {"Z": terminal_z()}).scope_fingerprint,
                            narrow.scope_fingerprint)

    def test_empty_or_misaligned_certificate_scope_is_rejected(self):
        lib = library("Z")
        with self.assertRaises(ValueError):
            compare_finite_protocols(lib, lib, {}, {"Z": terminal_z()})
        with self.assertRaises(ValueError):
            compare_finite_protocols(lib, lib, {"x": (R0, R1)}, {})
        with self.assertRaises(KeyError):
            compare_finite_protocols(lib, lib, {"x": (R0, R1)},
                                     {"H": ProtocolNode("H", {"ok": None})})

    def test_transport_budget_and_checked_recurrence(self):
        steps = [TransportStep(F(1, 2), F(1, 10), "declared step 0 bound"),
                 TransportStep(2, F(1, 20), "declared step 1 bound")]
        self.assertEqual(transport_budget(F(1, 5), steps), (F(1, 5), F(1, 5), F(9, 20)))
        receipt = verify_transport_trace([F(1, 10), F(1, 10), F(1, 5)], F(1, 5), steps)
        self.assertEqual(receipt.bounds[-1], F(9, 20))
        self.assertEqual(receipt.scope, "supplied-finite-scalar-trace")
        self.assertEqual(transport_budget(0, []), (F(0),))

    def test_transport_rejects_hidden_failed_local_premise(self):
        # This trace fits the loose global envelope but violates its local step.
        steps = [TransportStep(1, 0, "no local error")]
        with self.assertRaises(ValueError):
            verify_transport_trace([0, 1], 2, steps)
        with self.assertRaises(ValueError):
            TransportStep(-1, 0, "negative L is invalid")
        with self.assertRaises(ValueError):
            TransportStep(1, -1, "negative epsilon is invalid")
        with self.assertRaises(ValueError):
            verify_transport_trace([2, 2], 1, steps)
        with self.assertRaises(ValueError):
            verify_transport_trace([], 1, [])

    def test_postselection_amplifies_rare_record_difference(self):
        left = {"common": F(99, 100), "a": F(1, 100), "b": F(0)}
        right = {"common": F(99, 100), "a": F(0), "b": F(1, 100)}
        receipt = certify_postselection(left, right, {"a", "b"})
        self.assertEqual(receipt.original_tv, F(1, 100))
        self.assertEqual(receipt.minimum_event_mass, F(1, 100))
        self.assertEqual(receipt.conditional_tv, 1)
        self.assertEqual(receipt.conditional_upper_bound, 1)

    def test_postselection_positive_mass_guard_and_nontrivial_bound(self):
        with self.assertRaises(ValueError):
            certify_postselection({"a": 1}, {"b": 1}, {"a"})
        left = {"a": F(1, 2), "b": F(2, 5), "c": F(1, 10)}
        right = {"a": F(49, 100), "b": F(41, 100), "c": F(1, 10)}
        receipt = certify_postselection(left, right, {"a", "b"})
        self.assertEqual(receipt.original_tv, F(1, 100))
        self.assertEqual(receipt.conditional_tv, F(1, 90))
        self.assertEqual(receipt.conditional_upper_bound, F(1, 45))


if __name__ == "__main__":
    unittest.main(verbosity=2)
