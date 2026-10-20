"""Independent exact oracles and omitted-premise controls for v31.5."""

from fractions import Fraction as F
import unittest

from ueot_qm import Matrix, diagonal, identity, Instrument, KrausTerm, real_trace
from ueot_qm.finite_dynamics import (
    ProbabilityWeights, MixtureWeightBudget, mix_instruments,
    channel_operator, iterate_state, cesaro_average, substochastic_instrument,
)


class FiniteDynamicsTests(unittest.TestCase):
    def setUp(self):
        self.rho0 = diagonal([1, 0])
        self.rho1 = diagonal([0, 1])
        self.stay = Instrument({"ok": [KrausTerm(identity(2))]})
        self.flip = Instrument({"ok": [KrausTerm(Matrix([[0, 1], [1, 0]]))]})
        self.p = ProbabilityWeights([F(3, 4), F(1, 4)])
        self.q = ProbabilityWeights([F(1, 4), F(3, 4)])
        self.Q = ((F(1, 4), F(1, 2)), (F(1, 8), F(1, 4)))
        self.qsd = diagonal([F(1, 3), F(2, 3)])

    def test_exact_weights_reject_invalid_premises(self):
        for values in ([], [F(1, 2)], [-1, 2]):
            with self.assertRaises(ValueError):
                ProbabilityWeights(values)
        for values in ([0.5, 0.5], [True], ["1"]):
            with self.assertRaises(TypeError):
                ProbabilityWeights(values)
        with self.assertRaises(ValueError):
            self.p.total_variation(ProbabilityWeights([1]))

    def test_total_variation_bound_is_attained(self):
        budget = MixtureWeightBudget((self.stay, self.flip), self.p, self.q)
        self.assertEqual(budget.upper_bound, F(1, 2))
        left = channel_operator(budget.left, self.rho0)
        right = channel_operator(budget.right, self.rho0)
        self.assertEqual(left, diagonal([F(3, 4), F(1, 4)]))
        self.assertEqual(right, diagonal([F(1, 4), F(3, 4)]))
        self.assertEqual(abs(real_trace(self.rho0 @ (left - right))), budget.upper_bound)
        self.assertEqual(len(budget.component_fingerprint), 64)

    def test_budget_is_an_upper_bound_not_always_the_distance(self):
        budget = MixtureWeightBudget((self.stay, self.stay), self.p, self.q)
        self.assertEqual(budget.upper_bound, F(1, 2))
        self.assertEqual(channel_operator(budget.left, self.rho0), self.rho0)
        self.assertEqual(channel_operator(budget.right, self.rho0), self.rho0)

    def test_mixture_validates_common_context_even_at_zero_weight(self):
        with self.assertRaises(ValueError):
            mix_instruments((self.stay,), self.p)
        zero_last = ProbabilityWeights([1, 0])
        wrong_labels = Instrument({"different": [KrausTerm(identity(2))]})
        wrong_dimension = Instrument({"ok": [KrausTerm(identity(1))]})
        for other in (wrong_labels, wrong_dimension):
            with self.assertRaises(ValueError):
                mix_instruments((self.stay, other), zero_last)

    def test_weighted_kraus_component_needs_no_irrational_runtime(self):
        hadamard = Instrument({"ok": [KrausTerm(Matrix([[1, 1], [1, -1]]), F(1, 2))]})
        mixed = mix_instruments((self.stay, hadamard), ProbabilityWeights([F(1, 2)] * 2))
        self.assertEqual(mixed.completeness(), identity(2))
        self.assertEqual(channel_operator(mixed, self.rho0), Matrix([[F(3, 4), F(1, 4)],
                                                                 [F(1, 4), F(1, 4)]]))

    def test_equal_weights_do_not_control_a_changed_component_library(self):
        weights = ProbabilityWeights([1])
        self.assertEqual(weights.total_variation(weights), 0)
        separation = abs(real_trace(self.rho0 @ (channel_operator(self.stay, self.rho0)
                                                - channel_operator(self.flip, self.rho0))))
        self.assertEqual(separation, 1)

    def test_cesaro_cycle_boundary_and_sharp_odd_residual(self):
        for n in (1, 2, 3, 4, 5, 7):
            average = cesaro_average(self.flip, self.rho0, n)
            expected = diagonal([F((n + 1) // 2, n), F(n // 2, n)])
            self.assertEqual(average, expected)
            end = self.rho0 if n % 2 == 0 else self.rho1
            self.assertEqual(iterate_state(self.flip, self.rho0, n), end)
            residual = channel_operator(self.flip, average) - average
            self.assertEqual(residual * n, end - self.rho0)
            self.assertEqual(abs(real_trace(self.rho0 @ residual)), F(n % 2, n))
        self.assertEqual(cesaro_average(self.flip, self.rho0, 2), identity(2) / 2)
        self.assertNotEqual(iterate_state(self.flip, self.rho0, 100),
                            iterate_state(self.flip, self.rho0, 101))

    def test_stationary_existence_does_not_imply_uniqueness(self):
        self.assertNotEqual(self.rho0, self.rho1)
        for rho in (self.rho0, self.rho1):
            self.assertEqual(channel_operator(self.stay, rho), rho)
            self.assertEqual(cesaro_average(self.stay, rho, 5), rho)

    def test_cesaro_rejects_undefined_zero_average_and_invalid_state(self):
        for n in (0, -1):
            with self.assertRaises(ValueError):
                cesaro_average(self.flip, self.rho0, n)
        for n in (True, F(2), 2.0):
            with self.assertRaises(TypeError):
                cesaro_average(self.flip, self.rho0, n)
        with self.assertRaises(ValueError):
            cesaro_average(self.flip, identity(2), 2)

    def test_diagonal_success_word_has_geometric_mass_and_qsd_posterior(self):
        killed = substochastic_instrument(self.Q)
        self.assertEqual(killed.completeness(), identity(2))
        state = self.qsd
        for n in range(1, 7):
            state = killed.branch(state, "survive")
            self.assertEqual(state, self.qsd * F(1, 2) ** n)
            self.assertEqual(real_trace(state), F(1, 2) ** n)
            self.assertEqual(state / real_trace(state), self.qsd)
        self.assertEqual(killed.posterior(self.qsd, "survive"), self.qsd)

    def test_row_orientation_initial_law_and_loss_are_essential(self):
        killed = substochastic_instrument(self.Q)
        self.assertEqual(killed.probability(identity(2) / 2, "survive"), F(9, 16))
        self.assertNotEqual(F(9, 16), F(1, 2))
        transposed = substochastic_instrument(tuple(zip(*self.Q)))
        self.assertEqual(transposed.probability(self.qsd, "survive"), F(5, 8))
        with self.assertRaises(ValueError):
            Instrument({"survive": killed.terms("survive")})
        coherent = Matrix([[F(1, 2), F(1, 2)], [F(1, 2), F(1, 2)]])
        self.assertEqual(killed.branch(coherent, "survive"), diagonal([F(3, 16), F(3, 8)]))

    def test_doob_stationary_law_differs_from_qsd(self):
        h, q, r = (F(3, 2), F(3, 4)), (F(1, 3), F(2, 3)), F(1, 2)
        doob = tuple(tuple(self.Q[i][j] * h[j] / (r * h[i]) for j in range(2))
                     for i in range(2))
        self.assertEqual(doob, ((F(1, 2), F(1, 2)),) * 2)
        pi = tuple(q[i] * h[i] for i in range(2))
        self.assertEqual(pi, (F(1, 2), F(1, 2)))
        self.assertNotEqual(pi, q)
        conditioned = substochastic_instrument(doob)
        self.assertEqual(conditioned.probability(diagonal(pi), "lost"), 0)
        self.assertEqual(channel_operator(conditioned, diagonal(pi)), diagonal(pi))
        self.assertNotEqual(channel_operator(conditioned, self.qsd), self.qsd)

    def test_substochastic_validation_and_zero_event(self):
        for rows in (((1, 1), (0, 0)), ((-1, 0), (0, 1)), ((1, 0), (0,))):
            with self.assertRaises(ValueError):
                substochastic_instrument(rows)
        with self.assertRaises(TypeError):
            substochastic_instrument(((0.5, 0.5), (0, 1)))
        killed = substochastic_instrument(((0, 0), (0, 0)))
        self.assertEqual(killed.probability(self.qsd, "survive"), 0)
        self.assertIsNone(killed.posterior(self.qsd, "survive"))
        self.assertEqual(killed.probability(self.qsd, "lost"), 1)


if __name__ == "__main__":
    unittest.main()
