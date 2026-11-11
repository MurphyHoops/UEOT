import unittest
import numpy as np

from finite_conditioning import (
    Instrument, Leaf, Node, ZeroAcceptanceProbability, NumericalConditioningError,
    backward_effects, full_leaf_law, normalized_accepted_law, conditioned_reference,
    cq_distance, trace_distance, mass, expected_action_cost, independent_retry_cost,
    scaled_filter, branch_choi, common_observation_mixture, conditional_error_bound,
    psd_factors, repeated_success_tree,
)
from fixtures import (t3, singular_one_step, early_stop, diagonal_classical,
                      projective_record, deterministic_label, out_of_library, positive_chain)


class FiniteConditioningTests(unittest.TestCase):
    def assert_conditional_law(self, tree, rho, completion_label=None):
        ref = conditioned_reference(tree, rho, completion_label)
        raw, accepted = full_leaf_law(tree, rho)
        p, target = normalized_accepted_law(raw, accepted)
        got, got_accepted = full_leaf_law(ref.tree, ref.initial_state)
        self.assertEqual(set(got), set(raw))
        self.assertEqual(got_accepted, accepted)
        self.assertLess(cq_distance(target, got), 2e-8)
        self.assertAlmostEqual(sum(mass(x) for x in raw.values()), 1, places=9)
        self.assertAlmostEqual(sum(mass(x) for x in got.values()), 1, places=9)
        self.assertAlmostEqual(ref.acceptance_probability, p, places=11)
        return ref

    def test_t3_noncommuting_full_visible_cq(self):
        inst, tree, rho = t3()
        k0, k1 = inst.branches["0"][0], inst.branches["1"][0]
        self.assertGreater(np.linalg.norm(k0 @ k1 - k1 @ k0), 0.01)
        ref = self.assert_conditional_law(tree, rho)
        self.assertAlmostEqual(ref.acceptance_probability, 117 / 4096, places=12)
        raw, accepted = full_leaf_law(tree, rho)
        self.assertEqual(len(accepted), 8)
        self.assertEqual(len(raw), 15)  # all early failures are retained

    def test_complete_positive_chain_realization_and_cost(self):
        source, tree, rho, library = positive_chain()
        ref = self.assert_conditional_law(tree, rho)
        self.assertAlmostEqual(ref.acceptance_probability, 1 / 8)
        np.testing.assert_allclose(ref.initial_state, rho, atol=1e-12)
        for t in range(4):
            np.testing.assert_allclose(ref.effects[("0",) * t], np.eye(2) / (2 ** (3 - t)), atol=1e-12)
        result = common_observation_mixture({"x": ref.tree.instrument},
                                           {a: {"x": inst} for a, inst in library.items()})
        self.assertEqual(result["status"], "NUMERICAL_FEASIBLE_MIXTURE")
        self.assertAlmostEqual(result["weights"]["A0"], 1 / 2)
        self.assertAlmostEqual(result["weights"]["A1"], 1 / 2)
        physical = Instrument({o: tuple(k / np.sqrt(2) for a in library.values() for k in a.branches[o])
                               for o in source.branches})
        physical_tree = repeated_success_tree(physical, {"0", "1"}, 3)
        actual, accepted = full_leaf_law(physical_tree, rho)
        original, original_accepted = full_leaf_law(tree, rho)
        _, target = normalized_accepted_law(original, original_accepted)
        self.assertEqual(accepted, original_accepted)
        self.assertLess(cq_distance(actual, target), 1e-12)
        self.assertAlmostEqual(independent_retry_cost(tree, rho)["all_cost_per_output"], 14)
        self.assertAlmostEqual(expected_action_cost(physical_tree, rho), 3)

    def test_non_scalar_t3_original_only_library_is_separated(self):
        source, tree, rho = t3()
        ref = conditioned_reference(tree, rho)
        maximally_mixed = np.eye(2) / 2
        self.assertAlmostEqual(mass(source.branch("failure", maximally_mixed)), 23 / 32)
        self.assertAlmostEqual(mass(ref.tree.instrument.branch("failure", maximally_mixed)), 0)
        failure_effect = source.adjoint("failure", np.eye(2))
        self.assertGreaterEqual(np.linalg.eigvalsh(failure_effect).min(), 5 / 8)
        result = common_observation_mixture({"x": ref.tree.instrument}, {"original": {"x": source}})
        self.assertEqual(result["status"], "NUMERICAL_NO_FEASIBLE_MIXTURE")

    def test_hidden_kraus_not_observable(self):
        inst, tree, rho = t3()
        k = inst.branches["0"][0]
        split = Instrument({"0": (3 * k / 5, 4 * k / 5),
                            "1": inst.branches["1"], "failure": inst.branches["failure"]})
        split_tree = repeated_success_tree(split, {"0", "1"}, 3)
        a, aa = full_leaf_law(tree, rho)
        b, ba = full_leaf_law(split_tree, rho)
        self.assertEqual(aa, ba)
        self.assertEqual(set(a), set(b))
        self.assertLess(cq_distance(a, b), 1e-12)
        self.assert_conditional_law(split_tree, rho)

    def test_singular_positive_support_completion_independence(self):
        tree, rho = singular_one_step()
        a = self.assert_conditional_law(tree, rho, "0")
        b = self.assert_conditional_law(tree, rho, "1")
        np.testing.assert_allclose(a.supports[()], np.diag([1, 0]), atol=1e-12)
        la, _ = full_leaf_law(a.tree, a.initial_state)
        lb, _ = full_leaf_law(b.tree, b.initial_state)
        self.assertLess(cq_distance(la, lb), 1e-12)
        # Their all-space instruments differ. Only the support task is invariant.
        self.assertGreater(np.linalg.norm(branch_choi(a.tree.instrument.branches["0"])
                                           - branch_choi(b.tree.instrument.branches["0"])), 0.9)
        outside_support = np.diag([0, 1]).astype(complex)
        outside_a, _ = full_leaf_law(a.tree, outside_support)
        outside_b, _ = full_leaf_law(b.tree, outside_support)
        self.assertAlmostEqual(cq_distance(outside_a, outside_b), 1)

    def test_zero_probability_is_rejected(self):
        tree, _ = singular_one_step()
        with self.assertRaises(ZeroAcceptanceProbability):
            conditioned_reference(tree, np.diag([0, 1]))
        with self.assertRaises(ZeroAcceptanceProbability):
            conditioned_reference(Leaf(False), np.eye(2) / 2)

    def test_zero_horizon_identity(self):
        rho = np.array([[0.5, 0.25j], [-0.25j, 0.5]])
        ref = self.assert_conditional_law(Leaf(True), rho)
        self.assertAlmostEqual(ref.acceptance_probability, 1)

    def test_small_positive_eigenvalue_not_deleted(self):
        with self.assertRaises(NumericalConditioningError):
            psd_factors(np.diag([1, 1e-15]))
        # Uniform rarity is different from a nearly singular relative condition.
        factors = psd_factors(np.eye(2) * 1e-20)
        np.testing.assert_allclose(factors.support, np.eye(2), atol=1e-12)

    def test_diagonal_reduction_matches_classical_conditional_paths(self):
        inst, tree, rho, q = diagonal_classical()
        self.assert_conditional_law(tree, rho)
        raw, accepted = full_leaf_law(tree, rho)
        for record, block in raw.items():
            v = np.diag(rho).copy()
            for o in record:
                v = q[o] @ v
            np.testing.assert_allclose(block, np.diag(v), atol=1e-12)
        self.assertEqual(len(accepted), 4)

    def test_labels_swap_preserves_channel_but_not_record(self):
        a, b = projective_record(), projective_record(True)
        rho = np.diag([1, 0]).astype(complex)
        np.testing.assert_allclose(a.channel(rho), b.channel(rho), atol=1e-12)
        ta = Node(a, {"0": Leaf(True), "1": Leaf(True)})
        tb = Node(b, {"0": Leaf(True), "1": Leaf(True)})
        la, _ = full_leaf_law(ta, rho)
        lb, _ = full_leaf_law(tb, rho)
        self.assertAlmostEqual(cq_distance(la, lb), 1)

    def test_same_observation_requires_shared_weights(self):
        a0, a1 = deterministic_label("0"), deterministic_label("1")
        actions = {"a0": {"x0": a0, "x1": a0}, "a1": {"x0": a1, "x1": a1}}
        targets = {"x0": a0, "x1": a1}
        for x in targets:
            result = common_observation_mixture({x: targets[x]},
                                                {a: {x: cfg[x]} for a, cfg in actions.items()})
            self.assertEqual(result["status"], "NUMERICAL_FEASIBLE_MIXTURE")
        result = common_observation_mixture(targets, actions)
        self.assertEqual(result["status"], "NUMERICAL_NO_FEASIBLE_MIXTURE")
        self.assertFalse(result["exact_certificate"])

    def test_positive_mixture_realization(self):
        eye, zero = np.eye(2), np.zeros((2, 2))
        flip = np.array([[0, 1], [1, 0]])
        a0 = Instrument({"0": (eye,), "1": (zero,)})
        a1 = Instrument({"0": (zero,), "1": (flip,)})
        target = Instrument({"0": (eye / np.sqrt(2),), "1": (flip / np.sqrt(2),)})
        result = common_observation_mixture({"x": target},
                                           {"a0": {"x": a0}, "a1": {"x": a1}})
        self.assertEqual(result["status"], "NUMERICAL_FEASIBLE_MIXTURE")
        self.assertAlmostEqual(result["weights"]["a0"], 1 / 2)
        self.assertAlmostEqual(result["weights"]["a1"], 1 / 2)

    def test_rank_one_system_replacement_exception_and_reference_obstruction(self):
        p0 = np.diag([1, 0]).astype(complex)
        lower = np.array([[0, 1], [0, 0]], complex)
        replacement = Instrument({"out": (p0, lower)})
        replacement.validate_complete()
        rho = np.array([[0.6, 0.1j], [-0.1j, 0.4]])
        selected = p0 @ rho @ p0 / mass(p0 @ rho @ p0)
        np.testing.assert_allclose(selected, replacement.channel(rho), atol=1e-12)
        bell = np.array([1, 0, 0, 1], complex) / np.sqrt(2)
        joint = np.outer(bell, bell.conj())
        joint_filter = np.kron(p0, np.eye(2))
        selected_joint = joint_filter @ joint @ joint_filter
        selected_joint /= mass(selected_joint)
        replaced_joint = sum(np.kron(k, np.eye(2)) @ joint @ np.kron(k.conj().T, np.eye(2))
                             for k in replacement.branches["out"])
        self.assertAlmostEqual(trace_distance(selected_joint, replaced_joint), 1 / 2)
        selected_reference = np.trace(selected_joint.reshape(2, 2, 2, 2), axis1=0, axis2=2)
        replaced_reference = np.trace(replaced_joint.reshape(2, 2, 2, 2), axis1=0, axis2=2)
        np.testing.assert_allclose(selected_reference, p0)
        np.testing.assert_allclose(replaced_reference, np.eye(2) / 2)
        # Scalar sqrt(H) leaves the entire normalized reference joint state intact.
        scalar_joint = np.kron(np.eye(2) / 2, np.eye(2))
        np.testing.assert_allclose(scalar_joint @ joint @ scalar_joint / (1 / 4), joint)

    def test_legal_target_outside_library_and_fixed_input_gap(self):
        target, a0, a1 = out_of_library()
        for inst in (target, a0, a1):
            inst.validate_complete()
        result = common_observation_mixture({"x": target},
                                           {"a0": {"x": a0}, "a1": {"x": a1}})
        self.assertEqual(result["status"], "NUMERICAL_NO_FEASIBLE_MIXTURE")
        plus = np.ones((2, 2)) / 2
        self.assertAlmostEqual(trace_distance(target.channel(plus), a0.channel(plus)), 0.5)
        np.testing.assert_allclose(a0.channel(plus), a1.channel(plus))

    def test_adaptive_early_stop_and_actual_cost(self):
        tree, rho = early_stop()
        ref = self.assert_conditional_law(tree, rho)
        cost = independent_retry_cost(tree, rho)
        self.assertAlmostEqual(ref.acceptance_probability, 3 / 4)
        self.assertAlmostEqual(cost["action_cost_per_attempt"], 3 / 2)
        self.assertAlmostEqual(cost["all_cost_per_output"], 2)
        self.assertNotAlmostEqual(cost["all_cost_per_output"], 2 / (3 / 4))

    def test_scaled_filter_and_unknown_state_nonlinearity(self):
        h = np.diag([1 / 2, 1 / 8]).astype(complex)
        rho = np.eye(2) / 2
        inst, p = scaled_filter(h, rho, c=1 / 2)
        self.assertAlmostEqual(p, 5 / 8)
        target = inst.branch("pass", rho) / p
        np.testing.assert_allclose(target, np.diag([4 / 5, 1 / 5]))
        pure0, pure1 = np.diag([1, 0]), np.diag([0, 1])
        f0 = inst.branch("pass", pure0) / mass(inst.branch("pass", pure0))
        f1 = inst.branch("pass", pure1) / mass(inst.branch("pass", pure1))
        self.assertAlmostEqual(trace_distance(target, (f0 + f1) / 2), 3 / 10)
        scalar, _ = scaled_filter(np.eye(2) / 4, rho)
        np.testing.assert_allclose(scalar.branch("pass", rho), rho)

    def test_rare_acceptance_error_retains_failures_and_sharp_amplification(self):
        p, eps = 1 / 1000, 1 / 10000
        a = {("a",): np.array([[p]]), ("b",): np.array([[0.0]]),
             ("reject",): np.array([[1 - p]])}
        b = {("a",): np.array([[p - eps]]), ("b",): np.array([[eps]]),
             ("reject",): np.array([[1 - p]])}
        accepted = {("a",), ("b",)}
        pa, ca = normalized_accepted_law(a, accepted)
        pb, cb = normalized_accepted_law(b, accepted)
        full = cq_distance(a, b)
        self.assertAlmostEqual(full, eps)
        self.assertAlmostEqual(cq_distance(ca, cb), eps / p)
        self.assertAlmostEqual(cq_distance(ca, cb), conditional_error_bound(full, pa, pb))
        unequal = {("a",): np.array([[p]]), ("b",): np.array([[eps]]),
                   ("reject",): np.array([[1 - p - eps]])}
        q, cu = normalized_accepted_law(unequal, accepted)
        eu = cq_distance(a, unequal)
        self.assertAlmostEqual(cq_distance(ca, cu), 1 / 11)
        self.assertAlmostEqual(cq_distance(ca, cu), conditional_error_bound(eu, pa, q))
        with self.assertRaises(ValueError):
            conditional_error_bound(eps, 0, p)

    def test_changed_controller_requires_new_effect(self):
        inst = projective_record()
        old = Node(inst, {"0": Leaf(True), "1": Leaf(False)})
        new = Node(inst, {"0": Leaf(False), "1": Leaf(True)})
        self.assertGreater(np.linalg.norm(backward_effects(old, 2)[()]
                                           - backward_effects(new, 2)[()]), 1)
        rho = np.diag([3 / 4, 1 / 4])
        self.assertAlmostEqual(conditioned_reference(old, rho).acceptance_probability, 3 / 4)
        self.assertAlmostEqual(conditioned_reference(new, rho).acceptance_probability, 1 / 4)

    def test_incomplete_source_is_rejected(self):
        source = Instrument({"success": (np.eye(2) / 2,)})
        with self.assertRaises(ValueError):
            backward_effects(Node(source, {"success": Leaf(True)}), 2)


if __name__ == "__main__":
    unittest.main()
