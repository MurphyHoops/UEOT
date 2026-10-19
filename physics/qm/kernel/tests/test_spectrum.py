"""Exact spectrum examples with independently specified arithmetic oracles."""

from dataclasses import FrozenInstanceError, replace
from fractions import Fraction as F
import unittest

from ueot_qm.spectrum import (
    Orientation as O, MatterKind as M, Family, ExtraMatter, CubicCompletion,
    WeakWindow, Spectrum, inspect_spectrum, SU3Representation as R, Weyl331,
    local_331_anomalies, generalized_331_fields,
)


WINDOW = WeakWindow("declared ordinary SU(2) window", True, True, True, True)
HIGGS = ExtraMatter("H", M.COMPLEX_SCALAR, 1, F(1, 2))


def three(prefix="f"):
    return (Family(prefix + "1", O.R, O.R), Family(prefix + "2", O.R, O.RBAR),
            Family(prefix + "3", O.R, O.RBAR))


def inspect(families, *, nc=3, a=1, extras=(), completions=(), window=WINDOW):
    return inspect_spectrum(Spectrum(nc, a, families, window, extras, completions)).to_dict()


class SpectrumBridgeTests(unittest.TestCase):
    def test_actual_three_family_rows_and_higgs(self):
        result = inspect(three(), extras=(HIGGS,))
        self.assertEqual(result["status"], "SELECTOR_APPLIES")
        self.assertEqual(result["derived"]["selected_counts"], {"nc": 3, "nf": 3, "k": 1})
        self.assertEqual([r["cubic_contribution"] for r in result["rows"]],
                         ["1", "3", "1", "-3", "1", "-3", "0"])
        self.assertEqual([r["screening_contribution"] for r in result["rows"]],
                         ["1/3", "1", "1/3", "1", "1/3", "1", "1/6"])
        self.assertEqual(result["sums"]["total_cubic"], "0")
        self.assertEqual(result["sums"]["weak_b2"], "19/6")
        self.assertEqual(result["derived"]["ordinary_doublet_budget"], 12)

    def test_nonzero_anomaly_unit_may_have_either_sign(self):
        for a in (F(-7, 3), F(5, 11)):
            with self.subTest(a=a):
                result = inspect(three(), a=a)
                self.assertEqual(result["status"], "SELECTOR_APPLIES")
                self.assertEqual(result["sums"]["total_cubic"], "0")
                self.assertEqual(F(result["rows"][1]["cubic_contribution"]), 3 * a)

    def test_mixed_lepton_two_families_outside_homogeneous_contract(self):
        mixed = (Family("m1", O.R, O.R), Family("m2", O.RBAR, O.RBAR))
        result = inspect(mixed)
        self.assertEqual(result["sums"]["total_cubic"], "0")
        self.assertEqual(result["sums"]["weak_b2"], "14/3")
        self.assertEqual(result["failed_conditions"], ["homogeneous_lepton_R"])
        self.assertEqual(result["derived"]["homogeneous_integer_residual"], 2)
        self.assertIsNone(result["derived"]["selected_counts"])

    def test_six_family_replication_fails_full_weak_coefficient(self):
        result = inspect(three("a") + three("b"))
        self.assertEqual((result["nf"], result["quark_R_count"]), (6, 2))
        self.assertEqual(result["sums"]["total_cubic"], "0")
        self.assertEqual(result["sums"]["weak_b2"], "-2/3")
        self.assertEqual(result["derived"]["ordinary_doublet_budget"], 24)
        self.assertEqual(result["failed_conditions"], ["positive_full_one_loop_coefficient"])

    def test_compensated_one_family_does_not_pass_family_self_cancellation(self):
        one = (Family("one", O.R, O.RBAR),)
        extra = CubicCompletion("declared extra term", F(2), "separate mechanism obligation")
        result = inspect(one, completions=(extra,))
        self.assertEqual(result["sums"]["family_cubic"], "-2")
        self.assertEqual(result["sums"]["completion_cubic"], "2")
        self.assertEqual(result["sums"]["total_cubic"], "0")
        self.assertEqual(result["sums"]["weak_b2"], "6")
        self.assertEqual(result["failed_conditions"], ["extra_cubic_sum_zero"])

    def test_extra_weyl_compensation_and_inactive_parent_anomaly(self):
        one = (Family("one", O.R, O.RBAR),)
        compensator = ExtraMatter("extra fermion", M.WEYL, 1, F(1, 2), F(2))
        active = inspect(one, extras=(compensator,))
        self.assertEqual(active["sums"]["weak_b2"], "17/3")
        self.assertEqual(active["sums"]["total_cubic"], "0")
        inactive = inspect(one, extras=(replace(compensator, weak_active=False),))
        self.assertEqual(inactive["sums"]["weak_b2"], "6")
        self.assertEqual(inactive["sums"]["extra_matter_cubic"], "2")
        self.assertEqual(inactive["failed_conditions"], ["extra_cubic_sum_zero"])

    def test_only_combined_extra_cubic_sum_must_vanish(self):
        extras = (ExtraMatter("x", M.WEYL, 1, 0, 2), ExtraMatter("xc", M.WEYL, 1, 0, -2))
        result = inspect(three(), extras=extras)
        self.assertEqual(result["status"], "SELECTOR_APPLIES")
        self.assertEqual(result["sums"]["extra_matter_cubic"], "0")

    def test_zero_anomaly_unit_is_rejected_as_uninformative(self):
        result = inspect((Family("one", O.R, O.RBAR),), a=0)
        self.assertEqual(result["sums"]["total_cubic"], "0")
        self.assertEqual(result["sums"]["weak_b2"], "6")
        self.assertEqual(result["failed_conditions"], ["nonzero_anomaly_unit"])

    def test_wrong_quark_sign_is_detected_in_row_sum(self):
        families = tuple(Family(str(i), O.R, O.RBAR) for i in range(3))
        result = inspect(families)
        self.assertEqual(result["sums"]["family_cubic"], "-6")
        self.assertEqual(result["failed_conditions"], ["total_cubic_cancelled"])

    def test_four_families_with_nc_two_and_empty_spectrum(self):
        four = (Family("p", O.R, O.R),) + tuple(Family(str(i), O.R, O.RBAR) for i in range(3))
        result = inspect(four, nc=2)
        self.assertEqual(result["sums"]["total_cubic"], "0")
        self.assertEqual(result["sums"]["weak_b2"], "10/3")
        self.assertEqual(result["failed_conditions"], ["complex_color_template"])
        empty = inspect(())
        self.assertEqual(empty["sums"]["weak_b2"], "22/3")
        self.assertEqual(empty["failed_conditions"], ["families_nonempty"])

    def test_extra_screening_and_distinct_spin_weights(self):
        threshold = ExtraMatter("twenty doublets", M.COMPLEX_SCALAR, 20, F(1, 2))
        result = inspect(three(), extras=(threshold,))
        self.assertEqual(result["derived"]["ordinary_doublet_budget"], 12)
        self.assertEqual(result["sums"]["weak_b2"], "0")
        self.assertEqual(result["failed_conditions"], ["positive_full_one_loop_coefficient"])
        # A real adjoint is an allowed real-representation example, T(adj)=2.
        extras = (ExtraMatter("Weyl doublet", M.WEYL, 1, F(1, 2)), HIGGS,
                  ExtraMatter("real adjoint", M.REAL_SCALAR, 1, F(2)))
        result = inspect(three(), extras=extras)
        self.assertEqual(result["sums"]["extra_screening"], "5/6")
        self.assertEqual(result["sums"]["weak_b2"], "5/2")

    def test_weak_window_declarations_are_required(self):
        for field in ("su2_carrier", "perturbative", "active_spectrum_complete", "matching_established"):
            with self.subTest(field=field):
                result = inspect(three(), window=replace(WINDOW, **{field: False}))
                self.assertIn("weak_window_declared", result["failed_conditions"])
                self.assertIsNone(result["derived"]["selected_counts"])
                if field == "su2_carrier":
                    self.assertIsNone(result["sums"]["weak_b2"])

    def test_partial_threshold_activity_cannot_exclude_all_six_families(self):
        inactive_copy = tuple(replace(f, lepton_active=False, quark_active=False) for f in three("b"))
        result = inspect(three("a") + inactive_copy)
        self.assertEqual(result["sums"]["total_cubic"], "0")
        self.assertEqual(result["sums"]["weak_b2"], "10/3")
        self.assertEqual(result["derived"]["ordinary_doublet_budget"], 24)
        self.assertEqual(result["failed_conditions"], ["all_ordinary_doublets_active"])

    def test_integer_sign_scalar_and_weight_validation(self):
        for invalid in (0.5, "1/2", complex(1, 0), True):
            with self.subTest(invalid=invalid), self.assertRaises(TypeError):
                Spectrum(3, invalid, three(), WINDOW)
        for copies in (-1, F(3, 2), 1.0, True):
            with self.subTest(copies=copies), self.assertRaises((TypeError, ValueError)):
                ExtraMatter("bad", M.WEYL, copies, F(1, 2))
        with self.assertRaises(ValueError):
            ExtraMatter("negative index", M.WEYL, 1, -1)
        with self.assertRaises(ValueError):
            ExtraMatter("scalar anomaly", M.COMPLEX_SCALAR, 1, F(1, 2), 1)
        with self.assertRaises(TypeError):
            Family("bad sign", "R", O.R)
        with self.assertRaises(TypeError):
            Family("bad flag", O.R, O.R, 1, True)
        with self.assertRaises(ValueError):
            Spectrum(0, 1, three(), WINDOW)

    def test_unique_labels_and_receipt_identity(self):
        with self.assertRaises(ValueError):
            Spectrum(3, 1, (three()[0], three()[0]), WINDOW)
        with self.assertRaises(ValueError):
            CubicCompletion("x", 2, "")
        source = Spectrum(3, 1, three(), WINDOW, (HIGGS,))
        receipt = inspect_spectrum(source)
        digest = receipt.sha256
        changed = receipt.to_dict()
        changed["sums"]["weak_b2"] = "999"
        self.assertEqual(receipt.sha256, digest)
        self.assertEqual(receipt.to_dict()["sums"]["weak_b2"], "19/6")
        self.assertNotEqual(digest, inspect_spectrum(replace(source, window=replace(WINDOW, name="other"))).sha256)
        with self.assertRaises(FrozenInstanceError):
            source.nc = 4


class FullLocalAnomalyTests(unittest.TestCase):
    def test_complete_three_family_331_has_six_zero_coefficients(self):
        fields = generalized_331_fields(three(), F(0))
        result = local_331_anomalies(fields).to_dict()
        self.assertEqual(len(fields), 21)
        self.assertTrue(result["all_six_cancel"])
        self.assertEqual(result["totals"], {k: "0" for k in ("C3", "L3", "C2X", "L2X", "grav2X", "X3")})

    def test_arbitrary_exact_beta_samples_with_completion(self):
        for z in (F(-2), F(-1, 3), F(0), F(1, 5), F(5, 7)):
            with self.subTest(z=z):
                result = local_331_anomalies(generalized_331_fields(three(), z)).to_dict()
                self.assertTrue(result["all_six_cancel"])

    def test_mixed_two_family_six_anomaly_counterexample(self):
        mixed = (Family("a", O.R, O.R), Family("b", O.RBAR, O.RBAR))
        fields = generalized_331_fields(mixed, 0)
        result = local_331_anomalies(fields).to_dict()
        self.assertEqual(len(fields), 14)
        self.assertTrue(result["all_six_cancel"])
        self.assertEqual(inspect(mixed)["failed_conditions"], ["homogeneous_lepton_R"])

    def test_replicated_six_family_local_anomalies_cancel(self):
        families = three("a") + three("b")
        result = local_331_anomalies(generalized_331_fields(families, 0)).to_dict()
        self.assertTrue(result["all_six_cancel"])
        self.assertEqual(inspect(families)["sums"]["weak_b2"], "-2/3")

    def test_missing_exotic_lepton_completion_produces_exact_residue(self):
        for z, grav, cubic in ((F(0), "-3/2", "-3/8"), (F(1, 5), "-12/5", "-192/125")):
            with self.subTest(z=z):
                result = local_331_anomalies(generalized_331_fields(
                    three(), z, include_exotic_lepton_completion=False)).to_dict()
                self.assertFalse(result["all_six_cancel"])
                self.assertEqual(result["totals"]["grav2X"], grav)
                self.assertEqual(result["totals"]["X3"], cubic)
                for name in ("C3", "L3", "C2X", "L2X"):
                    self.assertEqual(result["totals"][name], "0")

    def test_neutral_rhn_special_point_does_not_hide_generic_failure(self):
        result = local_331_anomalies(generalized_331_fields(
            three(), -F(1, 3), include_exotic_lepton_completion=False)).to_dict()
        self.assertTrue(result["all_six_cancel"])

    def test_conjugation_charge_and_multiplicity_failure_controls(self):
        fields = list(generalized_331_fields(three(), 0))
        uc = next(i for i, field in enumerate(fields) if field.name == "f1/uc")
        wrong_color = fields.copy()
        wrong_color[uc] = replace(wrong_color[uc], color=R.FUNDAMENTAL)
        self.assertEqual(local_331_anomalies(wrong_color).to_dict()["totals"]["C3"], "2")
        ec = next(i for i, field in enumerate(fields) if field.name == "f1/Ec")
        wrong_charge = fields.copy()
        wrong_charge[ec] = replace(wrong_charge[ec], x=-F(1, 2))
        result = local_331_anomalies(wrong_charge).to_dict()
        self.assertEqual(result["totals"]["grav2X"], "-1")
        self.assertEqual(result["totals"]["X3"], "-1/4")
        wrong_weight = fields.copy()
        wrong_weight[ec] = replace(wrong_weight[ec], copies=2)
        result = local_331_anomalies(wrong_weight).to_dict()
        self.assertEqual(result["totals"]["grav2X"], "1/2")
        self.assertEqual(result["totals"]["X3"], "1/8")
        with self.assertRaises(TypeError):
            Weyl331("bad", R.SINGLET, R.SINGLET, F(1), F(3, 2))
        with self.assertRaises(TypeError):
            generalized_331_fields(three(), 0.1)
        with self.assertRaises(ValueError):
            local_331_anomalies((fields[0], fields[0]))


if __name__ == "__main__":
    unittest.main()
