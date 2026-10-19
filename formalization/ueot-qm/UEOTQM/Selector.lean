import Mathlib.Tactic

/-!
# Conditional family-count selection

This module contains integer theorems.  The anomaly equation and weak screening
budget are explicit hypotheses.  It does not construct a horizontal gauge
parent, select its representations, establish a weak effective-theory window,
or certify a complete quantum field theory.

The selection theorem has no primitive-packet or minimality hypothesis.
Counterexamples below record the roles of the remaining arithmetic premises.
-/

namespace UEOTQM.Selector

/-- The screening bound gives a complete finite search domain. -/
theorem selector_finite_bounds
    (nc nf : ℕ)
    (hcolor : 3 ≤ nc)
    (hfamilies : 0 < nf)
    (hweak : nf * (nc + 1) < 22) :
    nc ≤ 20 ∧ nf ≤ 5 := by
  have hnf_one : 1 ≤ nf := by omega
  have hnc_screen : nc + 1 ≤ nf * (nc + 1) := by
    simpa only [one_mul] using
      (Nat.mul_le_mul_right (nc + 1) hnf_one)
  have hfour : 4 ≤ nc + 1 := by omega
  have hnf_screen : nf * 4 ≤ nf * (nc + 1) :=
    Nat.mul_le_mul_left nf hfour
  constructor <;> omega

set_option maxHeartbeats 800000 in
/--
The declared homogeneous-lepton anomaly equation and weak budget select three
colors and three families.  This is an arithmetic implication with explicit
sector inputs, not a derivation of those physical inputs.
-/
theorem selects_three_without_atomicity
    (nc nf k : ℕ)
    (hcolor : 3 ≤ nc)
    (hfamilies : 0 < nf)
    (hquarks : k ≤ nf)
    (hanomaly : 2 * nc * k + nf = nc * nf)
    (hweak : nf * (nc + 1) < 22) :
    nc = 3 ∧ nf = 3 ∧ k = 1 := by
  obtain ⟨hnc_upper, hnf_upper⟩ :=
    selector_finite_bounds nc nf hcolor hfamilies hweak
  interval_cases nc <;> interval_cases nf <;> omega

/-- Without the complex-color lower bound, the arithmetic admits (2, 4, 1). -/
theorem dropping_color_bound_admits_four_families :
    ∃ nc nf k : ℕ,
      0 < nf ∧ k ≤ nf ∧
      2 * nc * k + nf = nc * nf ∧
      nf * (nc + 1) < 22 ∧ nc ≠ 3 ∧ nf ≠ 3 := by
  refine ⟨2, 4, 1, ?_⟩
  norm_num

/-- A duplicated three-family packet still cancels the cubic anomaly. -/
theorem dropping_weak_budget_admits_six_families :
    ∃ nc nf k : ℕ,
      3 ≤ nc ∧ 0 < nf ∧ k ≤ nf ∧
      2 * nc * k + nf = nc * nf ∧
      22 ≤ nf * (nc + 1) ∧ nf ≠ 3 := by
  refine ⟨3, 6, 2, ?_⟩
  norm_num

/-- The weak budget alone permits a one-family count with nonzero anomaly. -/
theorem dropping_cubic_equation_admits_one_family :
    ∃ nc nf k : ℕ,
      3 ≤ nc ∧ 0 < nf ∧ k ≤ nf ∧
      nf * (nc + 1) < 22 ∧
      2 * nc * k + nf ≠ nc * nf ∧ nf ≠ 3 := by
  refine ⟨3, 1, 0, ?_⟩
  norm_num

/-- A nonempty-family hypothesis excludes the otherwise allowed empty spectrum. -/
theorem dropping_nonempty_family_count_admits_empty_spectrum :
    ∃ nc nf k : ℕ,
      3 ≤ nc ∧ k ≤ nf ∧
      2 * nc * k + nf = nc * nf ∧
      nf * (nc + 1) < 22 ∧ nc ≠ 3 ∧ nf = 0 := by
  refine ⟨4, 0, 0, ?_⟩
  norm_num

/--
With both lepton orientations allowed, the all-positive natural-number form of
the cubic constraint is `2 * ell + 2 * nc * k = (nc + 1) * nf`.
Choosing every lepton in the same orientation recovers the selector equation.
-/
theorem homogeneous_leptons_recover_cubic_equation (nc nf k : ℕ) :
    (2 * nf + 2 * nc * k = (nc + 1) * nf) ↔
      (2 * nc * k + nf = nc * nf) := by
  simp only [Nat.add_mul, Nat.one_mul]
  omega

/--
The wider lepton template admits a two-family arithmetic witness.  This proves
only the displayed mixed cubic constraint and screening budget, not other
anomaly, vacuum, or phenomenological conditions on a physical spectrum.
-/
theorem mixed_lepton_template_admits_two_families :
    ∃ nc nf ell k : ℕ,
      3 ≤ nc ∧ 0 < nf ∧ ell ≤ nf ∧ k ≤ nf ∧
      2 * ell + 2 * nc * k = (nc + 1) * nf ∧
      nf * (nc + 1) < 22 ∧
      2 * nc * k + nf ≠ nc * nf ∧ nf ≠ 3 := by
  refine ⟨3, 2, 1, 1, ?_⟩
  norm_num

/-- Cubic anomaly cancellation is preserved by multiplying the whole packet. -/
theorem cubic_cancellation_replicates
    (nc nf k copies : ℕ)
    (hanomaly : 2 * nc * k + nf = nc * nf) :
    2 * nc * (copies * k) + copies * nf = nc * (copies * nf) := by
  calc
    2 * nc * (copies * k) + copies * nf =
        copies * (2 * nc * k + nf) := by ring
    _ = copies * (nc * nf) := by rw [hanomaly]
    _ = nc * (copies * nf) := by ring

/-- The same replication multiplies the weak screening budget. -/
theorem replicated_weak_screening (nc nf copies : ℕ) :
    (copies * nf) * (nc + 1) = copies * (nf * (nc + 1)) := by
  ring

/-- At least two copies of the three-family packet violate the stated budget. -/
theorem two_or_more_three_family_packets_fail_weak_budget
    (copies : ℕ) (hcopies : 2 ≤ copies) :
    ¬ ((copies * 3) * (3 + 1) < 22) := by
  omega

end UEOTQM.Selector
