import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RowwiseProbeSampling
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Registered finite-data numerical budgets

These are exact real inequalities for the registered consumer. The source/path
consumer supplies the semantic link to these scalar quantities; no data have
been sampled here and no occurrence of the calibration event is presumed.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataNumericalBounds

open scoped BigOperators
open Filter

noncomputable section

/-- The registered four scalar probes, with their allocation fixed before data. -/
def registeredScalarBudget : ℝ :=
  RowwiseProbeSampling.scalarBudget (J := Fin 4) (fun _ => 262144) (1 / 250)

theorem registeredScalarBudget_eq :
    registeredScalarBudget = 8 * Real.exp (-(131072 / 15625 : ℝ)) := by
  norm_num [registeredScalarBudget, RowwiseProbeSampling.scalarBudget, Fin.sum_univ_succ]
  ring

theorem registeredScalarBudget_lt : registeredScalarBudget < (1 / 300 : ℝ) := by
  have he : (8 / 3 : ℝ) ≤ Real.exp 1 := by
    have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num) 4
    norm_num [Finset.sum_range_succ] at h ⊢
    linarith
  have hp := pow_le_pow_left₀ (show (0 : ℝ) ≤ 8 / 3 by norm_num) he 8
  have hbig : (2400 : ℝ) < Real.exp 8 := by
    have heq : Real.exp 8 = (Real.exp 1) ^ 8 := by
      simp
    rw [heq]
    exact lt_of_lt_of_le (by norm_num) hp
  rw [registeredScalarBudget_eq, Real.exp_neg]
  have hmono : Real.exp 8 ≤ Real.exp (131072 / 15625 : ℝ) :=
    Real.exp_le_exp.mpr (by norm_num)
  have hinv : (Real.exp (131072 / 15625 : ℝ))⁻¹ < (1 / 2400 : ℝ) := by
    rw [inv_eq_one_div]
    exact one_div_lt_one_div_of_lt (by norm_num) (hbig.trans_le hmono)
  linarith

/-- Three registered records spend the confidence budget only once per record. -/
theorem three_record_calibration : 3 * (1 / 300 : ℝ) = 1 / 100 := by norm_num

theorem accepted_joint_risk :
    (1 / 300 : ℝ) + (1 - 1 / 300) * (1 / 5) = 76 / 375 := by norm_num

/-- The raw structural route includes the one actual preparation operation. -/
def prepBudget (T : ℕ) (e s : ℝ) : ℝ :=
  (T + 1 : ℕ) * e + (T + 1 : ℕ) * (1 / 250 : ℝ) +
    (T : ℝ) * (1 / 250 : ℝ) / s

/-- On Good, low true noise gives this worst empirical noise. -/
theorem low_noise_empirical_upper {e eh : ℝ}
    (he : e ≤ 1 / 200) (hgood : |eh - e| ≤ 1 / 250) :
    eh ≤ (1 / 200 : ℝ) + 1 / 250 := by
  have := (abs_le.mp hgood).2
  linarith

/-- The two risk probes retain a positive empirical denominator on Good. -/
theorem empirical_denominator_lower {r0 r1 rh0 rh1 : ℝ}
    (h0 : 2 / 3 ≤ r0) (h1 : 1 / 6 ≤ r1)
    (hg0 : |rh0 - r0| ≤ 1 / 250) (hg1 : |rh1 - r1| ≤ 1 / 250) :
    (5 / 6 : ℝ) - 2 / 250 ≤ rh0 + rh1 := by
  have hgood0 := (abs_le.mp hg0).1
  have hgood1 := (abs_le.mp hg1).1
  linarith

/-- Whole-box arithmetic margin; this is stronger than a zero-noise point. -/
theorem low_noise_budget_ten {e s : ℝ}
    (he : e ≤ (1 / 200 : ℝ) + 1 / 250)
    (hs : (5 / 6 : ℝ) - 2 / 250 ≤ s) : prepBudget 10 e s < 1 / 5 := by
  have hspos : 0 < s := by linarith
  have hdiv : (10 : ℝ) * (1 / 250) / s ≤
      10 * (1 / 250) / ((5 / 6 : ℝ) - 2 / 250) := by
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
  norm_num [prepBudget] at *
  linarith

theorem low_noise_budget_two {e s : ℝ}
    (he : e ≤ (1 / 200 : ℝ) + 1 / 250)
    (hs : (5 / 6 : ℝ) - 2 / 250 ≤ s) : prepBudget 2 e s < 1 / 5 := by
  have hdiv : (2 : ℝ) * (1 / 250) / s ≤
      2 * (1 / 250) / ((5 / 6 : ℝ) - 2 / 250) := by
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
  norm_num [prepBudget] at *
  linarith

/-- Rank-one normalization amplifies a common scalar radius by only the
empirical denominator. The true denominator cancels from the numerator. -/
theorem normalized_tilt_error {r0 r1 rh0 rh1 d : ℝ}
    (hr0 : 0 ≤ r0) (hr1 : 0 ≤ r1) (hs : 0 < r0 + r1)
    (hshat : 0 < rh0 + rh1)
    (hg0 : |rh0 - r0| ≤ d) (hg1 : |rh1 - r1| ≤ d) :
    |r0 / (r0 + r1) - rh0 / (rh0 + rh1)| ≤ d / (rh0 + rh1) := by
  have h0 := abs_le.mp hg0
  have h1 := abs_le.mp hg1
  have hnum : |r0 * rh1 - r1 * rh0| ≤ (r0 + r1) * d := by
    apply abs_le.mpr
    constructor
    · nlinarith [mul_nonneg hr0 (sub_nonneg.mpr h1.1),
        mul_nonneg hr1 (sub_nonneg.mpr h0.2)]
    · nlinarith [mul_nonneg hr0 (sub_nonneg.mpr h1.2),
        mul_nonneg hr1 (sub_nonneg.mpr h0.1)]
  have hid : r0 / (r0 + r1) - rh0 / (rh0 + rh1) =
      (r0 * rh1 - r1 * rh0) / ((r0 + r1) * (rh0 + rh1)) := by
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos (mul_pos hs hshat)]
  calc
    |r0 * rh1 - r1 * rh0| / ((r0 + r1) * (rh0 + rh1)) ≤
        ((r0 + r1) * d) / ((r0 + r1) * (rh0 + rh1)) :=
      div_le_div_of_nonneg_right hnum (mul_pos hs hshat).le
    _ = d / (rh0 + rh1) := by field_simp

/-- High-noise data on Good retain at least 0.042 after both radii. -/
theorem high_noise_lower {eh : ℝ}
    (hgood : |eh - (1 / 20 : ℝ)| ≤ 1 / 250) :
    (21 / 500 : ℝ) ≤ max 0 (eh - 1 / 250) := by
  have h := (abs_le.mp hgood).1
  exact le_trans (by linarith) (le_max_right _ _)

/-- Exact known high-noise obstruction at the target-window length. -/
theorem high_noise_ten : (1 / 5 : ℝ) < 1 - (19 / 20 : ℝ) ^ 10 := by norm_num

/-- Exact data-derived floor is already enough for statistical rejection. -/
theorem empirical_floor_ten : (1 / 5 : ℝ) < 1 - (1 - 21 / 500 : ℝ) ^ 10 := by
  norm_num

/-- The same positive low-noise point eventually violates the same threshold. -/
theorem low_noise_forty_five : (1 / 5 : ℝ) < 1 - (199 / 200 : ℝ) ^ 45 := by
  norm_num

/-- The selector's statistical lower bound is read only from the two noise counts. -/
def dataFailureFloor (eh0 eh1 : ℝ) : ℝ :=
  min (1 / 6) (min (max 0 (eh0 - 1 / 250)) (max 0 (eh1 - 1 / 250)))

/-- The full high-noise registered branch is rejected on the same Good event. -/
theorem high_noise_data_reject {eh0 eh1 : ℝ}
    (hg0 : |eh0 - (1 / 20 : ℝ)| ≤ 1 / 250)
    (hg1 : |eh1 - (1 / 20 : ℝ)| ≤ 1 / 250) :
    (1 / 5 : ℝ) < 1 - (1 - dataFailureFloor eh0 eh1) ^ 10 := by
  have hlower : (21 / 500 : ℝ) ≤ dataFailureFloor eh0 eh1 := by
    exact le_min (by norm_num) (le_min (high_noise_lower hg0) (high_noise_lower hg1))
  have hupper : dataFailureFloor eh0 eh1 ≤ (1 / 6 : ℝ) := min_le_left _ _
  have hp : (1 - dataFailureFloor eh0 eh1) ^ 10 ≤ (1 - 21 / 500 : ℝ) ^ 10 := by
    exact pow_le_pow_left₀ (by linarith) (by linarith) 10
  linarith [empirical_floor_ten]

/-- This theorem discharges the accepted low-noise interval directly from
all four simultaneous probe errors; no true parameters enter the selector. -/
theorem low_noise_good_accepts {r0 r1 e0 e1 rh0 rh1 eh0 eh1 : ℝ}
    (hr0 : 2 / 3 ≤ r0) (hr1 : 1 / 6 ≤ r1)
    (he0 : e0 ≤ 1 / 200) (he1 : e1 ≤ 1 / 200)
    (hg0 : |rh0 - r0| ≤ 1 / 250) (hg1 : |rh1 - r1| ≤ 1 / 250)
    (hg2 : |eh0 - e0| ≤ 1 / 250) (hg3 : |eh1 - e1| ≤ 1 / 250) :
    prepBudget 2 (max eh0 eh1) (rh0 + rh1) < 1 / 5 ∧
      prepBudget 10 (max eh0 eh1) (rh0 + rh1) < 1 / 5 := by
  have he : max eh0 eh1 ≤ (1 / 200 : ℝ) + 1 / 250 :=
    max_le (low_noise_empirical_upper he0 hg2) (low_noise_empirical_upper he1 hg3)
  have hs := empirical_denominator_lower hr0 hr1 hg0 hg1
  exact ⟨low_noise_budget_two he hs, low_noise_budget_ten he hs⟩

/-- The unprepared initial tilt gap for every risk parameter in the box. -/
theorem uniform_initial_tilt_gap {r0 r1 : ℝ}
    (h0 : 2 / 3 ≤ r0) (h1 : 0 ≤ r1) (h1upper : r1 ≤ 1 / 3) :
    (1 / 6 : ℝ) ≤ |r0 / (r0 + r1) - 1 / 2| := by
  have hs : 0 < r0 + r1 := by linarith
  have hfrac : (2 / 3 : ℝ) ≤ r0 / (r0 + r1) := by
    apply (le_div_iff₀ hs).mpr
    nlinarith
  exact le_trans (by linarith) (le_abs_self _)

theorem main_initial_tilt_gap :
    |(3 / 4 : ℝ) / (3 / 4 + 1 / 4) - 1 / 2| = 1 / 4 := by norm_num

/-- A per-step survival contraction gives the geometric upper bound.
The actual source consumer must prove its recurrence from all allowed actions. -/
theorem survival_le_geometric (survival : ℕ → ℝ) (l : ℝ)
    (hl : l ≤ 1) (hinit : survival 0 ≤ 1)
    (hstep : ∀ n, survival (n + 1) ≤ (1 - l) * survival n) :
    ∀ n, survival n ≤ (1 - l) ^ n := by
  intro n
  induction n with
  | zero => simpa using hinit
  | succ n ih =>
      calc
        survival (n + 1) ≤ (1 - l) * survival n := hstep n
        _ ≤ (1 - l) * (1 - l) ^ n :=
          mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hl)
        _ = (1 - l) ^ (n + 1) := by ring

/-- The same uniform positive floor rules out positive infinite survival. -/
theorem survival_tendsto_zero (survival : ℕ → ℝ) (l : ℝ)
    (hlpos : 0 < l) (hl : l ≤ 1)
    (hzero : ∀ n, 0 ≤ survival n) (hinit : survival 0 ≤ 1)
    (hstep : ∀ n, survival (n + 1) ≤ (1 - l) * survival n) :
    Tendsto survival atTop (nhds 0) := by
  apply squeeze_zero hzero (survival_le_geometric survival l hl hinit hstep)
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr hl) (by linarith)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataNumericalBounds
