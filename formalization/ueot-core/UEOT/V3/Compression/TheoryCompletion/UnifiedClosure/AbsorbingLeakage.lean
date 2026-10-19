import UEOT.V3.FiniteDiscountedApproxQuotient
import UEOT.V3.FiniteRecurrentDecompositionStability
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Absorbing leakage: finite local risk does not imply all-times safety

`false` is safe and `true` is failed. From the safe state the next state fails
with probability `epsilon`; the failed state is absorbing. The initial law
is the point mass at the safe state, and every later law is an actual PMF bind
through this kernel. In particular, the survival recurrence is proved from
the PMF transition, rather than supplied as an assumption.

For `0 <= epsilon <= 1`, the failure probability after `n` transitions is
`1 - (1 - epsilon)^n`. For fixed strictly positive epsilon it tends to one.
Every transition row is within canonical total variation `epsilon` of the
ideal identity kernel; this premise is proved using the registered finite
PMF TV identity, with equality at the safe row.
This is a finite-state mathematical counterexample, not empirical evidence
for a particular physical system or an autopoiesis mechanism.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.AbsorbingLeakage

open Filter Topology
open scoped BigOperators ENNReal
open UEOT.V3.FiniteDiscountedControl

noncomputable section

/-- The genuine stochastic row: failure is absorbing. -/
def transitionMass (epsilon : ℝ) : Bool → Bool → ℝ
  | false, false => 1 - epsilon
  | false, true => epsilon
  | true, false => 0
  | true, true => 1

theorem transitionMass_nonneg (epsilon : ℝ)
    (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) (x y : Bool) :
    0 ≤ transitionMass epsilon x y := by
  cases x <;> cases y <;> simp only [transitionMass]
  · exact sub_nonneg.mpr hone
  · exact hzero
  · norm_num
  · norm_num

theorem transitionMass_sum (epsilon : ℝ) (x : Bool) :
    (∑ y, transitionMass epsilon x y) = 1 := by
  cases x <;> simp [transitionMass]

/-- Rows are normalized PMFs, not merely real-valued recurrence data. -/
def kernel (epsilon : ℝ) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1)
    (x : Bool) : PMF Bool :=
  FiniteProbabilityRow.ofRealRow (transitionMass epsilon x)
    (transitionMass_nonneg epsilon hzero hone x)
    (transitionMass_sum epsilon x)

@[simp] theorem kernel_mass (epsilon : ℝ)
    (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) (x y : Bool) :
    ((kernel epsilon hzero hone x) y).toReal =
      transitionMass epsilon x y := by
  simp [kernel]

theorem failed_absorbing (epsilon : ℝ)
    (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    kernel epsilon hzero hone true = PMF.pure true := by
  apply PMF.ext
  intro y
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top (kernel epsilon hzero hone true) y)
    (PMF.apply_ne_top (PMF.pure true) y)).mp
  cases y <;> simp [transitionMass]

/-- The ideal comparison preserves each state with probability one. -/
def idealKernel (x : Bool) : PMF Bool := PMF.pure x

/-- Exact canonical row TV: the safe row differs by epsilon, the failed row
is unchanged. The half-L1 identity is reused from the registered source. -/
theorem row_tv_eq (epsilon : ℝ)
    (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) (x : Bool) :
    FiniteProbabilityRow.tvDist (idealKernel x) (kernel epsilon hzero hone x) =
      if x then 0 else epsilon := by
  let _ : MeasurableSpace Bool := ⊤
  unfold FiniteProbabilityRow.tvDist
  rw [UEOT.V3.FiniteRecurrentDecompositionStability.pmf_tv_eq_half_sum_abs]
  cases x <;>
    simp [idealKernel, transitionMass, abs_of_nonneg hzero]
  ring

/-- The negative example satisfies the genuine one-step TV error premise. -/
theorem row_tv_le (epsilon : ℝ)
    (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) (x : Bool) :
    FiniteProbabilityRow.tvDist (idealKernel x) (kernel epsilon hzero hone x) ≤
      epsilon := by
  rw [row_tv_eq]
  cases x <;> simp [hzero]

/-- Distribution after exactly `n` transitions, initially surely safe. -/
def law (epsilon : ℝ) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    ℕ → PMF Bool
  | 0 => PMF.pure false
  | n + 1 => (law epsilon hzero hone n).bind (kernel epsilon hzero hone)

@[simp] theorem law_zero (epsilon : ℝ)
    (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    law epsilon hzero hone 0 = PMF.pure false := rfl

/-- Expand the actual PMF bind into its two real-valued mass contributions. -/
theorem bind_mass (epsilon : ℝ)
    (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1)
    (p : PMF Bool) (y : Bool) :
    ((p.bind (kernel epsilon hzero hone)) y).toReal =
      (p false).toReal * transitionMass epsilon false y +
        (p true).toReal * transitionMass epsilon true y := by
  rw [PMF.bind_apply, tsum_fintype]
  rw [ENNReal.toReal_sum (by
    intro x _
    exact ENNReal.mul_ne_top (PMF.apply_ne_top p x)
      (PMF.apply_ne_top (kernel epsilon hzero hone x) y))]
  simp_rw [ENNReal.toReal_mul, kernel_mass]
  rw [Fintype.sum_bool]
  ring

/-- This recurrence is a consequence of the normalized PMF transition. -/
theorem safe_mass_succ (epsilon : ℝ)
    (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) (n : ℕ) :
    ((law epsilon hzero hone (n + 1)) false).toReal =
      ((law epsilon hzero hone n) false).toReal * (1 - epsilon) := by
  change (((law epsilon hzero hone n).bind
    (kernel epsilon hzero hone)) false).toReal = _
  rw [bind_mass]
  simp [transitionMass]

theorem failure_mass_succ (epsilon : ℝ)
    (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) (n : ℕ) :
    ((law epsilon hzero hone (n + 1)) true).toReal =
      ((law epsilon hzero hone n) false).toReal * epsilon +
        ((law epsilon hzero hone n) true).toReal := by
  change (((law epsilon hzero hone n).bind
    (kernel epsilon hzero hone)) true).toReal = _
  rw [bind_mass]
  simp [transitionMass]

/-- Exact finite-horizon survival probability. -/
theorem safe_mass_closed (epsilon : ℝ)
    (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) (n : ℕ) :
    ((law epsilon hzero hone n) false).toReal = (1 - epsilon) ^ n := by
  induction n with
  | zero => simp [law]
  | succ n ih => rw [safe_mass_succ, ih, pow_succ]

/-- Exact finite-horizon failure probability of the absorbing PMF process. -/
theorem failure_mass_closed (epsilon : ℝ)
    (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) (n : ℕ) :
    ((law epsilon hzero hone n) true).toReal =
      1 - (1 - epsilon) ^ n := by
  induction n with
  | zero => simp [law]
  | succ n ih =>
      rw [failure_mass_succ, safe_mass_closed, ih, pow_succ]
      ring

theorem one_step_failure (epsilon : ℝ)
    (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    ((law epsilon hzero hone 1) true).toReal = epsilon := by
  rw [failure_mass_closed]
  ring

/-- Any fixed positive local leakage defeats a probability-one guarantee
at every time, despite the surely safe initial state. -/
theorem positive_leakage_not_all_times_safe (epsilon : ℝ)
    (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) (hpos : 0 < epsilon) :
    ¬ (∀ n : ℕ, ((law epsilon hzero hone n) false).toReal = 1) := by
  intro hsafe
  have h := hsafe 1
  rw [safe_mass_closed] at h
  norm_num at h
  linarith

/-- Repeated fixed positive leakage accumulates to failure probability one. -/
theorem failure_mass_tendsto_one (epsilon : ℝ)
    (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) (hpos : 0 < epsilon) :
    Tendsto (fun n : ℕ => ((law epsilon hzero hone n) true).toReal)
      atTop (𝓝 1) := by
  have hpow : Tendsto (fun n : ℕ => (1 - epsilon) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr hone) (by linarith)
  have hsub : Tendsto (fun n : ℕ => (1 : ℝ) - (1 - epsilon) ^ n)
      atTop (𝓝 ((1 : ℝ) - 0)) :=
    tendsto_const_nhds.sub hpow
  simpa only [failure_mass_closed, sub_zero] using hsub

/-- A single actual PMF model simultaneously has a safe initial state, the
specified local TV bound, and cumulative failure tending to one. -/
theorem bounded_row_error_with_asymptotic_failure (epsilon : ℝ)
    (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) (hpos : 0 < epsilon) :
    (∀ x : Bool,
      FiniteProbabilityRow.tvDist (idealKernel x) (kernel epsilon hzero hone x) ≤
        epsilon) ∧
      law epsilon hzero hone 0 = PMF.pure false ∧
      Tendsto (fun n : ℕ => ((law epsilon hzero hone n) true).toReal)
        atTop (𝓝 1) := by
  exact ⟨row_tv_le epsilon hzero hone, law_zero epsilon hzero hone,
    failure_mass_tendsto_one epsilon hzero hone hpos⟩

end

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.AbsorbingLeakage
