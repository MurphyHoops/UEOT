import UEOT.V3.Compression.Objecthood.StationaryCausalPathLawBridge
import UEOT.V3.CompactCausalOptimalityCore
import UEOT.V3.FiniteDiscountedControl
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Track O / GCR1 — absorbed normalized discounted repair model

This stage supplies the exact discounted tool used later by GCR2--GCR4 without
mistaking discounted control for an undiscounted reachability theorem.

The target set is made absorbing.  Outside the target the source PMF is left
literally unchanged; inside the target it becomes a Dirac self-loop.  The stage
reward is normalized to `(1 - beta) * 1_K`, so an absorbed path that first hits
`K` at time `tau` has total infinite discounted target occupation `beta^tau`.
That path-law identity is intentionally deferred to GCR2.
-/

namespace UEOT.V3.Compression.Objecthood

open Set Finset MeasureTheory ProbabilityTheory
open UEOT.V3.ReflexiveStateAugmentation
open UEOT.V3.CompactCausalOptimalityCore
open UEOT.V3.ViabilityTrajectory
open scoped ENNReal ProbabilityTheory

universe uX uA
noncomputable section

/-- Absorb the repair target without changing any transition before first hit. -/
noncomputable def absorbedRepairPMF
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    (P : X → A → PMF X) (K : Set X) : X → A → PMF X := by
  classical
  exact fun x a => if x ∈ K then PMF.pure x else P x a

@[simp] theorem absorbedRepairPMF_of_mem
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    (P : X → A → PMF X) (K : Set X) {x : X} (hx : x ∈ K) (a : A) :
    absorbedRepairPMF P K x a = PMF.pure x := by
  simp [absorbedRepairPMF, hx]

@[simp] theorem absorbedRepairPMF_of_not_mem
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    (P : X → A → PMF X) (K : Set X) {x : X} (hx : x ∉ K) (a : A) :
    absorbedRepairPMF P K x a = P x a := by
  simp [absorbedRepairPMF, hx]

/-- The controlled kernel is exactly the source controlled kernel at every
pre-hit state.  This is the local semantic fact from which GCR2 derives exact
first-hitting-law preservation. -/
theorem pmfControlledKernel_absorbedRepair_of_not_mem
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (P : X → A → PMF X) (K : Set X) {x : X} (hx : x ∉ K) (a : A) :
    pmfControlledKernel (absorbedRepairPMF P K) (x, a) =
      pmfControlledKernel P (x, a) := by
  change (absorbedRepairPMF P K x a).toMeasure = (P x a).toMeasure
  rw [absorbedRepairPMF_of_not_mem P K hx a]

/-- In the exact complete-history semantics, every physical next-state kernel is
unchanged as long as the current state has not yet hit the target. -/
theorem controlledNext_absorbedRepair_of_current_not_mem
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (P : X → A → PMF X) (K : Set X) (n : ℕ)
    (h : UEOT.V3.FiniteHistory.HistoryFiber X A n)
    (hx : currentFiber n h ∉ K) (a : A) :
    controlledNext n (pmfControlledKernel (absorbedRepairPMF P K)) (h, a) =
      controlledNext n (pmfControlledKernel P) (h, a) := by
  unfold controlledNext
  rw [Kernel.comap_apply, Kernel.comap_apply]
  exact pmfControlledKernel_absorbedRepair_of_not_mem P K hx a

/-- At a target state every action induces the same absorbing Dirac transition. -/
theorem pmfControlledKernel_absorbedRepair_of_mem
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (P : X → A → PMF X) (K : Set X) {x : X} (hx : x ∈ K) (a : A) :
    pmfControlledKernel (absorbedRepairPMF P K) (x, a) = Measure.dirac x := by
  change (absorbedRepairPMF P K x a).toMeasure = Measure.dirac x
  rw [absorbedRepairPMF_of_mem P K hx a, PMF.toMeasure_pure]

/-- Finite Bellman model used only to synthesize an exact deterministic greedy
selector for the normalized absorbed repair objective. -/
noncomputable def finiteNormalizedRepairModel
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    (P : X → A → PMF X) (K : Set X)
    (beta : ℝ) (hbeta0 : 0 < beta) (hbeta1 : beta < 1) :
    UEOT.V3.FiniteDiscountedControl.Model X (fun _ : X => A) := by
  classical
  exact {
    transition := fun x a y => ((absorbedRepairPMF P K x a) y).toReal
    reward := fun x _ => if x ∈ K then 1 - beta else 0
    rewardBound := 1
    discount := beta
    transition_nonneg := fun _ _ _ => ENNReal.toReal_nonneg
    transition_sum_one := by
      intro x a
      have h := congrArg ENNReal.toReal (PMF.tsum_coe (absorbedRepairPMF P K x a))
      rw [tsum_fintype, ENNReal.toReal_sum
        (fun y _ => PMF.apply_ne_top (absorbedRepairPMF P K x a) y)] at h
      simpa using h
    reward_abs_le := by
      intro x a
      by_cases hx : x ∈ K
      · simp [hx, abs_of_nonneg (sub_nonneg.mpr hbeta1.le)]
        linarith
      · simp [hx]
    discount_pos := hbeta0
    discount_lt_one := hbeta1 }

/-- Kernel-valued complete-history model consumed by the existing all-causal
verification layer.  No compact/Feller assumption is added. -/
noncomputable def causalNormalizedRepairModel
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (P : X → A → PMF X) (K : Set X)
    (beta : ℝ) (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) :
    UEOT.V3.CompactCausalOptimalityCore.Model X A := by
  classical
  exact {
    transition := pmfControlledKernel (absorbedRepairPMF P K)
    transition_markov := pmfControlledKernel_isMarkov (absorbedRepairPMF P K)
    reward := fun x _ => if x ∈ K then 1 - beta else 0
    reward_measurable := measurable_of_finite _
    rewardBound := 1
    rewardBound_nonneg := by norm_num
    reward_abs_le := by
      intro x a
      by_cases hx : x ∈ K
      · simp [hx, abs_of_nonneg (sub_nonneg.mpr hbeta1.le)]
        linarith
      · simp [hx]
    discount := beta
    discount_nonneg := hbeta0
    discount_lt_one := hbeta1 }

private theorem integral_absorbedRepair_eq_sum
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (P : X → A → PMF X) (K : Set X) (V : X → ℝ) (x : X) (a : A) :
    (∫ y, V y ∂(pmfControlledKernel (absorbedRepairPMF P K)) (x, a)) =
      ∑ y, ((absorbedRepairPMF P K x a) y).toReal * V y := by
  change (∫ y, V y ∂(absorbedRepairPMF P K x a).toMeasure) = _
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul]

/-- Finite PMF Bellman data induces a genuine greedy certificate for the exact
kernel-valued complete-history model. -/
noncomputable def normalizedRepairGreedyCertificate
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (P : X → A → PMF X) (K : Set X)
    (beta : ℝ) (hbeta0 : 0 < beta) (hbeta1 : beta < 1) :
    UEOT.V3.CompactCausalOptimalityCore.Model.GreedyCertificate
      (causalNormalizedRepairModel P K beta hbeta0.le hbeta1) := by
  classical
  let F := finiteNormalizedRepairModel P K beta hbeta0 hbeta1
  let M := causalNormalizedRepairModel P K beta hbeta0.le hbeta1
  let V := F.optimalValue
  let g : X → A := fun x => F.greedyAction x
  refine {
    value := V
    value_measurable := measurable_of_finite _
    valueBound := ∑ x, |V x|
    valueBound_nonneg := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    value_abs_le := ?_
    action_le := ?_
    selector := g
    selector_measurable := measurable_of_finite _
    action_eq := ?_ }
  · intro x
    simpa using
      (Finset.single_le_sum (s := Finset.univ) (f := fun y : X => |V y|)
        (fun y _ => abs_nonneg (V y)) (Finset.mem_univ x))
  · intro x a
    have hq := F.qValue_optimal_le x a
    change M.reward x a + M.discount * (∫ y, V y ∂M.transition (x, a)) ≤ V x
    change (if x ∈ K then 1 - beta else 0) + beta *
      (∫ y, V y ∂(pmfControlledKernel (absorbedRepairPMF P K)) (x, a)) ≤ V x
    rw [integral_absorbedRepair_eq_sum P K V x a]
    simpa [F, V, finiteNormalizedRepairModel,
      UEOT.V3.FiniteDiscountedControl.Model.qValue,
      UEOT.V3.FiniteDiscountedControl.Model.expect] using hq
  · intro x
    have hg := F.greedyAction_spec x
    change M.reward x (g x) + M.discount * (∫ y, V y ∂M.transition (x, g x)) = V x
    change (if x ∈ K then 1 - beta else 0) + beta *
      (∫ y, V y ∂(pmfControlledKernel (absorbedRepairPMF P K)) (x, g x)) = V x
    rw [integral_absorbedRepair_eq_sum P K V x (g x)]
    simpa [F, V, g, finiteNormalizedRepairModel,
      UEOT.V3.FiniteDiscountedControl.Model.qValue,
      UEOT.V3.FiniteDiscountedControl.Model.expect] using hg

/-- Every randomized complete-history causal policy is dominated, for each
`0 < beta < 1`, by the deterministic stationary greedy certificate of the
normalized absorbed model.  This is still a discounted theorem. -/
theorem allCausal_normalizedDiscountedRepair_le_greedy
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (P : X → A → PMF X) (K : Set X)
    (beta : ℝ) (hbeta0 : 0 < beta) (hbeta1 : beta < 1) :
    let M := causalNormalizedRepairModel P K beta hbeta0.le hbeta1
    let G := normalizedRepairGreedyCertificate P K beta hbeta0 hbeta1
    ∀ (pi : CausalPolicy X A) [∀ n, IsMarkovKernel (pi n)] (x : X),
      M.infiniteValue pi 0 (initialHistory (A := A) x) ≤ G.value x := by
  dsimp only
  intro pi hpi x
  exact
    (normalizedRepairGreedyCertificate P K beta hbeta0 hbeta1).toBellmanUpperCertificate.infiniteValue_le_value
      pi 0 (initialHistory (A := A) x)

end
end UEOT.V3.Compression.Objecthood
