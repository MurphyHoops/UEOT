import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SourcePolicyPathBridge
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceKilledExitFlux
import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic

/-!
# Which target kernels can the original actions implement?

Randomizing allowed actions produces exactly the convex hull of their actual
transition rows.  Under partial observation the convex hull must be taken in
the space of ENTIRE observation-fiber row families: the same randomization
must work at every hidden state with that observation.  Rowwise feasibility
alone does not supply an observation-based policy.

The actual action/state experiment is connected to its target state path by
the existing source-policy bridge.  Independently, every causal transition
scheme preserves the initial marginal, so a survival tilt of the initial law
is a separate intervention requirement.  No conditioned-source equality or
implementability conclusion is supplied as a premise of the convex criteria.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionRealizabilityCheck

open MeasureTheory
open UEOT.V3.PathError UEOT.V3.TotalVariation
open UEOT.V3.FiniteDiscountedControl UEOT.V3.CoreOperationalAssembly
open SourcePolicyPathBridgeCheck SameSourceKilledExitFluxCheck
open scoped BigOperators Classical

noncomputable section
universe u v w uI

/-- Real atom coordinates of the actual PMF. -/
def realRow {X : Type u} (p : PMF X) : X → ℝ := fun x => (p x).toReal

private theorem realRow_injective {X : Type u} :
    Function.Injective (realRow (X := X)) := by
  intro p q h
  apply PMF.ext
  intro x
  exact (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top p x)
    (PMF.apply_ne_top q x)).mp (congrFun h x)

/-- Choose an allowed action, then use that action's actual source row. -/
def actionMixture {X : Type u} {A : Type v}
    (P : A → PMF X) (sigma : PMF A) : PMF X := sigma.bind P

/-- Conversion of the actual bind construction to finite real barycenters. -/
theorem realRow_actionMixture
    {X : Type u} {A : Type v} [Fintype A]
    (P : A → PMF X) (sigma : PMF A) :
    realRow (actionMixture P sigma) = ∑ a, (sigma a).toReal • realRow (P a) := by
  funext x
  simp only [realRow, actionMixture, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum (by
    intro a _
    exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _))]
  simp only [ENNReal.toReal_mul]

/-- Finite probability randomizations are exactly the real convex combinations.
This also applies to a whole family of rows, not just a single PMF. -/
theorem pmf_barycenter_exists_iff_mem_convexHull
    {A : Type u} [Fintype A] {E : Type v} [AddCommGroup E] [Module ℝ E]
    (v : A → E) (z : E) :
    (∃ sigma : PMF A, (∑ a, (sigma a).toReal • v a) = z) ↔
      z ∈ convexHull ℝ (Set.range v) := by
  constructor
  · rintro ⟨sigma, hz⟩
    exact mem_convexHull_of_exists_fintype (fun a => (sigma a).toReal) v
      (fun _ => ENNReal.toReal_nonneg) (coverage_sum_toReal sigma)
      (fun a => Set.mem_range_self a) hz
  · intro hz
    rw [convexHull_range_eq_exists_affineCombination] at hz
    rcases hz with ⟨s, weights, hnonneg, hsum, hcomb⟩
    let weights' : A → ℝ := fun a => if a ∈ s then weights a else 0
    have hnonneg' : ∀ a, 0 ≤ weights' a := by
      intro a
      by_cases ha : a ∈ s
      · simpa [weights', ha] using hnonneg a ha
      · simp [weights', ha]
    have hsum' : ∑ a, weights' a = 1 := by
      simpa [weights'] using hsum
    have hcomb' : ∑ a, weights' a • v a = z := by
      rw [Finset.affineCombination_eq_linear_combination s v weights hsum] at hcomb
      simpa [weights', ite_smul] using hcomb
    refine ⟨FiniteProbabilityRow.ofRealRow weights' hnonneg' hsum', ?_⟩
    simpa only [FiniteProbabilityRow.ofRealRow_apply_toReal] using hcomb'

/-- Necessary AND sufficient row criterion for implementation by the allowed
actions.  The action distribution is constructed from the convex weights. -/
theorem row_realizable_iff_mem_convexHull
    {X : Type u} {A : Type v} [Fintype A]
    (P : A → PMF X) (R : PMF X) :
    (∃ sigma : PMF A, actionMixture P sigma = R) ↔
      realRow R ∈ convexHull ℝ (Set.range (fun a => realRow (P a))) := by
  rw [← pmf_barycenter_exists_iff_mem_convexHull]
  constructor
  · rintro ⟨sigma, h⟩
    exact ⟨sigma, by rw [← realRow_actionMixture, h]⟩
  · rintro ⟨sigma, h⟩
    refine ⟨sigma, realRow_injective ?_⟩
    rw [realRow_actionMixture]
    exact h

/-- Exact partial-observation criterion.  The target family on each fiber
must be one common convex combination of that fiber's action-row families.
Empty fibers impose no hidden-state equation; nonempty action alphabets give
their vacuous convex witness.  No finite observation alphabet is required. -/
theorem observation_realizable_iff_fiber_convexHull
    {I : Type uI} {X : Type u} {Y : Type v} {A : Type w} [Fintype A]
    (q : I → Y) (P : I → A → PMF X) (R : I → PMF X) :
    (∃ sigma : Y → PMF A, ∀ x, actionMixture (P x) (sigma (q x)) = R x) ↔
      ∀ y, (fun x : {x : I // q x = y} => realRow (R x.val)) ∈
        convexHull ℝ (Set.range (fun a (x : {x : I // q x = y}) =>
          realRow (P x.val a))) := by
  constructor
  · rintro ⟨sigma, hsigma⟩ y
    apply (pmf_barycenter_exists_iff_mem_convexHull _ _).mp
    refine ⟨sigma y, ?_⟩
    funext x z
    have h := congrFun (congrArg realRow (hsigma x.val)) z
    rw [realRow_actionMixture, x.property] at h
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h
  · intro h
    have hex (y : Y) := (pmf_barycenter_exists_iff_mem_convexHull
      (fun a (x : {x : I // q x = y}) => realRow (P x.val a))
      (fun x : {x : I // q x = y} => realRow (R x.val))).mpr (h y)
    choose sigma hsigma using hex
    refine ⟨sigma, ?_⟩
    intro x
    apply realRow_injective
    rw [realRow_actionMixture]
    funext z
    have hx := congrFun (congrFun (hsigma (q x)) ⟨x, rfl⟩) z
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hx

/-- The existing real-policy PMF and the actual action mixture are the same
source row; their equality is derived from their definitions. -/
theorem stationary_row_eq_actionMixture
    {X Y A : Type u} [Fintype X] [Fintype A] [Nonempty A]
    (M : Model X (fun _ => A)) (q : X → Y) (sigma : Y → PMF A) (x : X) :
    policyTransitionPMF M (liftedStationaryPolicy q sigma) x =
      actionMixture (M.transitionPMF x) (sigma (q x)) := by
  apply realRow_injective
  rw [realRow_actionMixture]
  funext y
  simp only [realRow, policyTransitionPMF_apply_toReal, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Model.transitionPMF_apply_toReal,
    Model.policyTransition, liftedStationaryPolicy]

/-- A feasible observation policy implements the target in the ACTUAL
action/state experiment, after discarding the sampled action record. -/
theorem actual_next_state_eq_target
    {X Y A : Type u} [Fintype X] [Fintype A] [Nonempty A]
    (M : Model X (fun _ => A)) (q : X → Y) (sigma : Y → PMF A)
    (R : X → PMF X)
    (hreal : ∀ x, actionMixture (M.transitionPMF x) (sigma (q x)) = R x)
    (n : ℕ) (h : CausalHistory X (A × X) n) :
    (riskMicroControlKernel q (fun _ => M.transitionPMF)
      (observationMarkovPolicy sigma) n h).map Prod.snd = R (riskLastState n h) := by
  rw [actual_next_state_eq_stationary_row, stationary_row_eq_actionMixture, hreal]

/-- Whole-path implementation uses the SAME original model and SAME initial
PMF.  It is a consumer of the row criterion and source-policy path bridge. -/
theorem actual_state_path_eq_target
    {X Y A : Type u} [Fintype X] [Fintype A] [Nonempty A]
    (M : Model X (fun _ => A)) (q : X → Y) (sigma : Y → PMF A)
    (R : X → PMF X)
    (hreal : ∀ x, actionMixture (M.transitionPMF x) (sigma (q x)) = R x)
    (p0 : PMF X) (T : ℕ) :
    (causalLaw p0 (riskMicroControlKernel q (fun _ => M.transitionPMF)
      (observationMarkovPolicy sigma)) T).map (eraseActionHistory T) =
      causalLaw p0 (fun n h => R (currentState n h)) T := by
  rw [actual_state_path_eq_stationary_path]
  have hkernel : policyPathKernel M (liftedStationaryPolicy q sigma) =
      (fun n h => R (currentState n h)) := by
    funext n h
    change policyTransitionPMF M (liftedStationaryPolicy q sigma) (currentState n h) = _
    rw [stationary_row_eq_actionMixture, hreal]
  rw [hkernel]

/-- The original record, retained by every complete causal history. -/
def initialRecord {X Z : Type u} : ∀ n, CausalHistory X Z n → X
  | 0, x => x
  | n + 1, h => initialRecord n h.1

/-- No choice of future transition kernels changes the initial marginal.
The kernels here may depend on the complete history, not just the state. -/
theorem causalLaw_initial_marginal
    {X Z : Type u} (p0 : PMF X)
    (K : ∀ n, CausalHistory X Z n → PMF Z) :
    ∀ T, (causalLaw p0 K T).map (initialRecord T) = p0 := by
  intro T
  induction T with
  | zero => exact PMF.map_id p0
  | succ T ih =>
      change (pmfExtend (causalLaw p0 K T) (K T)).map
        (initialRecord T ∘ Prod.fst) = p0
      rw [← PMF.map_comp, pmfExtend_map_fst]
      exact ih

/-- A complete target path requires its own initial marginal to agree with
the original initial law, independently of all transition feasibility. -/
theorem path_implementation_requires_initial
    {X Z : Type u} (p0 : PMF X)
    (K : ∀ n, CausalHistory X Z n → PMF Z) (T : ℕ)
    (target : PMF (CausalHistory X Z T)) (heq : causalLaw p0 K T = target) :
    target.map (initialRecord T) = p0 := by
  rw [← heq]
  exact causalLaw_initial_marginal p0 K T

/-- The unavoidable initial mismatch lower-bounds the entire path error. -/
theorem initial_tv_le_path_tv
    {X Z : Type u} [Fintype X] [Fintype Z]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (p0 : PMF X) (K : ∀ n, CausalHistory X Z n → PMF Z) (T : ℕ)
    (target : PMF (CausalHistory X Z T)) :
    tvDist p0.toMeasure (target.map (initialRecord T)).toMeasure ≤
      tvDist (causalLaw p0 K T).toMeasure target.toMeasure := by
  have hm : Measurable (initialRecord (X := X) (Z := Z) T) := measurable_of_finite _
  have h := tvDist_map_le (causalLaw p0 K T).toMeasure target.toMeasure
    (initialRecord T) hm
  rw [PMF.toMeasure_map _ _ hm, PMF.toMeasure_map _ _ hm,
    causalLaw_initial_marginal] at h
  exact h

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionRealizabilityCheck
