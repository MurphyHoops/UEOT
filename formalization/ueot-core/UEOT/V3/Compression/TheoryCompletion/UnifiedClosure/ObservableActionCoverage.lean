import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DeploymentCoverage

/-!
# Observable controls and actual deployment coverage

Whole-observation-fiber certification bounds the existing actual deployment
occupancy. A proved occupancy cap can then replace the corresponding term
in the same-policy finite risk budget. Full-fiber nonemptiness is an
explicit sufficient condition for the included classical policy construction.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
namespace ObservableActionCoverageCheck

open MeasureTheory UEOT.V3.PathError
open scoped BigOperators

universe u

/-- A finite executable checker when q and registration have executable
implementations. It checks every modeled state in the current observation
fiber. No choice of an unknown microscopic representative occurs. -/
def fiberCertifiedActions
    {X Y A : Type u} [Fintype X] [Fintype A] [DecidableEq Y]
    (q : X → Y) (certified : ℕ → X → A → Prop)
    [∀ n x a, Decidable (certified n x a)]
    (n : ℕ) (hc : CausalHistory Y (A × Y) n) : Finset A :=
  Finset.univ.filter fun a =>
    ∀ x : X, q x = riskLastState n hc → certified n x a

theorem mem_fiberCertifiedActions
    {X Y A : Type u} [Fintype X] [Fintype A]
    [DecidableEq Y]
    (q : X → Y) (certified : ℕ → X → A → Prop)
    [∀ n x a, Decidable (certified n x a)]
    (n : ℕ) (hc : CausalHistory Y (A × Y) n) (a : A) :
    a ∈ fiberCertifiedActions q certified n hc ↔
      ∀ x : X, q x = riskLastState n hc → certified n x a := by
  simp only [fiberCertifiedActions, Finset.mem_filter, Finset.mem_univ, true_and]


noncomputable section
open scoped Classical

/-- The actual uncovered occupancy is bounded by the true prefix
average of the policy's observable disallowed-action mass. Full fiber
certification supplies the pointwise implication before taking any average. -/
theorem uncovered_occupancy_le_observable_action_leakage
    {X Y A : Type u} [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (certified : ℕ → X → A → Prop)
    (allowed : ∀ n, CausalHistory Y (A × Y) n → A → Prop)
    (n : ℕ)
    (hfiber : ∀ hc a, allowed n hc a →
      ∀ x, q x = riskLastState n hc → certified n x a) :
    (coverageDeploymentRowLaw p₀ q P π n).toMeasure.real
        {xa | ¬ certified n xa.1 xa.2} ≤
      ∑ h, (causalLaw p₀ (riskMicroControlKernel q P π) n h).toReal *
        (π n (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) n h)).toMeasure.real
          {a | ¬ allowed n
            (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) n h) a} := by
  rw [← coverage_uncovered_indicator_expectation, coverage_rowLaw_expectation]
  apply Finset.sum_le_sum
  intro h _
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  rw [← coverage_uncovered_indicator_expectation]
  apply Finset.sum_le_sum
  intro a _
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  by_cases ha : allowed n
      (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) n h) a
  · have hc : certified n (riskLastState n h) a :=
      hfiber _ a ha (riskLastState n h) (risk_last_project q n h).symm
    simp only [if_pos ha, if_pos hc, le_refl]
  · by_cases hc : certified n (riskLastState n h) a <;> simp [ha, hc]

/-- A pointwise, observable controller bound gives a numerical
coverage bound without evaluating any microscopic prefix probabilities. -/
theorem observable_action_restriction_bounds_coverage
    {X Y A : Type u} [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (certified : ℕ → X → A → Prop)
    (allowed : ∀ n, CausalHistory Y (A × Y) n → A → Prop)
    (n : ℕ) (κ : ℝ)
    (hfiber : ∀ hc a, allowed n hc a →
      ∀ x, q x = riskLastState n hc → certified n x a)
    (hpolicy : ∀ hc,
      (π n hc).toMeasure.real {a | ¬ allowed n hc a} ≤ κ) :
    (coverageDeploymentRowLaw p₀ q P π n).toMeasure.real
      {xa | ¬ certified n xa.1 xa.2} ≤ κ := by
  refine (uncovered_occupancy_le_observable_action_leakage
    p₀ q P π certified allowed n hfiber).trans ?_
  calc
    _ ≤ ∑ h, (causalLaw p₀ (riskMicroControlKernel q P π) n h).toReal * κ := by
      exact Finset.sum_le_sum fun h _ =>
        mul_le_mul_of_nonneg_left (hpolicy _) ENNReal.toReal_nonneg
    _ = κ := by rw [← Finset.sum_mul, coverage_sum_toReal, one_mul]

/-- A hard observable support restriction gives exactly zero
uncovered occupancy. Existence of such a policy is a separate obligation. -/
theorem hard_observable_action_restriction_has_zero_uncovered_mass
    {X Y A : Type u} [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (certified : ℕ → X → A → Prop)
    (allowed : ∀ n, CausalHistory Y (A × Y) n → A → Prop)
    (n : ℕ)
    (hfiber : ∀ hc a, allowed n hc a →
      ∀ x, q x = riskLastState n hc → certified n x a)
    (hsupport : ∀ hc a, ¬ allowed n hc a → π n hc a = 0) :
    (coverageDeploymentRowLaw p₀ q P π n).toMeasure.real
      {xa | ¬ certified n xa.1 xa.2} = 0 := by
  apply le_antisymm _ ENNReal.toReal_nonneg
  apply observable_action_restriction_bounds_coverage
    p₀ q P π certified allowed n 0 hfiber
  intro hc
  rw [← coverage_uncovered_indicator_expectation]
  apply le_of_eq
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : allowed n hc a
  · simp [ha]
  · simp [ha, hsupport hc a ha]


end
end ObservableActionCoverageCheck
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
namespace ObservableActionCoverageContinuationCheck

open MeasureTheory UEOT.V3.PathError UEOT.V3.TotalVariation
open scoped BigOperators Classical

universe u

noncomputable section

/-- Substitute a proved upper bound on the existing actual uncovered
occupancy into its existing additive budget. Only the upper half of the
usual interval condition epsilon in [0,1] is needed for this monotonicity. -/
theorem deployment_coverage_budget_le_of_actual_occupancy_cap
    {X Y A : Type u} [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (certified : ℕ → X → A → Prop) (ε κ : ℕ → ℝ) (T : ℕ)
    (hε : ∀ n, n < T → ε n ≤ 1)
    (hν : ∀ n, n < T →
      (coverageDeploymentRowLaw p₀ q P π n).toMeasure.real
        {xa | ¬ certified n xa.1 xa.2} ≤ κ n) :
    (∑ n ∈ Finset.range T, (ε n + (1 - ε n) *
      (coverageDeploymentRowLaw p₀ q P π n).toMeasure.real
        {xa | ¬ certified n xa.1 xa.2})) ≤
      ∑ n ∈ Finset.range T, (ε n + (1 - ε n) * κ n) := by
  apply Finset.sum_le_sum
  intro n hn
  exact add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (hν n (Finset.mem_range.mp hn))
      (sub_nonneg.mpr (hε n (Finset.mem_range.mp hn))))

/-- An observable policy leakage cap supplies the actual-occupancy premise
of the preceding budget theorem through the already checked fiber result. -/
theorem observable_action_coverage_budget_le
    {X Y A : Type u} [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (certified : ℕ → X → A → Prop)
    (allowed : ∀ n, CausalHistory Y (A × Y) n → A → Prop)
    (ε κ : ℕ → ℝ) (T : ℕ)
    (hε : ∀ n, n < T → ε n ≤ 1)
    (hfiber : ∀ n, n < T → ∀ hc a, allowed n hc a →
      ∀ x, q x = riskLastState n hc → certified n x a)
    (hpolicy : ∀ n, n < T → ∀ hc,
      (π n hc).toMeasure.real {a | ¬ allowed n hc a} ≤ κ n) :
    (∑ n ∈ Finset.range T, (ε n + (1 - ε n) *
      (coverageDeploymentRowLaw p₀ q P π n).toMeasure.real
        {xa | ¬ certified n xa.1 xa.2})) ≤
      ∑ n ∈ Finset.range T, (ε n + (1 - ε n) * κ n) := by
  apply deployment_coverage_budget_le_of_actual_occupancy_cap
    p₀ q P π certified ε κ T hε
  intro n hn
  exact ObservableActionCoverageCheck.observable_action_restriction_bounds_coverage
    p₀ q P π certified allowed n (κ n) (hfiber n hn) (hpolicy n hn)

/-- The existing microscopic event transfer plus the observable action cap
gives a numerical finite-horizon failure bound. The sound coarse envelope
and the actual shared policy are retained explicitly. -/
theorem microscopic_failure_risk_under_observable_action_cap
    {X Y A : Type u} [Fintype X] [Fintype Y] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p₀ : PMF X) (q : X → Y)
    (P : ℕ → X → A → PMF X) (Q : ℕ → Y → A → PMF Y)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (certified : ℕ → X → A → Prop)
    (allowed : ∀ n, CausalHistory Y (A × Y) n → A → Prop)
    (ε κ : ℕ → ℝ) (T : ℕ)
    (hε : ∀ n, n < T → ε n ≤ 1)
    (hcert : ∀ n, n < T → ∀ x a, certified n x a →
      tvDist ((P n x a).map q).toMeasure (Q n (q x) a).toMeasure ≤ ε n)
    (hfiber : ∀ n, n < T → ∀ hc a, allowed n hc a →
      ∀ x, q x = riskLastState n hc → certified n x a)
    (hpolicy : ∀ n, n < T → ∀ hc,
      (π n hc).toMeasure.real {a | ¬ allowed n hc a} ≤ κ n)
    (E : Set (CausalHistory X (A × X) T))
    (F : Set (CausalHistory Y (A × Y) T))
    (hEF : E ⊆ (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) T) ⁻¹' F) :
    (causalLaw p₀ (riskMicroControlKernel q P π) T).toMeasure.real E ≤
      min 1 ((causalLaw (p₀.map q) (riskMacroControlKernel Q π) T).toMeasure.real F +
        ∑ n ∈ Finset.range T, (ε n + (1 - ε n) * κ n)) := by
  refine (coverage_same_policy_microscopic_failure_risk
    p₀ q P Q π certified ε T hcert E F hEF).trans ?_
  apply le_min
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (add_le_add le_rfl
      (observable_action_coverage_budget_le
        p₀ q P π certified allowed ε κ T hε hfiber hpolicy))

/-- A genuine PMF-valued coarse-history policy is selected from each
nonempty permitted action set before T. Outside T, use the supplied fallback
PMF so that the result has the full policy type used by causalLaw. This is
classical mathematical selection, not a claimed executable policy search. -/
def finiteHorizonSupportedPolicy
    {Y A : Type u}
    (Γ : ∀ n, CausalHistory Y (A × Y) n → Finset A)
    (T : ℕ)
    (hne : ∀ n, n < T → ∀ hc, (Γ n hc).Nonempty)
    (fallback : PMF A) : ∀ n, CausalHistory Y (A × Y) n → PMF A :=
  fun n hc =>
    if hn : n < T then PMF.pure (Classical.choose (hne n hn hc)) else fallback

/-- The selected Dirac policy assigns zero mass to every action outside
the prescribed set, at every coarse history before the given horizon. -/
theorem finiteHorizonSupportedPolicy_hard_support
    {Y A : Type u}
    (Γ : ∀ n, CausalHistory Y (A × Y) n → Finset A)
    (T : ℕ)
    (hne : ∀ n, n < T → ∀ hc, (Γ n hc).Nonempty)
    (fallback : PMF A) (n : ℕ) (hn : n < T)
    (hc : CausalHistory Y (A × Y) n) (a : A) (ha : a ∉ Γ n hc) :
    finiteHorizonSupportedPolicy Γ T hne fallback n hc a = 0 := by
  have hmem : Classical.choose (hne n hn hc) ∈ Γ n hc :=
    Classical.choose_spec (hne n hn hc)
  have hneAction : a ≠ Classical.choose (hne n hn hc) := by
    intro heq
    apply ha
    rw [heq]
    exact hmem
  simp [finiteHorizonSupportedPolicy, hn, PMF.pure_apply, hneAction]

/-- Whole-fiber nonemptiness is a sufficient feasibility condition: it
constructs one actual PMF policy whose uncovered occupancy is zero at every
transition before T. Empty or conflicting fibers are not assumed away by a
conclusion-bearing structure; their nonemptiness is the explicit premise. -/
theorem nonempty_fiber_masks_give_zero_uncovered_policy
    {X Y A : Type u} [Fintype X] [Fintype A] [DecidableEq Y]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (certified : ℕ → X → A → Prop)
    [∀ n x a, Decidable (certified n x a)]
    (T : ℕ)
    (hne : ∀ n, n < T → ∀ hc,
      (ObservableActionCoverageCheck.fiberCertifiedActions q certified n hc).Nonempty)
    (fallback : PMF A) :
    ∃ π : ∀ n, CausalHistory Y (A × Y) n → PMF A,
      ∀ n, n < T →
        (coverageDeploymentRowLaw p₀ q P π n).toMeasure.real
          {xa | ¬ certified n xa.1 xa.2} = 0 := by
  let Γ := ObservableActionCoverageCheck.fiberCertifiedActions q certified
  let π := finiteHorizonSupportedPolicy Γ T hne fallback
  refine ⟨π, ?_⟩
  intro n hn
  apply ObservableActionCoverageCheck.hard_observable_action_restriction_has_zero_uncovered_mass
    p₀ q P π certified (fun i hc a => a ∈ Γ i hc) n
  · intro hc a ha
    exact (ObservableActionCoverageCheck.mem_fiberCertifiedActions
      q certified n hc a).mp ha
  · intro hc a ha
    exact finiteHorizonSupportedPolicy_hard_support Γ T hne fallback n hn hc a ha

end
end ObservableActionCoverageContinuationCheck
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
