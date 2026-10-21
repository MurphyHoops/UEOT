import SameSourceSafePrefix
import UEOT.V3.Compression.Objecthood.AbsorbedRepairHittingSemantics
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Same-source killed survival masses converge to actual infinite survival

This private adapter keeps the original p0 and the same M, q and stationary
current-observation randomized sigma. It applies continuity from above to
the actual infinite trajectory, then reuses the passed finite safe-prefix
identity. No initial normalization, positive survival, nonempty safe set,
QSD data, or unproved source identity is assumed.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceSurvivalTailCheck

open MeasureTheory ProbabilityTheory Filter Function
open UEOT.V3.DynamicsKernel
open UEOT.V3.RecoveryHittingNonnegative
open UEOT.V3.CoreOperationalAssembly
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.QSDPerron
open UEOT.V3.Compression.Objecthood
open SourcePolicyPathBridgeCheck SameSourceKilledPathCheck
open SameSourceInfinitePrefixCheck SameSourceSafePrefixCheck
open scoped Classical BigOperators ENNReal ProbabilityTheory

noncomputable section

universe u

/-- The actual unnormalized finite safe masses converge to the real mass of
never leaving K under the same infinite trajectory and original initial law. -/
theorem killed_survival_mass_tendsto_homogeneous_neverHit_real
    {X Y A : Type u} [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (M : Model X (fun _ => A)) (q : X → Y) (sigma : Y → PMF A)
    (p0 : PMF X) (K : Set X) :
    Tendsto
      (fun n : ℕ => ∑ v : K, rowApply (safeInitialRow p0 K)
        ((killedMatrix M (liftedStationaryPolicy q sigma) K) ^ n) v)
      atTop
      (nhds ((homTrajMeasure p0.toMeasure
        (pmfRowKernel
          (policyTransitionPMF M (liftedStationaryPolicy q sigma)))).real
            (neverHitSet Kᶜ))) := by
  let mu := homTrajMeasure p0.toMeasure
    (pmfRowKernel (policyTransitionPMF M (liftedStationaryPolicy q sigma)))
  letI : IsProbabilityMeasure mu := by
    dsimp [mu]
    infer_instance
  have hKc : MeasurableSet Kᶜ := (Set.toFinite Kᶜ).measurableSet
  have ht := tendsto_measure_iInter_atTop
    (μ := mu) (s := survivalSet Kᶜ)
    (fun n => (measurableSet_survivalSet hKc n).nullMeasurableSet)
    (antitone_survivalSet Kᶜ)
    ⟨0, measure_ne_top _ _⟩
  rw [← neverHitSet_eq_iInter_survivalSet Kᶜ] at ht
  have hreal := (ENNReal.tendsto_toReal
    (show mu (neverHitSet Kᶜ) ≠ ∞ from measure_ne_top _ _)).comp ht
  have hreal' : Tendsto (fun n => mu.real (survivalSet Kᶜ n)) atTop
      (nhds (mu.real (neverHitSet Kᶜ))) := by
    simpa only [Function.comp_def, Measure.real] using hreal
  have hfun :
      (fun n : ℕ => mu.real (survivalSet Kᶜ n)) =
        (fun n : ℕ => ∑ v : K, rowApply (safeInitialRow p0 K)
          ((killedMatrix M (liftedStationaryPolicy q sigma) K) ^ n) v) := by
    funext n
    exact homogeneous_survival_real_eq_killed_pow_sum M q sigma p0 K n
  rw [hfun] at hreal'
  exact hreal'

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceSurvivalTailCheck

#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceSurvivalTailCheck.killed_survival_mass_tendsto_homogeneous_neverHit_real
