import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceInfinitePrefix
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceKilledPath
import UEOT.V3.RecoveryHittingDrift
import Mathlib.MeasureTheory.Measure.Real

/-!
# Actual safe histories and finite survival of the same infinite trajectory

The source initial PMF is not filtered or normalized. Time zero, empty safe
sets and zero survival are included. The actual sigma is time-homogeneous
and depends only on the current observation, exactly as in the imported
source bridge and K1. No event identity or source equality is an input.

Existing historySurvivalSet/survivalSet take the failure target K complement.
The imported private K1 helper stateSurvives_erase_iff is not a public API;
the short structural action-erasure calculation is proved locally below.
No tail-limit, QSD, Doob or maximum-fixed-point assertion is made by this
finite-prefix adapter; the tail identity is in SameSourceSurvivalTail.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceSafePrefixCheck

open MeasureTheory ProbabilityTheory Function
open UEOT.V3.PathError
open UEOT.V3.DynamicsKernel
open UEOT.V3.RecoveryHittingNonnegative
open UEOT.V3.RecoveryHittingDrift
open UEOT.V3.CoreOperationalAssembly
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.QSDPerron
open SourcePolicyPathBridgeCheck SameSourceKilledPathCheck SameSourceInfinitePrefixCheck
open scoped Classical BigOperators ENNReal ProbabilityTheory

noncomputable section

universe u

/-- The complete state-history equivalence preserves safety at every recorded
time, including the initial state. No finiteness or probability is needed. -/
theorem stateHistoryEquiv_survival_iff
    {X : Type u} [MeasurableSpace X] (K : Set X) :
    ∀ (n : ℕ) (h : CausalHistory X X n),
      stateHistoryEquiv n h ∈ historySurvivalSet Kᶜ n ↔
        stateSurvives K n h := by
  intro n
  induction n with
  | zero =>
      intro h
      have h0 (i : Finset.Iic 0) : stateHistoryEquiv 0 h i = h := by
        rw [Subsingleton.elim i (lastHistoryIndex 0)]
        exact stateHistoryEquiv_last 0 h
      constructor
      · intro hs
        have hh := (mem_historySurvivalSet_iff Kᶜ 0 _).mp hs (lastHistoryIndex 0)
        rw [h0] at hh
        change ¬ ¬ (h ∈ K) at hh
        change h ∈ K
        exact not_not.mp hh
      · intro hs
        apply (mem_historySurvivalSet_iff Kᶜ 0 _).mpr
        intro i
        rw [h0 i]
        change ¬ ¬ (h ∈ K)
        change h ∈ K at hs
        exact not_not.mpr hs
  | succ n ih =>
      intro h
      rcases h with ⟨h, x⟩
      rw [stateHistoryEquiv_succ]
      change appendHistory n (stateHistoryEquiv n h, x) ∈
        historySurvivalSet Kᶜ (n + 1) ↔ stateSurvives K n h ∧ x ∈ K
      rw [appendHistory_mem_historySurvivalSet_iff, ih h]
      simp only [Set.mem_compl_iff, not_not]

/-- Pulling the safe prefix back to the original action/state record is the
actual no-failure event. The equality is derived from the real recursions. -/
theorem actual_safe_prefix_pullback
    {X A : Type u} [MeasurableSpace X] (K : Set X) (n : ℕ) :
    (stateHistoryEquiv n ∘ eraseActionHistory (X := X) (A := A) n) ⁻¹'
        historySurvivalSet Kᶜ n =
      {h : CausalHistory X (A × X) n |
        ¬ riskEverFailure (fun x => x ∉ K) n h} := by
  have herase : ∀ (k : ℕ) (h : CausalHistory X (A × X) k),
      stateSurvives K k (eraseActionHistory k h) ↔
        ¬ riskEverFailure (fun x => x ∉ K) k h := by
    intro k
    induction k with
    | zero =>
        intro h
        change (h ∈ K) ↔ ¬ (h ∉ K)
        tauto
    | succ k ih =>
        intro h
        change (stateSurvives K k (eraseActionHistory k h.1) ∧ h.2.2 ∈ K) ↔
          ¬ (riskEverFailure (fun x => x ∉ K) k h.1 ∨ h.2.2 ∉ K)
        rw [ih h.1]
        tauto
  ext h
  change stateHistoryEquiv n (eraseActionHistory n h) ∈ historySurvivalSet Kᶜ n ↔
    ¬ riskEverFailure (fun x => x ∉ K) n h
  exact (stateHistoryEquiv_survival_iff K n (eraseActionHistory n h)).trans (herase n h)

/-- K1's actual unnormalized safe mass is the finite survival probability
of the same infinite trajectory, in the existing real-valued measure API. -/
theorem homogeneous_survival_real_eq_killed_pow_sum
    {X Y A : Type u} [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (M : Model X (fun _ => A)) (q : X → Y) (sigma : Y → PMF A)
    (p0 : PMF X) (K : Set X) (n : ℕ) :
    (homTrajMeasure p0.toMeasure
      (pmfRowKernel
        (policyTransitionPMF M (liftedStationaryPolicy q sigma)))).real
          (survivalSet Kᶜ n) =
      ∑ v : K, rowApply (safeInitialRow p0 K)
        ((killedMatrix M (liftedStationaryPolicy q sigma) K) ^ n) v := by
  have hmass := actual_state_prefix_event_mass M q sigma p0 n
    (historySurvivalSet Kᶜ n)
  rw [actual_safe_prefix_pullback] at hmass
  have hreal := congrArg ENNReal.toReal hmass
  calc
    _ = (causalLaw p0
      (riskMicroControlKernel q (fun _ => M.transitionPMF)
        (observationMarkovPolicy sigma)) n).toMeasure.real
          {h | ¬ riskEverFailure (fun x => x ∉ K) n h} := by
      exact hreal.symm
    _ = _ := actual_survival_mass_eq_killed_pow_sum M q sigma p0 K n

/-- ENNReal form of the same finite-prefix identity. The finite-mass condition
is proved from the actual probability measure, not added as a hypothesis. -/
theorem homogeneous_survival_mass_eq_ofReal_killed_pow_sum
    {X Y A : Type u} [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (M : Model X (fun _ => A)) (q : X → Y) (sigma : Y → PMF A)
    (p0 : PMF X) (K : Set X) (n : ℕ) :
    homTrajMeasure p0.toMeasure
      (pmfRowKernel
        (policyTransitionPMF M (liftedStationaryPolicy q sigma)))
          (survivalSet Kᶜ n) =
      ENNReal.ofReal (∑ v : K, rowApply (safeInitialRow p0 K)
        ((killedMatrix M (liftedStationaryPolicy q sigma) K) ^ n) v) := by
  calc
    _ = ENNReal.ofReal
      ((homTrajMeasure p0.toMeasure
        (pmfRowKernel
          (policyTransitionPMF M (liftedStationaryPolicy q sigma)))).real
            (survivalSet Kᶜ n)) := by
      symm
      exact ofReal_measureReal (by finiteness)
    _ = _ := congrArg ENNReal.ofReal
      (homogeneous_survival_real_eq_killed_pow_sum M q sigma p0 K n)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceSafePrefixCheck
