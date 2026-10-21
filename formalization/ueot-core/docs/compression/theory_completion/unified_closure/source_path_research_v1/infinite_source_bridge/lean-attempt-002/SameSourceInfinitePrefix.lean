import SourcePolicyPathBridge
import UEOT.V3.DynamicsKernel
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# The actual finite state history is a prefix of the same infinite trajectory

PRIVATE CANDIDATE — actual execution status is recorded separately.
No equality between independently supplied processes is assumed.
No existing private evidence or production source is changed.

The first endpoint treats a finite state space and an arbitrary fixed PMF
row family J. The initial PMF is preserved, including its time-zero state.
The complete recursive history is measurably equivalent to the Iic prefix.
The second endpoint instantiates J with the already constructed randomized
stationary policy and invokes the passed actual action-erasure theorem.

This is a bridge to the existing homTrajMeasure, not another construction of
an infinite process. No positive survival, safe set, QSD, Perron vector, or
observed-process Markov assumption is needed. The actual policy remains
time-homogeneous and depends only on the current observation.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceInfinitePrefixCheck

open MeasureTheory ProbabilityTheory Function
open UEOT.V3.PathError
open UEOT.V3.DynamicsKernel
open UEOT.V3.CoreOperationalAssembly
open UEOT.V3.FiniteDiscountedControl
open SourcePolicyPathBridgeCheck
open scoped ENNReal ProbabilityTheory Classical

noncomputable section

universe u v w

/-- Conversion of the actual PMF rows to a measure kernel. -/
def pmfRowKernel
    {H : Type u} {Z : Type v} [Fintype H]
    [MeasurableSpace H] [MeasurableSingletonClass H] [MeasurableSpace Z]
    (J : H → PMF Z) : Kernel H Z :=
  Kernel.ofFunOfCountable fun h => (J h).toMeasure

@[simp] theorem pmfRowKernel_apply
    {H : Type u} {Z : Type v} [Fintype H]
    [MeasurableSpace H] [MeasurableSingletonClass H] [MeasurableSpace Z]
    (J : H → PMF Z) (h : H) : pmfRowKernel J h = (J h).toMeasure := rfl

instance pmfRowKernel_isMarkov
    {H : Type u} {Z : Type v} [Fintype H]
    [MeasurableSpace H] [MeasurableSingletonClass H] [MeasurableSpace Z]
    (J : H → PMF Z) : IsMarkovKernel (pmfRowKernel J) where
  isProbabilityMeasure h := by
    rw [pmfRowKernel_apply]
    infer_instance

/-- Actual PMF extension, including the old history, is the corresponding
measure/kernel compProd. This is a calculation, not an input identity. -/
private theorem pmfExtend_toMeasure_compProd
    {H : Type u} {Z : Type v} [Fintype H]
    [MeasurableSpace H] [MeasurableSingletonClass H] [MeasurableSpace Z]
    (p : PMF H) (J : H → PMF Z) :
    (pmfExtend p J).toMeasure = p.toMeasure ⊗ₘ pmfRowKernel J := by
  ext E hE
  rw [pmfExtend, PMF.toMeasure_bind_apply _ _ _ hE,
    Measure.compProd_apply hE, lintegral_countable']
  apply tsum_congr
  intro h
  rw [PMF.toMeasure_map_apply _ _ _ measurable_prodMk_left hE,
    PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton h)]
  change p h * (J h).toMeasure (Prod.mk h ⁻¹' E) =
    (J h).toMeasure (Prod.mk h ⁻¹' E) * p h
  exact mul_comm _ _

/-- Retain every state, including time zero. Existing interval gluing supplies
the inverse as well as measurability; this is not a terminal-state map. -/
def stateHistoryEquiv
    {X : Type u} [MeasurableSpace X] :
    ∀ n, CausalHistory X X n ≃ᵐ ((i : Finset.Iic n) → X)
  | 0 => (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => X)).symm
  | n + 1 =>
      ((stateHistoryEquiv n).prodCongr
        (MeasurableEquiv.piSingleton (X := fun _ : ℕ => X) n)).trans
          (MeasurableEquiv.IicProdIoc (X := fun _ : ℕ => X) (Nat.le_succ n))

@[simp] theorem stateHistoryEquiv_zero
    {X : Type u} [MeasurableSpace X] :
    stateHistoryEquiv (X := X) 0 =
      (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => X)).symm := rfl

theorem stateHistoryEquiv_succ
    {X : Type u} [MeasurableSpace X] (n : ℕ) :
    (stateHistoryEquiv (X := X) (n + 1) :
      CausalHistory X X (n + 1) → ((i : Finset.Iic (n + 1)) → X)) =
      appendHistory n ∘ Prod.map (stateHistoryEquiv n) id := rfl

@[simp] theorem stateHistoryEquiv_last
    {X : Type u} [MeasurableSpace X]
    (n : ℕ) (h : CausalHistory X X n) :
    stateHistoryEquiv n h (lastHistoryIndex n) = currentState n h := by
  cases n with
  | zero => rfl
  | succ n =>
      rw [stateHistoryEquiv_succ]
      simp [Function.comp_def, appendHistory, IicProdIoc_def,
        lastHistoryIndex, MeasurableEquiv.piSingleton, currentState, Prod.map]

private theorem historyRowKernel_eq_comap
    {X : Type u} [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (J : X → PMF X) (n : ℕ) :
    pmfRowKernel (fun h : CausalHistory X X n => J (currentState n h)) =
      Kernel.comap (homHistoryKernel (pmfRowKernel J) n)
        (stateHistoryEquiv n) (stateHistoryEquiv n).measurable := by
  ext h E hE
  change (J (currentState n h)).toMeasure E =
    (J (stateHistoryEquiv n h (lastHistoryIndex n))).toMeasure E
  rw [stateHistoryEquiv_last]

/-- Push the old history through its actual representation map and retain the
new state. The next-state kernel reads that same mapped old history. -/
private theorem compProd_comap_map_left
    {H : Type u} {W : Type v} {Z : Type w}
    [MeasurableSpace H] [MeasurableSpace W] [MeasurableSpace Z]
    (mu : Measure H) [IsFiniteMeasure mu]
    (R : Kernel W Z) [IsMarkovKernel R]
    (F : H → W) (hF : Measurable F) :
    (mu ⊗ₘ Kernel.comap R F hF).map (Prod.map F id) =
      (mu.map F) ⊗ₘ R := by
  ext E hE
  rw [Measure.map_apply (hF.prodMap measurable_id) hE,
    Measure.compProd_apply (hE.preimage (hF.prodMap measurable_id)),
    Measure.compProd_apply hE,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hE) hF]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Full finite-prefix identity for the same initial PMF and the same fixed
PMF rows. Neither side is supplied as a certificate for the other. -/
theorem state_history_eq_homogeneous_prefix
    {X : Type u} [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (p0 : PMF X) (J : X → PMF X) (n : ℕ) :
    ((causalLaw p0 (fun k h => J (currentState k h)) n).map
      (stateHistoryEquiv n)).toMeasure =
      (homTrajMeasure p0.toMeasure (pmfRowKernel J)).map
        (Preorder.frestrictLe n) := by
  rw [← PMF.toMeasure_map _ _ (stateHistoryEquiv n).measurable]
  induction n with
  | zero =>
      simpa only [causalLaw, stateHistoryEquiv_zero] using
        (homTrajMeasure_prefix_zero p0.toMeasure (pmfRowKernel J)).symm
  | succ n ih =>
      letI : IsMarkovKernel (homHistoryKernel (pmfRowKernel J) n) :=
        isMarkovKernel_homHistoryKernel (pmfRowKernel J) n
      change (pmfExtend
        (causalLaw p0 (fun k h => J (currentState k h)) n)
        (fun h => J (currentState n h))).toMeasure.map
          (stateHistoryEquiv (n + 1)) = _
      rw [pmfExtend_toMeasure_compProd, stateHistoryEquiv_succ]
      rw [← Measure.map_map (measurable_appendHistory n)
        ((stateHistoryEquiv n).measurable.prodMap measurable_id)]
      rw [historyRowKernel_eq_comap J n,
        compProd_comap_map_left, ih]
      exact homTrajMeasure_prefix_succ p0.toMeasure (pmfRowKernel J) n

/-- The actual action/state experiment, after erasing only its actions, is
the complete prefix of the infinite trajectory of its constructed random
stationary policy. The existing source bridge supplies the actual identity. -/
theorem actual_state_prefix_eq_homogeneous_prefix
    {X Y A : Type u} [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (M : Model X (fun _ => A)) (q : X → Y) (sigma : Y → PMF A)
    (p0 : PMF X) (n : ℕ) :
    ((causalLaw p0
      (riskMicroControlKernel q (fun _ => M.transitionPMF)
        (observationMarkovPolicy sigma)) n).map
          (stateHistoryEquiv n ∘ eraseActionHistory n)).toMeasure =
      (homTrajMeasure p0.toMeasure
        (pmfRowKernel
          (policyTransitionPMF M (liftedStationaryPolicy q sigma)))).map
            (Preorder.frestrictLe n) := by
  rw [← PMF.map_comp,
    actual_state_path_eq_stationary_path M q sigma p0 n]
  exact state_history_eq_homogeneous_prefix p0
    (policyTransitionPMF M (liftedStationaryPolicy q sigma)) n

/-- Every finite state-prefix event, evaluated on the original action/state
records, has its exact same-source cylinder probability in the infinite law.
Action-dependent events without this factorization are not asserted here. -/
theorem actual_state_prefix_event_mass
    {X Y A : Type u} [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (M : Model X (fun _ => A)) (q : X → Y) (sigma : Y → PMF A)
    (p0 : PMF X) (n : ℕ) (B : Set ((i : Finset.Iic n) → X)) :
    (causalLaw p0
      (riskMicroControlKernel q (fun _ => M.transitionPMF)
        (observationMarkovPolicy sigma)) n).toMeasure
          ((stateHistoryEquiv n ∘ eraseActionHistory n) ⁻¹' B) =
      homTrajMeasure p0.toMeasure
        (pmfRowKernel
          (policyTransitionPMF M (liftedStationaryPolicy q sigma)))
            ((Preorder.frestrictLe n) ⁻¹' B) := by
  have hB : MeasurableSet B := (Set.toFinite B).measurableSet
  have hmass := congrArg
    (fun mu : Measure ((i : Finset.Iic n) → X) => mu B)
    (actual_state_prefix_eq_homogeneous_prefix M q sigma p0 n)
  rw [PMF.toMeasure_map_apply _ _ _ (measurable_of_finite _) hB,
    Measure.map_apply (Preorder.measurable_frestrictLe n) hB] at hmass
  exact hmass

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceInfinitePrefixCheck

#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceInfinitePrefixCheck.state_history_eq_homogeneous_prefix
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceInfinitePrefixCheck.actual_state_prefix_eq_homogeneous_prefix
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceInfinitePrefixCheck.actual_state_prefix_event_mass
