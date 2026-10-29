import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataControl
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.TrainingDeploymentJoint

/-! The literal rational preparation and action rows returned by the program
are interpreted directly. Their checked coordinates identify the same direct
controller; no existence theorem supplies a replacement table. The full joint
experiment retains the original state, preparation action/new state, and every
later action/state record before taking its post-preparation state window. -/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataLiteral
open UEOT.V3.PathError UEOT.V3.FiniteDiscountedControl UEOT.V3.CoreOperationalAssembly
open FiniteDataSource FiniteActionRealizabilityCheck FiniteActionCertificateCheck
open ConditionedActionTransportCheck SourcePolicyPathBridgeCheck FinitePolicyPathCheck
open scoped BigOperators
noncomputable section

/-- This unknown initial law is constructed from the real source and the actual
returned preparation weights, with its failure mass retained. -/
def literalPrepared (p : Param) (hp : Admissible p) (prep : Action → ℚ)
    (hprep : ValidRow prep) : PMF State :=
  initial.bind (fun x => actionMixture ((model p hp).transitionPMF x) (rowPMF prep hprep))

/-- The actual deployment of the same preparation row and finite action table. -/
def literalDeployment (p : Param) (hp : Admissible p) (prep : Action → ℚ)
    (hprep : ValidRow prep) (T : ℕ) (w : Fin T → Unit → Action → ℚ)
    (hw : ∀ t y, ValidRow (w t y)) : PMF (CausalHistory State State T) :=
  causalLaw (literalPrepared p hp prep hprep)
    (timeMixtureKernel (model p hp) observe (policy w hw 0)) T

private theorem preparation_row_eq (estimate : Param) (he : Admissible estimate)
    (prep : Action → ℚ) (hprep : ValidRow prep)
    (hcoordinates : ∀ a, (prep a : ℝ) = ![0,tilt estimate,1-tilt estimate] a) :
    rowPMF prep hprep = selection (tilt estimate) (tilt_valid estimate he) := by
  apply PMF.ext
  intro a
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [rowPMF_toReal, selection_real]
  exact hcoordinates a

private theorem policy_before_horizon (estimate : Param) (he : Admissible estimate)
    (T : ℕ) (w : Fin T → Unit → Action → ℚ) (hw : ∀ t y, ValidRow (w t y))
    (hcoordinates : ∀ t a, (w t () a : ℝ) = if t.val+1<T then
      ![0,tilt estimate,1-tilt estimate] a else ![0,1/2,1/2] a)
    (t : ℕ) (ht : t<T) :
    policy w hw 0 t () = controller estimate he T t () := by
  rw [policy, dif_pos ht]
  apply PMF.ext
  intro a
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [rowPMF_toReal]
  unfold controller
  split_ifs with h
  · rw [selection_real]
    simpa only [if_pos h] using hcoordinates ⟨t,ht⟩ a
  · rw [selection_real]
    simpa only [if_neg h, show (1 : ℝ)-1/2=1/2 by norm_num] using hcoordinates ⟨t,ht⟩ a

/-- Checked coordinates certify that this literal deployment is the direct
same-source experiment used in the statistical bound. Post-horizon policy
values are irrelevant; the table is never discarded or replaced by choice. -/
theorem literal_deployment_eq_direct
    (p : Param) (hp : Admissible p) (estimate : Param) (he : Admissible estimate)
    (prep : Action → ℚ) (hprep : ValidRow prep)
    (T : ℕ) (w : Fin T → Unit → Action → ℚ) (hw : ∀ t y, ValidRow (w t y))
    (hpreparation : ∀ a, (prep a : ℝ) = ![0,tilt estimate,1-tilt estimate] a)
    (hweights : ∀ t a, (w t () a : ℝ) = if t.val+1<T then
      ![0,tilt estimate,1-tilt estimate] a else ![0,1/2,1/2] a) :
    literalDeployment p hp prep hprep T w hw = deployed p hp estimate he T := by
  have hprepEq := preparation_row_eq estimate he prep hprep hpreparation
  unfold literalDeployment literalPrepared
  rw [hprepEq]
  change causalLaw (prepared p hp (tilt estimate) (tilt_valid estimate he))
    (timeMixtureKernel (model p hp) observe (policy w hw 0)) T =
      causalLaw (prepared p hp (tilt estimate) (tilt_valid estimate he))
        (timeMixtureKernel (model p hp) observe (controller estimate he T)) T
  apply (causal_path_eq_iff _ _ _ _ T).mpr
  refine ⟨rfl, ?_⟩
  intro t ht h _
  simp only [timeMixtureKernel, observe]
  rw [policy_before_horizon estimate he T w hw hweights t ht]

private theorem causal_law_bind {I H Z : Type} (p : PMF I) (F : I → PMF H)
    (K : ∀ n, CausalHistory H Z n → PMF Z) :
    ∀ n, causalLaw (p.bind F) K n = p.bind (fun i => causalLaw (F i) K n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      change pmfExtend (causalLaw (p.bind F) K n) (K n) =
        p.bind (fun i => pmfExtend (causalLaw (F i) K n) (K n))
      rw [ih]
      simp only [pmfExtend, PMF.bind_bind]

private theorem extend_map_snd {H Z : Type} (p : PMF H) (K : H → PMF Z) :
    (pmfExtend p K).map Prod.snd = p.bind K :=
  selectedTrainingDeployment_path_marginal p id K

abbrev PreparationRecord := State × (Action × State)

/-- One genuine preparation operation, retaining the original state, sampled
allowed action and next state, including preparation failure. -/
def preparationRecords (p : Param) (hp : Admissible p) (prep : Action → ℚ)
    (hprep : ValidRow prep) : PMF PreparationRecord :=
  pmfExtend initial (fun x => pmfExtend (rowPMF prep hprep) ((model p hp).transitionPMF x))

/-- The full T+1-operation joint experiment. The future action/state history
starts at the recorded preparation state and uses the same literal table. No
success conditioning, resampling, or assumed suffix-path equality occurs. -/
def fullLiteralExperiment (p : Param) (hp : Admissible p) (prep : Action → ℚ)
    (hprep : ValidRow prep) (T : ℕ) (w : Fin T → Unit → Action → ℚ)
    (hw : ∀ t y, ValidRow (w t y)) :
    PMF (PreparationRecord × CausalHistory State (Action × State) T) :=
  pmfExtend (preparationRecords p hp prep hprep) (fun r =>
    causalLaw (PMF.pure r.2.2)
      (riskMicroControlKernel observe (fun _ => (model p hp).transitionPMF)
        (timeObservationPolicy (policy w hw 0))) T)

/-- Drop the original/preparation records, retain X1,...,X(T+1). The future
history's initial record is precisely the actual preparation state. -/
def postPreparationStateWindow (T : ℕ)
    (r : PreparationRecord × CausalHistory State (Action × State) T) :
    CausalHistory State State T := eraseActionHistory T r.2

/-- The retained preparation state has exactly the true-source law used by
the literal consumer; the identity is derived by actual PMF marginalization. -/
theorem preparation_state_marginal (p : Param) (hp : Admissible p)
    (prep : Action → ℚ) (hprep : ValidRow prep) :
    (preparationRecords p hp prep hprep).map (fun r => r.2.2) =
      literalPrepared p hp prep hprep := by
  change (preparationRecords p hp prep hprep).map (Prod.snd ∘ Prod.snd) = _
  rw [← PMF.map_comp]
  unfold preparationRecords
  rw [extend_map_snd, PMF.map_bind]
  simp_rw [extend_map_snd]
  rfl

/-- Executing the real preparation and all T later allowed actions, then
retaining the post-preparation full state window, gives literalDeployment.
The T+1 operation semantics is proved, not supplied as an external fit input. -/
theorem full_experiment_window_eq_literal
    (p : Param) (hp : Admissible p) (prep : Action → ℚ) (hprep : ValidRow prep)
    (T : ℕ) (w : Fin T → Unit → Action → ℚ) (hw : ∀ t y, ValidRow (w t y)) :
    (fullLiteralExperiment p hp prep hprep T w hw).map (postPreparationStateWindow T) =
      literalDeployment p hp prep hprep T w hw := by
  let D := preparationRecords p hp prep hprep
  let K := riskMicroControlKernel observe (fun _ => (model p hp).transitionPMF)
    (timeObservationPolicy (policy w hw 0))
  have hmixture : causalLaw (literalPrepared p hp prep hprep) K T =
      D.bind (fun r => causalLaw (PMF.pure r.2.2) K T) := by
    rw [← preparation_state_marginal p hp prep hprep]
    exact causal_law_bind D (fun r => PMF.pure r.2.2) K T
  change (pmfExtend D (fun r => causalLaw (PMF.pure r.2.2) K T)).map
    (eraseActionHistory T ∘ Prod.snd) = _
  rw [← PMF.map_comp, extend_map_snd, ← hmixture]
  exact time_action_state_path_eq_mixture (model p hp) observe (policy w hw 0)
    (literalPrepared p hp prep hprep) T

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataLiteral
