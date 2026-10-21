import UEOT.V3.CoreOperationalAssembly
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DeploymentCoverage

/-!
# One actual controlled source: action records to stationary state paths

Private research candidate, not a production import. Actual compile status is
recorded separately. No equality of independently supplied kernels is assumed.

The action PMF is sigma y at EVERY history whose current observation is y.
It is independent of time and of the earlier history. The induced stationary
micro-policy is constructed from precisely that PMF and the observation q.
The finite model's original transitionPMF supplies every successor law.

Erasing actions retains the complete microscopic STATE history. The result
does not assert that the observation process is Markov, and does not reduce a
general history-dependent policy to a stationary one. No Fintype Y, measurable
structure, observation lumpability, or positive-history condition is needed
for this exact finite-PMF identity.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SourcePolicyPathBridgeCheck

open UEOT.V3.PathError
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.CoreOperationalAssembly
open scoped BigOperators Classical

noncomputable section

universe u

/-- The same observation-based action PMF at every complete visible history. -/
def observationMarkovPolicy
    {Y A : Type u} (sigma : Y → PMF A) :
    ∀ n, CausalHistory Y (A × Y) n → PMF A :=
  fun n h => sigma (riskLastState n h)

/-- The real-valued stationary policy is constructed from that actual PMF.
It is not an independently supplied policy with an asserted equality. -/
def liftedStationaryPolicy
    {X Y A : Type u} [Fintype A]
    (q : X → Y) (sigma : Y → PMF A) :
    StationaryPolicy (fun _ : X => A) where
  prob := fun x a => (sigma (q x) a).toReal
  prob_nonneg := fun _ _ => ENNReal.toReal_nonneg
  prob_sum_one := fun x => coverage_sum_toReal (sigma (q x))

/-- Preserve all microscopic states and discard only the action records. -/
abbrev eraseActionHistory
    {X A : Type u} (n : ℕ) :
    CausalHistory X (A × X) n → CausalHistory X X n :=
  riskHistoryMap id Prod.snd n

private theorem currentState_eraseActionHistory
    {X A : Type u} (n : ℕ) (h : CausalHistory X (A × X) n) :
    currentState n (eraseActionHistory n h) = riskLastState n h := by
  cases n <;> rfl

private theorem pmfExtend_map_snd
    {A X : Type u} (p : PMF A) (K : A → PMF X) :
    (pmfExtend p K).map Prod.snd = p.bind K := by
  unfold pmfExtend
  rw [PMF.map_bind]
  congr 1
  funext a
  rw [PMF.map_comp]
  change (K a).map id = K a
  exact PMF.map_id (K a)

/-- Actual next-state marginal of the action/state risk kernel equals the
stationary PMF derived from the SAME model and SAME action distributions. -/
theorem actual_next_state_eq_stationary_row
    {X Y A : Type u} [Fintype X] [Fintype A] [Nonempty A]
    (M : Model X (fun _ => A)) (q : X → Y) (sigma : Y → PMF A)
    (n : ℕ) (h : CausalHistory X (A × X) n) :
    (riskMicroControlKernel q (fun _ => M.transitionPMF)
      (observationMarkovPolicy sigma) n h).map Prod.snd =
      policyTransitionPMF M (liftedStationaryPolicy q sigma) (riskLastState n h) := by
  unfold riskMicroControlKernel observationMarkovPolicy
  rw [risk_last_project, pmfExtend_map_snd]
  apply PMF.ext
  intro y
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [policyTransitionPMF_apply_toReal]
  rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum (by
    intro a _
    exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
      (PMF.apply_ne_top _ _))]
  simp only [ENNReal.toReal_mul, Model.transitionPMF_apply_toReal,
    Model.policyTransition, liftedStationaryPolicy]

/-- Exact complete state-path law obtained by erasing actions from the actual
risk path. The row source identity is proved above, not supplied as a premise.
The initial PMF, model, observation, and action PMFs are common to both sides. -/
theorem actual_state_path_eq_stationary_path
    {X Y A : Type u} [Fintype X] [Fintype A] [Nonempty A]
    (M : Model X (fun _ => A)) (q : X → Y) (sigma : Y → PMF A)
    (p0 : PMF X) (n : ℕ) :
    (causalLaw p0
      (riskMicroControlKernel q (fun _ => M.transitionPMF)
        (observationMarkovPolicy sigma)) n).map (eraseActionHistory n) =
      causalLaw p0 (policyPathKernel M (liftedStationaryPolicy q sigma)) n := by
  let K := riskMicroControlKernel q (fun _ => M.transitionPMF)
    (observationMarkovPolicy sigma)
  let L := policyPathKernel M (liftedStationaryPolicy q sigma)
  change (causalLaw p0 K n).map (eraseActionHistory n) = causalLaw p0 L n
  induction n with
  | zero =>
      change p0.map id = p0
      exact PMF.map_id p0
  | succ n ih =>
      have hrow :
          (fun h : CausalHistory X (A × X) n => (K n h).map Prod.snd) =
            (fun h => L n (eraseActionHistory n h)) := by
        funext h
        change
          (riskMicroControlKernel q (fun _ => M.transitionPMF)
            (observationMarkovPolicy sigma) n h).map Prod.snd =
          policyTransitionPMF M (liftedStationaryPolicy q sigma)
            (currentState n (eraseActionHistory n h))
        rw [currentState_eraseActionHistory]
        exact actual_next_state_eq_stationary_row M q sigma n h
      change
        (pmfExtend (causalLaw p0 K n) (K n)).map
            (fun hz => (eraseActionHistory n hz.1, hz.2.2)) =
          pmfExtend (causalLaw p0 L n) (L n)
      calc
        _ = ((pmfExtend (causalLaw p0 K n) (K n)).map
              (fun hz => (hz.1, hz.2.2))).map
              (fun hz => (eraseActionHistory n hz.1, hz.2)) := by
                rw [PMF.map_comp]
                rfl
        _ = (pmfExtend (causalLaw p0 K n)
              (fun h => L n (eraseActionHistory n h))).map
              (fun hz => (eraseActionHistory n hz.1, hz.2)) := by
                rw [risk_map_extend_right, hrow]
        _ = pmfExtend ((causalLaw p0 K n).map (eraseActionHistory n)) (L n) :=
              coverage_map_extend_reference (causalLaw p0 K n)
                (eraseActionHistory n) (L n)
        _ = _ := by rw [ih]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SourcePolicyPathBridgeCheck

#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SourcePolicyPathBridgeCheck.actual_next_state_eq_stationary_row
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SourcePolicyPathBridgeCheck.actual_state_path_eq_stationary_path
