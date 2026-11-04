import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionExecution
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionFilteredModel
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionSupportedPolicy

/-!
# Original mode law and actual multi-generation population witnesses

The rational primitive is precisely the original mode PMF multiplied by the
independent fair birth-label PMF, at the fixed source parameter. The complete
native Store execution also retains globally allocated child addresses, actual
parent identity, source birth history, clocks, fault failures and invalid-address
None records. None of that hidden metadata is returned as an observation.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionNativeLaw

open RegisterJointDecisionSource RegisterJointDecisionExecution
open RegisterFaultControlModel
open RegisterMechanismPurpose (Mechanism)
open FiniteJointDecisionSolver (Table)
open UEOT.V3.FiniteDiscountedControl

/-- Literal equality with the old source's mode and label primitives. The
parameter relation is evaluated at the one retained theta, not a new draw. -/
theorem primitiveWeight_eq_original {Theta : Type*} (r : Theta → ℚ)
    (w : World Theta) (z : Noise) (epsilon : NNReal) (he : epsilon ≤ 1)
    (hr : (r w.theta : ℝ) = repairChance epsilon) :
    (primitiveWeight r w z : ℝ) =
      (modeLaw epsilon he z.1).toReal * (PMF.uniformOfFintype Bool z.2).toReal := by
  rcases z with ⟨mode, label⟩
  cases mode <;>
    norm_num [primitiveWeight, modeLaw, FiniteProbabilityRow.ofRealRow_apply_toReal,
      modeProbability, PMF.uniformOfFintype_apply, hr, repairChance] <;> ring

noncomputable def rationalHazard (r : ℚ) (hr : r ≤ 1) : NNReal :=
  ⟨1 - (r : ℝ), by exact_mod_cast sub_nonneg.mpr hr⟩

theorem rationalHazard_le_one (r : ℚ) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    rationalHazard r h1 ≤ 1 := by
  change 1 - (r : ℝ) ≤ 1
  have h : (0 : ℝ) ≤ r := by exact_mod_cast h0
  linarith

theorem primitiveWeight_eq_rational_hazard {Theta : Type*} (r : Theta → ℚ)
    (hr : ∀ t, 0 ≤ r t ∧ r t ≤ 1) (w : World Theta) (z : Noise) :
    (primitiveWeight r w z : ℝ) =
      (modeLaw (rationalHazard (r w.theta) (hr w.theta).2)
        (rationalHazard_le_one (r w.theta) (hr w.theta).1 (hr w.theta).2) z.1).toReal *
      (PMF.uniformOfFintype Bool z.2).toReal := by
  apply primitiveWeight_eq_original
  change (r w.theta : ℝ) = 1 - (1 - (r w.theta : ℝ))
  ring

open FiniteJointDecisionBelief (Belief Source)
open FiniteJointDecisionSolver (Model CausalPolicy)
open FiniteJointDecisionFilteredModel (sourceCausalValue)

def pricedReceipt (price tariff : ℚ) (_a : Act) (o : Obs) : ℚ :=
  (if o.1 then 1 else 0) - price * (if o.2 then tariff else 0)

theorem nativePayoff_eq_pricedReceipt {Theta : Type*} {n : ℕ} (i : Fin n)
    (m : Mechanism) (price tariff : ℚ) (hc : (m.writeCost : ℝ) = (tariff : ℝ))
    (w : NativeWorld Theta n) (a : Act) (z : Noise) (hw : Aligned m.goal w.store) :
    nativePayoff price (nativeTransaction i m w a z) =
      (pricedReceipt price tariff a (RegisterJointDecisionSource.observe m.goal (projectWorld i w) a z) : ℝ) := by
  rw [nativePayoff_project i m price w a z hw, hc]
  cases hb : (RegisterJointDecisionSource.observe m.goal (projectWorld i w) a z).1 <;>
    cases hf : (RegisterJointDecisionSource.observe m.goal (projectWorld i w) a z).2 <;>
    simp [pricedReceipt, birthUnit, feeUnit, hb, hf] <;> ring

/-- A real randomized causal policy executed by the ORIGINAL Store. Its
action probabilities use only its permitted memory. The protected world is
used only by the physical dispatcher and the common registered noise source.
The source parameter remains inside the same NativeWorld at every step. -/
noncomputable def nativeCausalValue {Theta : Type*} {n : ℕ} {I : Type*}
    (K : Source (World Theta) Act Obs Noise) (i : Fin n) (m : Mechanism)
    (price d : ℚ) {N : Model I Act Obs} (pi : CausalPolicy N) :
    ℕ → pi.Memory → NativeWorld Theta n → ℝ
  | 0, _, _ => 0
  | H+1, h, w =>
      ∑ a, pi.actionProb h a * ∑ z, (K.chance (projectWorld i w) z : ℝ) *
        (nativePayoff price (nativeTransaction i m w a z) + (d : ℝ) *
          nativeCausalValue K i m price d pi H
            (pi.advance h a (nativeObs (nativeTransaction i m w a z)))
            (nativeStep i m w a z))

/-- Native source bridge for ALL permitted real-randomized competitors.
The two structural equalities are rfl for RegisterJointDecisionConsumer.source;
neither a value identity nor an optimality/funding conclusion is assumed.
The one-step Store simulation proved in Source supplies the entire bridge. -/
theorem nativeCausalValue_eq_packed {Theta : Type*} {n : ℕ} {M : Type*}
    (K : Source (World Theta) Act Obs Noise) (i : Fin n) (m : Mechanism)
    (hnext : K.next = step m.goal)
    (hobs : K.observe = RegisterJointDecisionSource.observe m.goal)
    (price tariff d : ℚ) (hc : (m.writeCost : ℝ) = (tariff : ℝ))
    {N : Model (Belief (World Theta) × M) Act Obs} (pi : CausalPolicy N) :
    ∀ H (h : pi.Memory) (w : NativeWorld Theta n), Aligned m.goal w.store →
      nativeCausalValue K i m price d pi H h w =
        sourceCausalValue K (pricedReceipt price tariff) d pi H h (projectWorld i w) := by
  intro H
  induction H with
  | zero => intros; rfl
  | succ H ih =>
      intro h w hw
      simp only [nativeCausalValue, sourceCausalValue]
      apply Finset.sum_congr rfl
      intro a ha
      apply congrArg (fun t : ℝ => pi.actionProb h a * t)
      apply Finset.sum_congr rfl
      intro z hz
      apply congrArg (fun t : ℝ => (K.chance (projectWorld i w) z : ℝ) * t)
      rw [nativePayoff_eq_pricedReceipt i m price tariff hc w a z hw,
        nativeObservation_project i m w a z hw,
        ih _ _ (nativeStep_aligned i m w a z hw),
        nativeStep_project i m w a z hw]
      simp only [hnext, hobs]

open FiniteJointDecisionSupportedPolicy (RawCausalPolicy rawSourceValue)

/-- The same original Store interpreter for a raw causal kernel. Admissibility
is deliberately external and need hold only on actual supported histories. -/
noncomputable def rawNativeCausalValue {Theta : Type*} {n : ℕ} {I : Type*}
    (K : Source (World Theta) Act Obs Noise) (i : Fin n) (m : Mechanism)
    (price d : ℚ) {N : Model I Act Obs} (pi : RawCausalPolicy N) :
    ℕ → pi.Memory → NativeWorld Theta n → ℝ
  | 0, _, _ => 0
  | H+1, h, w =>
      ∑ a, pi.actionProb h a * ∑ z, (K.chance (projectWorld i w) z : ℝ) *
        (nativePayoff price (nativeTransaction i m w a z) + (d : ℝ) *
          rawNativeCausalValue K i m price d pi H
            (pi.advance h a (nativeObs (nativeTransaction i m w a z)))
            (nativeStep i m w a z))

/-- This bridge has no all-counterfactual-menu premise. Together with
supported_actual_causal_le_returned it covers every same-information original
Store policy legal on the source-supported execution histories. -/
theorem rawNativeCausalValue_eq_packed {Theta : Type*} {n : ℕ} {M : Type*}
    (K : Source (World Theta) Act Obs Noise) (i : Fin n) (m : Mechanism)
    (hnext : K.next = step m.goal)
    (hobs : K.observe = RegisterJointDecisionSource.observe m.goal)
    (price tariff d : ℚ) (hc : (m.writeCost : ℝ) = (tariff : ℝ))
    {N : Model (Belief (World Theta) × M) Act Obs} (pi : RawCausalPolicy N) :
    ∀ H (h : pi.Memory) (w : NativeWorld Theta n), Aligned m.goal w.store →
      rawNativeCausalValue K i m price d pi H h w =
        rawSourceValue K (pricedReceipt price tariff) d pi H h (projectWorld i w) := by
  intro H
  induction H with
  | zero => intros; rfl
  | succ H ih =>
      intro h w hw
      simp only [rawNativeCausalValue, rawSourceValue]
      apply Finset.sum_congr rfl
      intro a ha
      apply congrArg (fun t : ℝ => pi.actionProb h a * t)
      apply Finset.sum_congr rfl
      intro z hz
      apply congrArg (fun t : ℝ => (K.chance (projectWorld i w) z : ℝ) * t)
      rw [nativePayoff_eq_pricedReceipt i m price tariff hc w a z hw,
        nativeObservation_project i m w a z hw,
        ih _ _ (nativeStep_aligned i m w a z hw),
        nativeStep_project i m w a z hw]
      simp only [hnext, hobs]

/-- This legal table repairs root0, then idles root0, then dispatches child1.
No lookup of hidden existence or ancestry is granted to the table. -/
def backupTable : Table Act Obs 3 :=
  .node (some (false, some true)) (fun _ =>
    .node (some (false, none)) (fun _ =>
      .node (some (true, none)) (fun _ => .halt)))

def damagedFounder : NativeWorld Unit 1 := ⟨(), initialStore true false, false⟩

def backupTape (l0 l1 l2 : Bool) : Fin 3 → Noise :=
  ![(true, l0), (false, l1), (true, l2)]

/-- The first actual birth occupies address1. A real fault leaves address2
empty. Dispatching actual child1 produces grandchild3 with the copied source
program, real birth history and timestamped owner extension. Root0 retains its
original owner. Labels may be equal; freshness comes from the original allocator. -/
theorem backup_population_identity (tariff : NNReal) (l0 l1 l2 : Bool) :
    let s := (nativeExecute (0 : Fin 1) ⟨true, tariff⟩ backupTable damagedFounder
      (backupTape l0 l1 l2)).finalWorld.store
    s.length = 4 ∧
      (RegisterPopulationHistorySource.lookup s 0).map (fun p => p.identity) = some [(0,false)] ∧
      RegisterPopulationHistorySource.lookup s 2 = none ∧
      (RegisterPopulationHistorySource.lookup s 3).map (fun p => p.identity) =
        some [(0,false), (1,l0), (3,l2)] ∧
      (RegisterPopulationHistorySource.lookup s 3).map (fun p => p.organism.history) = some [l0,l2] ∧
      (RegisterPopulationHistorySource.lookup s 3).map (fun p => p.organism.program) = some true ∧
      (RegisterPopulationHistorySource.lookup s 1).map (fun p => p.clock) = some 4 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem backup_legal_receipts (tariff : NNReal) (l0 l1 l2 : Bool) :
    (nativeExecute (0 : Fin 1) ⟨true, tariff⟩ backupTable damagedFounder
      (backupTape l0 l1 l2)).history =
      [(some (false, some true), (true,true)), (some (false, none), (false,false)),
        (some (true, none), (true,false))] := by
  rw [native_history_eq (0 : Fin 1) ⟨true, tariff⟩ backupTable damagedFounder
    (backupTape l0 l1 l2) (initial_aligned true false)]
  rfl

/-- If the earlier birth fails, the identical later child-address request is
handled by the original dispatcher as None. The failed record is not removed,
and its clock position still contributes to the length of the actual Store. -/
theorem invalid_child_dispatch_kept (tariff : NNReal) (l0 l1 l2 : Bool) :
    let x := nativeExecute (0 : Fin 1) ⟨true, tariff⟩ backupTable damagedFounder
      ![(false,l0), (false,l1), (true,l2)]
    x.finalWorld.store.length = 4 ∧ x.records[2]? = some none ∧
      RegisterPopulationHistorySource.lookup x.finalWorld.store 3 = none := by
  exact ⟨rfl, rfl, rfl⟩

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionNativeLaw
