import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterSemanticInstructionInfinite

/-!
Original promise: actual P9 repairability needs a damaged-state return source, beyond interpreter target preservation.
Existing result: semantic synthesis returns the SAME coarse AST and preserves full records/validity; ValidProgram alone admits idle forever outside target.
Reduced premise: compute actual interpreter/update restoration truth table, derive original dynamics implementation, recovery basin and P9 repairability for that actual returned AST.
Model/witness: original finite Bool registers/one allowed write port and protected Bool target; nested repair and paid always-write restore, while idle remains damaged.
Consumer/boundary: original RepairProgramRecoverableAt/eventual-permanent recovery and P9 on the executable restoration-checked family; actual recurring faults remain in complete records, not erased.

No AST is installed into the protected Bool source or reconstructed from a
physical seed. Instruction is the existing external controller evaluated by the
same trusted interpreter. Restoration check is computed over its actual finite
truth table; no desired implementation/recovery/preservation field is input.
The original no-fault stationary recovery consumer and fault-inclusive literal
record conclusions are distinguished. Recovery is not price optimality, free
resource supply, all six P9 properties, or split/merge semantics.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterInstructionRecoveryScale
open Set MeasureTheory ProbabilityTheory
open UEOT.V3.ViabilityKernel UEOT.V3.ViabilityTrajectory
open UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.Objecthood UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultJointRecord
open RegisterActuatorScaleSource RegisterInstructionScaleSource RegisterSemanticInstructionScale
open scoped ENNReal

local instance {d : ℕ} : MeasurableSpace (ModeRecord d) := ⊤
local instance {d : ℕ} : MeasurableSingletonClass (ModeRecord d) := ⟨fun _ => trivial⟩

/-- Check the submitted program's real update, not its syntax or a supplied
recovery specification. True means it restores target from EVERY state. -/
def restorationCheck {n : ℕ} (i : Fin n) (b : Bool) (p : Instruction n) : Bool :=
  decide (∀ x : State n, update i x (interpret p x) i=b)

theorem restorationCheck_iff {n : ℕ} (i : Fin n) (b : Bool) (p : Instruction n) :
    restorationCheck i b p=true ↔ ∀ x : State n, update i x (interpret p x) i=b := by
  simp only [restorationCheck,decide_eq_true_eq]

/-- A passed real update check gives the SAME full physical state transition
as a reliable target write, including every unchanged passive register. -/
theorem checked_update_eq_write {n : ℕ} (i : Fin n) (b : Bool) (p : Instruction n)
    (hc : restorationCheck i b p=true) (x : State n) :
    update i x (interpret p x)=update i x (some b) := by
  ext j
  by_cases hj : j=i
  · subst j
    simpa [update,Function.update_apply] using (restorationCheck_iff i b p).mp hc x
  · rw [other_register_unchanged i j hj,other_register_unchanged i j hj]

/-- THIS external literal program implements the original repair/preserve
physical dynamics. Its action labels/paid costs need not equal compiled idle. -/
theorem actual_dynamics_implements {n : ℕ} (i : Fin n) (b : Bool) (p : Instruction n)
    (hc : restorationCheck i b p=true) :
    RepairProgramDynamicsImplementsPolicy (instructionSubstrate n) (physical i) p
      (repairThenPreservePolicy (physical i) (target i b) (target_fixed i b) (repair i b)) := by
  intro x
  change physical i x (interpret p x)=_
  have hcomp : update i x ((substrate i).execute b x)=update i x (some b) := by
    by_cases hx : x i=b
    · simp only [execute_compiled,if_pos hx,update]
      ext j
      by_cases hj : j=i
      · subst j; simpa [Function.update_apply] using hx
      · simp [Function.update_of_ne hj]
    · simp [execute_compiled,hx]
  calc
    physical i x (interpret p x)=physical i x ((substrate i).execute b x) := by
      unfold physical
      rw [checked_update_eq_write i b p hc x,hcomp]
    _ = _ := compiled_dynamics_implements i b x

/-- Target preservation is DERIVED and is weaker than the checked restoration. -/
theorem actual_valid {n : ℕ} (i : Fin n) (b : Bool) (p : Instruction n)
    (hc : restorationCheck i b p=true) : ValidProgram i b p :=
  repairProgramValid_of_dynamicsImplements_repairThenPreserve (instructionSubstrate n)
    (physical i) (target i b) (target_fixed i b) (repair i b) p (actual_dynamics_implements i b p hc)

noncomputable section
variable {n : ℕ} [MeasurableSpace (State n)] [MeasurableSingletonClass (State n)]

/-- Original program-specific expected-hitting basin for THIS checked p,
from every actual physical state, rather than another chosen repair program. -/
theorem actual_recoverable (i : Fin n) (b : Bool) (p : Instruction n)
    (hc : restorationCheck i b p=true) (x : State n) :
    RepairProgramRecoverableAt (instructionSubstrate n) (physical i) (target i b) p x := by
  have hx : x∈(certificate i b).basin := by
    change (if x i=b then (0 : ℝ≥0∞) else 1)≠∞
    split_ifs <;> simp
  exact repairProgramRecoverableAt_of_dynamicsImplements_repairThenPreserve
    (instructionSubstrate n) (physical i) (target i b) (target_fixed i b) (repair i b) p
    (actual_dynamics_implements i b p hc) ((certificate i b).expectedHittingTime_ne_top_of_mem_basin hx)

/-- Original stationary/no-fault physical execution of the SAME p eventually
and permanently reaches target. Recurring external faults are not suppressed. -/
theorem actual_eventually_always (i : Fin n) (b : Bool) (p : Instruction n)
    (hc : restorationCheck i b p=true) (x : State n) :
    ∀ᵐ w ∂stationaryTrajMeasure (physical i) (interpret p) (PMF.pure x),
      ∃ N : ℕ, ∀ t≥N, w t∈target i b :=
  reconstructedProgram_eventually_always_target_ae (instructionSubstrate n) (physical i) (target i b)
    (actual_valid i b p hc) (actual_recoverable i b p hc x)

omit [MeasurableSpace (State n)] [MeasurableSingletonClass (State n)] in
/-- Semantic synthesis preserves the actual restoration check in BOTH
directions, by actual action/update transport and the registered representative. -/
theorem returned_restoration_iff (i : Fin n) (b : Bool) (p : Instruction n) (q : Instruction 1)
    (hs : synthesize i p=some q) : restorationCheck i b p=true ↔ restorationCheck (0 : Fin 1) b q=true := by
  rw [restorationCheck_iff,restorationCheck_iff]
  constructor
  · intro h y
    have hp:=h (representative i y)
    have he:=active_update i (representative i y) (interpret p (representative i y))
    have ha : interpret q y=interpret p (representative i y) := by
      simpa using (synthesize_actual i p q hs).2 (representative i y)
    rw [representative_project,←ha] at he
    rw [←ha] at hp
    exact he.trans hp
  · intro h x
    have hp:=h (projectState i x)
    rw [(synthesize_actual i p q hs).2 x,active_update] at hp
    exact hp

/-- The actual accepted pair additionally passes an executable physical
restoration test; this is not a caller-supplied recovery certificate. -/
abbrev RecoveringPair (i : Fin n) (b : Bool) :=
  {pq : Accepted i // restorationCheck i b pq.val.1=true}

def recoveryScale (i : Fin n) (b : Bool) :
    ObjectScaleMap (State n) (State 1) (RecoveringPair i b) (Instruction 1) :=
  ⟨projectState i,fun pq => pq.val.val.2⟩

def RecoversEverywhere (i : Fin n) (b : Bool) (p : Instruction n) : Prop :=
  ∀ x, RepairProgramRecoverableAt (instructionSubstrate n) (physical i) (target i b) p x

/-- Original P9 repairability preservation is DERIVED on this computationally
admitted family; the object-scale map carries no hpres field. -/
theorem actual_preserves_repairability (i : Fin n) (b : Bool) :
    PreservesRepairability (recoveryScale i b)
      (fun pq => RecoversEverywhere i b pq.val.val.1) (RecoversEverywhere (0 : Fin 1) b) := by
  intro pq _ x
  exact actual_recoverable 0 b _ ((returned_restoration_iff i b _ _ pq.val.property).mp pq.property) x

/-- ORIGINAL P9 now actually transports original program recovery semantics
for the SAME checked p and SAME synthesized q, with no external hpres/basin. -/
theorem p9_actual_returned_recovery (i : Fin n) (b : Bool) (pq : RecoveringPair i b) :
    RecoversEverywhere (0 : Fin 1) b pq.val.val.2 :=
  transport_object_property (recoveryScale i b)
    (fun r => RecoversEverywhere i b r.val.val.1) (RecoversEverywhere (0 : Fin 1) b)
    rfl (actual_preserves_repairability i b) (actual_recoverable i b _ pq.property)

omit [MeasurableSpace (State n)] [MeasurableSingletonClass (State n)] in
/-- In the original fault-inclusive mechanism, every real repair-mode step
restores THIS target, while every real fault-mode step damages it. -/
theorem actual_fault_repair_boundary (i : Fin n) (b : Bool) (cost : NNReal) (p : Instruction n)
    (hc : restorationCheck i b p=true) (o : Organism n) (mode label : Bool) :
    (modeRecordStep i ⟨b,cost⟩ o (interpret p o.physical) mode label).transaction.parentAfter.physical i=b ↔ mode=true := by
  cases mode
  · cases b <;> simp [modeRecordStep]
  · simpa only [modeRecordStep,if_true,RegisterJointRecord.recordStep] using
      (show update i o.physical (interpret p o.physical) i=b ↔ True from
        iff_true_intro ((restorationCheck_iff i b p).mp hc o.physical))

omit [MeasurableSpace (State n)] [MeasurableSingletonClass (State n)] in
/-- SAME actual retained-parent run, including every failed/fault record.
Permanence is not asserted if the primitive stream keeps producing faults. -/
theorem actual_stream_legitimacy (i : Fin n) (b : Bool) (cost : NNReal) (p : Instruction n)
    (hc : restorationCheck i b p=true) (o : Organism n) (hp : o.program=b)
    (w : RegisterSemanticInstructionInfinite.Stream) (t : ℕ) :
    Legitimate i (RegisterSemanticInstructionInfinite.parentAt i ⟨b,cost⟩ p o w (t+1)) ↔ (w t).1=true := by
  unfold Legitimate
  rw [RegisterSemanticInstructionInfinite.actual_protected_program,hp,
    RegisterSemanticInstructionInfinite.parentAt_succ]
  exact actual_fault_repair_boundary i b cost p hc _ (w t).1 (w t).2

omit [MeasurableSpace (State n)] [MeasurableSingletonClass (State n)] in
/-- The positive family includes an actual always-paid write, not just the
old compiled action labels. -/
theorem always_write_restores (i : Fin n) (b : Bool) : restorationCheck i b (.emit (some b))=true := by
  simp [restorationCheck_iff,interpret,update]

theorem benign_restores : restorationCheck (0 : Fin 2) true benignHidden=true := by
  rw [restorationCheck_iff]
  intro x
  cases hx : x 0 <;> simp [benignHidden,nestedRepair,interpret,hx,update]

/-- Native recovery semantics and literal countable records use the SAME
actual benignHidden p and SAME synthesized q; no new program is selected. -/
theorem benign_actual_recovery (μ : Measure RegisterSemanticInstructionInfinite.Stream) :
    RecoversEverywhere (0 : Fin 1) true (compile 0 true) ∧
    (RegisterSemanticInstructionInfinite.recordPathLaw (0 : Fin 2) ⟨true,1⟩ benignHidden
      (passiveInitial true) μ).map (RegisterSemanticInstructionInfinite.projectPath 0)=
        RegisterSemanticInstructionInfinite.recordPathLaw (0 : Fin 1) ⟨true,1⟩ (compile 0 true)
          (projectOrganism 0 (passiveInitial true)) μ := by
  let pq : RecoveringPair (0 : Fin 2) true :=
    ⟨⟨(benignHidden,compile 0 true),benign_static_rejects_semantic_accepts.2⟩,benign_restores⟩
  exact ⟨p9_actual_returned_recovery 0 true pq,
    RegisterSemanticInstructionInfinite.actual_countable_path_law 0 ⟨true,1⟩ _ _
      benign_static_rejects_semantic_accepts.2 _ μ⟩

omit [MeasurableSpace (State n)] [MeasurableSingletonClass (State n)] in
/-- Strict old-validity boundary: idle preserves an intact target, passes
semantic synthesis, but fails the executable restoration check. -/
theorem idle_valid_not_restoring (i : Fin n) (b : Bool) :
    ValidProgram i b (.emit none) ∧ restorationCheck i b (.emit none)=false := by
  constructor
  · simp [ValidProgram,RepairProgramValid,PreservingController,StaysIn,
      instructionSubstrate,interpret,physical,update,PMF.support_pure]
  · apply Bool.eq_false_iff.mpr
    intro h
    have hbad:=(restorationCheck_iff i b (.emit none)).mp h (fun _=>!b)
    cases b <;> simp [interpret,update] at hbad

omit [MeasurableSpace (State n)] [MeasurableSingletonClass (State n)] in
/-- Actual endless repair opportunities still do not help THIS idle program:
its damaged retained parent is literally unchanged at every time. -/
theorem idle_parent_unchanged (i : Fin n) (b : Bool) (cost : NNReal) (o : Organism n)
    (w : RegisterSemanticInstructionInfinite.Stream) (hw : ∀ t,(w t).1=true) (t : ℕ) :
    RegisterSemanticInstructionInfinite.parentAt i ⟨b,cost⟩ (.emit none) o w t=o := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [RegisterSemanticInstructionInfinite.parentAt_succ]
    simp only [RegisterSemanticInstructionInfinite.recordAt,ih,interpret,hw,modeRecordStep,if_true,
      RegisterJointRecord.recordStep,update]

omit [MeasurableSpace (State n)] [MeasurableSingletonClass (State n)] in
theorem idle_actual_never_recovers (i : Fin n) (cost : NNReal)
    (w : RegisterSemanticInstructionInfinite.Stream) (hw : ∀ t,(w t).1=true) :
    ∀ t, ¬ Legitimate i (RegisterSemanticInstructionInfinite.parentAt i ⟨true,cost⟩ (.emit none)
      (⟨[],fun _=>false,true⟩ : Organism n) w t) := by
  intro t
  rw [idle_parent_unchanged i true cost _ w hw]
  simp [Legitimate]

/-- Dynamics-level recovery equivalence does NOT erase actual action/fee
semantics. Always-write and compiled-idle on an intact seed pay differently. -/
theorem same_recovery_different_fee :
    let o : Organism 1 := ⟨[],fun _=>true,true⟩
    physical (0 : Fin 1) o.physical (interpret (.emit (some true)) o.physical)=
      physical 0 o.physical (interpret (compile 0 true) o.physical) ∧
    (modeRecordStep 0 ⟨true,1⟩ o (interpret (.emit (some true)) o.physical) true false).transaction.expenditure=1 ∧
    (modeRecordStep 0 ⟨true,1⟩ o (interpret (compile 0 true) o.physical) true false).transaction.expenditure=0 := by
  norm_num [physical,interpret,compile,update,modeRecordStep,RegisterJointRecord.recordStep,cost]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterInstructionRecoveryScale
