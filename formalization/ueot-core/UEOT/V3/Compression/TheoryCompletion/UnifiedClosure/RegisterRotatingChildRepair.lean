import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterRotatingBodyReturns
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RepairProgramSafeControlBridge

/-!
Original promise: an actually copied organism has an executed repair basin and a parent/identity bridge, rather than an externally replaced legitimate seed.
Existing hypotheses: registered Fin n sweep, original Option Bool compiler, protected program, literal ModeRecordStep and original mode/label source; old P5 uses a SINGLE stationary physical port.
Reduced premise: derive the actual child's inherited program/history, all-repair-cycle full-body recovery, and SAME-child continuation; derive each phase's full-body program validity and native safe-control/P5 consumers.
Model/boundary: continuation runs the ALREADY registered sweep on the actual child at a round boundary; no reset, installation, new observation/action/resource, population scheduler or global identifier is supplied. Local birth remains weaker than full-body birth.
Consumer: original P8 distinguishes this same-child repair from reproduction; original P5 consumes the repaired literal seed at every port, and original SafeControl consumes its full-body validity on the actual repair-mode kernel.

The n transactions, including writes/fees/failures and intermediate births,
are exactly roundTrace; the final organism is roundParent, not a chosen seed.
All-repair is a source event, NOT a claim of permanent full-body safety under
positive faults. Fresh future rounds have the original registered law. Their
independence from a previous birth is a separate source registration, not a
conditioning/retry on successful bodies. The single-port P5 systems below form
a family: none is falsely called the time-varying full-body recovery system.
List Bool is the existing readable birth-history identity; repeated labels do
not give globally fresh concurrent IDs.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterRotatingChildRepair
open MeasureTheory Set ProbabilityTheory
open UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.Objecthood UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open UEOT.V3.Compression.Objecthood.JointHomeostasis UEOT.V3.Compression.Objecthood.OntogeneticConstruction
open UEOT.V3.ViabilityKernel UEOT.V3.FiniteDiscountedControl
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultJointRecord
open RegisterFaultSource RegisterRotatingBodySource
open scoped ENNReal
noncomputable section

/-- Literal successful old birth, with the executed parent retained. -/
theorem actual_child_provenance {n : ℕ} (b : Bool) (fee : NNReal)
    (raw : RoundRaw n) (o : Organism n) (hp : o.program=b)
    (ports : List (Fin n)) (r : ModeRecord n) (hr : r∈tracePorts b fee raw o ports)
    (child : Organism n) (hc : r.transaction.child=some child) :
    ∃ i : Fin n, child.program=b ∧
      (lineage i).OffspringOf r.transaction.parentAfter child ∧
      child.history=r.transaction.parentAfter.history++[(raw i).2] ∧
      r.transaction.parentAfter.history=o.history ∧
      child.history.dropLast=o.history := by
  obtain ⟨i,parent,he,hp',hh⟩:=actual_record_origin b fee raw o ports r hr
  subst r
  have hx:=actual_child_requires_repair i ⟨b,fee⟩ parent child
    ((substrate i).execute b parent.physical) (raw i).1 (raw i).2 hc
  have hs:=RegisterJointRecord.record_child_source i ⟨b,fee⟩ parent
    ((substrate i).execute b parent.physical) (raw i).2 child hx.2
  have hparent : (transaction i b fee parent (raw i)).transaction.parentAfter.history=o.history :=
    (transaction_history i b fee parent _).trans hh
  have hb : child.history=(transaction i b fee parent (raw i)).transaction.parentAfter.history++[(raw i).2] := by
    rw [hs.1]
    simp only [transaction, hx.1, modeRecordStep, if_true]
    rfl
  refine ⟨i,hs.2.2.trans (hp'.trans hp),?_,hb,hparent,?_⟩
  · simpa only [transaction,hx.1,modeRecordStep,if_true] using hs.2.1
  · rw [hb,hparent]
    simp

/-- Actual finite all-repair execution restores every coordinate, while
preserving the same child's code and readable identity. -/
theorem actual_cycle_repairs {n : ℕ} (b : Bool) (fee : NNReal)
    (future : RoundRaw n) (child : Organism n) (hg : ∀i,(future i).1=true) :
    BodyGoal b (roundParent b fee future child).physical ∧
    (roundParent b fee future child).program=child.program ∧
    (roundParent b fee future child).history=child.history ∧
    (roundTrace b fee future child).length=n := by
  exact ⟨(actual_round_goal_iff b fee future child).mpr hg,
    runPorts_program b fee future child _,runPorts_history b fee future child _,by simp [roundTrace]⟩

/-- P8 classifies the actual n-step restoration as this SAME child, not an
additional offspring; this holds even for failed future modes. -/
theorem actual_cycle_same_child {n : ℕ} (i : Fin n) (b : Bool) (fee : NNReal)
    (future : RoundRaw n) (child : Organism n) :
    (lineage i).SameObject child (roundParent b fee future child) ∧
    ¬(lineage i).OffspringOf child (roundParent b fee future child) := by
  have hh : (lineage i).SameObject child (roundParent b fee future child) :=
    (runPorts_history b fee future child _).symm
  exact ⟨hh,LineageSemantics.sameObjectRepair_not_offspring _ hh⟩

/-- Actual same-child repair never changes the preceding birth's parent
history prefix. This is provenance, not a global parent-ID uniqueness claim. -/
theorem repaired_child_parent_history {n : ℕ} (b : Bool) (fee : NNReal)
    (raw future : RoundRaw n) (o : Organism n) (hp : o.program=b)
    (ports : List (Fin n)) (r : ModeRecord n) (hr : r∈tracePorts b fee raw o ports)
    (child : Organism n) (hc : r.transaction.child=some child) :
    (roundParent b fee future child).program=b ∧
    (roundParent b fee future child).history.dropLast=o.history := by
  obtain ⟨_,hp',_,_,_,hh⟩:=actual_child_provenance b fee raw o hp ports r hr child hc
  simpa only [roundParent,runPorts_program,runPorts_history] using And.intro hp' hh

/-- The exact future success law applies to the literal inherited child,
including children born with a damaged passive port. -/
theorem actual_child_cycle_probability {n : ℕ} (b : Bool) (fee : NNReal)
    (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) (child : Organism n) :
    roundLaw n noise epsilon he {future | BodyGoal b (roundParent b fee future child).physical}=
      ((1-epsilon : NNReal) : ℝ≥0∞)^n :=
  actual_body_probability b fee noise epsilon he child

/-- The original infinite raw source repairs this actual inherited child
repeatedly, with its copied program and original birth provenance intact.
There is no successful-body resampling or replacement of the initial child. -/
theorem actual_child_returns_same_identity {n : ℕ} (b : Bool) (fee : NNReal)
    (raw : RoundRaw n) (o : Organism n) (hp : o.program=b)
    (ports : List (Fin n)) (r : ModeRecord n) (hr : r∈tracePorts b fee raw o ports)
    (child : Organism n) (hc : r.transaction.child=some child)
    (noise : PMF Bool) (epsilon : NNReal) (he : epsilon<1) :
    ∀ᵐ w ∂ RegisterRotatingBodyReturns.infiniteLaw n noise epsilon he.le,
      ∀N : ℕ,∃k≥N,
        BodyGoal b (RegisterRotatingBodyReturns.parentAt b fee child w (k+1)).physical ∧
        (RegisterRotatingBodyReturns.parentAt b fee child w (k+1)).program=b ∧
        (RegisterRotatingBodyReturns.parentAt b fee child w (k+1)).history=child.history ∧
        (RegisterRotatingBodyReturns.parentAt b fee child w (k+1)).history.dropLast=o.history := by
  obtain ⟨_,hp',_,_,_,hh⟩:=actual_child_provenance b fee raw o hp ports r hr child hc
  filter_upwards [RegisterRotatingBodyReturns.actual_returns_forever b fee noise epsilon he child] with w hw
  intro N
  obtain ⟨k,hk,hgood⟩:=hw N
  refine ⟨k,hk,hgood,?_,?_,?_⟩
  · simpa only [RegisterRotatingBodyReturns.parent_program] using hp'
  · exact RegisterRotatingBodyReturns.parent_history b fee child w (k+1)
  · simpa only [RegisterRotatingBodyReturns.parent_history] using hh

/-- Full-body validity is DERIVED from the executable compiler on each
actual repair-mode port, rather than supplied as an independent predicate. -/
theorem actual_body_valid {n : ℕ} (i : Fin n) (b : Bool) :
    RepairProgramValid (substrate i) (physical i) {x | BodyGoal b x} b := by
  intro x hx y hy
  have hi : x i=b := hx i
  have he : (substrate i).execute b x=none := by simp [execute_compiled,hi]
  have hy' : y=x := by
    simpa only [he,physical,update,PMF.support_pure,Set.mem_singleton_iff] using hy
  exact hy' ▸ hx

/-- The native control row is the original physical PMF, not a newly chosen
source with a desired invariant. Evaluation parameters do not change it. -/
theorem actual_model_row {n : ℕ} (i : Fin n) (noise : PMF Bool) (price : NNReal)
    (d : ℝ) (hd : 0<d ∧ d<1) (m : Mechanism) (x : State n) (a : Action) :
    (model i noise price d hd m).transitionPMF x a=physical i x a := by
  ext y
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [Model.transitionPMF_apply_toReal,model_transition_eq_physical]

theorem actual_body_model_valid {n : ℕ} (i : Fin n) (b : Bool)
    (noise : PMF Bool) (price : NNReal) (d : ℝ) (hd : 0<d ∧ d<1) (m : Mechanism) :
    RepairProgramValid (substrate i)
      (fun x a=>(model i noise price d hd m).transitionPMF x a) {x | BodyGoal b x} b := by
  simpa only [actual_model_row] using actual_body_valid i b

/-- The original autonomous program/safe-control consumer, now at EVERY
registered phase, for the SAME actually repaired body. This concerns repair
mode; physical fault safety was not silently strengthened to permanent BodyGoal. -/
theorem actual_cycle_source_and_joint_safety {n : ℕ} (i : Fin n) (b : Bool)
    (fee : NNReal) (future : RoundRaw n) (child : Organism n) (hg : ∀j,(future j).1=true)
    (noise : PMF Bool) (price : NNReal) (d : ℝ) (hd : 0<d ∧ d<1) :
    let M:=model i noise price d hd ⟨b,fee⟩
    let K : Set (State n):={x | BodyGoal b x}
    let hv:=actual_body_model_valid i b noise price d hd ⟨b,fee⟩
    let x:=(roundParent b fee future child).physical
    StaysIn (M.transitionPMF x (recoveredProgramSourceSafeAction M K (substrate i) b hv x).1) K ∧
      StaysIn (jointRepairKernel (substrate i) (fun x a=>M.transitionPMF x a)
        (restoredJointState (substrate i) b x)) (RecoveredJointTarget (substrate i) K b) := by
  exact reconstructed_program_joint_and_source_safety _ _ _ _ _ _
    (actual_cycle_repairs b fee future child hg).1

section LocalP5
variable {n : ℕ} [MeasurableSpace (State n)] [MeasurableSingletonClass (State n)]

/-- Original P5 gets the ACTUAL repaired child's physical state and copied
program. Its old fixed-port contract applies separately at every phase. -/
theorem repaired_actual_child_enters_p5 (b : Bool) (fee : NNReal)
    (raw future : RoundRaw n) (o : Organism n) (hp : o.program=b)
    (ports : List (Fin n)) (r : ModeRecord n) (hr : r∈tracePorts b fee raw o ports)
    (child : Organism n) (hc : r.transaction.child=some child) (hg : ∀j,(future j).1=true)
    (i : Fin n) (epsilon : NNReal) (he : epsilon≤1) :
    let repaired:=roundParent b fee future child
    let seed : OntogeneticSeed (State n) Bool:=⟨repaired.physical,repaired.program⟩
    let S:=finiteJointRecurrentHomeostasisSystem
      (physical i) (target i b) (target_fixed i b) (certificate i b)
      (substrate i) codec b (compiled_dynamics_implements i b)
      (fault i) epsilon he (actual_fault_envelope i b)
    StaysIn (PMF.pure (assembleRepairOrganization (substrate i) codec seed)) S.carrier := by
  have hprogram:=(repaired_child_parent_history b fee raw future o hp ports r hr child hc).1
  dsimp only
  rw [hprogram]
  exact assembled_enters_actual_fault_system i b _
    ((actual_cycle_repairs b fee future child hg).1 i) epsilon he
end LocalP5

/-- Exact static-interface limitation: a fixed port cannot repair a damaged
different coordinate by ANY original allowed action. Rotating recovery above
therefore cannot be justified by substituting BodyGoal into the old local P5. -/
theorem fixed_port_passive_damage {n : ℕ} (i j : Fin n) (hji : j≠i)
    (b : Bool) (x : State n) (hx : x j≠b) (a : Action) :
    ¬BodyGoal b (update i x a) := by
  intro h
  apply hx
  have hj:=h j
  cases a <;> simpa [RegisterRepairSource.update,hji] using hj

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterRotatingChildRepair
