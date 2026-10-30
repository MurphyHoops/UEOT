import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterInstructionGOASource
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterBirthMaintenance
import Mathlib.MeasureTheory.Constructions.Pi

/-!
Original promise: C4 time-dependent mechanism/recovery must follow actual program execution and retain failed births, paid actions and parent provenance.
Existing result: single FIXED port actual ModeRecordStep/compiler/P5 are available; they do not imply whole-body recovery under a changing physical port.
Reduced premise: execute a pre-registered Fin n port sweep using the SAME original Option Bool action, derive every final body coordinate and exact full-body probability from actual independent old primitive draws.
New model/boundary: environment clock fixes List.finRange n per round, SAME parent/history/protected target and original mode/label laws; BodyGoal means ALL ports equal b, explicitly DIFFERENT from old single-port Legitimate.
Consumer: actual full transaction trace/law, nonzero-noise full-body source and actual born-child/local-P5 boundary; ongoing round return/P10 tails and phase-aware C4 continuation are subsequent source obligations.

The port schedule is new deterministic time dependence of the environment,
NOT a new selectable action. The controller still sees the old full physical
register state and the registered clock; no current-port-only observation is
silently upgraded. No reset, installation, initial preparation, energy port,
sampling or old dataset/threshold change occurs. n=0 executes zero transactions:
its empty BodyGoal is vacuous, not physical ongoing maintenance or a birth.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterRotatingBodySource
open MeasureTheory ProbabilityTheory Set
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultJointRecord
open RegisterInstructionPurposeScale RegisterInstructionRecoveryScale RegisterInstructionGOASource
open RegisterInstructionHomeostasis RegisterFaultFinitePurposeProbe
open scoped ENNReal BigOperators
noncomputable section

abbrev RoundRaw (n : ℕ) := Fin n → Bool × Bool

def BodyGoal {n : ℕ} (b : Bool) (x : State n) : Prop := ∀ j,x j=b

/-- Actual old allowed action and actual old transaction at this registered
clock port. Modes/labels are source outcomes, not controller observations. -/
def transaction {n : ℕ} (i : Fin n) (b : Bool) (cost : NNReal)
    (o : Organism n) (z : Bool × Bool) : ModeRecord n :=
  modeRecordStep i ⟨b,cost⟩ o ((substrate i).execute b o.physical) z.1 z.2

def runPorts {n : ℕ} (b : Bool) (cost : NNReal) (raw : RoundRaw n) : Organism n → List (Fin n) → Organism n
  | o,[] => o
  | o,i::ports => runPorts b cost raw (transaction i b cost o (raw i)).transaction.parentAfter ports

def tracePorts {n : ℕ} (b : Bool) (cost : NNReal) (raw : RoundRaw n) : Organism n → List (Fin n) → List (ModeRecord n)
  | _,[] => []
  | o,i::ports => transaction i b cost o (raw i) ::
      tracePorts b cost raw (transaction i b cost o (raw i)).transaction.parentAfter ports

def roundParent {n : ℕ} (b : Bool) (cost : NNReal) (raw : RoundRaw n) (o : Organism n) : Organism n :=
  runPorts b cost raw o (List.finRange n)

def roundTrace {n : ℕ} (b : Bool) (cost : NNReal) (raw : RoundRaw n) (o : Organism n) : List (ModeRecord n) :=
  tracePorts b cost raw o (List.finRange n)

@[simp] theorem transaction_physical {n : ℕ} (i : Fin n) (b : Bool) (cost : NNReal)
    (o : Organism n) (z : Bool × Bool) :
    (transaction i b cost o z).transaction.parentAfter.physical=
      Function.update o.physical i (if z.1 then b else !b) := by
  rw [transaction,step_physical]
  exact actual_mode_next i ⟨b,cost⟩ (compile i b) (actual_compiled_restores i b) o.physical z.1

@[simp] theorem transaction_program {n : ℕ} (i : Fin n) (b : Bool) (cost : NNReal)
    (o : Organism n) (z : Bool × Bool) : (transaction i b cost o z).transaction.parentAfter.program=o.program :=
  step_program _ _ _ _ _ _

@[simp] theorem transaction_history {n : ℕ} (i : Fin n) (b : Bool) (cost : NNReal)
    (o : Organism n) (z : Bool × Bool) : (transaction i b cost o z).transaction.parentAfter.history=o.history :=
  step_history _ _ _ _ _ _

/-- Actual coordinate reset for the executed list. The actual registered list
below has every port exactly once; this proof does not replace execution by a
chosen desired state or omit failed modes. -/
theorem runPorts_physical {n : ℕ} (b : Bool) (cost : NNReal) (raw : RoundRaw n)
    (o : Organism n) (ports : List (Fin n)) (j : Fin n) :
    (runPorts b cost raw o ports).physical j=
      if j∈ports then (if (raw j).1 then b else !b) else o.physical j := by
  induction ports generalizing o with
  | nil => rfl
  | cons i ports ih =>
    rw [runPorts,ih]
    by_cases hj : j∈ports
    · simp only [List.mem_cons,hj,or_true,if_true]
    · simp only [List.mem_cons,hj,or_false,if_false,transaction_physical]
      by_cases hji : j=i
      · subst j; simp
      · simp [hji]

@[simp] theorem round_physical {n : ℕ} (b : Bool) (cost : NNReal) (raw : RoundRaw n) (o : Organism n) (j : Fin n) :
    (roundParent b cost raw o).physical j=(if (raw j).1 then b else !b) := by
  simpa only [roundParent,List.mem_finRange,if_true] using runPorts_physical b cost raw o (List.finRange n) j

@[simp] theorem runPorts_program {n : ℕ} (b : Bool) (cost : NNReal) (raw : RoundRaw n) (o : Organism n) (ports : List (Fin n)) :
    (runPorts b cost raw o ports).program=o.program := by
  induction ports generalizing o with
  | nil => rfl
  | cons i ports ih => rw [runPorts,ih,transaction_program]

@[simp] theorem runPorts_history {n : ℕ} (b : Bool) (cost : NNReal) (raw : RoundRaw n) (o : Organism n) (ports : List (Fin n)) :
    (runPorts b cost raw o ports).history=o.history := by
  induction ports generalizing o with
  | nil => rfl
  | cons i ports ih => rw [runPorts,ih,transaction_history]

@[simp] theorem trace_length {n : ℕ} (b : Bool) (cost : NNReal) (raw : RoundRaw n) (o : Organism n) (ports : List (Fin n)) :
    (tracePorts b cost raw o ports).length=ports.length := by
  induction ports generalizing o with
  | nil => rfl
  | cons i ports ih => simp only [tracePorts,List.length_cons,ih]

theorem actual_registration (n : ℕ) : (List.finRange n).Nodup ∧ (List.finRange n).length=n := by
  exact ⟨List.nodup_finRange n,by simp⟩

/-- Actual whole-body goal iff ALL actual repair modes in this round succeed.
This is a derived event equality, not an old single-port safety redefinition. -/
theorem actual_round_goal_iff {n : ℕ} (b : Bool) (cost : NNReal) (raw : RoundRaw n) (o : Organism n) :
    BodyGoal b (roundParent b cost raw o).physical ↔ ∀j,(raw j).1=true := by
  unfold BodyGoal
  simp only [round_physical]
  constructor
  · intro h j
    have hh:=h j
    cases hb : b <;> cases hm : (raw j).1 <;> simp [hb,hm] at hh ⊢
  · intro h j
    simp [h j]

/-- Complete raw round: n independent original mode/label draws, no retry or
success filtering. The labels remain in every actual complete trace. -/
def roundLaw (n : ℕ) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) : Measure (RoundRaw n) :=
  Measure.pi (fun _ : Fin n => (primitiveLaw noise epsilon he).toMeasure)

instance roundLaw_probability (n : ℕ) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) :
    IsProbabilityMeasure (roundLaw n noise epsilon he) := by unfold roundLaw; infer_instance

local instance {n : ℕ} : MeasurableSpace (ModeRecord n) := ⊤
local instance {n : ℕ} : MeasurableSpace (List (ModeRecord n)) := ⊤
local instance {n : ℕ} : MeasurableSingletonClass (ModeRecord n) := ⟨fun _ => trivial⟩

def roundRecordLaw {n : ℕ} (b : Bool) (cost : NNReal) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) (o : Organism n) :
    Measure (List (ModeRecord n)) := (roundLaw n noise epsilon he).map (fun raw=>roundTrace b cost raw o)

instance roundRecordLaw_probability {n : ℕ} (b : Bool) (cost : NNReal) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) (o : Organism n) :
    IsProbabilityMeasure (roundRecordLaw b cost noise epsilon he o) :=
  Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

theorem actual_complete_body_law {n : ℕ} (b : Bool) (cost : NNReal) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) (o : Organism n) :
    (roundLaw n noise epsilon he).map (fun raw=>(roundParent b cost raw o).physical)=
      (roundLaw n noise epsilon he).map (fun raw j=>if (raw j).1 then b else !b) := by
  congr 1
  funext raw j
  exact round_physical b cost raw o j

theorem primitive_repair_mass (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) :
    (primitiveLaw noise epsilon he).toMeasure {z | z.1=true}=((1-epsilon : NNReal) : ℝ≥0∞) := by
  have hh:=primitive_mode noise epsilon he
  have hmap : (primitiveLaw noise epsilon he).toMeasure {z | z.1=true}=
      ((primitiveLaw noise epsilon he).map Prod.fst).toMeasure {true} := by
    rw [←PMF.toMeasure_map _ _ measurable_fst,Measure.map_apply measurable_fst (measurableSet_singleton true)]
    rfl
  rw [hmap,hh,PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton true)]
  change ENNReal.ofReal (1-(epsilon : ℝ))=((1-epsilon : NNReal) : ℝ≥0∞)
  have hcoe : ((1-epsilon : NNReal) : ℝ)=1-(epsilon : ℝ) := by
    simpa only [NNReal.coe_one] using NNReal.coe_sub he
  rw [←hcoe]
  simp

/-- Exact nonzero-noise whole-body success, from the SAME complete raw product.
All failures, costs and partial births remain in its complete record law. -/
theorem actual_body_probability {n : ℕ} (b : Bool) (cost : NNReal) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) (o : Organism n) :
    roundLaw n noise epsilon he {raw | BodyGoal b (roundParent b cost raw o).physical}=
      ((1-epsilon : NNReal) : ℝ≥0∞)^n := by
  simp_rw [actual_round_goal_iff]
  have hs : {raw : RoundRaw n | ∀j,(raw j).1=true}=Set.univ.pi (fun _ : Fin n=>{z : Bool×Bool | z.1=true}) := by
    ext raw
    simp [Set.mem_pi]
  rw [hs,roundLaw,Measure.pi_pi]
  simp only [primitive_repair_mass,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

/-- Every retained record is a literal transaction of this actual same-parent
run, with protected program/history inherited through all earlier phases. -/
theorem actual_record_origin {n : ℕ} (b : Bool) (cost : NNReal) (raw : RoundRaw n) (o : Organism n)
    (ports : List (Fin n)) (r : ModeRecord n) (hr : r∈tracePorts b cost raw o ports) :
    ∃ i parent, r=transaction i b cost parent (raw i) ∧ parent.program=o.program ∧ parent.history=o.history := by
  induction ports generalizing o with
  | nil => simp [tracePorts] at hr
  | cons i ports ih =>
    simp only [tracePorts,List.mem_cons] at hr
    rcases hr with he | hr
    · exact ⟨i,o,he,rfl,rfl⟩
    · obtain ⟨j,parent,hj,hp,hh⟩:=ih (transaction i b cost o (raw i)).transaction.parentAfter hr
      exact ⟨j,parent,hj,hp.trans (transaction_program i b cost o _),hh.trans (transaction_history i b cost o _)⟩

/-- This is the SAME actually last transaction, not a fabricated complete-body
child or a selected replacement seed. Empty traces have no last record. -/
theorem actual_last_parent {n : ℕ} (b : Bool) (cost : NNReal) (raw : RoundRaw n) (o : Organism n)
    (ports : List (Fin n)) (r : ModeRecord n) (hr : (tracePorts b cost raw o ports).getLast?=some r) :
    r.transaction.parentAfter=runPorts b cost raw o ports := by
  induction ports generalizing o with
  | nil => simp [tracePorts] at hr
  | cons i ports ih =>
    cases ports with
    | nil =>
      simp only [tracePorts,List.getLast?_singleton,Option.some.injEq] at hr
      subst r
      rfl
    | cons j ports =>
      change (transaction i b cost o (raw i)::transaction j b cost _ (raw j):: _).getLast?=some r at hr
      rw [List.getLast?_cons_cons] at hr
      exact ih (transaction i b cost o (raw i)).transaction.parentAfter hr

theorem actual_record_child_physical {n : ℕ} (b : Bool) (cost : NNReal) (raw : RoundRaw n) (o : Organism n)
    (ports : List (Fin n)) (r : ModeRecord n) (hr : r∈tracePorts b cost raw o ports)
    (child : Organism n) (hc : r.transaction.child=some child) :
    child.physical=r.transaction.parentAfter.physical := by
  obtain ⟨i,parent,he,_,_⟩:=actual_record_origin b cost raw o ports r hr
  subst r
  have hx:=actual_child_requires_repair i ⟨b,cost⟩ parent child ((substrate i).execute b parent.physical)
    (raw i).1 (raw i).2 hc
  change child.physical=(modeRecordStep i ⟨b,cost⟩ parent ((substrate i).execute b parent.physical) (raw i).1 (raw i).2).transaction.parentAfter.physical
  rw [hx.1]
  exact RegisterJointRecord.record_child_physical i ⟨b,cost⟩ parent _ _ child hx.2

/-- A genuinely successful LAST birth is full-body legitimate only under the
new complete-round event; earlier/local successful births are not promoted. -/
theorem actual_last_child_full_body {n : ℕ} (b : Bool) (cost : NNReal) (raw : RoundRaw n) (o : Organism n)
    (hgood : ∀i,(raw i).1=true) (r : ModeRecord n) (hr : (roundTrace b cost raw o).getLast?=some r)
    (child : Organism n) (hc : r.transaction.child=some child) :
    BodyGoal b child.physical := by
  have hm : r∈tracePorts b cost raw o (List.finRange n) :=
    List.mem_of_mem_getLast? (by rw [←show roundTrace b cost raw o=tracePorts b cost raw o (List.finRange n) from rfl,hr]; simp)
  have hphys:=actual_record_child_physical b cost raw o (List.finRange n) r hm child hc
  rw [hphys,actual_last_parent b cost raw o (List.finRange n) r hr]
  exact (actual_round_goal_iff b cost raw o).mpr hgood

section LocalP5
open UEOT.V3.ViabilityKernel
open UEOT.V3.Compression.Objecthood UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open UEOT.V3.Compression.Objecthood.JointHomeostasis UEOT.V3.Compression.Objecthood.OntogeneticConstruction
open RegisterFaultSource
/-- Original P5 consumes the SAME actual child at its actual serviced port.
This is LOCAL-port maintenance, not a claim of full-body validity or of a
fixed-port P5 theorem automatically governing the rotating environment. -/
theorem actual_trace_child_local_p5 {n : ℕ} (b : Bool) (cost : NNReal) (raw : RoundRaw n) (o : Organism n)
    (hp : o.program=b) (ports : List (Fin n)) (r : ModeRecord n) (hr : r∈tracePorts b cost raw o ports)
    (child : Organism n) (hc : r.transaction.child=some child) (epsilon : NNReal) (he : epsilon≤1) :
    ∃ i : Fin n,
      let seed : OntogeneticSeed (State n) Bool:=⟨child.physical,child.program⟩
      let S:=finiteJointRecurrentHomeostasisSystem
        (physical i) (target i b) (target_fixed i b) (certificate i b)
        (substrate i) codec b (compiled_dynamics_implements i b) (fault i) epsilon he (actual_fault_envelope i b)
      StaysIn (PMF.pure (assembleRepairOrganization (substrate i) codec seed)) S.carrier := by
  obtain ⟨i,parent,hr,hp',_⟩:=actual_record_origin b cost raw o ports r hr
  subst r
  exact ⟨i,actual_mode_birth_enters_maintenance i ⟨b,cost⟩ epsilon he parent child _ _ _ (hp'.trans hp) hc⟩
end LocalP5

/-- Current-port-only state cannot compute the next port's actual readout,
even with known phase and identical actual first action/mode/label. This only
rejects that exact dynamic factor for all registered initial bodies. -/
theorem next_port_information_obstruction :
    ¬∃ next : State 1→State 1,∀ o : Organism 2,
      RegisterActuatorScaleSource.projectState 1 (transaction 0 true 1 o (true,false)).transaction.parentAfter.physical=
        next (RegisterActuatorScaleSource.projectState 0 o.physical) := by
  rintro ⟨next,h⟩
  let a : Organism 2:=⟨[],(fun _=>false),true⟩
  let c : Organism 2:=⟨[],(fun j=>if j=0 then false else true),true⟩
  have hobs : RegisterActuatorScaleSource.projectState (0 : Fin 2) a.physical=
      RegisterActuatorScaleSource.projectState 0 c.physical := rfl
  have ha:=congrArg (fun x : State 1=>x 0) (h a)
  have hc:=congrArg (fun x : State 1=>x 0) (h c)
  rw [hobs] at ha
  have he:=ha.trans hc.symm
  change false=true at he
  cases he

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterRotatingBodySource
