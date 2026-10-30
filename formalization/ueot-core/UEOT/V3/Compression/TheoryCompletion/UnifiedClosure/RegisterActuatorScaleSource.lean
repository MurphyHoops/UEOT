import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterOwnProgramPopulation
import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.C4FBT

/-!
Original commitment: C4/P9 transport actual formation, execution, purpose and object properties under one scale map.
Existing premises: formation/binding/property transport are explicit interfaces; no actual Register dimension projection discharged them.
Premise reduced: derive actuator-retaining physical/object/record projection from literal interpreter/write/fault/birth semantics.
Models: SAME fixed mechanism across scales, with explicit existing own-program instances for birth/binding; coarse-observable controllers.
Consumers: SAME full finite/countable record laws, actual C4 birth/next-binding, P9 operational target/repair properties.

Physical projection keeps the actual actuator and protected program/history;
it genuinely forgets passive register coordinates. It is NOT ontic equality or
permission to merge registered owners. Policies are explicitly lifted from the
coarse observation/memory; arbitrary fine policies reading hidden registers are
outside the claim. Fresh modes/labels remain hidden from policy advance as in
the existing source, and every failed/fault record is retained. No new action,
reset, installation, resource port or sampling is introduced. The subsequent
population/resource bridge must preserve actual IDs/ledgers using this SAME
map; no independent desired scale fields or a general World are supplied.
The P9 consumer here is operational repaired-target preservation, not all six
terminal semantic predicates, merge/split or a physical RG interpretation.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterActuatorScaleSource
open MeasureTheory ProbabilityTheory
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose
open RegisterFaultControlModel RegisterFaultJointRecord
open scoped BigOperators ENNReal
noncomputable section

def projectState {n : ℕ} (i : Fin n) (x : State n) : State 1 := fun _ => x i

def projectOrganism {n : ℕ} (i : Fin n) (o : Organism n) : Organism 1 :=
  ⟨o.history,projectState i o.physical,o.program⟩

def projectRecord {n : ℕ} (i : Fin n) (r : RegisterJointRecord.Record n) : RegisterJointRecord.Record 1 :=
  ⟨projectOrganism i r.parentBefore,r.action,r.label,projectOrganism i r.parentAfter,
    r.child.map (projectOrganism i),r.expenditure⟩

def projectModeRecord {n : ℕ} (i : Fin n) (r : ModeRecord n) : ModeRecord 1 :=
  ⟨r.repairMode,projectRecord i r.transaction⟩

@[simp] theorem projectState_apply {n : ℕ} (i : Fin n) (x : State n) (j : Fin 1) : projectState i x j=x i := rfl

@[simp] theorem project_update {n : ℕ} (i : Fin n) (x : State n) (a : Action) :
    projectState i (update i x a)=update (0 : Fin 1) (projectState i x) a := by
  cases a with
  | none => rfl
  | some b =>
    ext j
    have hj : j=(0 : Fin 1) := Subsingleton.elim _ _
    subst j
    simp [projectState,update]

@[simp] theorem compiled_action_transport {n : ℕ} (i : Fin n) (b : Bool) (x : State n) :
    (substrate (0 : Fin 1)).execute b (projectState i x)=(substrate i).execute b x := rfl

@[simp] theorem project_repair {n : ℕ} (i : Fin n) (o : Organism n) :
    projectOrganism i (repairEvent i o)=repairEvent (0 : Fin 1) (projectOrganism i o) := by
  cases o
  simp only [projectOrganism,repairEvent,project_update,compiled_action_transport]

@[simp] theorem project_birth {n : ℕ} (i : Fin n) (o : Organism n) (label : Bool) :
    projectOrganism i (birthEvent i label o)=birthEvent (0 : Fin 1) label (projectOrganism i o) := by
  cases o
  simp only [projectOrganism,birthEvent,repairEvent,project_update,compiled_action_transport]

private theorem project_post {n : ℕ} (i : Fin n) (o : Organism n) (a : Action) :
    projectOrganism i {o with physical:=update i o.physical a}=
      {projectOrganism i o with physical:=update (0 : Fin 1) (projectOrganism i o).physical a} := by
  cases o
  simp [projectOrganism,project_update]

@[simp] theorem active_update {n : ℕ} (i : Fin n) (x : State n) (a : Action) :
    update (0 : Fin 1) (projectState i x) a 0=update i x a i := by
  cases a <;> simp [projectState,update]

/-- The actual birth guard, inherited program, future physical seed and paid
fee commute. A failed birth stays None, not replaced by a selected success. -/
theorem record_step_transport {n : ℕ} (i : Fin n) (m : Mechanism) (o : Organism n) (a : Action) (label : Bool) :
    projectRecord i (RegisterJointRecord.recordStep i m o a label)=
      RegisterJointRecord.recordStep (0 : Fin 1) m (projectOrganism i o) a label := by
  unfold RegisterJointRecord.recordStep
  dsimp only
  by_cases h : update i o.physical a i=o.program
  · have hc : update (0 : Fin 1) (projectOrganism i o).physical a 0=(projectOrganism i o).program := by
      change update (0 : Fin 1) (projectState i o.physical) a 0=o.program
      rwa [active_update]
    simp only [projectRecord,if_pos h,if_pos hc,Option.map_some,project_birth,project_post]
  · have hc : update (0 : Fin 1) (projectOrganism i o).physical a 0≠(projectOrganism i o).program := by
      change update (0 : Fin 1) (projectState i o.physical) a 0≠o.program
      rwa [active_update]
    simp only [projectRecord,if_neg h,if_neg hc,Option.map_none,project_post]

@[simp] theorem project_set {n : ℕ} (i : Fin n) (x : State n) (b : Bool) :
    projectState i (Function.update x i b)=Function.update (projectState i x) (0 : Fin 1) b :=
  project_update i x (some b)

/-- SAME actual environmental fault target and protected code. -/
theorem mode_step_transport {n : ℕ} (i : Fin n) (m : Mechanism) (o : Organism n)
    (a : Action) (mode label : Bool) :
    projectModeRecord i (modeRecordStep i m o a mode label)=
      modeRecordStep (0 : Fin 1) m (projectOrganism i o) a mode label := by
  cases mode
  · simp only [modeRecordStep,Bool.false_eq_true,if_false,projectModeRecord,projectRecord,projectOrganism,project_set,Option.map_none]
  · exact congrArg (ModeRecord.mk true) (record_step_transport i m o a label)

@[simp] theorem projected_parent {n : ℕ} (i : Fin n) (m : Mechanism) (o : Organism n)
    (a : Action) (mode label : Bool) :
    projectOrganism i (modeRecordStep i m o a mode label).transaction.parentAfter=
      (modeRecordStep (0 : Fin 1) m (projectOrganism i o) a mode label).transaction.parentAfter := by
  exact congrArg (fun r : ModeRecord 1 => r.transaction.parentAfter) (mode_step_transport i m o a mode label)

@[simp] theorem projected_physical_next {n : ℕ} (i : Fin n) (m : Mechanism) (o : Organism n)
    (a : Action) (mode label : Bool) :
    projectState i (modeRecordStep i m o a mode label).transaction.parentAfter.physical=
      (modeRecordStep (0 : Fin 1) m (projectOrganism i o) a mode label).transaction.parentAfter.physical :=
  congrArg Organism.physical (projected_parent i m o a mode label)


/-- The only controller decision memory is the coarse memory. The extra fine
current-state slot fulfills CausalPolicy.current_advance and is IGNORED by the
actual action selector; only projected next states enter coarse advance. -/
def liftPolicy {n : ℕ} (i : Fin n) (pi : CausalPolicy.{0,0,0} (State 1) (fun _ => Action)) :
    CausalPolicy.{0,0,0} (State n) (fun _ => Action) where
  Memory t := State n × pi.Memory t
  current h := h.1
  advance h a y := (y,pi.advance h.2 a (projectState i y))
  current_advance := by intros; rfl
  actionProb h a := pi.actionProb h.2 a
  actionProb_nonneg h a := pi.actionProb_nonneg h.2 a
  actionProb_sum_one h := pi.actionProb_sum_one h.2

section Policies
variable {n : ℕ} (i : Fin n) (m : Mechanism)
variable (pi : CausalPolicy.{0,0,0} (State 1) (fun _ => Action))

/-- Pointwise literal execution on the SAME primitive action/mode/label word. -/
theorem records_transport : ∀ k {t : ℕ} (h : pi.Memory t) (x : State n) (o : Organism n) (w : Tape k),
    (records i m (liftPolicy i pi) k (t:=t) (x,h) o w).map (projectModeRecord i)=
      records (0 : Fin 1) m pi k h (projectOrganism i o) w := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    rintro t h x o ⟨a,mode,label,rest⟩
    simp only [records,List.map_cons,mode_step_transport]
    congr 1
    have hh := ih (pi.advance h a (projectState i (modeRecordStep i m o a mode label).transaction.parentAfter.physical))
      (modeRecordStep i m o a mode label).transaction.parentAfter.physical
      (modeRecordStep i m o a mode label).transaction.parentAfter rest
    simpa only [liftPolicy,projected_parent,projected_physical_next] using hh

variable (noise : PMF Bool) (epsilon : NNReal) (he : epsilon ≤ 1)

/-- Same returned-policy action weights, same noise/hazard, same entire tape;
there is no independent desired coarse joint law or existential other policy. -/
theorem weight_transport : ∀ k {t : ℕ} (h : pi.Memory t) (x : State n) (o : Organism n) (w : Tape k),
    weight i noise m epsilon he (liftPolicy i pi) k (t:=t) (x,h) o w=
      weight (0 : Fin 1) noise m epsilon he pi k h (projectOrganism i o) w := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    rintro t h x o ⟨a,mode,label,rest⟩
    simp only [weight,liftPolicy]
    have hh := ih (pi.advance h a (projectState i (modeRecordStep i m o a mode label).transaction.parentAfter.physical))
      (modeRecordStep i m o a mode label).transaction.parentAfter.physical
      (modeRecordStep i m o a mode label).transaction.parentAfter rest
    simpa only [liftPolicy,projected_parent,projected_physical_next] using
      congrArg (fun z : ℝ => pi.actionProb h a * ((modeLaw epsilon he) mode).toReal * (noise label).toReal * z) hh

theorem tapeLaw_transport (k : ℕ) {t : ℕ} (h : pi.Memory t) (x : State n) (o : Organism n) :
    tapeLaw i noise m epsilon he (liftPolicy i pi) k (t:=t) (x,h) o=
      tapeLaw (0 : Fin 1) noise m epsilon he pi k h (projectOrganism i o) := by
  apply PMF.ext
  intro w
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  simp only [tapeLaw,FiniteProbabilityRow.ofRealRow_apply_toReal,weight_transport]

/-- FULL finite transaction-law transport, retaining fault/failed-birth/fee
records. Source, initial parent, policy and primitive law are all the originals. -/
theorem recordLaw_transport (k : ℕ) {t : ℕ} (h : pi.Memory t) (x : State n) (o : Organism n) :
    (recordLaw i noise m epsilon he (liftPolicy i pi) k (t:=t) (x,h) o).map (List.map (projectModeRecord i))=
      recordLaw (0 : Fin 1) noise m epsilon he pi k h (projectOrganism i o) := by
  unfold recordLaw
  rw [PMF.map_comp,tapeLaw_transport]
  congr 1
  funext w
  exact records_transport i m pi k h x o w
end Policies


section Infinite
open RegisterFaultInfiniteRecord
variable {n : ℕ} (i : Fin n) (m : Mechanism)
variable (pi : CausalPolicy.{0,0,0} (State 1) (fun _ => Action))

def projectConfig (c : Config (liftPolicy i pi)) : Config pi :=
  ⟨c.1,c.2.1.2,projectOrganism i c.2.2⟩

@[simp] theorem advance_transport (c : Config (liftPolicy i pi)) (e : Event) :
    projectConfig i pi (advance i m (liftPolicy i pi) c e)=
      advance (0 : Fin 1) m pi (projectConfig i pi c) e := by
  rcases c with ⟨t,⟨x,h⟩,o⟩
  simp only [projectConfig,advance,liftPolicy,projected_parent,projected_physical_next]

@[simp] theorem run_transport (c : Config (liftPolicy i pi)) (es : List Event) :
    projectConfig i pi (run i m (liftPolicy i pi) c es)=
      run (0 : Fin 1) m pi (projectConfig i pi c) es := by
  induction es generalizing c with
  | nil => rfl
  | cons e es ih =>
    change projectConfig i pi (run i m (liftPolicy i pi) (advance i m (liftPolicy i pi) c e) es)=_
    rw [ih,advance_transport]
    rfl

@[simp] theorem run_organism_transport (c : Config (liftPolicy i pi)) (es : List Event) :
    projectOrganism i (run i m (liftPolicy i pi) c es).2.2=
      (run (0 : Fin 1) m pi (projectConfig i pi c) es).2.2 :=
  congrArg (fun c : Config pi => c.2.2) (run_transport i m pi c es)

variable (noise : PMF Bool) (epsilon : NNReal) (he : epsilon ≤ 1)

/-- SAME actual primitive kernel, rather than a separately requested path law. -/
theorem eventLaw_transport (c : Config (liftPolicy i pi)) :
    eventLaw noise epsilon he (liftPolicy i pi) c=eventLaw noise epsilon he pi (projectConfig i pi c) := rfl

theorem wordRow_transport (c : Config (liftPolicy i pi)) (es : List Event) :
    wordRow i noise m epsilon he (liftPolicy i pi) c es=
      wordRow (0 : Fin 1) noise m epsilon he pi (projectConfig i pi c) es := by
  unfold wordRow
  rw [eventLaw_transport,run_transport]

theorem wordKernel_transport (c : Config (liftPolicy i pi)) :
    wordKernel i noise m epsilon he (liftPolicy i pi) c=
      wordKernel (0 : Fin 1) noise m epsilon he pi (projectConfig i pi c) := by
  ext es s hs
  change (wordRow i noise m epsilon he (liftPolicy i pi) c es).toMeasure s=_
  rw [wordRow_transport]
  rfl

/-- Equality of the ORIGINAL infinite primitive word processes follows by
actual kernel equality. No projective-limit/desired transport field is assumed. -/
theorem wordPathLaw_transport (c : Config (liftPolicy i pi)) :
    wordPathLaw i noise m epsilon he (liftPolicy i pi) c=
      wordPathLaw (0 : Fin 1) noise m epsilon he pi (projectConfig i pi c) := by
  simp only [wordPathLaw,wordKernel_transport]

@[simp] theorem recordAt_transport (c : Config (liftPolicy i pi)) (z : ℕ → List Event) (k : ℕ) :
    projectModeRecord i (recordAt i m (liftPolicy i pi) c z k)=
      recordAt (0 : Fin 1) m pi (projectConfig i pi c) z k := by
  simp only [recordAt,mode_step_transport,run_organism_transport]

local instance {d : ℕ} : MeasurableSpace (ModeRecord d) := ⊤
local instance {d : ℕ} : MeasurableSingletonClass (ModeRecord d) := ⟨fun _ => trivial⟩

/-- Full actual countable complete-record law transport, including every fault,
failed birth and fee. The measurable readout is the literal source projection. -/
theorem recordPathLaw_transport (c : Config (liftPolicy i pi)) :
    (recordPathLaw i noise m epsilon he (liftPolicy i pi) c).map
      (fun (rs : ℕ → ModeRecord n) k => projectModeRecord i (rs k))=
      recordPathLaw (0 : Fin 1) noise m epsilon he pi (projectConfig i pi c) := by
  have hm : Measurable (fun (rs : ℕ → ModeRecord n) k => projectModeRecord i (rs k)) := by
    apply measurable_pi_lambda
    intro k
    have hf : Measurable (projectModeRecord i) := by intro s hs; trivial
    exact hf.comp (measurable_pi_apply k)
  rw [recordPathLaw,Measure.map_map hm (measurable_recordStream i m (liftPolicy i pi) c),wordPathLaw_transport]
  unfold recordPathLaw
  congr 1
  funext z k
  exact recordAt_transport i m pi c z k
end Infinite


@[simp] theorem projected_child {n : ℕ} (i : Fin n) (m : Mechanism) (o : Organism n)
    (a : Action) (mode label : Bool) :
    (modeRecordStep i m o a mode label).transaction.child.map (projectOrganism i)=
      (modeRecordStep (0 : Fin 1) m (projectOrganism i o) a mode label).transaction.child :=
  congrArg (fun r : ModeRecord 1 => r.transaction.child) (mode_step_transport i m o a mode label)

/-- Formation means an ACTUAL born child of this original own-program
transaction. It is not arbitrary response-fit membership or token equality. -/
def birthFormation {n : ℕ} (i : Fin n) (cost : NNReal) (a : Action) (mode label : Bool) :
    FormationRelation (Organism n) (Organism n) := fun o d =>
  (modeRecordStep i ⟨o.program,cost⟩ o a mode label).transaction.child=some d

/-- Actual next binding of the SAME child's own protected program. -/
def ownBinding {n : ℕ} (i : Fin n) (cost : NNReal) (a : Action) (mode label : Bool) (o : Organism n) : ModeRecord n :=
  modeRecordStep i ⟨o.program,cost⟩ o a mode label

theorem actual_formation_transport {n : ℕ} (i : Fin n) (cost : NNReal) (a : Action) (mode label : Bool) :
    FormationTransportCompatible (birthFormation i cost a mode label)
      (birthFormation (0 : Fin 1) cost a mode label) (projectOrganism i) (projectOrganism i) := by
  intro o d hd
  have h := projected_child i ⟨o.program,cost⟩ o a mode label
  rw [hd,Option.map_some] at h
  exact h.symm

theorem actual_binding_transport {n : ℕ} (i : Fin n) (cost : NNReal) (a : Action) (mode label : Bool) :
    BindingTransportCompatible (ownBinding i cost a mode label)
      (ownBinding (0 : Fin 1) cost a mode label) (projectOrganism i) (projectModeRecord i) := by
  intro o
  exact (mode_step_transport i ⟨o.program,cost⟩ o a mode label).symm

/-- The ORIGINAL C4 exact FBT theorem actually consumes derived literal birth
formation and next-transaction binding for the SAME child, not supplied scale
compatibility. Failure outcomes stay in full laws; this event conclusion only
requires the target really was born. -/
theorem c4_actual_birth_next_binding {n : ℕ} (i : Fin n) (cost : NNReal)
    (a nextAction : Action) (mode label nextMode nextLabel : Bool) (o d : Organism n)
    (hd : birthFormation i cost a mode label o d) :
    birthFormation (0 : Fin 1) cost a mode label (projectOrganism i o) (projectOrganism i d) ∧
      ownBinding (0 : Fin 1) cost nextAction nextMode nextLabel (projectOrganism i d)=
        projectModeRecord i (ownBinding i cost nextAction nextMode nextLabel d) :=
  exact_fbt_composition (birthFormation i cost a mode label) (birthFormation 0 cost a mode label)
    (projectOrganism i) (projectOrganism i) (ownBinding i cost nextAction nextMode nextLabel)
    (ownBinding 0 cost nextAction nextMode nextLabel) (projectModeRecord i)
    (actual_formation_transport i cost a mode label) (actual_binding_transport i cost nextAction nextMode nextLabel) hd

/-- Actual typed object-scale map; it contains NO desired preservation field. -/
def objectScale {n : ℕ} (i : Fin n) : ObjectScaleMap (State n) (State 1) (Organism n) (Organism 1) :=
  ⟨projectState i,projectOrganism i⟩

def Legitimate {n : ℕ} (i : Fin n) (o : Organism n) : Prop := o.physical i=o.program

/-- Operational target/legitimacy is actually preserved because the active
port AND protected program are retained; arbitrary hidden-register predicates
have no such conclusion. -/
theorem legitimate_preservation {n : ℕ} (i : Fin n) :
    PreservesObjectPredicate (objectScale i) (Legitimate i) (Legitimate (0 : Fin 1)) := by
  intro o ho
  exact ho

/-- Original P9 object-property transport consumes SAME literal source map
and the repair target certificate, with no externally supplied hpres field. -/
theorem p9_actual_repaired_object {n : ℕ} (i : Fin n) (o : Organism n) :
    Legitimate (0 : Fin 1) (projectOrganism i (repairEvent i o)) := by
  exact transport_object_property (objectScale i) (Legitimate i) (Legitimate 0) rfl
    (legitimate_preservation i) (RegisterRepairHistory.repair_reaches_target i o)


/-- Literal compiled action probabilities agree after the registered memory
projection. After advance the pair is again(nextFine,project nextFine). -/
theorem lifted_compiled_action {n : ℕ} (i : Fin n) (b : Bool) (x : State n) (a : Action) {t : ℕ} :
    (liftPolicy i (selectorPolicy ((substrate (0 : Fin 1)).execute b))).actionProb (t:=t) (x,projectState i x) a=
      (selectorPolicy ((substrate i).execute b)).actionProb (t:=t) x a := by
  cases a with
  | none =>
    cases b <;> cases hx : x i <;>
      simp [liftPolicy,selectorPolicy_actionProb,execute_compiled,projectState_apply,hx]
  | some a =>
    cases a <;> cases b <;> cases hx : x i <;>
      simp [liftPolicy,selectorPolicy_actionProb,execute_compiled,projectState_apply,hx]

@[simp] theorem lifted_compiled_advance {n : ℕ} (i : Fin n) (b : Bool) (x y : State n) (a : Action) {t : ℕ} :
    (liftPolicy i (selectorPolicy ((substrate (0 : Fin 1)).execute b))).advance (t:=t) (x,projectState i x) a y=
      (y,projectState i y) := rfl

@[simp] theorem payoff_transport {n : ℕ} (i : Fin n) (price : NNReal) (r : ModeRecord n) :
    RegisterJointRecord.payoff price (projectModeRecord i r).transaction=RegisterJointRecord.payoff price r.transaction := by
  cases hc : r.transaction.child <;>
    simp [RegisterJointRecord.payoff,projectModeRecord,projectRecord,childCount,hc]

@[simp] theorem discountedPayoff_transport {n : ℕ} (i : Fin n) (price : NNReal) (d : ℝ) (rs : List (ModeRecord n)) :
    discountedPayoff price d (rs.map (projectModeRecord i))=discountedPayoff price d rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [discountedPayoff,ih]

/-- SAME source-priced birth/cost purpose functional, not just physical rows. -/
theorem actualExpectation_transport {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon ≤ 1) (pi : CausalPolicy.{0,0,0} (State 1) (fun _ => Action))
    (price : NNReal) (d : ℝ) (k : ℕ) {t : ℕ} (h : pi.Memory t) (x : State n) (o : Organism n) :
    actualExpectation i noise m epsilon he (liftPolicy i pi) price d k (t:=t) (x,h) o=
      actualExpectation (0 : Fin 1) noise m epsilon he pi price d k h (projectOrganism i o) := by
  unfold actualExpectation
  rw [tapeLaw_transport]
  apply Finset.sum_congr rfl
  intro w _
  rw [← records_transport i m pi k h x o w,discountedPayoff_transport]

/-- Two distinct passive physical states, same protected code/history and
same projected active state. This quotient genuinely forgets information. -/
def passiveInitial (hidden : Bool) : Organism 2 :=
  ⟨[],![false,hidden],true⟩

theorem noninjective_actual_projection :
    passiveInitial false ≠ passiveInitial true ∧
      projectOrganism (0 : Fin 2) (passiveInitial false)=projectOrganism (0 : Fin 2) (passiveInitial true) := by
  constructor
  · intro h
    have hh := congrArg (fun o : Organism 2 => o.physical 1) h
    norm_num [passiveInitial] at hh
  · simp [projectOrganism,passiveInitial]
    funext j
    rfl

/-- Registered actual fine initial states and SAME coarse compiled memory;
their complete finite record experiments coincide after projection. No initial
preparation or hidden-bit-dependent initial controller memory is added. -/
theorem passive_bit_same_actual_full_finite_law (noise : PMF Bool) (epsilon : NNReal) (he : epsilon ≤ 1) (k : ℕ) :
    let pi := selectorPolicy ((substrate (0 : Fin 1)).execute true)
    let h : State 1 := fun _ => false
    (recordLaw (0 : Fin 2) noise ⟨true,1⟩ epsilon he (liftPolicy (0 : Fin 2) pi) k (t:=0)
      ((passiveInitial false).physical,h) (passiveInitial false)).map (List.map (projectModeRecord (0 : Fin 2)))=
    (recordLaw (0 : Fin 2) noise ⟨true,1⟩ epsilon he (liftPolicy (0 : Fin 2) pi) k (t:=0)
      ((passiveInitial true).physical,h) (passiveInitial true)).map (List.map (projectModeRecord (0 : Fin 2))) := by
  dsimp only
  let pi := selectorPolicy ((substrate (0 : Fin 1)).execute true)
  let h : pi.Memory 0 := (fun _ => false : State 1)
  have hf := recordLaw_transport (0 : Fin 2) ⟨true,1⟩ pi noise epsilon he k h
    (passiveInitial false).physical (passiveInitial false)
  have ht := recordLaw_transport (0 : Fin 2) ⟨true,1⟩ pi noise epsilon he k h
    (passiveInitial true).physical (passiveInitial true)
  rw [noninjective_actual_projection.2] at hf
  exact hf.trans ht.symm

/-- Counterexample to hiding the actual actuator: the retained passive bit
is identical, but the SAME allowed idle action has different actual births.
The original compiled programme additionally requests different paid actions. -/
def activeInitial (active : Bool) : Organism 2 :=
  ⟨[],![active,false],true⟩

theorem hiding_active_birth_fee_obstruction :
    projectOrganism (1 : Fin 2) (activeInitial true)=projectOrganism (1 : Fin 2) (activeInitial false) ∧
    (modeRecordStep (0 : Fin 2) ⟨true,1⟩ (activeInitial true) none true true).transaction.child.isSome=true ∧
    (modeRecordStep (0 : Fin 2) ⟨true,1⟩ (activeInitial false) none true true).transaction.child=none ∧
    (modeRecordStep (0 : Fin 2) ⟨true,1⟩ (activeInitial true)
      ((substrate (0 : Fin 2)).execute true (activeInitial true).physical) true true).transaction.expenditure=0 ∧
    (modeRecordStep (0 : Fin 2) ⟨true,1⟩ (activeInitial false)
      ((substrate (0 : Fin 2)).execute true (activeInitial false).physical) true true).transaction.expenditure=1 := by
  norm_num [projectOrganism,projectState,activeInitial,modeRecordStep,RegisterJointRecord.recordStep,
    execute_compiled,update,cost]
  funext j
  rfl

/-- No action rule using only that bad coarse observation can implement the
SAME original compiled programme at both actual fine states. -/
theorem hiding_active_no_compiled_policy_factor :
    ¬ ∃ sigma : State 1 → Action, ∀ x : State 2,
      sigma (projectState (1 : Fin 2) x)=(substrate (0 : Fin 2)).execute true x := by
  rintro ⟨sigma,hs⟩
  have ha := hs (activeInitial true).physical
  have hb := hs (activeInitial false).physical
  have hc := congrArg Organism.physical hiding_active_birth_fee_obstruction.1
  change projectState (1 : Fin 2) (activeInitial true).physical=projectState (1 : Fin 2) (activeInitial false).physical at hc
  rw [hc] at ha
  have he := ha.symm.trans hb
  norm_num [execute_compiled,activeInitial] at he
  cases he


def witnessPolicy : CausalPolicy.{0,0,0} (State 1) (fun _ => Action) :=
  selectorPolicy ((substrate (0 : Fin 1)).execute true)
def witnessMemory : witnessPolicy.Memory 0 := (fun _ => false : State 1)

def actualBorn (hidden : Bool) : Organism 2 :=
  birthEvent (0 : Fin 2) true {passiveInitial hidden with physical:=update 0 (passiveInitial hidden).physical (some true)}

theorem witness_actual_formation (hidden : Bool) :
    birthFormation (0 : Fin 2) 1 (some true) true true (passiveInitial hidden) (actualBorn hidden) := by
  norm_num [birthFormation,modeRecordStep,RegisterJointRecord.recordStep,passiveInitial,actualBorn,update]

/-- Nonempty same-source C4 consumer: actual born child, followed by its
actual own-program fault record (including failed birth/no write fee). -/
theorem witness_c4_actual_consumer (hidden : Bool) :
    birthFormation (0 : Fin 1) 1 (some true) true true
      (projectOrganism (0 : Fin 2) (passiveInitial hidden)) (projectOrganism (0 : Fin 2) (actualBorn hidden)) ∧
    ownBinding (0 : Fin 1) 1 none false true (projectOrganism (0 : Fin 2) (actualBorn hidden))=
      projectModeRecord (0 : Fin 2) (ownBinding (0 : Fin 2) 1 none false true (actualBorn hidden)) :=
  c4_actual_birth_next_binding (0 : Fin 2) 1 (some true) none true true false true
    (passiveInitial hidden) (actualBorn hidden) (witness_actual_formation hidden)

private theorem quarter_le_one : (1/4 : NNReal) ≤ 1 := by
  exact_mod_cast (by norm_num : (1/4 : ℝ) ≤ 1)

/-- The displayed actual birth is not an unsupported/null primitive word:
the SAME compiled interpreter gives it positive mass at nonzero fault hazard. -/
theorem witness_actual_birth_weight (hidden : Bool) :
    weight (0 : Fin 2) (PMF.pure true) ⟨true,1⟩ (1/4) quarter_le_one
      (liftPolicy (0 : Fin 2) witnessPolicy) 1 (t:=0)
      ((passiveInitial hidden).physical,witnessMemory) (passiveInitial hidden) (some true,true,true,())=(3/4 : ℝ) := by
  have ha : (liftPolicy (0 : Fin 2) witnessPolicy).actionProb (t:=0)
      ((passiveInitial hidden).physical,witnessMemory) (some true)=1 := by
    change witnessPolicy.actionProb (t:=0) witnessMemory (some true)=1
    change (selectorPolicy ((substrate (0 : Fin 1)).execute true)).actionProb (t:=0)
      (fun _ => false : State 1) (some true)=1
    norm_num [selectorPolicy_actionProb,execute_compiled]
  norm_num [weight,ha,modeLaw,FiniteProbabilityRow.ofRealRow_apply_toReal,
    modeProbability,repairChance,PMF.pure_apply]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterActuatorScaleSource
