import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterActuatorPopulationScale
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterRotatingChildRepair
import Mathlib.Probability.Independence.Basic

/-!
Original promise: book11 next-time dynamics transport and34.4 C4 must bind ACTUAL formed offspring and its executed continuation, not merely a frozen response fit.
Existing source: fixed-port C4/P8/population-journal transport and rotating next_port_information_obstruction already hold; none supplies multiport block transport.
Premise reduced: derive formation/binding and whole registered time-varying trace transport by retaining exactly an injective block containing every executed port.
Model/boundary: original Bool registers, Option Bool actions, protected program/history and complete mode/label source; arbitrary embedded port lists, including empty/repeated, with existing per-port raw semantics.
Consumer: original exact_fbt_composition and actual rotating body/source; forgotten-future-port obstruction is reused, not bypassed by an oracle or silently enlarged action set.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterBlockFormationTransport
open MeasureTheory ProbabilityTheory
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultJointRecord
open RegisterRotatingBodySource
local instance {n : ℕ} : MeasurableSpace (ModeRecord n) := ⊤
local instance {n : ℕ} : MeasurableSpace (List (ModeRecord n)) := ⊤
open scoped NNReal ENNReal
noncomputable section

/-- Exactly the registered block; inactive unobserved coordinates are forgotten. -/
def state {k n : ℕ} (e : Fin k ↪ Fin n) (x : State n) : State k:=fun j=>x (e j)
def organism {k n : ℕ} (e : Fin k ↪ Fin n) (o : Organism n) : Organism k:=⟨o.history,state e o.physical,o.program⟩
def record {k n : ℕ} (e : Fin k ↪ Fin n) (r : RegisterJointRecord.Record n) : RegisterJointRecord.Record k:=
  ⟨organism e r.parentBefore,r.action,r.label,organism e r.parentAfter,r.child.map (organism e),r.expenditure⟩
def modeRecord {k n : ℕ} (e : Fin k ↪ Fin n) (r : ModeRecord n) : ModeRecord k:=⟨r.repairMode,record e r.transaction⟩

@[simp] theorem state_update {k n : ℕ} (e : Fin k ↪ Fin n) (j : Fin k) (x : State n) (b : Bool) :
    state e (Function.update x (e j) b)=Function.update (state e x) j b :=by
  ext l
  simp [state,Function.update_apply,e.injective.eq_iff]

@[simp] theorem action_update {k n : ℕ} (e : Fin k ↪ Fin n) (j : Fin k) (x : State n) (a : Action) :
    state e (update (e j) x a)=update j (state e x) a :=by
  cases a <;> simp [update]

@[simp] theorem compiled_action {k n : ℕ} (e : Fin k ↪ Fin n) (j : Fin k) (b : Bool) (x : State n) :
    (substrate j).execute b (state e x)=(substrate (e j)).execute b x :=rfl

@[simp] theorem repair_transport {k n : ℕ} (e : Fin k ↪ Fin n) (j : Fin k) (o : Organism n) :
    organism e (repairEvent (e j) o)=repairEvent j (organism e o) :=by
  cases o
  simp only [organism,repairEvent,action_update,compiled_action]

@[simp] theorem birth_transport {k n : ℕ} (e : Fin k ↪ Fin n) (j : Fin k) (o : Organism n) (label : Bool) :
    organism e (birthEvent (e j) label o)=birthEvent j label (organism e o) :=by
  cases o
  simp only [organism,birthEvent,repairEvent,action_update,compiled_action]

private theorem post_transport {k n : ℕ} (e : Fin k ↪ Fin n) (j : Fin k) (o : Organism n) (a : Action) :
    organism e {o with physical:=update (e j) o.physical a}=
      {organism e o with physical:=update j (organism e o).physical a} :=by
  cases o
  simp only [organism,action_update]

/-- Literal record, not a separately supplied binding law. -/
theorem record_transport {k n : ℕ} (e : Fin k ↪ Fin n) (j : Fin k) (m : Mechanism) (o : Organism n)
    (a : Action) (label : Bool) :
    record e (RegisterJointRecord.recordStep (e j) m o a label)=RegisterJointRecord.recordStep j m (organism e o) a label :=by
  unfold RegisterJointRecord.recordStep
  dsimp only
  have ha : update j (organism e o).physical a j=update (e j) o.physical a (e j) :=by
    change update j (state e o.physical) a j=_
    rw [←action_update]
    rfl
  by_cases hx : update (e j) o.physical a (e j)=o.program
  · have hc : update j (organism e o).physical a j=(organism e o).program :=by
      change update j (organism e o).physical a j=o.program
      exact ha.trans hx
    simp only [record,if_pos hx,if_pos hc,Option.map_some,birth_transport,post_transport]
  · have hc : update j (organism e o).physical a j≠(organism e o).program :=by
      change update j (organism e o).physical a j≠o.program
      exact fun h=>hx (ha.symm.trans h)
    simp only [record,if_neg hx,if_neg hc,Option.map_none,post_transport]

/-- Same failure/success decision, actual label, paid fee and retained parent. -/
theorem step_transport {k n : ℕ} (e : Fin k ↪ Fin n) (j : Fin k) (m : Mechanism) (o : Organism n)
    (a : Action) (mode label : Bool) :
    modeRecord e (modeRecordStep (e j) m o a mode label)=modeRecordStep j m (organism e o) a mode label :=by
  cases mode
  · simp only [modeRecordStep,Bool.false_eq_true,if_false,modeRecord,record,organism,state_update,Option.map_none]
  · exact congrArg (ModeRecord.mk true) (record_transport e j m o a label)

/-- Actual child's birth and DIFFERENT next-port own-program binding both
consume the original C4 interface; neither compatibility is an input field. -/
theorem actual_birth_next_port_binding {k n : ℕ} (e : Fin k ↪ Fin n) (j next : Fin k) (fee : NNReal)
    (a nextAction : Action) (mode label nextMode nextLabel : Bool) (o child : Organism n)
    (hc : RegisterActuatorScaleSource.birthFormation (e j) fee a mode label o child) :
    RegisterActuatorScaleSource.birthFormation j fee a mode label (organism e o) (organism e child) ∧
      RegisterActuatorScaleSource.ownBinding next fee nextAction nextMode nextLabel (organism e child)=
        modeRecord e (RegisterActuatorScaleSource.ownBinding (e next) fee nextAction nextMode nextLabel child) :=by
  apply exact_fbt_composition (RegisterActuatorScaleSource.birthFormation (e j) fee a mode label)
    (RegisterActuatorScaleSource.birthFormation j fee a mode label) (organism e) (organism e)
    (RegisterActuatorScaleSource.ownBinding (e next) fee nextAction nextMode nextLabel)
    (RegisterActuatorScaleSource.ownBinding next fee nextAction nextMode nextLabel) (modeRecord e) _ _ hc
  · intro p c hpc
    have hh:=congrArg (fun r : ModeRecord k=>r.transaction.child) (step_transport e j ⟨p.program,fee⟩ p a mode label)
    change (modeRecordStep j ⟨p.program,fee⟩ (organism e p) a mode label).transaction.child=some (organism e c)
    rw [←hh]
    change (modeRecordStep (e j) ⟨p.program,fee⟩ p a mode label).transaction.child.map (organism e)=_
    rw [hpc]
    rfl
  · intro p
    exact (step_transport e next ⟨p.program,fee⟩ p nextAction nextMode nextLabel).symm

/-- Pull back the SAME complete registered mode/label word; no new draws. -/
def raw {k n : ℕ} (e : Fin k ↪ Fin n) (z : RoundRaw n) : RoundRaw k:=fun j=>z (e j)

theorem transaction_transport {k n : ℕ} (e : Fin k ↪ Fin n) (j : Fin k) (b : Bool) (fee : NNReal)
    (o : Organism n) (z : Bool×Bool) :
    modeRecord e (RegisterRotatingBodySource.transaction (e j) b fee o z)=
      RegisterRotatingBodySource.transaction j b fee (organism e o) z :=by
  unfold RegisterRotatingBodySource.transaction
  rw [step_transport]
  rfl

/-- Ordered next-time transport: every transaction uses the actual next
retained parent and its registered port; all intermediate failures stay. -/
theorem run_transport {k n : ℕ} (e : Fin k ↪ Fin n) (b : Bool) (fee : NNReal) (z : RoundRaw n)
    (o : Organism n) (ports : List (Fin k)) :
    organism e (runPorts b fee z o (ports.map e))=runPorts b fee (raw e z) (organism e o) ports :=by
  induction ports generalizing o with
  | nil => rfl
  | cons j ports ih =>
    simp only [List.map_cons,runPorts,ih]
    have hh:=congrArg (fun r : ModeRecord k=>r.transaction.parentAfter) (transaction_transport e j b fee o (z (e j)))
    exact congrArg (fun p=>runPorts b fee (raw e z) p ports) hh

theorem trace_transport {k n : ℕ} (e : Fin k ↪ Fin n) (b : Bool) (fee : NNReal) (z : RoundRaw n)
    (o : Organism n) (ports : List (Fin k)) :
    (tracePorts b fee z o (ports.map e)).map (modeRecord e)=tracePorts b fee (raw e z) (organism e o) ports :=by
  induction ports generalizing o with
  | nil => rfl
  | cons j ports ih =>
    simp only [List.map_cons,tracePorts,ih,transaction_transport]
    have hh:=congrArg (fun r : ModeRecord k=>r.transaction.parentAfter) (transaction_transport e j b fee o (z (e j)))
    dsimp only [modeRecord,record] at hh
    rw [hh]
    rfl

/-- A full registered BLOCK sweep gives exactly its original whole-block
success event. This does not infer success of forgotten fine coordinates. -/
theorem block_round_goal_iff {k n : ℕ} (e : Fin k ↪ Fin n) (b : Bool) (fee : NNReal) (z : RoundRaw n) (o : Organism n) :
    BodyGoal b (state e (runPorts b fee z o ((List.finRange k).map e)).physical) ↔ ∀ j,(z (e j)).1=true :=by
  change BodyGoal b (organism e (runPorts b fee z o ((List.finRange k).map e))).physical ↔ _
  rw [run_transport]
  exact actual_round_goal_iff b fee (raw e z) (organism e o)

/-- The original n-product draw law really projects to the registered k-product
law: independence is proved by native coordinate-family restriction. -/
theorem raw_source_law {k n : ℕ} (e : Fin k ↪ Fin n) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon ≤ 1) :
    (roundLaw n noise epsilon he).map (raw e)=roundLaw k noise epsilon he :=by
  let mu:=(RegisterFaultFinitePurposeProbe.primitiveLaw noise epsilon he).toMeasure
  have hi : iIndepFun (fun j : Fin n=>fun z : RoundRaw n=>z j) (Measure.pi (fun _ : Fin n=>mu)) :=
    iIndepFun_pi (fun _=>measurable_id.aemeasurable)
  have his:=hi.precomp e.injective
  change (Measure.pi (fun _ : Fin n=>mu)).map (fun z j=>z (e j))=Measure.pi (fun _ : Fin k=>mu)
  rw [his.map_fun_eq_pi_map (fun j=>(measurable_pi_apply (e j)).aemeasurable)]
  congr 1
  funext j
  exact (measurePreserving_eval (fun _ : Fin n=>mu) (e j)).map_eq

/-- SAME actual fine-source complete trace under the EMBEDDED k-port ordered
sweep. Its projected law is exactly the OLD k-body roundRecordLaw. This is not
an assertion about the DIFFERENT original n-port full-sweep clock. -/
theorem block_round_record_law {k n : ℕ} (e : Fin k ↪ Fin n) (b : Bool) (fee : NNReal)
    (noise : PMF Bool) (epsilon : NNReal) (he : epsilon ≤ 1) (o : Organism n) :
    ((roundLaw n noise epsilon he).map
      (fun z=>tracePorts b fee z o ((List.finRange k).map e))).map (fun rs=>rs.map (modeRecord e))=
        roundRecordLaw b fee noise epsilon he (organism e o) :=by
  have hm : Measurable (fun rs : List (ModeRecord n)=>rs.map (modeRecord e)) :=by intro s hs; trivial
  rw [Measure.map_map hm (measurable_of_finite _)]
  have hf : (fun z=>(tracePorts b fee z o ((List.finRange k).map e)).map (modeRecord e))=
      (fun z=>roundTrace b fee (raw e z) (organism e o)) :=by
    funext z
    exact trace_transport e b fee z o (List.finRange k)
  simp only [Function.comp_def]
  rw [hf]
  change (roundLaw n noise epsilon he).map ((fun z=>roundTrace b fee z (organism e o))∘raw e)=_
  rw [←Measure.map_map (measurable_of_finite _) (measurable_of_finite _),raw_source_law]
  rfl

/-- Exact full-body boundary: forgotten coordinates must ALREADY meet the
same target; the source execution preserves them. Block success alone is not
promoted to full n-body success. -/
theorem full_body_after_block_iff {k n : ℕ} (e : Fin k ↪ Fin n) (b : Bool) (fee : NNReal)
    (z : RoundRaw n) (o : Organism n) :
    BodyGoal b (runPorts b fee z o ((List.finRange k).map e)).physical ↔
      (∀ j,(z (e j)).1=true) ∧ ∀ l,l∉Set.range e → o.physical l=b :=by
  have hm (l : Fin n) : l∈(List.finRange k).map e ↔ l∈Set.range e :=by simp [Set.mem_range]
  constructor
  · intro h
    constructor
    · apply (block_round_goal_iff e b fee z o).mp
      exact fun j=>h (e j)
    · intro l hl
      have hh:=h l
      rw [runPorts_physical,if_neg ((hm l).not.mpr hl)] at hh
      exact hh
  · rintro ⟨hr,hp⟩ l
    rw [runPorts_physical]
    by_cases hl : l∈Set.range e
    · obtain ⟨j,rfl⟩:=hl
      simp [show e j∈(List.finRange k).map e from (hm _).mpr ⟨j,rfl⟩,hr j]
    · simp only [if_neg ((hm l).not.mpr hl)]
      exact hp l hl

/-- The original evaluator reads the SAME actual birth count and fee after
transport; a label/program copy is not reinterpreted as a new utility. -/
theorem payoff_transport {k n : ℕ} (e : Fin k ↪ Fin n) (price : NNReal) (r : ModeRecord n) :
    RegisterJointRecord.payoff price (modeRecord e r).transaction=RegisterJointRecord.payoff price r.transaction :=by
  cases hc : r.transaction.child <;> simp [RegisterJointRecord.payoff,modeRecord,record,hc,childCount]

/-- P8 history identity is exactly retained, while real offspring remains
real offspring under this declared block map. This is not global ID recovery. -/
theorem same_object_iff {k n : ℕ} (e : Fin k ↪ Fin n) (j : Fin k) (p q : Organism n) :
    (lineage j).SameObject (organism e p) (organism e q) ↔ (lineage (e j)).SameObject p q :=Iff.rfl

theorem offspring_transport {k n : ℕ} (e : Fin k ↪ Fin n) (j : Fin k) (p q : Organism n)
    (h : (lineage (e j)).OffspringOf p q) : (lineage j).OffspringOf (organism e p) (organism e q) :=by
  obtain ⟨⟨label,hq⟩,_⟩:=h
  subst q
  simpa only [birth_transport] using birth_is_distinct_offspring j label (organism e p)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterBlockFormationTransport
