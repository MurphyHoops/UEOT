import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultInfiniteRecord

/-!
Original commitment: true offspring identity and parental provenance follow actual execution.
Existing result: literal register births enter P5, but repeated Boolean labels can reuse child IDs.
Premise reduced: derive timestamp freshness and parent interpretation from a transaction counter.
Model/witness: one serialized retained-parent run; founder ID/start clock are declared inputs; failures count.
Consumers: original P5 child maintenance, P8 repair/offspring distinction and P12 journal discovery.

The counter advances on every transaction, including environmental faults and
failed births. A new child's address appends the actual event counter and label.
This is a reliable serialized metadata journal with no additional fee in the
existing controlled-write cost model, not information inferred from unlabelled
physics. Arbitrary concurrent-world IDs, unique founder allocation and fertility
or Price/Perron source inputs remain separate obligations.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterTimestampedBirthSource
open Set MeasureTheory Filter Topology
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.TheoryCompletion.InverseObjecthood
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose
open RegisterJointRecord RegisterFaultJointRecord
noncomputable section

abbrev Identity := List (ℕ × Bool)

structure ClockedOrganism (n : ℕ) where
  organism : Organism n
  identity : Identity
  clock : ℕ

structure ClockedRecord (n : ℕ) where
  parentBefore : ClockedOrganism n
  action : Action
  repairMode : Bool
  label : Bool
  parentAfter : ClockedOrganism n
  child : Option (ClockedOrganism n)
  expenditure : ℝ

def eraseRecord {n : ℕ} (r : ClockedRecord n) : ModeRecord n :=
  ⟨r.repairMode, {
    parentBefore := r.parentBefore.organism
    action := r.action
    label := r.label
    parentAfter := r.parentAfter.organism
    child := r.child.map ClockedOrganism.organism
    expenditure := r.expenditure }⟩

/-- Execute the old literal transaction once. Only the journal/counter fields
are added; failed births remain None and the original parent is retained. -/
def step {n : ℕ} (i : Fin n) (m : Mechanism) (p : ClockedOrganism n)
    (a : Action) (mode label : Bool) : ClockedRecord n :=
  let r := modeRecordStep i m p.organism a mode label
  { parentBefore := p
    action := r.transaction.action
    repairMode := r.repairMode
    label := r.transaction.label
    parentAfter := ⟨r.transaction.parentAfter,p.identity,p.clock+1⟩
    child := r.transaction.child.map (fun c => ⟨c,p.identity ++ [(p.clock,label)],0⟩)
    expenditure := r.transaction.expenditure }

@[simp] theorem step_erase {n : ℕ} (i : Fin n) (m : Mechanism) (p : ClockedOrganism n)
    (a : Action) (mode label : Bool) :
    eraseRecord (step i m p a mode label) = modeRecordStep i m p.organism a mode label := by
  cases mode <;> simp [step,eraseRecord,modeRecordStep,recordStep]

@[simp] theorem step_parent_identity {n : ℕ} (i : Fin n) (m : Mechanism)
    (p : ClockedOrganism n) (a : Action) (mode label : Bool) :
    (step i m p a mode label).parentAfter.identity = p.identity := rfl

@[simp] theorem step_clock {n : ℕ} (i : Fin n) (m : Mechanism)
    (p : ClockedOrganism n) (a : Action) (mode label : Bool) :
    (step i m p a mode label).parentAfter.clock = p.clock+1 := rfl

@[simp] theorem step_parent_organism {n : ℕ} (i : Fin n) (m : Mechanism)
    (p : ClockedOrganism n) (a : Action) (mode label : Bool) :
    (step i m p a mode label).parentAfter.organism =
      (modeRecordStep i m p.organism a mode label).transaction.parentAfter := rfl

theorem actual_child_source {n : ℕ} (i : Fin n) (m : Mechanism)
    (p c : ClockedOrganism n) (a : Action) (mode label : Bool)
    (hc : (step i m p a mode label).child = some c) :
    (modeRecordStep i m p.organism a mode label).transaction.child = some c.organism ∧
      c.identity = p.identity ++ [(p.clock,label)] ∧ c.clock = 0 := by
  change Option.map (fun o : Organism n => (⟨o,p.identity ++ [(p.clock,label)],0⟩ : ClockedOrganism n))
    (modeRecordStep i m p.organism a mode label).transaction.child = some c at hc
  obtain ⟨o,ho,heq⟩ := Option.map_eq_some_iff.mp hc
  subst c
  exact ⟨ho,rfl,rfl⟩


/-- Forgetting timestamps recovers the old source birth-history extension.
Agreement of the founder's already supplied two journals is an explicit initial
condition; it is not inferred from physical state. -/
theorem actual_child_erases_timestamp_history {n : ℕ} (i : Fin n) (m : Mechanism)
    (p c : ClockedOrganism n) (a : Action) (mode label : Bool)
    (halign : p.identity.map Prod.snd = p.organism.history)
    (hc : (step i m p a mode label).child = some c) :
    c.identity.map Prod.snd = c.organism.history := by
  have hsrc := actual_child_source i m p c a mode label hc
  have hrepair := actual_child_requires_repair i m p.organism c.organism a mode label hsrc.1
  have hbirth := RegisterJointRecord.record_child_source i m p.organism a label c.organism hrepair.2
  have hh := congrArg Organism.history hbirth.1
  rw [hsrc.2.1,List.map_append]
  simpa [halign,birthEvent,repairEvent,recordStep] using hh.symm

/-- Parent identity is recovered from the produced child's literal history. -/
theorem actual_child_parent_prefix {n : ℕ} (i : Fin n) (m : Mechanism)
    (p c : ClockedOrganism n) (a : Action) (mode label : Bool)
    (hc : (step i m p a mode label).child = some c) :
    c.identity.dropLast = p.identity := by
  rw [(actual_child_source i m p c a mode label hc).2.1]
  simp

def lineage {n : ℕ} (i : Fin n) (m : Mechanism) :
    LineageSemantics (ClockedOrganism n) Identity where
  identity := ClockedOrganism.identity
  parentOf := fun p c => ∃ a mode label, (step i m p a mode label).child = some c

theorem actual_child_offspring {n : ℕ} (i : Fin n) (m : Mechanism)
    (p c : ClockedOrganism n) (a : Action) (mode label : Bool)
    (hc : (step i m p a mode label).child = some c) :
    (lineage i m).OffspringOf p c := by
  refine ⟨⟨a,mode,label,hc⟩,?_⟩
  intro heq
  change p.identity = c.identity at heq
  rw [(actual_child_source i m p c a mode label hc).2.1] at heq
  have hlen := congrArg List.length heq
  simp at hlen

/-- The original P8 endpoint consumes source-derived same-parent repair/fault
identity. Neither kind of retained-parent transition is a new offspring. -/
theorem retained_parent_not_offspring {n : ℕ} (i : Fin n) (m : Mechanism)
    (p : ClockedOrganism n) (a : Action) (mode label : Bool) :
    ¬ (lineage i m).OffspringOf p (step i m p a mode label).parentAfter := by
  apply LineageSemantics.sameObjectRepair_not_offspring
  rfl

abbrev Event := RegisterFaultInfiniteRecord.Event

def runParent {n : ℕ} (i : Fin n) (m : Mechanism) (p : ClockedOrganism n)
    (es : List Event) : ClockedOrganism n :=
  es.foldl (fun q e => (step i m q e.1 e.2.1 e.2.2).parentAfter) p

def trace {n : ℕ} (i : Fin n) (m : Mechanism) (p : ClockedOrganism n) :
    List Event → List (ClockedRecord n)
  | [] => []
  | e :: es => step i m p e.1 e.2.1 e.2.2 ::
      trace i m (step i m p e.1 e.2.1 e.2.2).parentAfter es

@[simp] theorem runParent_identity {n : ℕ} (i : Fin n) (m : Mechanism)
    (p : ClockedOrganism n) (es : List Event) :
    (runParent i m p es).identity = p.identity := by
  induction es generalizing p with
  | nil => rfl
  | cons e es ih => change (runParent i m (step i m p e.1 e.2.1 e.2.2).parentAfter es).identity = _; rw [ih]; rfl

@[simp] theorem runParent_clock {n : ℕ} (i : Fin n) (m : Mechanism)
    (p : ClockedOrganism n) (es : List Event) :
    (runParent i m p es).clock = p.clock + es.length := by
  induction es generalizing p with
  | nil => simp [runParent]
  | cons e es ih =>
      change (runParent i m (step i m p e.1 e.2.1 e.2.2).parentAfter es).clock = _
      rw [ih,step_clock,List.length_cons]
      omega

/-- Erasure of the entire actual transaction trace is the existing original
interpreter trace for the SAME causal policy memory and literal event word. -/
theorem trace_erase {n : ℕ} (i : Fin n) (m : Mechanism)
    (pi : CausalPolicy.{0,0,0} (State n) (fun _ => Action)) :
    ∀ es {t} (h : pi.Memory t) (p : ClockedOrganism n),
      (trace i m p es).map eraseRecord =
        RegisterFaultInfiniteRecord.trace i m pi ⟨t,h,p.organism⟩ es := by
  intro es
  induction es with
  | nil => intros; rfl
  | cons e es ih =>
      intro t h p
      simp only [trace,List.map_cons,step_erase,RegisterFaultInfiniteRecord.trace]
      rw [ih]
      rfl

/-- Same original input tape law and same initialized causal policy; only a
computed timestamped journal is returned. No new randomness or success filter. -/
def recordLaw {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon ≤ 1)
    (pi : CausalPolicy.{0,0,0} (State n) (fun _ => Action)) (k : ℕ)
    {t : ℕ} (h : pi.Memory t) (p : ClockedOrganism n) : PMF (List (ClockedRecord n)) :=
  (RegisterFaultJointRecord.tapeLaw i noise m epsilon he pi k h p.organism).map
    (fun w => trace i m p (RegisterFaultInfiniteRecord.tapeEvents k w))

/-- The whole timestamped experiment erases to the original full record law,
with the same initial organism, policy, hazard, labels and failures. -/
theorem recordLaw_erase {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon ≤ 1)
    (pi : CausalPolicy.{0,0,0} (State n) (fun _ => Action)) (k : ℕ)
    {t : ℕ} (h : pi.Memory t) (p : ClockedOrganism n) :
    (recordLaw i noise m epsilon he pi k h p).map (List.map eraseRecord) =
      RegisterFaultJointRecord.recordLaw i noise m epsilon he pi k h p.organism := by
  rw [recordLaw,RegisterFaultJointRecord.recordLaw,PMF.map_comp]
  congr 1
  funext w
  rw [Function.comp_apply,trace_erase i m pi _ h p,
    RegisterFaultInfiniteRecord.trace_tapeEvents]


def recordAt {n : ℕ} (i : Fin n) (m : Mechanism) (p : ClockedOrganism n)
    (es : List Event) (k : ℕ) : ClockedRecord n :=
  let e := (es[k]?).getD (none,false,false)
  step i m (runParent i m p (es.take k)) e.1 e.2.1 e.2.2

theorem actual_run_child_identity {n : ℕ} (i : Fin n) (m : Mechanism)
    (p c : ClockedOrganism n) (es : List Event) (k : ℕ) (hk : k < es.length)
    (hc : (recordAt i m p es k).child = some c) :
    c.identity = p.identity ++ [(p.clock+k,((es[k]?).getD (none,false,false)).2.2)] := by
  have hsrc := actual_child_source i m (runParent i m p (es.take k)) c _ _ _ hc
  rw [runParent_identity,runParent_clock,List.length_take, min_eq_left hk.le] at hsrc
  exact hsrc.2.1


/-- Parental provenance in the ACTUAL executed prefix, rather than an attached
parent token: the real prefix state is an offspring parent, and its identity
is exactly the child's journal prefix. -/
theorem actual_run_parent_provenance {n : ℕ} (i : Fin n) (m : Mechanism)
    (p c : ClockedOrganism n) (es : List Event) (k : ℕ) (hk : k < es.length)
    (hc : (recordAt i m p es k).child = some c) :
    (lineage i m).OffspringOf (runParent i m p (es.take k)) c ∧
      c.identity.dropLast = p.identity ∧
      c.identity = p.identity ++ [(p.clock+k,((es[k]?).getD (none,false,false)).2.2)] := by
  refine ⟨actual_child_offspring i m _ c _ _ _ hc,?_,actual_run_child_identity i m p c es k hk hc⟩
  rw [actual_child_parent_prefix i m _ c _ _ _ hc,runParent_identity]

/-- The same retained parent's distinct actual transaction times produce
unequal child identities, even when sampled Boolean labels are equal. -/
theorem distinct_births_in_run {n : ℕ} (i : Fin n) (m : Mechanism)
    (p c d : ClockedOrganism n) (es : List Event) (j k : ℕ)
    (hj : j < es.length) (hk : k < es.length) (hne : j ≠ k)
    (hc : (recordAt i m p es j).child = some c)
    (hd : (recordAt i m p es k).child = some d) : c.identity ≠ d.identity := by
  rw [actual_run_child_identity i m p c es j hj hc,
    actual_run_child_identity i m p d es k hk hd]
  intro heq
  have hsing := List.append_cancel_left heq
  have htime : p.clock+j = p.clock+k := congrArg Prod.fst (List.singleton_inj.mp hsing)
  exact hne (by omega)

section Maintenance
open UEOT.V3.Compression.Objecthood
open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open UEOT.V3.Compression.Objecthood.JointHomeostasis
open UEOT.V3.Compression.Objecthood.OntogeneticConstruction
open UEOT.V3.ViabilityKernel
open RegisterFaultSource
variable {n : ℕ} [MeasurableSpace (State n)] [MeasurableSingletonClass (State n)]

/-- The timestamped child is the original source's literal child, so its SAME
physical/program seed enters the original P5 family under the same hazard. -/
theorem actual_child_enters_maintenance (i : Fin n) (m : Mechanism)
    (p c : ClockedOrganism n) (a : Action) (mode label : Bool)
    (hp : p.organism.program = m.goal)
    (hc : (step i m p a mode label).child = some c) (epsilon : NNReal) (he : epsilon ≤ 1) :
    let seed : OntogeneticSeed (State n) Bool := ⟨c.organism.physical,c.organism.program⟩
    let S := finiteJointRecurrentHomeostasisSystem
      (physical i) (target i m.goal) (target_fixed i m.goal) (certificate i m.goal)
      (substrate i) codec m.goal (compiled_dynamics_implements i m.goal)
      (fault i) epsilon he (actual_fault_envelope i m.goal)
    StaysIn (PMF.pure (assembleRepairOrganization (substrate i) codec seed)) S.carrier := by
  exact actual_mode_birth_enters_maintenance i m epsilon he p.organism c.organism a mode label hp
    (actual_child_source i m p c a mode label hc).1
end Maintenance

/-- A raw request is executed by the literal mechanism. There is no attached
birth-success or parent certificate. Clocked parent states in a run are computed
by runParent; arbitrary supplied founders remain declared model inputs. -/
structure Request (n : ℕ) where
  parent : ClockedOrganism n
  action : Action
  mode : Bool
  label : Bool

def observedChildID {n : ℕ} (i : Fin n) (m : Mechanism) (q : Request n) : Option Identity :=
  (step i m q.parent q.action q.mode q.label).child.map ClockedOrganism.identity

def actualParent {n : ℕ} (i : Fin n) (m : Mechanism) (q : Request n) : Option Identity :=
  (step i m q.parent q.action q.mode q.label).child.map (fun _ => q.parent.identity)

/-- Failed births retain None. For actual births, the interpreted parent is
the prefix of the actual produced child journal, proved by execution. -/
theorem actualParent_eq_child_prefix {n : ℕ} (i : Fin n) (m : Mechanism) (q : Request n) :
    actualParent i m q = (observedChildID i m q).map List.dropLast := by
  cases hc : (step i m q.parent q.action q.mode q.label).child with
  | none => simp [actualParent,observedChildID,hc]
  | some c =>
      simp only [actualParent,observedChildID,hc,Option.map_some]
      exact congrArg some (actual_child_parent_prefix i m q.parent c q.action q.mode q.label hc).symm

def childJournalClass {n : ℕ} (i : Fin n) (m : Mechanism) : Setoid (Request n) :=
  Setoid.ker (observedChildID i m)

theorem child_journal_parent_bridge {n : ℕ} (i : Fin n) (m : Mechanism) :
    ObjectClassParentBridge (childJournalClass i m) (actualParent i m) where
  parent_eq_of_class := by
    intro a b hab
    change observedChildID i m a = observedChildID i m b at hab
    rw [actualParent_eq_child_prefix,actualParent_eq_child_prefix,hab]

/-- Original P12 consumer with the parent bridge discharged. Statistical
recovery of this permitted timestamped child/failure journal remains the stated
learning contract; no journal access is inferred from unlabelled physics. -/
theorem journal_discovery_consumes_p12 {n : ℕ} (i : Fin n) (m : Mechanism)
    {Omega : ℕ → Type*} [∀ k, MeasurableSpace (Omega k)]
    (C : StatisticalConsistency.ChangingSampleEventContract Omega)
    (truth : Request n) (estimate : ∀ k, Omega k → Request n)
    (hgood : ∀ k w, w ∈ C.good k → observedChildID i m (estimate k w) = observedChildID i m truth) :
    let D := objectClassDiscoveryContract_of_goodEvent C (fun _ => True)
      (childJournalClass i m) truth estimate trivial (fun _ _ => trivial) hgood
    Tendsto (fun k => (D.mu k).real
      {w | actualParent i m (D.estimate k w) ≠ actualParent i m truth}) atTop (𝓝 0) := by
  dsimp only
  exact p12_discovered_parent_tendsto_lifecycleParent
    (objectClassDiscoveryContract_of_goodEvent C (fun _ => True)
      (childJournalClass i m) truth estimate trivial (fun _ _ => trivial) hgood)
    (actualParent i m) (child_journal_parent_bridge i m) (actualParent i m truth) rfl

def witnessParent : ClockedOrganism 1 := ⟨⟨[],fun _ => false,true⟩,[],0⟩
def witnessEvents : List Event := [(some true,true,true),(none,false,true),(some true,true,true)]

/-- Repeated equal labels at different actual times yield new child IDs.
The middle environmental fault is retained as a failed birth and advances time. -/
theorem repeated_label_failure_preserving_witness :
    let i : Fin 1 := 0
    let m : Mechanism := ⟨true,1⟩
    ((recordAt i m witnessParent witnessEvents 0).child.map ClockedOrganism.identity = some [(0,true)]) ∧
    ((recordAt i m witnessParent witnessEvents 1).child = none) ∧
    ((recordAt i m witnessParent witnessEvents 2).child.map ClockedOrganism.identity = some [(2,true)]) ∧
    (runParent i m witnessParent witnessEvents).clock = 3 ∧
    ((recordAt i m witnessParent witnessEvents 0).child.map (fun c => c.organism.history) = some [true]) ∧
    ((recordAt i m witnessParent witnessEvents 2).child.map (fun c => c.organism.history) = some [true]) := by
  norm_num [recordAt,witnessParent,witnessEvents,runParent,step,modeRecordStep,recordStep,
    birthEvent,repairEvent,execute_compiled,update]

/-- The same failed-middle-stage word has positive mass under the SAME
compiled program, hazard 1/4 and fair source labels, without retries. -/
theorem positive_noise_witness_mass :
    let pi := selectorPolicy ((substrate (0 : Fin 1)).execute true)
    let w : RegisterFaultJointRecord.Tape 3 := (some true,true,true,none,false,true,some true,true,true,())
    (RegisterFaultJointRecord.tapeLaw 0 (PMF.uniformOfFintype Bool) (⟨true,1⟩ : Mechanism) (1/4)
      (by exact_mod_cast (by norm_num : (1/4 : ℝ) ≤ 1)) pi 3 (t:=0)
      (fun _ => false) witnessParent.organism w).toReal = 9/512 := by
  norm_num [RegisterFaultJointRecord.tapeLaw,FiniteProbabilityRow.ofRealRow_apply_toReal,
    RegisterFaultJointRecord.weight,selectorPolicy,
    witnessParent,modeRecordStep,recordStep,RegisterFaultControlModel.modeLaw,
    RegisterFaultControlModel.modeProbability,RegisterFaultControlModel.repairChance,
    execute_compiled,update,PMF.uniformOfFintype_apply]


end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterTimestampedBirthSource
