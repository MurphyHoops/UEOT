import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterTimestampedBirthSource

/-!
Original commitment: actual repair retains identity; actual multi-parent births create fresh offspring and determine provenance.
Existing premise: the timestamp source treats one retained parent; P12/Price still consume independent population lineage bridges.
Premise reduced: derive fresh global slot identity and unique actual parent from a finite founder store and literal event allocator.
Models: NEW addressable serialized population with reliable chronological journal; failures and invalid addresses consume ticks.
Consumers: original timestamp birth/physical erasure, P5 child maintenance, P8 repair distinction, and P12 journal-parent discovery.

Founder IDs are their positions in the supplied finite founder list, not supplied
unique labels. Founder slots are explicitly registered owned individuals; equal
organism values do not identify their owners. IDs are local to this one registered
serialized population, not independent concurrent runs. Every transaction appends exactly one optional slot: a successful
birth occupies the fresh slot, while faults/failed births/invalid addresses leave
None. Existing parent slots are updated in place. A request contains only a
parent slot address and the OLD register action/mode/label. Population addressing
and the reliable journal are explicit additional model permissions; there is no
new organism action, parent reset, installation, or inferred ancestry from bare
physical state. The actual global event clock is store.length. Timestamp metadata
is re-clocked at dispatch while organism and identity are retained.

This first source module does not assume or construct a normalized transmission
kernel, fertility, a random-generation ratio, or a Perron limit. Actual inherited
program types and nonempty-generation normalization are a subsequent consumer.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationHistorySource
open Set MeasureTheory Filter Topology
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.TheoryCompletion.InverseObjecthood
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose
open RegisterFaultJointRecord
open RegisterTimestampedBirthSource (ClockedOrganism ClockedRecord)
noncomputable section

/-- Slot addresses ARE identities. Empty slots retain failed actual ticks. -/
abbrev Store (n : ℕ) := List (Option (ClockedOrganism n))

structure Request where
  parent : ℕ
  action : Action
  mode : Bool
  label : Bool
  deriving DecidableEq

/-- Fixed scheduler input; validity is checked by actual lookup, not assumed. -/
def defaultRequest : Request := ⟨0,none,false,false⟩

def founders {n : ℕ} (os : List (Organism n)) : Store n :=
  os.mapIdx (fun j o => some ⟨o,[(j,false)],0⟩)

@[simp] theorem founders_length {n : ℕ} (os : List (Organism n)) :
    (founders os).length = os.length := by simp [founders]

def lookup {n : ℕ} (s : Store n) (j : ℕ) : Option (ClockedOrganism n) := (s[j]?).join

/-- Re-clock only source metadata at actual dispatch, then reuse the original
literal timestamped transaction. It executes on the stored organism itself. -/
def transaction {n : ℕ} (i : Fin n) (m : Mechanism) (s : Store n) (q : Request) : Option (ClockedRecord n) :=
  (lookup s q.parent).map (fun p =>
    RegisterTimestampedBirthSource.step i m {p with clock := s.length} q.action q.mode q.label)

def child {n : ℕ} (i : Fin n) (m : Mechanism) (s : Store n) (q : Request) : Option (ClockedOrganism n) :=
  (transaction i m s q).bind ClockedRecord.child

def next {n : ℕ} (i : Fin n) (m : Mechanism) (s : Store n) (q : Request) : Store n :=
  (match transaction i m s q with
  | none => s
  | some r => s.set q.parent (some r.parentAfter)) ++ [child i m s q]

@[simp] theorem next_length {n : ℕ} (i : Fin n) (m : Mechanism) (s : Store n) (q : Request) :
    (next i m s q).length = s.length+1 := by
  unfold next
  split <;> simp

/-- A missing/invalid address executes no parent transaction, creates no child,
and still appends the failed tick instead of borrowing or resetting a parent. -/
theorem invalid_request {n : ℕ} (i : Fin n) (m : Mechanism) (s : Store n) (q : Request)
    (h : lookup s q.parent = none) :
    transaction i m s q = none ∧ child i m s q = none ∧ next i m s q = s ++ [none] := by
  simp [transaction,child,next,h]

/-- Dispatching one parent preserves EVERY other already registered slot. -/
theorem next_other_slot {n : ℕ} (i : Fin n) (m : Mechanism) (s : Store n) (q : Request)
    (j : ℕ) (hj : j < s.length) (hne : q.parent ≠ j) :
    lookup (next i m s q) j = lookup s j := by
  unfold next
  split
  · simp only [lookup]
    rw [List.getElem?_append_left hj]
  · simp only [lookup]
    rw [List.getElem?_append_left (by simpa using hj),List.getElem?_set_ne hne]

/-- A successful fresh slot ID is computed from actual birth, not an input token. -/
def childID {n : ℕ} (i : Fin n) (m : Mechanism) (s : Store n) (q : Request) : Option ℕ :=
  (child i m s q).map (fun _ => s.length)

def parentID {n : ℕ} (i : Fin n) (m : Mechanism) (s : Store n) (q : Request) : Option ℕ :=
  (child i m s q).map (fun _ => q.parent)

def run {n : ℕ} (i : Fin n) (m : Mechanism) (s : Store n) (es : List Request) : Store n :=
  es.foldl (next i m) s

@[simp] theorem run_length {n : ℕ} (i : Fin n) (m : Mechanism) (s : Store n) (es : List Request) :
    (run i m s es).length = s.length+es.length := by
  induction es generalizing s with
  | nil => simp [run]
  | cons e es ih => change (run i m (next i m s e) es).length = _; rw [ih,next_length]; simp; omega

/-- The ACTUAL prefix store is replayed; no independently supplied parent is
attached to a requested transaction. -/
def storeBefore {n : ℕ} (i : Fin n) (m : Mechanism) (os : List (Organism n))
    (es : List Request) (k : ℕ) : Store n := run i m (founders os) (es.take k)

def requestAt (es : List Request) (k : ℕ) : Request := (es[k]?).getD defaultRequest

def childAt {n : ℕ} (i : Fin n) (m : Mechanism) (os : List (Organism n))
    (es : List Request) (k : ℕ) : Option (ClockedOrganism n) :=
  child i m (storeBefore i m os es k) (requestAt es k)

def observedChildID {n : ℕ} (i : Fin n) (m : Mechanism) (os : List (Organism n))
    (es : List Request) (k : Fin es.length) : Option ℕ :=
  childID i m (storeBefore i m os es k) (requestAt es k)

def actualParent {n : ℕ} (i : Fin n) (m : Mechanism) (os : List (Organism n))
    (es : List Request) (k : Fin es.length) : Option ℕ :=
  parentID i m (storeBefore i m os es k) (requestAt es k)

@[simp] theorem storeBefore_length {n : ℕ} (i : Fin n) (m : Mechanism)
    (os : List (Organism n)) (es : List Request) (k : ℕ) (hk : k ≤ es.length) :
    (storeBefore i m os es k).length = os.length+k := by
  simp [storeBefore,List.length_take,min_eq_left hk]

/-- Original physical/program/birth/cost transaction on the actually addressed
parent. Re-clocking adds no physical write and leaves every old record field. -/
theorem transaction_erasure {n : ℕ} (i : Fin n) (m : Mechanism) (s : Store n) (q : Request)
    (p : ClockedOrganism n) (hp : lookup s q.parent = some p) :
    (transaction i m s q).map RegisterTimestampedBirthSource.eraseRecord =
      some (modeRecordStep i m p.organism q.action q.mode q.label) := by
  simp [transaction,hp]

/-- Execution derives both the actual source child and its inherited program. -/
theorem actual_child_source {n : ℕ} (i : Fin n) (m : Mechanism) (s : Store n) (q : Request)
    (c : ClockedOrganism n) (hc : child i m s q = some c) :
    ∃ p : ClockedOrganism n, lookup s q.parent = some p ∧
      (modeRecordStep i m p.organism q.action q.mode q.label).transaction.child = some c.organism ∧
      c.organism.program = p.organism.program ∧ q.parent < s.length := by
  unfold child transaction at hc
  cases hp : lookup s q.parent with
  | none => simp [hp] at hc
  | some p =>
    simp only [hp,Option.map_some,Option.bind_some] at hc
    have hsrc := RegisterTimestampedBirthSource.actual_child_source i m
      {p with clock := s.length} c q.action q.mode q.label hc
    have hrepair := actual_child_requires_repair i m p.organism c.organism q.action q.mode q.label hsrc.1
    have hprogram := (RegisterJointRecord.record_child_source i m p.organism q.action q.label c.organism hrepair.2).2.2
    refine ⟨p,rfl,hsrc.1,hprogram,?_⟩
    by_contra hn
    have hz : lookup s q.parent = none := by
      simp [lookup,List.getElem?_eq_none (by omega : s.length ≤ q.parent)]
    rw [hz] at hp
    cases hp

/-- The allocated ID is outside the entire prior finite store, including all
other parents and descendants, so no global uniqueness certificate is assumed. -/
theorem actual_child_fresh {n : ℕ} (i : Fin n) (m : Mechanism) (s : Store n) (q : Request)
    (c : ClockedOrganism n) (hc : child i m s q = some c) :
    childID i m s q = some s.length ∧ lookup s s.length = none ∧ q.parent < s.length := by
  refine ⟨by simp [childID,hc],by simp [lookup],(actual_child_source i m s q c hc).choose_spec.2.2.2⟩

/-- At the actual new slot the allocated child is the literal source child. -/
theorem next_new_slot {n : ℕ} (i : Fin n) (m : Mechanism) (s : Store n) (q : Request) :
    lookup (next i m s q) s.length = child i m s q := by
  unfold next
  split <;> simp [lookup]

/-- Distinct transaction indices allocate unequal IDs even for different
parents, different generations and repeated equal labels. Failures still tick. -/
theorem distinct_actual_births {n : ℕ} (i : Fin n) (m : Mechanism)
    (os : List (Organism n)) (es : List Request) (j k : Fin es.length)
    (cj ck : ClockedOrganism n) (hj : childAt i m os es j = some cj)
    (hk : childAt i m os es k = some ck) (hne : j ≠ k) :
    observedChildID i m os es j ≠ observedChildID i m os es k := by
  simp only [observedChildID,childID,childAt] at *
  rw [hj,hk,Option.map_some,Option.map_some,storeBefore_length i m os es j j.isLt.le,
    storeBefore_length i m os es k k.isLt.le]
  intro heq
  have hv : (j : ℕ) = k := by simpa using Option.some.inj heq
  exact hne (Fin.ext hv)

/-- Repair and fault update the addressed parent's physical state in its SAME
slot; that retained address is never the newly allocated child address. -/
theorem retained_parent_identity {n : ℕ} (i : Fin n) (m : Mechanism) (s : Store n) (q : Request)
    (p : ClockedOrganism n) (hp : lookup s q.parent = some p) :
    let r := RegisterTimestampedBirthSource.step i m {p with clock := s.length} q.action q.mode q.label
    lookup (next i m s q) q.parent = some r.parentAfter ∧
      q.parent < s.length := by
  have hlt : q.parent < s.length := by
    by_contra hn
    have hz : lookup s q.parent = none := by simp [lookup,List.getElem?_eq_none (by omega : s.length ≤ q.parent)]
    rw [hz] at hp
    cases hp
  refine ⟨?_,hlt⟩
  have ht : transaction i m s q = some
      (RegisterTimestampedBirthSource.step i m {p with clock := s.length} q.action q.mode q.label) := by
    simp [transaction,hp]
  rw [next,ht]
  simp only [lookup]
  rw [List.getElem?_append_left (by simpa using hlt),List.getElem?_set_self hlt]
  rfl


private theorem observedChildID_eq {n : ℕ} (i : Fin n) (m : Mechanism)
    (os : List (Organism n)) (es : List Request) (k : Fin es.length) :
    observedChildID i m os es k = (childAt i m os es k).map (fun _ => os.length+k) := by
  unfold observedChildID childID childAt
  rw [storeBefore_length i m os es k k.isLt.le]

private theorem actualParent_eq {n : ℕ} (i : Fin n) (m : Mechanism)
    (os : List (Organism n)) (es : List Request) (k : Fin es.length) :
    actualParent i m os es k = (childAt i m os es k).map (fun _ => (requestAt es k).parent) := rfl

/-- The actual recorded child ID determines ONE actual executed parent across
all parents and generations of this registered run. Empty outcomes stay None. -/
theorem parent_eq_of_childID {n : ℕ} (i : Fin n) (m : Mechanism)
    (os : List (Organism n)) (es : List Request) (j k : Fin es.length)
    (h : observedChildID i m os es j = observedChildID i m os es k) :
    actualParent i m os es j = actualParent i m os es k := by
  rw [observedChildID_eq,observedChildID_eq] at h
  rw [actualParent_eq,actualParent_eq]
  cases hj : childAt i m os es j with
  | none =>
    cases hk : childAt i m os es k <;> simp [hj,hk] at h ⊢
  | some cj =>
    cases hk : childAt i m os es k with
    | none => simp [hj,hk] at h
    | some ck =>
      simp only [hj,hk,Option.map_some,Option.some.injEq] at h
      have heq : j = k := Fin.ext (by omega)
      subst k
      rfl

/-- Parent attribution is not an input function: it is computed from the
actually executed addressed requests, and is functional on every actual child. -/
theorem actual_parent_unique {n : ℕ} (i : Fin n) (m : Mechanism)
    (os : List (Organism n)) (es : List Request) (id p q : ℕ)
    (hp : ∃ j, observedChildID i m os es j = some id ∧ actualParent i m os es j = some p)
    (hq : ∃ k, observedChildID i m os es k = some id ∧ actualParent i m os es k = some q) : p = q := by
  obtain ⟨j,hj,hjp⟩ := hp
  obtain ⟨k,hk,hkq⟩ := hq
  have heq := parent_eq_of_childID i m os es j k (hj.trans hk.symm)
  rw [hjp,hkq] at heq
  exact Option.some.inj heq

/-- P8 lineage is the actual finite birth journal, not a supplied genealogy. -/
def lineage {n : ℕ} (i : Fin n) (m : Mechanism) (os : List (Organism n)) (es : List Request) :
    LineageSemantics ℕ ℕ where
  identity := id
  parentOf := fun p c => ∃ k, observedChildID i m os es k = some c ∧ actualParent i m os es k = some p

/-- Each successful allocated child is downstream of an actual existing parent
with strictly smaller ID, hence never the parent's same-object repair. -/
theorem actual_birth_offspring {n : ℕ} (i : Fin n) (m : Mechanism)
    (os : List (Organism n)) (es : List Request) (k : Fin es.length)
    (c : ClockedOrganism n) (hc : childAt i m os es k = some c) :
    (lineage i m os es).OffspringOf (requestAt es k).parent (os.length+k) := by
  have hsrc := actual_child_source i m (storeBefore i m os es k) (requestAt es k) c hc
  have hlt := hsrc.choose_spec.2.2.2
  rw [storeBefore_length i m os es k k.isLt.le] at hlt
  refine ⟨⟨k,?_,?_⟩,?_⟩
  · rw [observedChildID_eq,hc]; rfl
  · rw [actualParent_eq,hc]; rfl
  · change (requestAt es k).parent ≠ os.length+k
    exact ne_of_lt hlt

def childJournalClass {n : ℕ} (i : Fin n) (m : Mechanism)
    (os : List (Organism n)) (es : List Request) : Setoid (Fin es.length) :=
  Setoid.ker (observedChildID i m os es)

/-- Original P12 parent bridge now follows from actual multi-parent allocation
and chronological source execution, without a global uniqueness/parent field. -/
theorem child_journal_parent_bridge {n : ℕ} (i : Fin n) (m : Mechanism)
    (os : List (Organism n)) (es : List Request) :
    ObjectClassParentBridge (childJournalClass i m os es) (actualParent i m os es) where
  parent_eq_of_class := by
    intro a b hab
    exact parent_eq_of_childID i m os es a b hab

/-- Statistical recovery is explicitly of this permitted SAME population-run
birth/failure journal. No history recovery is inferred from unlabelled physics. -/
theorem journal_discovery_consumes_p12 {n : ℕ} (i : Fin n) (m : Mechanism)
    (os : List (Organism n)) (es : List Request)
    {Omega : ℕ → Type*} [∀ k, MeasurableSpace (Omega k)]
    (C : StatisticalConsistency.ChangingSampleEventContract Omega)
    (truth : Fin es.length) (estimate : ∀ k, Omega k → Fin es.length)
    (hgood : ∀ k w, w ∈ C.good k →
      observedChildID i m os es (estimate k w) = observedChildID i m os es truth) :
    let D := objectClassDiscoveryContract_of_goodEvent C (fun _ => True)
      (childJournalClass i m os es) truth estimate trivial (fun _ _ => trivial) hgood
    Tendsto (fun k => (D.mu k).real
      {w | actualParent i m os es (D.estimate k w) ≠ actualParent i m os es truth}) atTop (𝓝 0) := by
  dsimp only
  exact p12_discovered_parent_tendsto_lifecycleParent
    (objectClassDiscoveryContract_of_goodEvent C (fun _ => True)
      (childJournalClass i m os es) truth estimate trivial (fun _ _ => trivial) hgood)
    (actualParent i m os es) (child_journal_parent_bridge i m os es) (actualParent i m os es truth) rfl

section Maintenance
open UEOT.V3.Compression.Objecthood
open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open UEOT.V3.Compression.Objecthood.JointHomeostasis
open UEOT.V3.Compression.Objecthood.OntogeneticConstruction
open UEOT.V3.ViabilityKernel
open RegisterFaultSource
variable {n : ℕ} [MeasurableSpace (State n)] [MeasurableSingletonClass (State n)]

/-- A child from the ACTUAL finite population store enters the SAME original P5
maintenance family. Program equality is checked on the addressed stored parent. -/
theorem actual_child_enters_maintenance (i : Fin n) (m : Mechanism) (s : Store n) (q : Request)
    (p c : ClockedOrganism n) (hp : lookup s q.parent = some p)
    (hprogram : p.organism.program = m.goal) (hc : child i m s q = some c)
    (epsilon : NNReal) (he : epsilon ≤ 1) :
    let seed : OntogeneticSeed (State n) Bool := ⟨c.organism.physical,c.organism.program⟩
    let S := finiteJointRecurrentHomeostasisSystem
      (physical i) (target i m.goal) (target_fixed i m.goal) (certificate i m.goal)
      (substrate i) codec m.goal (compiled_dynamics_implements i m.goal)
      (fault i) epsilon he (actual_fault_envelope i m.goal)
    StaysIn (PMF.pure (assembleRepairOrganization (substrate i) codec seed)) S.carrier := by
  have hstep : (RegisterTimestampedBirthSource.step i m {p with clock := s.length}
      q.action q.mode q.label).child = some c := by
    simpa [child,transaction,hp] using hc
  exact RegisterTimestampedBirthSource.actual_child_enters_maintenance i m
    {p with clock := s.length} c q.action q.mode q.label hprogram hstep epsilon he
end Maintenance

/-- Two registered founders with different inherited programs. All four birth
labels are equal; the third tick fails and is retained as an empty slot. -/
def witnessFounders : List (Organism 1) := [⟨[],fun _ => false,false⟩,⟨[],fun _ => false,true⟩]
def witnessRequests : List Request :=
  [⟨0,none,true,true⟩,⟨1,some true,true,true⟩,⟨2,none,false,true⟩,⟨3,none,true,true⟩]

/-- Actual two-parent/two-generation source witness: children at 2 and 3 have
different source programs; ID 4 is a retained failure; parent 3 creates child 5.
The observed Boolean label true does NOT equal the first child's type false. -/
theorem multi_parent_generation_witness :
    let s := run (0 : Fin 1) ⟨true,1⟩ (founders witnessFounders) witnessRequests
    (s.length = 6) ∧
      ((lookup s 2).map (fun c => c.organism.program) = some false) ∧
      ((lookup s 3).map (fun c => c.organism.program) = some true) ∧
      (lookup s 4 = none) ∧
      ((lookup s 5).map (fun c => c.organism.program) = some true) := by
  norm_num [run,founders,witnessFounders,witnessRequests,next,transaction,lookup,child,
    RegisterTimestampedBirthSource.step,modeRecordStep,RegisterJointRecord.recordStep,
    birthEvent,repairEvent,execute_compiled,update]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationHistorySource
