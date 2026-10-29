import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationTypePrice
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultFeedbackResource

/-!
Original commitment: actual mixed-program copying, maintenance, purpose and Price must share compatible source conditions.
Existing premise: fixed-goal population P5 needs parent.program=m.goal; mixed-program Price alone gives only counts.
Premise reduced: compute EACH mechanism from the actual addressed parent's protected program, then derive its child's OWN P5.
Models: NEW own-program-fault environment, common write cost c; old fixed-goal source/data/theorems remain unchanged.
Consumers: source birth/freshness/provenance, every-type original P5, exact old-cohort offspring projection/Price, literal paid repair.

At each actual lookup, m_parent=(stored parent.program,c). Faults now write the
opposite of THAT protected program. This is a genuinely different environment
from the old fixed global m.goal. No action, reset or installation is added.
A frozen OLD-address cohort visits each pre-existing address once; only its
actual offspring array is projected to old TypePrice. Retained faulted parents
and the whole final store need not match the old model. No whole-store frequency,
population-wide optimum, arbitrary scheduler P5 invariance, or closed-resource
energy creation is asserted. The inherited protection/finite metadata and old
address/journal permissions remain declared model inputs.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterOwnProgramPopulation
open MeasureTheory ProbabilityTheory
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.EvolutionPrice
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose
open RegisterFaultControlModel RegisterFaultJointRecord
open RegisterPopulationHistorySource (Store Request)
open RegisterTimestampedBirthSource (ClockedOrganism ClockedRecord)
open scoped BigOperators
noncomputable section

/-- Actual stored code determines the NEW fault target. Invalid addresses
execute no transaction, so their fixed fallback target has no physical effect. -/
def mechanism {n : ℕ} (c : NNReal) (s : Store n) (q : Request) : Mechanism :=
  ⟨match RegisterPopulationHistorySource.lookup s q.parent with
    | none => false | some p => p.organism.program,c⟩

theorem mechanism_eq {n : ℕ} (c : NNReal) (s : Store n) (q : Request) (p : ClockedOrganism n)
    (hp : RegisterPopulationHistorySource.lookup s q.parent = some p) :
    mechanism c s q = ⟨p.organism.program,c⟩ := by simp [mechanism,hp]

def transaction {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (q : Request) : Option (ClockedRecord n) :=
  RegisterPopulationHistorySource.transaction i (mechanism c s q) s q

def child {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (q : Request) : Option (ClockedOrganism n) :=
  RegisterPopulationHistorySource.child i (mechanism c s q) s q

def next {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (q : Request) : Store n :=
  RegisterPopulationHistorySource.next i (mechanism c s q) s q

def childID {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (q : Request) : Option ℕ :=
  RegisterPopulationHistorySource.childID i (mechanism c s q) s q

def parentID {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (q : Request) : Option ℕ :=
  RegisterPopulationHistorySource.parentID i (mechanism c s q) s q

@[simp] theorem next_length {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (q : Request) :
    (next i c s q).length = s.length+1 := RegisterPopulationHistorySource.next_length i _ s q

theorem next_other_slot {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (q : Request)
    (j : ℕ) (hj : j < s.length) (hne : q.parent ≠ j) :
    RegisterPopulationHistorySource.lookup (next i c s q) j = RegisterPopulationHistorySource.lookup s j :=
  RegisterPopulationHistorySource.next_other_slot i _ s q j hj hne

theorem next_new_slot {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (q : Request) :
    RegisterPopulationHistorySource.lookup (next i c s q) s.length = child i c s q :=
  RegisterPopulationHistorySource.next_new_slot i _ s q

/-- Old allocator provenance is reused at the mechanism actually computed by
lookup. The program/goal equality is DERIVED and never an external field. -/
theorem actual_child_source {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (q : Request)
    (d : ClockedOrganism n) (hd : child i c s q = some d) :
    ∃ p : ClockedOrganism n, RegisterPopulationHistorySource.lookup s q.parent = some p ∧
      (modeRecordStep i ⟨p.organism.program,c⟩ p.organism q.action q.mode q.label).transaction.child = some d.organism ∧
      d.organism.program = p.organism.program ∧ q.parent < s.length := by
  obtain ⟨p,hp,hstep,hprogram,hlt⟩ := RegisterPopulationHistorySource.actual_child_source i (mechanism c s q) s q d hd
  rw [mechanism_eq c s q p hp] at hstep
  exact ⟨p,hp,hstep,hprogram,hlt⟩

theorem actual_child_fresh {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (q : Request)
    (d : ClockedOrganism n) (hd : child i c s q = some d) :
    childID i c s q = some s.length ∧ RegisterPopulationHistorySource.lookup s s.length = none ∧ q.parent < s.length :=
  RegisterPopulationHistorySource.actual_child_fresh i _ s q d hd

/-- Full physical/birth/fee erasure is the original transaction for the ACTUAL
parent with its OWN mechanism, not an old global target silently replaced. -/
theorem transaction_erasure {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (q : Request)
    (p : ClockedOrganism n) (hp : RegisterPopulationHistorySource.lookup s q.parent = some p) :
    (transaction i c s q).map RegisterTimestampedBirthSource.eraseRecord =
      some (modeRecordStep i ⟨p.organism.program,c⟩ p.organism q.action q.mode q.label) := by
  unfold transaction
  rw [mechanism_eq c s q p hp]
  exact RegisterPopulationHistorySource.transaction_erasure i ⟨p.organism.program,c⟩ s q p hp

theorem retained_parent_identity {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (q : Request)
    (p : ClockedOrganism n) (hp : RegisterPopulationHistorySource.lookup s q.parent = some p) :
    let r := RegisterTimestampedBirthSource.step i ⟨p.organism.program,c⟩ {p with clock := s.length} q.action q.mode q.label
    RegisterPopulationHistorySource.lookup (next i c s q) q.parent = some r.parentAfter ∧ q.parent < s.length := by
  unfold next
  rw [mechanism_eq c s q p hp]
  exact RegisterPopulationHistorySource.retained_parent_identity i ⟨p.organism.program,c⟩ s q p hp

/-- A real newborn is already physically legitimate for its inherited code;
this conclusion does not rely on a free assembly/repair of an arbitrary seed. -/
theorem child_legitimate {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (q : Request)
    (d : ClockedOrganism n) (hd : child i c s q = some d) : d.organism.physical i = d.organism.program := by
  obtain ⟨p,hp,hstep,hprogram,_⟩ := actual_child_source i c s q d hd
  have hr := actual_child_requires_repair i ⟨p.organism.program,c⟩ p.organism d.organism q.action q.mode q.label hstep
  have hphys := RegisterJointRecord.record_child_physical i ⟨p.organism.program,c⟩ p.organism q.action q.label d.organism hr.2
  have hg : update i p.organism.physical q.action i = p.organism.program := by
    by_contra hn
    simp [RegisterJointRecord.recordStep,hn] at hr
  rw [hphys,hprogram]
  exact hg

section Maintenance
open UEOT.V3.Compression.Objecthood
open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open UEOT.V3.Compression.Objecthood.JointHomeostasis
open UEOT.V3.Compression.Objecthood.OntogeneticConstruction
open UEOT.V3.ViabilityKernel
open RegisterFaultSource
variable {n : ℕ} [MeasurableSpace (State n)] [MeasurableSingletonClass (State n)]

/-- Every actual program type enters its OWN original P5 using the SAME literal
child. No cross-type parent.program=m.goal premise remains. -/
theorem actual_child_enters_own_maintenance (i : Fin n) (c : NNReal) (s : Store n) (q : Request)
    (d : ClockedOrganism n) (hd : child i c s q = some d) (epsilon : NNReal) (he : epsilon ≤ 1) :
    let b := d.organism.program
    let seed : OntogeneticSeed (State n) Bool := ⟨d.organism.physical,b⟩
    let S := finiteJointRecurrentHomeostasisSystem
      (physical i) (target i b) (target_fixed i b) (certificate i b)
      (substrate i) codec b (compiled_dynamics_implements i b)
      (fault i) epsilon he (actual_fault_envelope i b)
    StaysIn (PMF.pure (assembleRepairOrganization (substrate i) codec seed)) S.carrier := by
  obtain ⟨p,_,hstep,hprogram,_⟩ := actual_child_source i c s q d hd
  rw [← hprogram] at hstep
  exact actual_mode_birth_enters_maintenance i ⟨d.organism.program,c⟩ epsilon he
    p.organism d.organism q.action q.mode q.label hprogram.symm hstep
end Maintenance

/-- The actual reproduction/cost payoff is exactly the ORIGINAL own-program
purpose source. This is an individual registered evaluation, not a global
population objective or optimal scheduling assertion. -/
theorem actual_payoff_eq {n : ℕ} (i : Fin n) (c price : NNReal) (s : Store n) (q : Request)
    (p : ClockedOrganism n) (hp : RegisterPopulationHistorySource.lookup s q.parent = some p) :
    ((transaction i c s q).map (fun r => RegisterJointRecord.payoff price
      (RegisterTimestampedBirthSource.eraseRecord r).transaction)) =
      some (modePayoff i ⟨p.organism.program,c⟩ price p.organism.physical q.action q.mode q.label) := by
  have ht := transaction_erasure i c s q p hp
  have hf := congrArg (Option.map (fun r : ModeRecord n => RegisterJointRecord.payoff price r.transaction)) ht
  simp only [Option.map_some] at hf
  rw [step_payoff i ⟨p.organism.program,c⟩ price p.organism q.action q.mode q.label rfl] at hf
  rw [Option.map_map] at hf
  exact hf

/-- Existing all-causal individual optimum for that parent's OWN registered
source, under its original price-cost condition. No global-clock population
optimality or common target across all types is inferred. -/
theorem own_individual_optimal {n : ℕ} (i : Fin n) (noise : PMF Bool) (c price epsilon : NNReal)
    (he : epsilon ≤ 1) (d : ℝ) (hd : 0 < d ∧ d < 1) (hc : (price : ℝ) * c ≤ 1) (p : ClockedOrganism n) :
    let M := RegisterFaultControlModel.model i noise ⟨p.organism.program,c⟩ price epsilon he d hd
    (selectorPolicy ((substrate i).execute p.organism.program)).infiniteValue M (t:=0) p.organism.physical =
      M.optimalValue p.organism.physical :=
  (compiled_optimal_against_all_causal.{0} i noise ⟨p.organism.program,c⟩ price epsilon he d hd hc).1 (t:=0) _


/-- Serialized scheduler: recompute the own-program mechanism at EVERY lookup. -/
def run {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (es : List Request) : Store n :=
  es.foldl (next i c) s

@[simp] theorem run_length {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (es : List Request) :
    (run i c s es).length = s.length+es.length := by
  induction es generalizing s with
  | nil => simp [run]
  | cons e es ih => change (run i c (next i c s e) es).length = _; rw [ih,next_length]; simp; omega

section Cohort
variable {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n)
variable (actions : ℕ → Action) (modes labels : ℕ → Bool)

def before (j : ℕ) : Store n :=
  run i c s ((RegisterPopulationTypePrice.cohortRequests s actions modes labels).take j)

def offspring (j : Fin s.length) : Option (ClockedOrganism n) :=
  child i c (before i c s actions modes labels j) (RegisterPopulationTypePrice.request actions modes labels j)

private theorem lookup_run_other (j : ℕ) (es : List Request) (hj : j < s.length)
    (hne : ∀ q ∈ es, q.parent ≠ j) :
    RegisterPopulationHistorySource.lookup (run i c s es) j = RegisterPopulationHistorySource.lookup s j := by
  induction es generalizing s with
  | nil => rfl
  | cons q es ih =>
    change RegisterPopulationHistorySource.lookup (run i c (next i c s q) es) j = _
    rw [ih _ (by rw [next_length]; omega) (fun r hr => hne r (by simp [hr]))]
    exact next_other_slot i c s q j hj (hne q (by simp))

theorem before_lookup (j : Fin s.length) :
    RegisterPopulationHistorySource.lookup (before i c s actions modes labels j) j =
      RegisterPopulationHistorySource.lookup s j := by
  unfold before RegisterPopulationTypePrice.cohortRequests
  rw [← List.map_take,List.take_range,min_eq_left j.isLt.le]
  apply lookup_run_other i c s j _ j.isLt
  intro q hq
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hq
  have hk' : k < (j : ℕ) := List.mem_range.mp hk
  change k ≠ (j : ℕ)
  omega

@[simp] theorem before_length (j : Fin s.length) :
    (before i c s actions modes labels j).length = s.length+j := by
  simp [before,RegisterPopulationTypePrice.cohortRequests,List.length_take]

/-- Changing the fault target changes the faulted PARENT, but never creates a
fault child. The actual repair/birth branch does not read that target. -/
private theorem timestamp_child_goal_irrelevant (p : ClockedOrganism n)
    (b b' : Bool) (a : Action) (mode label : Bool) :
    (RegisterTimestampedBirthSource.step i ⟨b,c⟩ p a mode label).child =
      (RegisterTimestampedBirthSource.step i ⟨b',c⟩ p a mode label).child := by
  cases mode <;> rfl

private theorem old_child_lookup (m : Mechanism) (s : Store n) (q : Request) (p : ClockedOrganism n)
    (hp : RegisterPopulationHistorySource.lookup s q.parent = some p) :
    RegisterPopulationHistorySource.child i m s q =
      (RegisterTimestampedBirthSource.step i m {p with clock := s.length} q.action q.mode q.label).child := by
  simp [RegisterPopulationHistorySource.child,RegisterPopulationHistorySource.transaction,hp]

/-- EXACT SAME actual offspring, including code, physical seed, timestamp
identity and failure None, for this one frozen OLD-address cohort. Only this
projection is equal; the retained faulted parents can differ. -/
theorem offspring_eq_old (b : Bool) (j : Fin s.length) :
    offspring i c s actions modes labels j =
      RegisterPopulationTypePrice.offspring i ⟨b,c⟩ s actions modes labels j := by
  have ho := before_lookup i c s actions modes labels j
  have hf := RegisterPopulationTypePrice.before_lookup i ⟨b,c⟩ s actions modes labels j
  cases hp : RegisterPopulationHistorySource.lookup s j with
  | none =>
    have ho' : RegisterPopulationHistorySource.lookup (before i c s actions modes labels j)
        (RegisterPopulationTypePrice.request actions modes labels j).parent = none := ho.trans hp
    have hf' : RegisterPopulationHistorySource.lookup
        (RegisterPopulationTypePrice.before i ⟨b,c⟩ s actions modes labels j)
        (RegisterPopulationTypePrice.request actions modes labels j).parent = none := hf.trans hp
    exact (RegisterPopulationHistorySource.invalid_request i _ _ _ ho').2.1.trans
      (RegisterPopulationHistorySource.invalid_request i _ _ _ hf').2.1.symm
  | some p =>
    have ho' : RegisterPopulationHistorySource.lookup (before i c s actions modes labels j)
        (RegisterPopulationTypePrice.request actions modes labels j).parent = some p := ho.trans hp
    have hf' : RegisterPopulationHistorySource.lookup
        (RegisterPopulationTypePrice.before i ⟨b,c⟩ s actions modes labels j)
        (RegisterPopulationTypePrice.request actions modes labels j).parent = some p := hf.trans hp
    unfold offspring child RegisterPopulationTypePrice.offspring
    rw [old_child_lookup i _ _ _ p ho',old_child_lookup i _ _ _ p hf',mechanism_eq c _ _ p ho',
      before_length,RegisterPopulationTypePrice.before_length]
    exact timestamp_child_goal_irrelevant i c _ _ _ _ _ _

/-- Source-derived active child census reused verbatim from old TypePrice.
The equality above licenses EACH member as this NEW episode's actual child. -/
theorem census_child_actual (b : Bool)
    (d : RegisterPopulationTypePrice.Children i ⟨b,c⟩ s actions modes labels) :
    offspring i c s actions modes labels d.val =
      some (RegisterPopulationTypePrice.childObject i ⟨b,c⟩ s actions modes labels d) := by
  rw [offspring_eq_old i c s actions modes labels b]
  exact (Option.some_get d.property).symm

/-- Empirical mean reads THIS episode's actual children. The exact projection
identifies its active index/count with the already-normalized old census. -/
def actualCensusMean (b : Bool) (z : Bool → ℝ) : ℝ :=
  ∑ d : RegisterPopulationTypePrice.Children i ⟨b,c⟩ s actions modes labels,
    (1 / (RegisterPopulationTypePrice.birthCount i ⟨b,c⟩ s actions modes labels : ℝ)) *
      ((offspring i c s actions modes labels d.val).map (fun x => z x.organism.program)).getD 0

def actualFertility (j : Fin s.length) : ℝ :=
  if (offspring i c s actions modes labels j).isSome then 1 else 0

theorem actualFertility_eq_old (b : Bool) :
    actualFertility i c s actions modes labels =
      RegisterPopulationTypePrice.fertility i ⟨b,c⟩ s actions modes labels := by
  funext j
  simp only [actualFertility,offspring_eq_old i c s actions modes labels b,
    RegisterPopulationTypePrice.fertility,RegisterPopulationTypePrice.born]
  exact if_congr Iff.rfl rfl rfl

theorem actualCensusMean_eq_old (b : Bool) (z : Bool → ℝ) :
    actualCensusMean i c s actions modes labels b z =
      RegisterPopulationTypePrice.empiricalOffspringMean i ⟨b,c⟩ s actions modes labels z := by
  unfold actualCensusMean RegisterPopulationTypePrice.empiricalOffspringMean
  apply Finset.sum_congr rfl
  intro d _
  rw [census_child_actual i c s actions modes labels b d]
  rfl

/-- Core P-EVO-01 on the actual new-model offspring, not the whole final store.
The baseline b is an arbitrary projection parameter, not a shared fault goal. -/
theorem own_program_type_price (b : Bool)
    (hB : 0 < RegisterPopulationTypePrice.birthCount i ⟨b,c⟩ s actions modes labels) (z : Bool → ℝ) :
    actualCensusMean i c s actions modes labels b z -
      weightedMean (RegisterPopulationTypePrice.frequency s) (RegisterPopulationTypePrice.parentTrait s z) =
    weightedCov (RegisterPopulationTypePrice.frequency s) (actualFertility i c s actions modes labels)
      (RegisterPopulationTypePrice.parentTrait s z) /
    weightedMean (RegisterPopulationTypePrice.frequency s) (actualFertility i c s actions modes labels) := by
  rw [actualCensusMean_eq_old i c s actions modes labels b z,actualFertility_eq_old i c s actions modes labels b]
  exact RegisterPopulationTypePrice.actual_program_type_price i ⟨b,c⟩ s actions modes labels hB z
end Cohort

section CensusMaintenance
open UEOT.V3.Compression.Objecthood
open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open UEOT.V3.Compression.Objecthood.JointHomeostasis
open UEOT.V3.Compression.Objecthood.OntogeneticConstruction
open UEOT.V3.ViabilityKernel
open RegisterFaultSource
variable {n : ℕ} [MeasurableSpace (State n)] [MeasurableSingletonClass (State n)]

/-- Each child counted in SAME actual Price census enters its OWN P5. In
particular two different types never need the same global target certificate. -/
theorem census_child_enters_own_maintenance (i : Fin n) (c : NNReal) (s : Store n)
    (actions : ℕ → Action) (modes labels : ℕ → Bool) (b : Bool)
    (d : RegisterPopulationTypePrice.Children i ⟨b,c⟩ s actions modes labels)
    (epsilon : NNReal) (he : epsilon ≤ 1) :
    let o := RegisterPopulationTypePrice.childObject i ⟨b,c⟩ s actions modes labels d
    let seed : OntogeneticSeed (State n) Bool := ⟨o.organism.physical,o.organism.program⟩
    let S := finiteJointRecurrentHomeostasisSystem
      (physical i) (target i o.organism.program) (target_fixed i o.organism.program) (certificate i o.organism.program)
      (substrate i) codec o.organism.program (compiled_dynamics_implements i o.organism.program)
      (fault i) epsilon he (actual_fault_envelope i o.organism.program)
    StaysIn (PMF.pure (assembleRepairOrganization (substrate i) codec seed)) S.carrier :=
  actual_child_enters_own_maintenance i c (before i c s actions modes labels d.val)
    (RegisterPopulationTypePrice.request actions modes labels d.val) _
    (census_child_actual i c s actions modes labels b d) epsilon he
end CensusMaintenance

/-- Literal compiled controller reads only the actual addressed parent's own
protected code and physical state; invalid lookup retains the old idle fallback. -/
def compiledRequest {n : ℕ} (i : Fin n) (s : Store n) (j : ℕ) (mode label : Bool) : Request :=
  ⟨j,match RegisterPopulationHistorySource.lookup s j with
      | none => none | some p => (substrate i).execute p.organism.program p.organism.physical,mode,label⟩

/-- Local resource port belongs to THIS addressed parent. This consumes the
old source-derived cushion invariant; no whole-population funding field is
assumed. g is the explicitly NEW protected requested-idle energy input. -/
theorem actual_compiled_step_funded {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (j : ℕ)
    (p : ClockedOrganism n) (hp : RegisterPopulationHistorySource.lookup s j = some p)
    (g reserve : ℝ) (hg : (c : ℝ) ≤ g)
    (hr : RegisterFaultFeedbackResource.cushion i ⟨p.organism.program,c⟩ p.organism.physical ≤ reserve)
    (mode label : Bool) :
    let q := compiledRequest i s j mode label
    let r := modeRecordStep i ⟨p.organism.program,c⟩ p.organism q.action mode label
    (transaction i c s q).map RegisterTimestampedBirthSource.eraseRecord = some r ∧
    RegisterFaultFeedbackResource.cushion i ⟨p.organism.program,c⟩ r.transaction.parentAfter.physical ≤
      reserve + RegisterFaultFeedbackResource.idleInflow g r - r.transaction.expenditure := by
  dsimp only
  refine ⟨transaction_erasure i c s _ p hp,?_⟩
  have hq : (compiledRequest i s j mode label).action =
      (substrate i).execute p.organism.program p.organism.physical := by simp [compiledRequest,hp]
  rw [hq]
  exact RegisterFaultFeedbackResource.actual_step_funded i ⟨p.organism.program,c⟩ g reserve hg p.organism hr mode label

/-- A real child starts with zero cushion under its inherited OWN target. Its
first own-program compiled transaction can therefore use reserve=0, g≥c. This
is local funding, not a free global bank or a costed population birth model. -/
theorem actual_child_zero_cushion {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (q : Request)
    (d : ClockedOrganism n) (hd : child i c s q = some d) :
    RegisterFaultFeedbackResource.cushion i ⟨d.organism.program,c⟩ d.organism.physical = 0 := by
  simp [RegisterFaultFeedbackResource.cushion,child_legitimate i c s q d hd]



/-- The SAME actual newborn is found at its new slot. Its next own compiled
step starts from zero reserve and preserves the original local cushion. -/
theorem actual_child_first_step_funded {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (q : Request)
    (d : ClockedOrganism n) (hd : child i c s q = some d) (g : ℝ) (hg : (c : ℝ) ≤ g)
    (mode label : Bool) :
    let s' := next i c s q
    let q' := compiledRequest i s' s.length mode label
    let r := modeRecordStep i ⟨d.organism.program,c⟩ d.organism q'.action mode label
    (transaction i c s' q').map RegisterTimestampedBirthSource.eraseRecord = some r ∧
    RegisterFaultFeedbackResource.cushion i ⟨d.organism.program,c⟩ r.transaction.parentAfter.physical ≤
      RegisterFaultFeedbackResource.idleInflow g r - r.transaction.expenditure := by
  have hp := (next_new_slot i c s q).trans hd
  have hr : RegisterFaultFeedbackResource.cushion i ⟨d.organism.program,c⟩ d.organism.physical ≤ (0 : ℝ) :=
    le_of_eq (actual_child_zero_cushion i c s q d hd)
  simpa only [zero_add] using actual_compiled_step_funded i c (next i c s q) s.length d hp g 0 hg hr mode label

/-- Full actual execution provenance with one global serialized allocator. -/
def storeBefore {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (es : List Request) (k : ℕ) : Store n :=
  run i c s (es.take k)

def childAt {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (es : List Request) (k : Fin es.length) :
    Option (ClockedOrganism n) :=
  child i c (storeBefore i c s es k) (RegisterPopulationHistorySource.requestAt es k)

def observedChildID {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (es : List Request) (k : Fin es.length) : Option ℕ :=
  (childAt i c s es k).map (fun _ => s.length+k)

def actualParent {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (es : List Request) (k : Fin es.length) : Option ℕ :=
  (childAt i c s es k).map (fun _ => (RegisterPopulationHistorySource.requestAt es k).parent)

/-- The recorded global ID is computed from THIS prefix's literal allocator. -/
theorem observedChildID_eq_allocator {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n)
    (es : List Request) (k : Fin es.length) :
    observedChildID i c s es k = childID i c (storeBefore i c s es k) (RegisterPopulationHistorySource.requestAt es k) := by
  unfold observedChildID childAt childID RegisterPopulationHistorySource.childID
  simp [storeBefore,List.length_take,child]

theorem distinct_actual_births {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (es : List Request)
    (j k : Fin es.length) (a b : ClockedOrganism n) (hj : childAt i c s es j = some a)
    (hk : childAt i c s es k = some b) (hne : j ≠ k) :
    observedChildID i c s es j ≠ observedChildID i c s es k := by
  simp only [observedChildID,hj,hk,Option.map_some,ne_eq,Option.some.injEq]
  intro h
  exact hne (Fin.ext (by omega))

/-- Parent is derived from the actual successful dispatch, not an independently
provided genealogy function. None denotes failed birth, not its attempted actor. -/
theorem parent_eq_of_childID {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n)
    (es : List Request) (j k : Fin es.length)
    (h : observedChildID i c s es j = observedChildID i c s es k) :
    actualParent i c s es j = actualParent i c s es k := by
  unfold observedChildID at h
  unfold actualParent
  cases hj : childAt i c s es j with
  | none => cases hk : childAt i c s es k <;> simp [hj,hk] at h ⊢
  | some a =>
    cases hk : childAt i c s es k with
    | none => simp [hj,hk] at h
    | some b =>
      simp only [hj,hk,Option.map_some,Option.some.injEq] at h
      have heq : j = k := Fin.ext (by omega)
      subst k
      rfl

def witnessFounders : List (Organism 1) :=
  [⟨[],fun _ => false,false⟩,⟨[],fun _ => false,false⟩,⟨[],fun _ => true,true⟩]
def witnessInitial : Store 1 := RegisterPopulationHistorySource.founders witnessFounders
def witnessActions (j : ℕ) : Action := (compiledRequest (0 : Fin 1) witnessInitial j true true).action
def witnessModes (j : ℕ) : Bool := if j = 1 then false else true
/-- Initial fixed cohort actions are evaluated from each parent's own code. -/
def witnessEpisode : List Request :=
  RegisterPopulationTypePrice.cohortRequests witnessInitial witnessActions witnessModes (fun _ => true)
def witnessAfterCohort : Store 1 := run (0 : Fin 1) 1 witnessInitial witnessEpisode
def witnessRepair : Request := compiledRequest (0 : Fin 1) witnessAfterCohort 1 true true

/-- Same episode: two different copied programs, one retained failed birth,
actual damage of the middle false-type parent, and its ensuing literal paid
write-false. No new seed/reset/install is inserted between these events. -/
theorem two_type_paid_repair_witness :
    witnessAfterCohort.length = 6 ∧
    (RegisterPopulationHistorySource.lookup witnessAfterCohort 3).map (fun d => d.organism.program) = some false ∧
    (RegisterPopulationHistorySource.lookup witnessAfterCohort 5).map (fun d => d.organism.program) = some true ∧
    RegisterPopulationHistorySource.lookup witnessAfterCohort 4 = none ∧
    (RegisterPopulationHistorySource.lookup witnessAfterCohort 1).map (fun d => d.organism.program) = some false ∧
    (RegisterPopulationHistorySource.lookup witnessAfterCohort 1).map (fun d => d.organism.physical 0) = some true ∧
    witnessRepair.action = some false ∧
    (transaction (0 : Fin 1) 1 witnessAfterCohort witnessRepair).map ClockedRecord.expenditure = some 1 ∧
    (RegisterPopulationHistorySource.lookup (next (0 : Fin 1) 1 witnessAfterCohort witnessRepair) 1).map
      (fun d => d.organism.physical 0) = some false ∧
    (RegisterPopulationHistorySource.lookup (next (0 : Fin 1) 1 witnessAfterCohort witnessRepair) 6).map
      (fun d => d.organism.program) = some false := by
  norm_num [witnessAfterCohort,witnessInitial,witnessFounders,witnessEpisode,witnessActions,witnessModes,witnessRepair,
    RegisterPopulationTypePrice.cohortRequests,RegisterPopulationTypePrice.request,
    compiledRequest,run,next,transaction,child,mechanism,
    RegisterPopulationHistorySource.founders,RegisterPopulationHistorySource.next,
    RegisterPopulationHistorySource.transaction,RegisterPopulationHistorySource.lookup,RegisterPopulationHistorySource.child,
    RegisterTimestampedBirthSource.step,modeRecordStep,RegisterJointRecord.recordStep,
    birthEvent,repairEvent,execute_compiled,update,cost,List.range_succ]


private theorem witness_born_iff (j : Fin witnessInitial.length) :
    RegisterPopulationTypePrice.born (0 : Fin 1) ⟨false,1⟩ witnessInitial witnessActions witnessModes (fun _ => true) j ↔
      (j : ℕ) ≠ 1 := by
  fin_cases j <;>
    norm_num [RegisterPopulationTypePrice.born,RegisterPopulationTypePrice.offspring,
      RegisterPopulationTypePrice.before,RegisterPopulationTypePrice.cohortRequests,RegisterPopulationTypePrice.request,
      witnessInitial,witnessFounders,witnessActions,witnessModes,compiledRequest,
      RegisterPopulationHistorySource.founders,RegisterPopulationHistorySource.run,
      RegisterPopulationHistorySource.next,RegisterPopulationHistorySource.transaction,
      RegisterPopulationHistorySource.lookup,RegisterPopulationHistorySource.child,
      RegisterTimestampedBirthSource.step,modeRecordStep,RegisterJointRecord.recordStep,
      birthEvent,repairEvent,execute_compiled,update,List.range_succ]

theorem witness_birthCount :
    RegisterPopulationTypePrice.birthCount (0 : Fin 1) ⟨false,1⟩ witnessInitial witnessActions witnessModes (fun _ => true) = 2 := by
  unfold RegisterPopulationTypePrice.birthCount
  rw [Fintype.card_subtype]
  simp only [witness_born_iff]
  change (Finset.univ.filter (fun j : Fin 3 => (j : ℕ) ≠ 1)).card = 2
  decide

/-- Same three-parent episode actually consumes original Core Price. The
census excludes the retained parents and the later repair-event child. -/
theorem witness_price (z : Bool → ℝ) :
    actualCensusMean (0 : Fin 1) 1 witnessInitial witnessActions witnessModes (fun _ => true) false z -
      weightedMean (RegisterPopulationTypePrice.frequency witnessInitial) (RegisterPopulationTypePrice.parentTrait witnessInitial z) =
    weightedCov (RegisterPopulationTypePrice.frequency witnessInitial)
      (actualFertility (0 : Fin 1) 1 witnessInitial witnessActions witnessModes (fun _ => true))
      (RegisterPopulationTypePrice.parentTrait witnessInitial z) /
    weightedMean (RegisterPopulationTypePrice.frequency witnessInitial)
      (actualFertility (0 : Fin 1) 1 witnessInitial witnessActions witnessModes (fun _ => true)) :=
  own_program_type_price (0 : Fin 1) 1 witnessInitial witnessActions witnessModes (fun _ => true) false
    (by rw [witness_birthCount]; norm_num) z

/-- A registered four-draw product source; its first three addresses are the
frozen old cohort, while the fourth action is computed from the REAL prefix. -/
def fourStepRequests (omega : Fin 4 → Bool × Bool) : List Request :=
  let es := List.ofFn (fun j : Fin 3 => (⟨j,witnessActions j,(omega j.castSucc).1,(omega j.castSucc).2⟩ : Request))
  let s := run (0 : Fin 1) 1 witnessInitial es
  es ++ [compiledRequest (0 : Fin 1) s 1 (omega 3).1 (omega 3).2]

def witnessRaw (j : Fin 4) : Bool × Bool := (witnessModes j,true)

theorem witness_same_actual_episode : fourStepRequests witnessRaw = witnessEpisode ++ [witnessRepair] := by
  norm_num [fourStepRequests,witnessRaw,witnessModes,witnessEpisode,witnessRepair,witnessAfterCohort,
    RegisterPopulationTypePrice.cohortRequests,witnessInitial,witnessFounders,
    RegisterPopulationHistorySource.founders,RegisterPopulationTypePrice.request,List.ofFn_succ,List.range_succ]

def fourDrawLaw : Measure (Fin 4 → Bool × Bool) :=
  Measure.pi (fun _ => (RegisterFaultFinitePurposeProbe.primitiveLaw (PMF.uniformOfFintype Bool)
    (1/4) (by exact_mod_cast (by norm_num : (1/4 : ℝ) ≤ 1))).toMeasure)

instance fourDrawLaw_probability : IsProbabilityMeasure fourDrawLaw := by unfold fourDrawLaw; infer_instance

/-- The very SAME complete four-draw execution above has strictly positive
mass at nonzero hazard. No unsupported/null draw or real resampling is used. -/
theorem witness_source_mass : fourDrawLaw.real {witnessRaw} = 27/4096 := by
  rw [Measure.real,fourDrawLaw,Measure.pi_singleton,ENNReal.toReal_prod]
  simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  norm_num [Fin.prod_univ_succ,witnessRaw,witnessModes,
    RegisterFaultFinitePurposeProbe.primitiveLaw_apply,ENNReal.toReal_mul,modeLaw,
    FiniteProbabilityRow.ofRealRow_apply_toReal,modeProbability,repairChance,PMF.uniformOfFintype_apply]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterOwnProgramPopulation
