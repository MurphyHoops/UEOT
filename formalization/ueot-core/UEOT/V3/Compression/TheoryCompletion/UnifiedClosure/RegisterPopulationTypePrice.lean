import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationHistorySource
import UEOT.V3.EvolutionPrice

/-!
Original commitment: actual finite-population reproduction and inherited programs determine type-frequency change.
Existing premise: allocator gives actual children; Core Price still receives external frequency/fertility/transmission arrays.
Premise reduced: compute one frozen cohort, actual offspring counts, normalized actual-child kernel and empirical frequencies.
Models: one fixed pass through the OLD address table; new children do not enter this cohort; empty generations remain empty.
Consumer: original Core EvolutionPrice on SAME realized offspring, with b*K-positive actual provenance and inherited program traits.

The current finite store and registered action/environment arrays are model inputs.
Each original address is dispatched once in increasing order; holes retain failed
ticks. Modes/labels are environmental realizations, not extra controlled actions.
The actual parent cohort excludes holes (zero frequency weight). Normalization
requires a strictly positive ACTUAL birth count. An infertile row may totalize to
an actual child but has zero fertility; only b*K-positive entries represent births.
This is a samplewise empirical Price identity, not an expectation-of-ratios claim.
Retained parents remain in the final store; the next frequency is an
offspring-only census, not the frequency of all surviving old plus new nodes.
The original P8 stronger all-K-positive lineage interface is not asserted here.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationTypePrice
open MeasureTheory
open UEOT.V3.EvolutionPrice
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultJointRecord
open RegisterPopulationHistorySource (Store Request)
open RegisterTimestampedBirthSource (ClockedOrganism)
open scoped BigOperators
noncomputable section

variable {n : ℕ} (i : Fin n) (m : Mechanism) (s : Store n)
variable (actions : ℕ → Action) (modes labels : ℕ → Bool)

def request (j : ℕ) : Request := ⟨j,actions j,modes j,labels j⟩

def cohortRequests : List Request := (List.range s.length).map (request actions modes labels)

def before (j : ℕ) : Store n :=
  RegisterPopulationHistorySource.run i m s ((cohortRequests s actions modes labels).take j)

def offspring (j : Fin s.length) : Option (ClockedOrganism n) :=
  RegisterPopulationHistorySource.child i m (before i m s actions modes labels j) (request actions modes labels j)

private theorem lookup_run_other (j : ℕ) (es : List Request) (hj : j < s.length)
    (hne : ∀ q ∈ es, q.parent ≠ j) :
    RegisterPopulationHistorySource.lookup (RegisterPopulationHistorySource.run i m s es) j =
      RegisterPopulationHistorySource.lookup s j := by
  induction es generalizing s with
  | nil => rfl
  | cons q es ih =>
    change RegisterPopulationHistorySource.lookup
      (RegisterPopulationHistorySource.run i m (RegisterPopulationHistorySource.next i m s q) es) j = _
    rw [ih _ (by rw [RegisterPopulationHistorySource.next_length]; omega)
      (fun r hr => hne r (by simp [hr]))]
    exact RegisterPopulationHistorySource.next_other_slot i m s q j hj (hne q (by simp))

/-- Every scheduled parent is the SAME actual object from the frozen original
address table. Earlier steps change only other slots and append new slots. -/
theorem before_lookup (j : Fin s.length) :
    RegisterPopulationHistorySource.lookup (before i m s actions modes labels j) j =
      RegisterPopulationHistorySource.lookup s j := by
  unfold before cohortRequests
  rw [← List.map_take,List.take_range,min_eq_left j.isLt.le]
  apply lookup_run_other i m s j _ j.isLt
  intro q hq
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hq
  have hk' : k < (j : ℕ) := List.mem_range.mp hk
  change k ≠ (j : ℕ)
  omega

@[simp] theorem before_length (j : Fin s.length) :
    (before i m s actions modes labels j).length = s.length+j := by
  simp [before,cohortRequests,List.length_take]

/-- Actual newborn slots in the final store are exactly the source-computed
cohort offspring. Newborns are not silently rescheduled in their own generation. -/
theorem generation_new_slot (j : Fin s.length) :
    RegisterPopulationHistorySource.lookup
      (RegisterPopulationHistorySource.run i m s (cohortRequests s actions modes labels)) (s.length+j) =
      offspring i m s actions modes labels j := by
  let es := cohortRequests s actions modes labels
  let b := before i m s actions modes labels j
  let q := request actions modes labels j
  have hj : (j : ℕ) < es.length := by simp [es,cohortRequests]
  have hevent : es[(j : ℕ)] = q := by simp [es,cohortRequests,q,request]
  have hsplit : es = es.take j ++ q :: es.drop (j+1) := by
    calc
      es = es.take j ++ es.drop j := (List.take_append_drop _ _).symm
      _ = _ := by rw [List.drop_eq_getElem_cons hj,hevent]
  have hrun : RegisterPopulationHistorySource.run i m s es =
      RegisterPopulationHistorySource.run i m (RegisterPopulationHistorySource.next i m b q) (es.drop (j+1)) := by
    calc
      _ = RegisterPopulationHistorySource.run i m s (es.take j ++ q :: es.drop (j+1)) := congrArg _ hsplit
      _ = _ := by simp only [RegisterPopulationHistorySource.run,List.foldl_append,List.foldl_cons]; rfl
  change RegisterPopulationHistorySource.lookup (RegisterPopulationHistorySource.run i m s es) (s.length+j) = _
  rw [hrun]
  have hlt : s.length+(j : ℕ) < (RegisterPopulationHistorySource.next i m b q).length := by
    rw [RegisterPopulationHistorySource.next_length]
    dsimp only [b]
    rw [before_length]
    omega
  have hnever : ∀ r ∈ es.drop (j+1), r.parent ≠ s.length+j := by
    intro r hr
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp (List.mem_of_mem_drop hr)
    have hk' : k < s.length := List.mem_range.mp hk
    change k ≠ s.length+j
    omega
  rw [lookup_run_other i m (RegisterPopulationHistorySource.next i m b q) (s.length+j) _ hlt hnever]
  have hslot := RegisterPopulationHistorySource.next_new_slot i m b q
  change RegisterPopulationHistorySource.lookup (RegisterPopulationHistorySource.next i m b q)
    (before i m s actions modes labels j).length = _ at hslot
  rw [before_length] at hslot
  exact hslot

/-- The inherited type is the program of the actual frozen-cohort parent,
not the sampled label and not a separately supplied mutation kernel. -/
theorem offspring_program (j : Fin s.length) (c : ClockedOrganism n)
    (hc : offspring i m s actions modes labels j = some c) :
    ∃ p : ClockedOrganism n, RegisterPopulationHistorySource.lookup s j = some p ∧
      c.organism.program = p.organism.program := by
  obtain ⟨p,hp,_,hprogram,_⟩ := RegisterPopulationHistorySource.actual_child_source
    i m (before i m s actions modes labels j) (request actions modes labels j) c hc
  refine ⟨p,?_,hprogram⟩
  change RegisterPopulationHistorySource.lookup (before i m s actions modes labels j) j = some p at hp
  rw [before_lookup] at hp
  exact hp

def occupied (j : Fin s.length) : Prop := (RegisterPopulationHistorySource.lookup s j).isSome

def born (j : Fin s.length) : Prop := (offspring i m s actions modes labels j).isSome

instance occupied_decidable (j : Fin s.length) : Decidable (occupied s j) := inferInstanceAs (Decidable (_ = true))
instance born_decidable (j : Fin s.length) : Decidable (born i m s actions modes labels j) := inferInstanceAs (Decidable (_ = true))

/-- Actual cohort is the occupied part of the finite address table. -/
def parentCount : ℕ := (Finset.univ.filter (occupied s)).card

abbrev Children := {j : Fin s.length // born i m s actions modes labels j}

instance childrenFintype : Fintype (Children i m s actions modes labels) := by
  unfold Children
  infer_instance

def birthCount : ℕ := Fintype.card (Children i m s actions modes labels)

def childObject (c : Children i m s actions modes labels) : ClockedOrganism n :=
  (offspring i m s actions modes labels c.val).get c.property

/-- Actual distinct child slots, not just transaction multiplicities. -/
def childIdentity (c : Children i m s actions modes labels) : ℕ := s.length+c.val

theorem childIdentity_injective : Function.Injective (childIdentity i m s actions modes labels) := by
  intro c d h
  apply Subtype.ext
  apply Fin.ext
  unfold childIdentity at h
  omega

/-- Only existing registered parents carry frequency. Holes have weight zero. -/
def frequency (j : Fin s.length) : ℝ := if occupied s j then 1 / (parentCount s : ℝ) else 0

def fertility (j : Fin s.length) : ℝ := if born i m s actions modes labels j then 1 else 0

private theorem born_occupied (j : Fin s.length) (hj : born i m s actions modes labels j) : occupied s j := by
  obtain ⟨p,hp,_⟩ := offspring_program i m s actions modes labels j
    ((offspring i m s actions modes labels j).get hj) (Option.some_get hj).symm
  simp [occupied,hp]

private theorem parentCount_pos (hB : 0 < birthCount i m s actions modes labels) : 0 < parentCount s := by
  obtain ⟨c⟩ := Fintype.card_pos_iff.mp hB
  exact Finset.card_pos.mpr ⟨c.val,by simp [born_occupied i m s actions modes labels c.val c.property]⟩

/-- Null-fertility rows choose an ACTUAL offspring only after actual nonemptiness.
Their choice never contributes to the source operator fertility*transmission. -/
def fallbackChild (hB : 0 < birthCount i m s actions modes labels) : Children i m s actions modes labels :=
  Classical.choice (Fintype.card_pos_iff.mp hB)

def transmission (hB : 0 < birthCount i m s actions modes labels)
    (p : Fin s.length) (c : Children i m s actions modes labels) : ℝ :=
  if born i m s actions modes labels p then (if c.val = p then 1 else 0)
  else if c = fallbackChild i m s actions modes labels hB then 1 else 0


/-- The normalized row is derived, including a harmless actual-child fallback
for zero-fertility parents. It does not assert that this fallback is a birth. -/
theorem transmission_sum (hB : 0 < birthCount i m s actions modes labels) (p : Fin s.length) :
    ∑ c, transmission i m s actions modes labels hB p c = 1 := by
  classical
  by_cases hp : born i m s actions modes labels p
  · let cp : Children i m s actions modes labels := ⟨p,hp⟩
    have heq (c : Children i m s actions modes labels) : c.val = p ↔ c = cp := by
      constructor
      · exact fun h => Subtype.ext h
      · exact congrArg Subtype.val
    simp only [transmission,if_pos hp,heq]
    simp
  · simp [transmission,hp]

theorem transmission_nonneg (hB : 0 < birthCount i m s actions modes labels)
    (p : Fin s.length) (c : Children i m s actions modes labels) :
    0 ≤ transmission i m s actions modes labels hB p c := by
  unfold transmission
  split_ifs <;> norm_num

/-- Source operator is exactly the actual parent-to-child incidence matrix.
Inactive row totalization disappears; no false genealogical edge is introduced. -/
theorem source_entry (hB : 0 < birthCount i m s actions modes labels)
    (p : Fin s.length) (c : Children i m s actions modes labels) :
    fertility i m s actions modes labels p * transmission i m s actions modes labels hB p c =
      if c.val = p then 1 else 0 := by
  classical
  by_cases hp : born i m s actions modes labels p
  · simp [fertility,transmission,hp]
  · have hne : c.val ≠ p := by intro heq; exact hp (heq ▸ c.property)
    simp [fertility,transmission,hp,hne]

private theorem frequency_mul_fertility (p : Fin s.length) :
    frequency s p * fertility i m s actions modes labels p =
      (1 / (parentCount s : ℝ)) * fertility i m s actions modes labels p := by
  by_cases hp : born i m s actions modes labels p
  · simp [frequency,fertility,hp,born_occupied i m s actions modes labels p hp]
  · simp [fertility,hp]

/-- Parent frequencies count only actual occupied initial cohort slots. -/
theorem frequency_sum (hB : 0 < birthCount i m s actions modes labels) : ∑ p, frequency s p = 1 := by
  have hcount : (parentCount s : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (parentCount_pos i m s actions modes labels hB))
  calc
    ∑ p, frequency s p = (∑ p : Fin s.length, if occupied s p then (1 : ℝ) else 0) / parentCount s := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p _
      unfold frequency
      split_ifs <;> simp
    _ = (parentCount s : ℝ) / parentCount s := by rw [Finset.sum_boole]; rfl
    _ = 1 := div_self hcount

theorem fertility_sum : ∑ p, fertility i m s actions modes labels p = (birthCount i m s actions modes labels : ℝ) := by
  unfold fertility birthCount
  rw [Finset.sum_boole,Fintype.card_subtype]

/-- Actual mean fertility is a ratio of ACTUAL counts, with no expected-ratio
substitution. This denominator is positive precisely on the registered domain. -/
theorem mean_fertility_eq :
    weightedMean (frequency s) (fertility i m s actions modes labels) =
      (1 / (parentCount s : ℝ)) * birthCount i m s actions modes labels := by
  unfold weightedMean
  simp_rw [frequency_mul_fertility]
  rw [← Finset.mul_sum,fertility_sum]

private theorem mean_fertility_pos (hB : 0 < birthCount i m s actions modes labels) :
    0 < weightedMean (frequency s) (fertility i m s actions modes labels) := by
  rw [mean_fertility_eq]
  have hp : (0 : ℝ) < parentCount s := by exact_mod_cast parentCount_pos i m s actions modes labels hB
  have hb : (0 : ℝ) < birthCount i m s actions modes labels := by exact_mod_cast hB
  positivity

/-- Every actual child has unit empirical multiplicity. Its source-computed
f*w*K update equals the uniform empirical frequency over the ACTUAL births. -/
theorem actual_offspring_frequency (hB : 0 < birthCount i m s actions modes labels)
    (c : Children i m s actions modes labels) :
    nextFrequency (frequency s) (fertility i m s actions modes labels)
      (transmission i m s actions modes labels hB) c = 1 / (birthCount i m s actions modes labels : ℝ) := by
  classical
  have hp : (parentCount s : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (parentCount_pos i m s actions modes labels hB)
  have hb : (birthCount i m s actions modes labels : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hB
  unfold nextFrequency meanOffspringEntry
  simp_rw [source_entry]
  have hnum : (∑ p : Fin s.length, frequency s p * (if c.val = p then 1 else 0)) =
      1 / (parentCount s : ℝ) := by
    simp_rw [mul_ite,mul_one,mul_zero]
    simp [frequency,born_occupied i m s actions modes labels c.val c.property]
  rw [hnum,mean_fertility_eq]
  field_simp

/-- Every positive source matrix entry is the ACTUAL addressed birth, with
its fresh global slot and actual parent. Only fertility*K-positive provenance
is asserted; no infertile fallback is promoted to a genealogical edge. -/
theorem positive_entry_actual_birth (hB : 0 < birthCount i m s actions modes labels)
    (p : Fin s.length) (c : Children i m s actions modes labels)
    (hpos : 0 < fertility i m s actions modes labels p * transmission i m s actions modes labels hB p c) :
    c.val = p ∧
      RegisterPopulationHistorySource.child i m (before i m s actions modes labels p)
        (request actions modes labels p) = some (childObject i m s actions modes labels c) ∧
      RegisterPopulationHistorySource.childID i m (before i m s actions modes labels p)
        (request actions modes labels p) = some (s.length+p) ∧
      RegisterPopulationHistorySource.parentID i m (before i m s actions modes labels p)
        (request actions modes labels p) = some (p : ℕ) := by
  have hcp : c.val = p := by
    by_contra hn
    rw [source_entry,if_neg hn] at hpos
    exact (lt_irrefl 0) hpos
  subst p
  have hc : offspring i m s actions modes labels c.val = some (childObject i m s actions modes labels c) :=
    (Option.some_get c.property).symm
  refine ⟨rfl,hc,?_,?_⟩
  · simp [RegisterPopulationHistorySource.childID,show RegisterPopulationHistorySource.child i m
      (before i m s actions modes labels c.val) (request actions modes labels c.val) =
      some (childObject i m s actions modes labels c) from hc,before_length]
  · change (offspring i m s actions modes labels c.val).map (fun _ => (c.val : ℕ)) = some (c.val : ℕ)
    rw [hc]
    rfl

/-- Traits read actual inherited source programs. Missing parent addresses have
zero frequency and a harmless zero trait totalization. -/
def parentTrait (z : Bool → ℝ) (p : Fin s.length) : ℝ :=
  ((RegisterPopulationHistorySource.lookup s p).map (fun node => z node.organism.program)).getD 0

def childTrait (z : Bool → ℝ) (c : Children i m s actions modes labels) : ℝ :=
  z (childObject i m s actions modes labels c).organism.program

private theorem inherited_child_trait (z : Bool → ℝ) (c : Children i m s actions modes labels) :
    childTrait i m s actions modes labels z c = parentTrait s z c.val := by
  obtain ⟨p,hp,hprogram⟩ := offspring_program i m s actions modes labels c.val
    (childObject i m s actions modes labels c) (Option.some_get c.property).symm
  simp [childTrait,parentTrait,hprogram,hp]

private theorem transmitted_on_fertile (hB : 0 < birthCount i m s actions modes labels)
    (z : Bool → ℝ) (p : Fin s.length) (hp : born i m s actions modes labels p) :
    transmittedTrait (transmission i m s actions modes labels hB) (childTrait i m s actions modes labels z) p =
      parentTrait s z p := by
  classical
  let cp : Children i m s actions modes labels := ⟨p,hp⟩
  have heq (c : Children i m s actions modes labels) : c.val = p ↔ c = cp := by
    constructor
    · exact fun h => Subtype.ext h
    · exact congrArg Subtype.val
  unfold transmittedTrait
  simp only [transmission,if_pos hp,heq,ite_mul,one_mul,zero_mul]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  exact inherited_child_trait i m s actions modes labels z cp

/-- The ACTUAL empirical offspring trait mean, over the nonempty child cohort. -/
def empiricalOffspringMean (z : Bool → ℝ) : ℝ :=
  ∑ c : Children i m s actions modes labels,
    (1 / (birthCount i m s actions modes labels : ℝ)) * childTrait i m s actions modes labels z c

/-- Core P-EVO-01 genuinely consumes the source-derived frequency/fertility/K.
Program copying eliminates the transmission term, leaving exact empirical
selection covariance. There is no claim that selection converges to an optimum. -/
theorem actual_program_type_price (hB : 0 < birthCount i m s actions modes labels) (z : Bool → ℝ) :
    empiricalOffspringMean i m s actions modes labels z - weightedMean (frequency s) (parentTrait s z) =
      weightedCov (frequency s) (fertility i m s actions modes labels) (parentTrait s z) /
        weightedMean (frequency s) (fertility i m s actions modes labels) := by
  have hprice := p_evo_01 (frequency s) (fertility i m s actions modes labels) (parentTrait s z)
    (transmission i m s actions modes labels hB) (childTrait i m s actions modes labels z)
    (fun p => by unfold frequency; split_ifs <;> positivity)
    (frequency_sum i m s actions modes labels hB)
    (fun p => by unfold fertility; split_ifs <;> norm_num)
    (transmission_nonneg i m s actions modes labels hB)
    (transmission_sum i m s actions modes labels hB)
    (mean_fertility_pos i m s actions modes labels hB)
  have hmean : offspringTraitMean
      (nextFrequency (frequency s) (fertility i m s actions modes labels) (transmission i m s actions modes labels hB))
      (childTrait i m s actions modes labels z) = empiricalOffspringMean i m s actions modes labels z := by
    unfold offspringTraitMean empiricalOffspringMean
    simp_rw [actual_offspring_frequency]
  have hzero : weightedMean (frequency s) (fun p => fertility i m s actions modes labels p *
      (transmittedTrait (transmission i m s actions modes labels hB) (childTrait i m s actions modes labels z) p -
        parentTrait s z p)) = 0 := by
    apply Finset.sum_eq_zero
    intro p _
    dsimp only
    by_cases hp : born i m s actions modes labels p
    · rw [transmitted_on_fertile i m s actions modes labels hB z p hp]
      ring
    · simp [fertility,hp]
  rw [hmean,hzero,zero_div,add_zero] at hprice
  exact hprice

/-- Empty generations are retained and never passed through nonempty Price
normalization. This includes every actual all-fault realization. -/
theorem all_faults_empty (j : Fin s.length) : offspring i m s actions (fun _ => false) labels j = none := by
  unfold offspring RegisterPopulationHistorySource.child RegisterPopulationHistorySource.transaction
  cases h : RegisterPopulationHistorySource.lookup (before i m s actions (fun _ => false) labels j)
      (request actions (fun _ => false) labels j).parent <;>
    simp [RegisterTimestampedBirthSource.step,modeRecordStep,request]

theorem all_faults_birthCount_zero : birthCount i m s actions (fun _ => false) labels = 0 := by
  rw [birthCount,Fintype.card_eq_zero_iff]
  refine ⟨fun c => ?_⟩
  have hc := c.property
  simp [born,all_faults_empty] at hc


/-- Both program types exist in the SAME registered population. Constant idle
lets the false program reproduce while the true program's bad state fails;
all environmental labels are true and do not serve as inherited types. -/
def selectionStore : Store 1 := RegisterPopulationHistorySource.founders RegisterPopulationHistorySource.witnessFounders

def typeOne : Bool → ℝ := fun b => if b then 1 else 0

private theorem selection_born_iff (j : Fin selectionStore.length) :
    born (0 : Fin 1) ⟨true,1⟩ selectionStore (fun _ => none) (fun _ => true) (fun _ => true) j ↔ (j : ℕ) = 0 := by
  fin_cases j <;>
    norm_num [born,offspring,before,cohortRequests,request,selectionStore,
      RegisterPopulationHistorySource.founders,RegisterPopulationHistorySource.witnessFounders,
      RegisterPopulationHistorySource.run,RegisterPopulationHistorySource.next,
      RegisterPopulationHistorySource.transaction,RegisterPopulationHistorySource.lookup,RegisterPopulationHistorySource.child,
      RegisterTimestampedBirthSource.step,modeRecordStep,RegisterJointRecord.recordStep,
      birthEvent,repairEvent,execute_compiled,update,List.range_succ]

private theorem selection_occupied (j : Fin selectionStore.length) : occupied selectionStore j := by
  fin_cases j <;> norm_num [occupied,selectionStore,RegisterPopulationHistorySource.lookup,
    RegisterPopulationHistorySource.founders,RegisterPopulationHistorySource.witnessFounders]

theorem selection_parentCount : parentCount selectionStore = 2 := by
  unfold parentCount
  simp only [selection_occupied,Finset.filter_true]
  change Fintype.card (Fin 2) = 2
  rfl

theorem selection_birthCount :
    birthCount (0 : Fin 1) ⟨true,1⟩ selectionStore (fun _ => none) (fun _ => true) (fun _ => true) = 1 := by
  unfold birthCount
  rw [Fintype.card_subtype]
  simp only [selection_born_iff]
  change (Finset.univ.filter (fun j : Fin 2 => (j : ℕ) = 0)).card = 1
  decide

theorem selection_parent_mean : weightedMean (frequency selectionStore) (parentTrait selectionStore typeOne) = 1/2 := by
  unfold weightedMean
  change (∑ p : Fin 2, frequency selectionStore p * parentTrait selectionStore typeOne p) = 1/2
  rw [Fin.sum_univ_two]
  simp only [frequency,selection_parentCount]
  norm_num [parentTrait,typeOne,selectionStore,
    RegisterPopulationHistorySource.lookup,RegisterPopulationHistorySource.founders,RegisterPopulationHistorySource.witnessFounders]
  exact selection_occupied _

theorem selection_offspring_mean :
    empiricalOffspringMean (0 : Fin 1) ⟨true,1⟩ selectionStore
      (fun _ => none) (fun _ => true) (fun _ => true) typeOne = 0 := by
  unfold empiricalOffspringMean
  apply Finset.sum_eq_zero
  intro c _
  have hc : (c.val : ℕ) = 0 := (selection_born_iff c.val).mp c.property
  have hfin : c.val = ⟨0,by norm_num [selectionStore,RegisterPopulationHistorySource.founders,
      RegisterPopulationHistorySource.witnessFounders]⟩ := Fin.ext hc
  rw [inherited_child_trait,hfin]
  norm_num [parentTrait,typeOne,selectionStore,RegisterPopulationHistorySource.lookup,
    RegisterPopulationHistorySource.founders,RegisterPopulationHistorySource.witnessFounders]

/-- Nondegenerate two-type actual Price consumer: the true-program fraction
falls from 1/2 to 0 in the nonempty actual offspring census. Failures are retained.
The same permitted all-fault generation has no offspring and is not normalized. -/
theorem selection_and_empty_generation_witness :
    empiricalOffspringMean (0 : Fin 1) ⟨true,1⟩ selectionStore
      (fun _ => none) (fun _ => true) (fun _ => true) typeOne -
        weightedMean (frequency selectionStore) (parentTrait selectionStore typeOne) = -1/2 ∧
      weightedCov (frequency selectionStore)
        (fertility (0 : Fin 1) ⟨true,1⟩ selectionStore (fun _ => none) (fun _ => true) (fun _ => true))
        (parentTrait selectionStore typeOne) /
        weightedMean (frequency selectionStore)
          (fertility (0 : Fin 1) ⟨true,1⟩ selectionStore (fun _ => none) (fun _ => true) (fun _ => true)) = -1/2 ∧
      birthCount (0 : Fin 1) ⟨true,1⟩ selectionStore (fun _ => none) (fun _ => false) (fun _ => true) = 0 := by
  have hB : 0 < birthCount (0 : Fin 1) ⟨true,1⟩ selectionStore
      (fun _ => none) (fun _ => true) (fun _ => true) := by rw [selection_birthCount]; decide
  have hprice := actual_program_type_price (0 : Fin 1) ⟨true,1⟩ selectionStore
    (fun _ => none) (fun _ => true) (fun _ => true) hB typeOne
  rw [selection_offspring_mean,selection_parent_mean] at hprice
  refine ⟨by rw [selection_offspring_mean,selection_parent_mean]; norm_num,?_,?_⟩
  · linarith
  · exact all_faults_birthCount_zero _ _ _ _ _

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationTypePrice
