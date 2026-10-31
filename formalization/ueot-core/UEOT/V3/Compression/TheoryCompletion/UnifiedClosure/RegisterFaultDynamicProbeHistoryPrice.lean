import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicProbePopulation

/-!
Original promise: actual program-driven population change has a nonconstant source trait and genuine Price selection/transmission terms.
Existing source: THIS Batch AST runs the original serial single-founder protocol and actual child/parent IDs; TypePrice incidence/census is source-derived but its Bool trait copies unchanged.
Reduced premise: read trait from real Clocked identity depth, derive one-birth transmission increment, and feed original Core Price on the actual frozen cohort, with no extra founder or trait mutation kernel.
Family: same original data, actual post-parent/slot0/AST/actions/faults/fees; first real dispatch0 then fixed OLD-address cohort[0,1], complete three future draws, failed tick keeps None.
Consumers: actual source fertility/K/children and Core p_evo_01; a positive-mass[T,F,T] word has selection1/2 and transmission1, while empty/first-failed branches remain.

This explicitly registered finite extension changes the dispatch plan to
[0,0,1]; it does not replace old fixed-parent native deployment or the previous
[0,1] population experiment. No second founder, resampling, action, program
installation, funding port or observation to the Batch selector is added.
History depth is a registered realized trait, not utility/fitness/empirical
adaptation. Normalize only on the actually computed nonempty child cohort.
Failed middle tick occupies slot2; the third-tick newborn has fresh ID3.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicProbeHistoryPrice
open Set MeasureTheory ProbabilityTheory
open UEOT.V3.EvolutionPrice
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose
open RegisterFaultFinitePurposeProbe RegisterFaultFinitePurposeInfinite RegisterFaultDynamicProbe
open RegisterFaultDynamicProbePopulation
open RegisterTimestampedBirthSource (ClockedOrganism ClockedRecord)
open RegisterPopulationHistorySource (Store Request)
noncomputable section

/-- The actual source first transaction; it is not assumed successful. -/
def afterFirst {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (w : Fin 3→Bool×Bool) : Store n:=
  let s:=registeredParent i m omega o
  let p:=returnedAST i (classify price width d u (sourceData m width omega))
  RegisterOwnProgramPopulation.next i m.writeCost s (astRequest p s 0 (w 0).1 (w 0).2)

@[simp] theorem afterFirst_length {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (w : Fin 3→Bool×Bool) :
    (afterFirst i m price width d u omega o w).length=2 :=by
  simp only [afterFirst,RegisterOwnProgramPopulation.next_length,registered_length]

def modes (w : Fin 3→Bool×Bool) (j : ℕ) : Bool:=if j=0 then (w 1).1 else (w 2).1
def labels (w : Fin 3→Bool×Bool) (j : ℕ) : Bool:=if j=0 then (w 1).2 else (w 2).2

/-- SAME computed AST, with actual lookup actions on the frozen old cohort. -/
def requests {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (w : Fin 3→Bool×Bool) : List Request:=
  let s:=registeredParent i m omega o
  let p:=returnedAST i (classify price width d u (sourceData m width omega))
  let S:=afterFirst i m price width d u omega o w
  astRequest p s 0 (w 0).1 (w 0).2 ::
    RegisterPopulationTypePrice.cohortRequests S (cohortActions p S) (modes w) (labels w)

/-- The frozen-cohort request list truly executes THIS AST at every actual
lookup. Previous dispatch0 leaves old slot1 unchanged, even if slot1 is None. -/
theorem requests_actual_ast {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (w : Fin 3→Bool×Bool) :
    requests i m price width d u omega o w=
      astEpisode (returnedAST i (classify price width d u (sourceData m width omega))) i m.writeCost
        (registeredParent i m omega o)
        [(0,(w 0).1,(w 0).2),(0,(w 1).1,(w 1).2),(1,(w 2).1,(w 2).2)] :=by
  let S:=afterFirst i m price width d u omega o w
  let p:=returnedAST i (classify price width d u (sourceData m width omega))
  let q:=astRequest p S 0 (w 1).1 (w 1).2
  have hlookup : RegisterPopulationHistorySource.lookup (RegisterOwnProgramPopulation.next i m.writeCost S q) 1=
      RegisterPopulationHistorySource.lookup S 1 :=
    RegisterOwnProgramPopulation.next_other_slot i m.writeCost S q 1
      (by rw [show S.length=2 from afterFirst_length _ _ _ _ _ _ _ _ _];decide) (by change (0 : ℕ)≠1;decide)
  have hlast : astRequest p (RegisterOwnProgramPopulation.next i m.writeCost S q) 1 (w 2).1 (w 2).2=
      astRequest p S 1 (w 2).1 (w 2).2 :=by simp only [astRequest,hlookup]
  simp only [requests,RegisterPopulationTypePrice.cohortRequests,afterFirst_length,List.range_succ,List.range_zero,
    List.map_append,List.map_singleton,List.nil_append,RegisterPopulationTypePrice.request,
    astEpisode]
  change _ :: [astRequest p S 0 (w 1).1 (w 1).2,astRequest p S 1 (w 2).1 (w 2).2]=
    _ :: [q,astRequest p (RegisterOwnProgramPopulation.next i m.writeCost S q) 1 (w 2).1 (w 2).2]
  rw [hlast]

/-- Source trait is actual serial ancestry depth, not copied Bool program. -/
def parentDepth {n : ℕ} (s : Store n) (j : Fin s.length) : ℝ:=
  ((RegisterPopulationHistorySource.lookup s j).map (fun node=>(node.identity.length : ℝ))).getD 0

def childDepth {n : ℕ} (i : Fin n) (m : Mechanism) (s : Store n)
    (actions : ℕ→Action) (modes labels : ℕ→Bool)
    (child : RegisterPopulationTypePrice.Children i m s actions modes labels) : ℝ:=
  (RegisterPopulationTypePrice.childObject i m s actions modes labels child).identity.length

/-- Actual one-birth history extension gives an exact nonzero transmission
increment, derived from real step semantics and the original frozen lookup. -/
theorem actual_child_depth_step {n : ℕ} (i : Fin n) (m : Mechanism) (s : Store n)
    (actions : ℕ→Action) (modes labels : ℕ→Bool)
    (child : RegisterPopulationTypePrice.Children i m s actions modes labels) :
    childDepth i m s actions modes labels child=parentDepth s child.val+1 :=by
  let S:=RegisterPopulationTypePrice.before i m s actions modes labels child.val
  let q:=RegisterPopulationTypePrice.request actions modes labels child.val
  let c:=RegisterPopulationTypePrice.childObject i m s actions modes labels child
  have hc : RegisterPopulationHistorySource.child i m S q=some c :=(Option.some_get child.property).symm
  unfold RegisterPopulationHistorySource.child RegisterPopulationHistorySource.transaction at hc
  cases hp : RegisterPopulationHistorySource.lookup S q.parent with
  | none=>simp [hp] at hc
  | some node=>
    simp only [hp,Option.map_some,Option.bind_some] at hc
    have hsrc:=RegisterTimestampedBirthSource.actual_child_source i m {node with clock:=S.length} c q.action q.mode q.label hc
    have hlookup : RegisterPopulationHistorySource.lookup s child.val=some node :=by
      have hh:=RegisterPopulationTypePrice.before_lookup i m s actions modes labels child.val
      exact hh.symm.trans hp
    change (c.identity.length : ℝ)=parentDepth s child.val+1
    rw [hsrc.2.1]
    simp [parentDepth,hlookup]

/-- Actual own-program child mean, using the unchanged incidence index set.
Existing census_child_actual proves every counted object is a real NEW-source
child; no type coincidence or separately declared offspring list is used. -/
def actualMeanDepth {n : ℕ} (i : Fin n) (m : Mechanism) (s : Store n)
    (actions : ℕ→Action) (modes labels : ℕ→Bool) : ℝ:=
  ∑child : RegisterPopulationTypePrice.Children i m s actions modes labels,
    (1/(RegisterPopulationTypePrice.birthCount i m s actions modes labels : ℝ))*
      ((RegisterOwnProgramPopulation.offspring i m.writeCost s actions modes labels child.val).map
        (fun node=>(node.identity.length : ℝ))).getD 0

private theorem mean_fertility_pos {n : ℕ} (i : Fin n) (m : Mechanism) (s : Store n)
    (actions : ℕ→Action) (modes labels : ℕ→Bool)
    (hB : 0<RegisterPopulationTypePrice.birthCount i m s actions modes labels) :
    0<weightedMean (RegisterPopulationTypePrice.frequency s)
      (RegisterPopulationTypePrice.fertility i m s actions modes labels) :=by
  have hparent : 0<RegisterPopulationTypePrice.parentCount s :=by
    obtain ⟨child⟩:=Fintype.card_pos_iff.mp hB
    obtain ⟨node,hlookup,_⟩:=RegisterPopulationTypePrice.offspring_program i m s actions modes labels
      child.val (RegisterPopulationTypePrice.childObject i m s actions modes labels child)
      (Option.some_get child.property).symm
    apply Finset.card_pos.mpr
    exact ⟨child.val,by simp [RegisterPopulationTypePrice.occupied,hlookup]⟩
  have hbar : 0<weightedMean (RegisterPopulationTypePrice.frequency s)
      (RegisterPopulationTypePrice.fertility i m s actions modes labels) :=by
    rw [RegisterPopulationTypePrice.mean_fertility_eq]
    have hp : (0 : ℝ)<RegisterPopulationTypePrice.parentCount s:=by exact_mod_cast hparent
    have hb : (0 : ℝ)<RegisterPopulationTypePrice.birthCount i m s actions modes labels:=by exact_mod_cast hB
    positivity
  exact hbar

/-- Generic Core Price on THIS actual source cohort and history trait. The
nonempty condition is an ACTUAL count event; later consumers derive it from
execution and retain the complementary empty source events. -/
theorem actual_history_price {n : ℕ} (i : Fin n) (m : Mechanism) (s : Store n)
    (actions : ℕ→Action) (modes labels : ℕ→Bool)
    (hB : 0<RegisterPopulationTypePrice.birthCount i m s actions modes labels) :
    actualMeanDepth i m s actions modes labels-
      weightedMean (RegisterPopulationTypePrice.frequency s) (parentDepth s)=
    weightedCov (RegisterPopulationTypePrice.frequency s)
      (RegisterPopulationTypePrice.fertility i m s actions modes labels) (parentDepth s) /
      weightedMean (RegisterPopulationTypePrice.frequency s) (RegisterPopulationTypePrice.fertility i m s actions modes labels) +
    weightedMean (RegisterPopulationTypePrice.frequency s)
      (fun j=>RegisterPopulationTypePrice.fertility i m s actions modes labels j *
        (transmittedTrait (RegisterPopulationTypePrice.transmission i m s actions modes labels hB)
          (childDepth i m s actions modes labels) j-parentDepth s j)) /
      weightedMean (RegisterPopulationTypePrice.frequency s) (RegisterPopulationTypePrice.fertility i m s actions modes labels) :=by
  have hbar:=mean_fertility_pos i m s actions modes labels hB
  have h:=p_evo_01 (RegisterPopulationTypePrice.frequency s) (RegisterPopulationTypePrice.fertility i m s actions modes labels)
    (parentDepth s) (RegisterPopulationTypePrice.transmission i m s actions modes labels hB) (childDepth i m s actions modes labels)
    (fun j=>by unfold RegisterPopulationTypePrice.frequency;split_ifs <;> positivity)
    (RegisterPopulationTypePrice.frequency_sum i m s actions modes labels hB)
    (fun j=>by unfold RegisterPopulationTypePrice.fertility;split_ifs <;> norm_num)
    (RegisterPopulationTypePrice.transmission_nonneg i m s actions modes labels hB)
    (RegisterPopulationTypePrice.transmission_sum i m s actions modes labels hB)
    hbar
  have hmean : offspringTraitMean
      (nextFrequency (RegisterPopulationTypePrice.frequency s) (RegisterPopulationTypePrice.fertility i m s actions modes labels)
        (RegisterPopulationTypePrice.transmission i m s actions modes labels hB)) (childDepth i m s actions modes labels)=
      actualMeanDepth i m s actions modes labels :=by
    unfold offspringTraitMean actualMeanDepth
    apply Finset.sum_congr rfl
    intro child _
    rw [RegisterPopulationTypePrice.actual_offspring_frequency i m s actions modes labels hB child,
      RegisterOwnProgramPopulation.census_child_actual i m.writeCost s actions modes labels m.goal child]
    rfl
  rwa [hmean] at h

/-- A fertile incidence row really transmits to its own actual child. The
history increment is derived above; it is not an external mutation channel. -/
theorem actual_fertile_depth_increment {n : ℕ} (i : Fin n) (m : Mechanism) (s : Store n)
    (actions : ℕ→Action) (modes labels : ℕ→Bool)
    (hB : 0<RegisterPopulationTypePrice.birthCount i m s actions modes labels)
    (j : Fin s.length) (hj : RegisterPopulationTypePrice.born i m s actions modes labels j) :
    transmittedTrait (RegisterPopulationTypePrice.transmission i m s actions modes labels hB)
      (childDepth i m s actions modes labels) j=parentDepth s j+1 :=by
  let child : RegisterPopulationTypePrice.Children i m s actions modes labels:=⟨j,hj⟩
  have heq (c : RegisterPopulationTypePrice.Children i m s actions modes labels) : c.val=j ↔ c=child :=
    ⟨fun h=>Subtype.ext h,fun h=>congrArg Subtype.val h⟩
  have htrans : transmittedTrait (RegisterPopulationTypePrice.transmission i m s actions modes labels hB)
      (childDepth i m s actions modes labels) j=childDepth i m s actions modes labels child :=by
    simp [transmittedTrait,RegisterPopulationTypePrice.transmission,hj,heq]
  exact htrans.trans (actual_child_depth_step i m s actions modes labels child)

/-- True transmission part of realized Price is exactly one ancestry step.
Infertile-row fallback is multiplied by zero, never promoted to an actual edge. -/
theorem actual_history_transmission_one {n : ℕ} (i : Fin n) (m : Mechanism) (s : Store n)
    (actions : ℕ→Action) (modes labels : ℕ→Bool)
    (hB : 0<RegisterPopulationTypePrice.birthCount i m s actions modes labels) :
    weightedMean (RegisterPopulationTypePrice.frequency s)
      (fun j=>RegisterPopulationTypePrice.fertility i m s actions modes labels j *
        (transmittedTrait (RegisterPopulationTypePrice.transmission i m s actions modes labels hB)
          (childDepth i m s actions modes labels) j-parentDepth s j)) /
      weightedMean (RegisterPopulationTypePrice.frequency s) (RegisterPopulationTypePrice.fertility i m s actions modes labels)=1 :=by
  have hprod : (fun j=>RegisterPopulationTypePrice.fertility i m s actions modes labels j *
      (transmittedTrait (RegisterPopulationTypePrice.transmission i m s actions modes labels hB)
        (childDepth i m s actions modes labels) j-parentDepth s j))=
      RegisterPopulationTypePrice.fertility i m s actions modes labels :=by
    funext j
    by_cases hj : RegisterPopulationTypePrice.born i m s actions modes labels j
    · rw [actual_fertile_depth_increment i m s actions modes labels hB j hj]
      ring
    · simp [RegisterPopulationTypePrice.fertility,hj]
  rw [hprod]
  exact div_self (mean_fertility_pos i m s actions modes labels hB).ne'

/-- Realized historical Price: source-driven selection covariance plus the
source-derived transmission increment, not an expectation/fitness assertion. -/
theorem actual_history_price_selection_plus_one {n : ℕ} (i : Fin n) (m : Mechanism) (s : Store n)
    (actions : ℕ→Action) (modes labels : ℕ→Bool)
    (hB : 0<RegisterPopulationTypePrice.birthCount i m s actions modes labels) :
    actualMeanDepth i m s actions modes labels-weightedMean (RegisterPopulationTypePrice.frequency s) (parentDepth s)=
      weightedCov (RegisterPopulationTypePrice.frequency s)
        (RegisterPopulationTypePrice.fertility i m s actions modes labels) (parentDepth s) /
        weightedMean (RegisterPopulationTypePrice.frequency s) (RegisterPopulationTypePrice.fertility i m s actions modes labels)+1 :=by
  have h:=actual_history_price i m s actions modes labels hB
  rwa [actual_history_transmission_one i m s actions modes labels hB] at h

/-- The failed first source transaction is kept: old slot1 is None when the
cohort begins. Its later request is never replaced by a newly born slot2. -/
theorem first_failure_slot_missing {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (w : Fin 3→Bool×Bool) (hf : (w 0).1=false) :
    RegisterPopulationHistorySource.lookup (afterFirst i m price width d u omega o w) 1=none :=by
  unfold afterFirst
  rw [hf]
  exact (actual_first_fault_none i m price width d u omega o (w 0).2).2

/-- Complete registered original training source and THREE fresh primitive
inputs. All first-failed and empty generations remain in this probability law. -/
def experimentLaw (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) (N : ℕ) :
    Measure ((Coordinate N→Bool×Bool)×(Fin 3→Bool×Bool)):=
  (rawLaw noise epsilon he N).prod (RegisterRotatingBodySource.roundLaw 3 noise epsilon he)
instance experimentLaw_probability (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) (N : ℕ) :
    IsProbabilityMeasure (experimentLaw noise epsilon he N):=by unfold experimentLaw;infer_instance

theorem experimentLaw_training_marginal (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) (N : ℕ) :
    (experimentLaw noise epsilon he N).fst=rawLaw noise epsilon he N:=Measure.fst_prod

local instance {n : ℕ} : MeasurableSpace (List (Option (ClockedRecord n))) := ⊤
def experimentRecords {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (price width d u : ℚ) (o : Organism n) :
    Measure (List (Option (ClockedRecord n))):=
  (experimentLaw noise epsilon he N).map (fun z=>
    RegisterActuatorPopulationScale.transactionTrace i m.writeCost (registeredParent i m z.1 o)
      (requests i m price width d u z.1 o z.2))
instance experimentRecords_probability {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (price width d u : ℚ) (o : Organism n) :
    IsProbabilityMeasure (experimentRecords (N:=N) i noise m epsilon he price width d u o):=
  Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicProbeHistoryPrice
