import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationFundedProtocol
import Mathlib.Probability.ProductMeasure

/-!
Original commitment: ongoing actual population work has a funded infinite source, not a terminated finite trace with a zero tail.
Existing result: every fixed finite idle-before-work protocol is funded and commutes with the retained-actuator scale.
Premise reduced: construct ONE genuine infinite primitive product and actual recursive store/records; derive all finite registered prefix laws.
Model: SAME serialized own-program faults, registered address/work schedule and valid-object shared idle port; no new actions, resets or draws.
Consumer: original ResourceViable on actual ongoing records, exact full-path scale/ledger transport and retained-parent continuing-work witness.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationFundedInfinite
open MeasureTheory ProbabilityTheory
open UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.Objecthood.ResourceClosure
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose
open RegisterTimestampedBirthSource (ClockedOrganism ClockedRecord)
open RegisterPopulationHistorySource (Store Request)
open RegisterActuatorScaleSource RegisterActuatorPopulationScale RegisterPopulationFundedProtocol
noncomputable section

abbrev InfiniteRaw := ℕ × Bool → Bool × Bool

def infiniteSource (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) : Measure InfiniteRaw :=
  Measure.infinitePi (fun _ : ℕ × Bool => (RegisterFaultFinitePurposeProbe.primitiveLaw noise epsilon he).toMeasure)
instance infiniteSource_probability (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) :
    IsProbabilityMeasure (infiniteSource noise epsilon he) := by unfold infiniteSource; infer_instance

def prefixRaw (N : ℕ) (w : InfiniteRaw) : Raw N := fun j => w (j.1,j.2)
def prefixPlan (N : ℕ) (plan : ℕ → ℕ × Command) : Fin N → ℕ × Command := fun j => plan j

def coordinateSet (N : ℕ) : Finset (ℕ × Bool) := (Finset.range N).product Finset.univ

def coordinateEquiv (N : ℕ) : (Fin N × Bool) ≃ coordinateSet N where
  toFun j := ⟨(j.1,j.2),by simp [coordinateSet,j.1.isLt]⟩
  invFun j := (⟨j.val.1,by simpa [coordinateSet] using j.property⟩,j.val.2)
  left_inv j := rfl
  right_inv j := by cases j; rfl

@[fun_prop] theorem measurable_prefixRaw (N : ℕ) : Measurable (prefixRaw N) := by
  apply measurable_pi_lambda
  intro j
  exact (measurable_pi_apply ((j.1 : ℕ),j.2) : Measurable (fun w : InfiniteRaw => w ((j.1 : ℕ),j.2)))

/-- SAME infinite product has EXACTLY the frozen finite full raw law on every
registered prefix; all idle/work draws and all failures are retained. -/
theorem infinite_raw_prefix_law (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) (N : ℕ) :
    (infiniteSource noise epsilon he).map (prefixRaw N)=sourceLaw noise epsilon he N := by
  let mu := (RegisterFaultFinitePurposeProbe.primitiveLaw noise epsilon he).toMeasure
  have hr := Measure.infinitePi_map_restrict (fun _ : ℕ × Bool => mu) (I:=coordinateSet N)
  have heq := Measure.pi_map_piCongrLeft (coordinateEquiv N).symm (fun _ : Fin N × Bool => mu)
  rw [← hr,Measure.map_map (MeasurableEquiv.piCongrLeft (fun _ : Fin N × Bool => Bool × Bool) (coordinateEquiv N).symm).measurable
    (Finset.measurable_restrict _)] at heq
  exact heq

def roundAt (plan : ℕ → ℕ × Command) (w : InfiniteRaw) (k : ℕ) : Round :=
  ⟨(plan k).1,(plan k).2,(w (k,false)).1,(w (k,false)).2,(w (k,true)).1,(w (k,true)).2⟩
def roundPrefix (plan : ℕ → ℕ × Command) (w : InfiniteRaw) (N : ℕ) : List Round :=
  List.ofFn (fun j : Fin N => roundAt plan w j)

@[simp] theorem roundPrefix_registered (plan : ℕ → ℕ × Command) (w : InfiniteRaw) (N : ℕ) :
    roundPrefix plan w N=registeredRounds (prefixPlan N plan) (prefixRaw N w) := rfl

def stageStore {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (plan : ℕ → ℕ × Command) (w : InfiniteRaw) : ℕ → Store n
  | 0 => s
  | k+1 => roundNext i c (stageStore i c s plan w k) (roundAt plan w k)

/-- Actual chronological record at EVERY natural time, not zero padding. Both
steps execute on the retained store, which includes all preceding appends. -/
def recordAt {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (plan : ℕ → ℕ × Command) (w : InfiniteRaw) (t : ℕ) :
    Option (ClockedRecord n) :=
  let k := t/2
  let u := stageStore i c s plan w k
  let r := roundAt plan w k
  if t%2=0 then RegisterOwnProgramPopulation.transaction i c u (idleRequest r)
  else RegisterOwnProgramPopulation.transaction i c (middle i c u r) (workRequest i c u r)

@[simp] theorem actual_even {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (plan : ℕ → ℕ × Command) (w : InfiniteRaw) (k : ℕ) :
    recordAt i c s plan w (2*k)=RegisterOwnProgramPopulation.transaction i c (stageStore i c s plan w k) (idleRequest (roundAt plan w k)) := by
  simp only [recordAt,show (2*k)/2=k by omega,show (2*k)%2=0 by omega,if_true]
@[simp] theorem actual_odd {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (plan : ℕ → ℕ × Command) (w : InfiniteRaw) (k : ℕ) :
    recordAt i c s plan w (2*k+1)=RegisterOwnProgramPopulation.transaction i c
      (middle i c (stageStore i c s plan w k) (roundAt plan w k))
      (workRequest i c (stageStore i c s plan w k) (roundAt plan w k)) := by
  simp only [recordAt,show (2*k+1)/2=k by omega,show (2*k+1)%2=1 by omega,show ¬(1:ℕ)=0 by decide,if_false]

def roundFold {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (rs : List Round) : Store n := rs.foldl (roundNext i c) s

private theorem fold_append {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (rs qs : List Round) :
    roundFold i c s (rs++qs)=roundFold i c (roundFold i c s rs) qs := List.foldl_append

private theorem trace_append {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (rs qs : List Round) :
    completeTrace i c s (rs++qs)=completeTrace i c s rs ++ completeTrace i c (roundFold i c s rs) qs := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih =>
    change _ :: _ :: completeTrace i c (roundNext i c s r) (rs++qs)=_
    rw [ih]
    rfl

theorem actual_store_finite_prefix {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (plan : ℕ → ℕ × Command) (w : InfiniteRaw) (N : ℕ) :
    stageStore i c s plan w N=roundFold i c s (roundPrefix plan w N) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [stageStore,roundPrefix,List.ofFn_succ',List.concat_eq_append]
    rw [fold_append]
    change roundNext i c _ _=roundNext i c _ _
    rw [ih]
    rfl

private theorem ofFn_two {α : Type} (f : ℕ → α) (k : ℕ) :
    List.ofFn (fun j : Fin (k+2) => f j)=List.ofFn (fun j : Fin k => f j)++[f k,f (k+1)] := by
  rw [List.ofFn_succ',List.ofFn_succ']
  simp [List.concat_eq_append,List.append_assoc]

/-- Entire actual physical/identity/cost journal prefix is literally the old
finite protocol on the SAME restricted raw word, not only equal in law. -/
theorem actual_record_finite_prefix {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (plan : ℕ → ℕ × Command) (w : InfiniteRaw) (N : ℕ) :
    List.ofFn (fun j : Fin (2*N) => recordAt i c s plan w j)=
      completeTrace i c s (registeredRounds (prefixPlan N plan) (prefixRaw N w)) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [show 2*(N+1)=2*N+2 by omega,ofFn_two,ih]
    rw [← roundPrefix_registered plan w (N+1)]
    have hp : roundPrefix plan w (N+1)=roundPrefix plan w N++[roundAt plan w N] := by
      simp only [roundPrefix,List.ofFn_succ',List.concat_eq_append,Fin.val_castSucc,Fin.val_last]
    rw [hp,trace_append,← actual_store_finite_prefix,roundPrefix_registered]
    simp only [actual_even,actual_odd]
    rfl

local instance {d : ℕ} : MeasurableSpace (Option (ClockedRecord d)) := ⊤
local instance {d : ℕ} : MeasurableSpace (List (Option (ClockedRecord d))) := ⊤

@[fun_prop] theorem measurable_actual_record {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (plan : ℕ → ℕ × Command) (t : ℕ) :
    Measurable (fun w => recordAt i c s plan w t) := by
  let f : Raw (t+1) → Option (ClockedRecord n) := fun v =>
    ((completeTrace i c s (registeredRounds (prefixPlan (t+1) plan) v))[t]?).getD none
  have heq : (fun w => recordAt i c s plan w t)=f ∘ prefixRaw (t+1) := by
    funext w
    simp only [Function.comp_apply,f,← actual_record_finite_prefix]
    simp only [List.getElem?_ofFn,dif_pos (show t<2*(t+1) by omega),Option.getD_some]
  rw [heq]
  exact (measurable_of_finite f).comp (measurable_prefixRaw _)

@[fun_prop] theorem measurable_recordStream {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (plan : ℕ → ℕ × Command) :
    Measurable (fun w t => recordAt i c s plan w t) :=
  measurable_pi_lambda _ (fun t => measurable_actual_record i c s plan t)

def recordPathLaw {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (plan : ℕ → ℕ × Command)
    (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) : Measure (ℕ → Option (ClockedRecord n)) :=
  (infiniteSource noise epsilon he).map (fun w t => recordAt i c s plan w t)

instance recordPathLaw_probability {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (plan : ℕ → ℕ × Command)
    (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) : IsProbabilityMeasure (recordPathLaw i c s plan noise epsilon he) :=
  Measure.isProbabilityMeasure_map (measurable_recordStream i c s plan).aemeasurable

/-- List-coded complete finite journal law read DIRECTLY from the one raw
infinite source. The readout factors through exactly its N registered draws. -/
theorem source_actual_prefix_law {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (plan : ℕ → ℕ × Command)
    (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) (N : ℕ) :
    (infiniteSource noise epsilon he).map (fun w => List.ofFn (fun j : Fin (2*N) => recordAt i c s plan w j))=
      (sourceLaw noise epsilon he N).map (fun v => completeTrace i c s (registeredRounds (prefixPlan N plan) v)) := by
  simp_rw [actual_record_finite_prefix]
  rw [← infinite_raw_prefix_law noise epsilon he N,Measure.map_map (measurable_of_finite _) (measurable_prefixRaw N)]
  rfl

/-- The actual infinite RECORD law has the SAME original finite protocol
law at each full prefix, in the standard finite-coordinate representation.
No ambient List.ofFn measurability for arbitrary Real-valued records is assumed. -/
theorem recordPath_prefix_law {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (plan : ℕ → ℕ × Command)
    (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) (N : ℕ) :
    (recordPathLaw i c s plan noise epsilon he).map (fun rs (j : Fin (2*N)) => rs j)=
      (sourceLaw noise epsilon he N).map (fun v (j : Fin (2*N)) =>
        ((completeTrace i c s (registeredRounds (prefixPlan N plan) v))[j.val]?).getD none) := by
  rw [recordPathLaw,Measure.map_map (by fun_prop) (measurable_recordStream i c s plan)]
  rw [← infinite_raw_prefix_law noise epsilon he N,Measure.map_map (measurable_of_finite _) (measurable_prefixRaw N)]
  congr 1
  funext w j
  simp only [Function.comp_apply,← actual_record_finite_prefix]
  simp [j.isLt]

private theorem balance_ofFn {n : ℕ} (reserve g : ℝ) (ts : ℕ → Option (ClockedRecord n)) (k : ℕ) :
    balance reserve g (List.ofFn (fun j : Fin k => ts j))=
      cumulativeResourceBalance reserve (fun t => credit g (ts t)) (fun t => fee (ts t)) k := by
  induction k with
  | zero => simp [cumulativeResourceBalance]
  | succ k ih =>
    rw [List.ofFn_succ',List.concat_eq_append]
    change (List.foldl (fun R t => R+credit g t-fee t) reserve
      (List.ofFn (fun j : Fin k => ts j)++[ts k]))=_
    rw [List.foldl_append]
    change balance reserve g (List.ofFn (fun j : Fin k => ts j))+credit g (ts k)-fee (ts k)=_
    rw [ih]
    simp only [cumulativeResourceBalance,Finset.sum_range_succ]
    ring

/-- Pathwise original P6 for the actual ONGOING recursion; at no point is the
process stopped or replaced by a zero tail. Same g/R rights as finite source. -/
theorem every_actual_infinite_prefix_funded {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (plan : ℕ → ℕ × Command)
    (w : InfiniteRaw) (g reserve : ℝ) (hg : (c : ℝ)≤g) (hr : 0≤reserve) :
    ResourceViable reserve (fun t => credit g (recordAt i c s plan w t)) (fun t => fee (recordAt i c s plan w t)) := by
  intro k
  rw [← balance_ofFn]
  have ht := Fin.ofFn_take_eq_take_ofFn (show k≤2*k by omega) (fun j : Fin (2*k) => recordAt i c s plan w j)
  change List.ofFn (fun j : Fin k => recordAt i c s plan w j)=_ at ht
  rw [ht,actual_record_finite_prefix]
  exact all_prefixes_nonnegative i c s _ g reserve hg hr k

private theorem measurable_viable {n : ℕ} (reserve g : ℝ) :
    MeasurableSet {ts : ℕ → Option (ClockedRecord n) | ResourceViable reserve (fun t => credit g (ts t)) (fun t => fee (ts t))} := by
  have heq : {ts : ℕ → Option (ClockedRecord n) | ResourceViable reserve (fun t => credit g (ts t)) (fun t => fee (ts t))}=
      ⋂ k : ℕ, {ts | 0≤cumulativeResourceBalance reserve (fun t => credit g (ts t)) (fun t => fee (ts t)) k} := by
    ext ts
    simp [ResourceViable]
  rw [heq]
  apply MeasurableSet.iInter
  intro k
  apply measurableSet_le measurable_const
  unfold cumulativeResourceBalance
  have hc : Measurable (credit (n:=n) g) := by intro t ht; trivial
  have hf : Measurable (fee (n:=n)) := by intro t ht; trivial
  exact (measurable_const.add (Finset.measurable_sum _ (fun t _ => hc.comp (measurable_pi_apply t)))).sub
    (Finset.measurable_sum _ (fun t _ => hf.comp (measurable_pi_apply t)))

/-- Original P6 on the genuine probability law of the actual infinite
population journal. This uses no finite stopping or supplied funding field. -/
theorem actual_infinite_law_resource_viable {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (plan : ℕ → ℕ × Command)
    (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) (g reserve : ℝ) (hg : (c : ℝ)≤g) (hr : 0≤reserve) :
    ∀ᵐ ts ∂recordPathLaw i c s plan noise epsilon he,
      ResourceViable reserve (fun t => credit g (ts t)) (fun t => fee (ts t)) := by
  rw [recordPathLaw]
  apply (ae_map_iff (measurable_recordStream i c s plan).aemeasurable (measurable_viable reserve g)).mpr
  exact ae_of_all _ (fun w => every_actual_infinite_prefix_funded i c s plan w g reserve hg hr)

/-- Actual global allocator advances twice per round even for failures; no
newly born slot is confused with a retained parent or a nonexistent request. -/
theorem stage_length {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (plan : ℕ → ℕ × Command) (w : InfiniteRaw) (N : ℕ) :
    (stageStore i c s plan w N).length=s.length+2*N := by
  induction N with
  | zero => simp [stageStore]
  | succ N ih => simp only [stageStore,roundNext,middle,RegisterOwnProgramPopulation.next_length,ih]; omega

private theorem next_existing {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (q : Request)
    (j : ℕ) (p : ClockedOrganism n) (hp : RegisterPopulationHistorySource.lookup s j=some p) :
    ∃ p', RegisterPopulationHistorySource.lookup (RegisterOwnProgramPopulation.next i c s q) j=some p' := by
  by_cases hq : q.parent=j
  · have h := RegisterOwnProgramPopulation.retained_parent_identity i c s q p (by simpa only [hq] using hp)
    exact ⟨_,by simpa only [hq] using h.1⟩
  · have hj : j<s.length := by
      by_contra hn
      have hz : RegisterPopulationHistorySource.lookup s j=none := by
        simp [RegisterPopulationHistorySource.lookup,List.getElem?_eq_none (by omega : s.length≤j)]
      rw [hz] at hp
      cases hp
    exact ⟨p,(RegisterOwnProgramPopulation.next_other_slot i c s q j hj hq).trans hp⟩

/-- Initial occupied addresses stay ACTUALLY occupied through every real
population recursion. This is derived from retained lookup/append, not assumed
as a future supply or genealogy certificate. -/
theorem retained_address_exists {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (plan : ℕ → ℕ × Command) (w : InfiniteRaw)
    (j : ℕ) (p : ClockedOrganism n) (hp : RegisterPopulationHistorySource.lookup s j=some p) (N : ℕ) :
    ∃ p', RegisterPopulationHistorySource.lookup (stageStore i c s plan w N) j=some p' := by
  induction N with
  | zero => exact ⟨p,hp⟩
  | succ N ih =>
    obtain ⟨p',hp'⟩ := ih
    obtain ⟨p'',hp''⟩ := next_existing i c _ (idleRequest (roundAt plan w N)) j p' hp'
    exact next_existing i c _ (workRequest i c _ (roundAt plan w N)) j p'' hp''

/-- A registered scheduler selecting initially occupied addresses performs
actual idle AND work forever. No zero padding represents those steps. Invalid
addresses outside this assumption are still supported, with no phantom credit. -/
theorem ongoing_real_transactions {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (plan : ℕ → ℕ × Command)
    (hplan : ∀ k, ∃ p, RegisterPopulationHistorySource.lookup s (plan k).1=some p) (w : InfiniteRaw) (k : ℕ) :
    (recordAt i c s plan w (2*k)).isSome ∧ (recordAt i c s plan w (2*k+1)).isSome := by
  obtain ⟨p,hp⟩ := hplan k
  obtain ⟨p',hp'⟩ := retained_address_exists i c s plan w (plan k).1 p hp k
  obtain ⟨p'',hp''⟩ := next_existing i c _ (idleRequest (roundAt plan w k)) (plan k).1 p' hp'
  simp only [actual_even,actual_odd]
  simp [RegisterOwnProgramPopulation.transaction,RegisterPopulationHistorySource.transaction,idleRequest,workRequest,
    roundAt,hp',hp'',middle] at *

/-- Concrete SAME two inherited program founders from the finite positive
source. Even and odd rounds alternate real parent0(false) and parent2(true). -/
def alternatingPlan (k : ℕ) : ℕ × Command := (if k%2=0 then 0 else 2,.compiled)

theorem alternating_actual_work_forever (w : InfiniteRaw) (k : ℕ) :
    (recordAt (0 : Fin 1) 1 RegisterOwnProgramPopulation.witnessInitial alternatingPlan w (2*k)).isSome ∧
    (recordAt (0 : Fin 1) 1 RegisterOwnProgramPopulation.witnessInitial alternatingPlan w (2*k+1)).isSome := by
  apply ongoing_real_transactions
  intro j
  simp only [alternatingPlan]
  split_ifs <;>
    simp [RegisterOwnProgramPopulation.witnessInitial,RegisterOwnProgramPopulation.witnessFounders,
      RegisterPopulationHistorySource.founders,RegisterPopulationHistorySource.lookup]

/-- SAME recursive population state transport, not an independent simulation
or desired commuting-field assumption. -/
theorem actual_store_transport {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (plan : ℕ → ℕ × Command) (w : InfiniteRaw) (N : ℕ) :
    projectStore i (stageStore i c s plan w N)=stageStore (0 : Fin 1) c (projectStore i s) plan w N := by
  induction N with
  | zero => rfl
  | succ N ih => rw [stageStore,round_next_transport,ih]; rfl

theorem actual_record_transport {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (plan : ℕ → ℕ × Command) (w : InfiniteRaw) (t : ℕ) :
    (recordAt i c s plan w t).map (projectClockedRecord i)=recordAt (0 : Fin 1) c (projectStore i s) plan w t := by
  unfold recordAt
  split_ifs
  · rw [own_transaction_transport,actual_store_transport]
  · rw [own_transaction_transport,middle_transport,work_request_transport,actual_store_transport]

/-- Full infinite complete-journal probability law preserves actual owner IDs,
code, failed ticks, physical seed, fees and idle credits on the SAME source. -/
theorem infinite_journal_law_transport {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (plan : ℕ → ℕ × Command)
    (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) :
    (recordPathLaw i c s plan noise epsilon he).map (fun ts k => (ts k).map (projectClockedRecord i))=
      recordPathLaw (0 : Fin 1) c (projectStore i s) plan noise epsilon he := by
  have hm : Measurable (fun (ts : ℕ → Option (ClockedRecord n)) k => (ts k).map (projectClockedRecord i)) := by
    apply measurable_pi_lambda
    intro k
    have hf : Measurable (Option.map (projectClockedRecord i)) := by intro t ht; trivial
    exact hf.comp (measurable_pi_apply k)
  rw [recordPathLaw,Measure.map_map hm (measurable_recordStream i c s plan)]
  unfold recordPathLaw
  congr 1
  funext w k
  exact actual_record_transport i c s plan w k

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationFundedInfinite
