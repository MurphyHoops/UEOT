import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationOwnerClockTransport
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationFundedProtocol

/-!
Original promise: SAME training and actual finite population episode must have a realizable pathwise payment account.
Existing source: exact owner/phase/AST/offspring transport; neither fixed-parent native funding nor idle-before-work funds THIS episode.
Premise reduced: derive every literal expenditure and whole-prefix budget from actual interpreter, registered tariff cap and finite pre-funded reserve.
Class/boundary: arbitrary finite dispatch plan within registered H, all original2N probes and all Option population records; no idle/credit/action/extra draw.
Consumer: original P6 ResourceViable/prepay for this SAME finite source, including B0; it is an experimenter's explicit finite account, not endogenous energy or infinite maintenance.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationFiniteEpisodeResource
open MeasureTheory ProbabilityTheory
open UEOT.V3.Compression.Objecthood.ResourceClosure
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultJointRecord
open RegisterTimestampedBirthSource (ClockedOrganism ClockedRecord)
open RegisterPopulationHistorySource (Store Request)
open RegisterFaultFinitePurposeProbe RegisterFaultDynamicProbe
open RegisterPopulationOwnerClockTransport
open RegisterPopulationFundedProtocol (fee recordAt)
open scoped BigOperators
noncomputable section

/-- ALL original probe transactions followed by THIS actual computed AST and
registered population plan. Training children remain in training records;
the population study registers only the actual retained post-probe founder. -/
def wholeTrace {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : ClockedOrganism n) (plan : List (ℕ×Bool×Bool)) :
    List (Option (ClockedRecord n)) :=
  let p:=returnedAST i (classify price width d u (sourceData m width omega))
  let s:=[some (RegisterFaultDynamicProbeClocked.postClocked i m omega o)]
  let epoch:=o.clock+2*N
  (RegisterTimestampedBirthSource.trace i m o (RegisterFaultDynamicProbeClocked.probeEvents omega (registration N))).map some ++
    RegisterPopulationOwnerClockTransport.trace i m.writeCost epoch s
      (RegisterPopulationOwnerClockTransport.astEpisode p i m.writeCost epoch s plan)

/-- This totalization is ONLY the finite account: after the registered run
there are no more fees/credits. It is not an infinite execution with fake None. -/
def costStream {n : ℕ} (rs : List (Option (ClockedRecord n))) (k : ℕ) : ℝ :=fee (recordAt rs k)

private theorem literal_fee_bounds {n : ℕ} (i : Fin n) (m : Mechanism) (p : ClockedOrganism n)
    (a : Action) (mode label : Bool) :
    0 ≤ (RegisterTimestampedBirthSource.step i m p a mode label).expenditure ∧
      (RegisterTimestampedBirthSource.step i m p a mode label).expenditure ≤ m.writeCost :=by
  cases mode <;> cases a <;>
    simp [RegisterTimestampedBirthSource.step,modeRecordStep,RegisterJointRecord.recordStep,cost,m.writeCost.coe_nonneg]

private theorem probe_fee_bounds {n : ℕ} (i : Fin n) (m : Mechanism) (p : ClockedOrganism n)
    (es : List RegisterTimestampedBirthSource.Event) (r : ClockedRecord n)
    (hr : r∈RegisterTimestampedBirthSource.trace i m p es) :
    0 ≤ r.expenditure ∧ r.expenditure ≤ m.writeCost :=by
  induction es generalizing p with
  | nil=>simp [RegisterTimestampedBirthSource.trace] at hr
  | cons e es ih=>
    simp only [RegisterTimestampedBirthSource.trace,List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact literal_fee_bounds i m p e.1 e.2.1 e.2.2
    · exact ih _ hr

private theorem transaction_fee_bounds {n : ℕ} (i : Fin n) (c : NNReal) (R : ℕ) (s : Store n) (q : Request) :
    0 ≤ fee (RegisterPopulationOwnerClockTransport.transaction i c R s q) ∧
      fee (RegisterPopulationOwnerClockTransport.transaction i c R s q) ≤ c :=by
  unfold RegisterPopulationOwnerClockTransport.transaction
  cases hp : RegisterPopulationHistorySource.lookup s q.parent with
  | none=>simp [fee]
  | some p=>
    have h:=literal_fee_bounds i (RegisterOwnProgramPopulation.mechanism c s q)
      {p with clock:=R+s.length} q.action q.mode q.label
    have hc : (RegisterOwnProgramPopulation.mechanism c s q).writeCost=c:=rfl
    rw [hc] at h
    simpa only [Option.map_some,fee] using h

private theorem population_fee_bounds {n : ℕ} (i : Fin n) (c : NNReal) (R : ℕ) (s : Store n)
    (es : List Request) (r : Option (ClockedRecord n))
    (hr : r∈RegisterPopulationOwnerClockTransport.trace i c R s es) : 0 ≤ fee r ∧ fee r ≤ c :=by
  induction es generalizing s with
  | nil=>simp [RegisterPopulationOwnerClockTransport.trace] at hr
  | cons q es ih=>
    simp only [RegisterPopulationOwnerClockTransport.trace,List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact transaction_fee_bounds i c R s q
    · exact ih _ hr

/-- Both original physical tariffs are the SAME c, including preempted-fault
fee0 and invalid None fee0. No funding predicate is an input. -/
theorem whole_fee_bounds {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : ClockedOrganism n) (plan : List (ℕ×Bool×Bool))
    (r : Option (ClockedRecord n)) (hr : r∈wholeTrace i m price width d u omega o plan) :
    0 ≤ fee r ∧ fee r ≤ m.writeCost :=by
  unfold wholeTrace at hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨t,ht,rfl⟩:=List.mem_map.mp hr
    exact probe_fee_bounds i m o _ t ht
  · exact population_fee_bounds i m.writeCost _ _ _ _ hr

private theorem literal_trace_length {n : ℕ} (i : Fin n) (m : Mechanism) (p : ClockedOrganism n)
    (es : List RegisterTimestampedBirthSource.Event) :
    (RegisterTimestampedBirthSource.trace i m p es).length=es.length :=by
  induction es generalizing p with
  | nil=>rfl
  | cons e es ih=>simpa only [RegisterTimestampedBirthSource.trace,List.length_cons] using congrArg Nat.succ (ih _)

private theorem population_trace_length {n : ℕ} (i : Fin n) (c : NNReal) (R : ℕ) (s : Store n) (es : List Request) :
    (RegisterPopulationOwnerClockTransport.trace i c R s es).length=es.length :=by
  induction es generalizing s with
  | nil=>rfl
  | cons e es ih=>simpa only [RegisterPopulationOwnerClockTransport.trace,List.length_cons] using congrArg Nat.succ (ih _)

private theorem ast_episode_length {n : ℕ} (p : Instruction n) (i : Fin n) (c : NNReal) (R : ℕ)
    (s : Store n) (plan : List (ℕ×Bool×Bool)) :
    (RegisterPopulationOwnerClockTransport.astEpisode p i c R s plan).length=plan.length :=by
  induction plan generalizing s with
  | nil=>rfl
  | cons e es ih=>
    rcases e with ⟨j,mode,label⟩
    simpa only [RegisterPopulationOwnerClockTransport.astEpisode,List.length_cons] using congrArg Nat.succ (ih _)

/-- Planned slots count the available fee positions, not necessarily real
transactions. The bound is conservative and does not change the actual trace. -/
theorem wholeTrace_length {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : ClockedOrganism n) (plan : List (ℕ×Bool×Bool)) :
    (wholeTrace i m price width d u omega o plan).length=2*N+plan.length :=by
  simp only [wholeTrace,List.length_append,List.length_map,literal_trace_length,population_trace_length,
    ast_episode_length,RegisterFaultDynamicProbeClocked.probeEvents,registration_length]

private theorem bounded_cost_prefix {n : ℕ} (rs : List (Option (ClockedRecord n))) (cap : ℝ)
    (hcap : 0 ≤ cap) (hb : ∀r∈rs,fee r ≤ cap) (K : ℕ) :
    (∑k∈Finset.range K,costStream rs k) ≤ (rs.length : ℝ)*cap :=by
  induction rs generalizing K with
  | nil=>simp [costStream,recordAt,fee]
  | cons r rs ih=>
    cases K with
    | zero=>simp only [Finset.range_zero,Finset.sum_empty,List.length_cons,Nat.cast_add,Nat.cast_one];positivity
    | succ K=>
      have ht:=ih (fun t ht=>hb t (by simp [ht])) K
      have hh:=hb r (by simp)
      simp only [costStream,Finset.sum_range_succ',recordAt,List.getElem?_cons_zero,List.getElem?_cons_succ,
        Option.join_some,List.length_cons,Nat.cast_add,Nat.cast_one]
      simp only [costStream,recordAt] at ht
      nlinarith

/-- Original P6 is fulfilled for the SAME complete finite trace by a REGISTERED
finite experiment reserve. No credit is introduced, including at None slots. -/
theorem actual_whole_p6 {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : ClockedOrganism n) (plan : List (ℕ×Bool×Bool))
    (H : ℕ) (hplan : plan.length ≤ H) (cap reserve : ℝ)
    (htariff : (m.writeCost : ℝ) ≤ cap) (hr : ((2*N+H : ℕ) : ℝ)*cap ≤ reserve) :
    ResourceViable reserve (fun _=>0) (costStream (wholeTrace i m price width d u omega o plan)) :=by
  have hc : 0 ≤ cap:=m.writeCost.coe_nonneg.trans htariff
  rw [resourceViable_iff_cumulative_cost_le]
  intro K
  have hb:=bounded_cost_prefix (wholeTrace i m price width d u omega o plan) cap hc
    (fun r hr=>(whole_fee_bounds i m price width d u omega o plan r hr).2.trans htariff) K
  rw [wholeTrace_length] at hb
  have hlen : ((2*N+plan.length : ℕ) : ℝ) ≤ ((2*N+H : ℕ) : ℝ):=by exact_mod_cast Nat.add_le_add_left hplan (2*N)
  have hbound:=hb.trans ((mul_le_mul_of_nonneg_right hlen hc).trans hr)
  simpa using hbound

/-- Pay BEFORE each actual fee; this follows from the next-prefix budget.
It is not a balance checked only after borrowing or after a new credit. -/
theorem actual_whole_prepay {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : ClockedOrganism n) (plan : List (ℕ×Bool×Bool))
    (H : ℕ) (hplan : plan.length ≤ H) (cap reserve : ℝ)
    (htariff : (m.writeCost : ℝ) ≤ cap) (hr : ((2*N+H : ℕ) : ℝ)*cap ≤ reserve) (k : ℕ) :
    costStream (wholeTrace i m price width d u omega o plan) k ≤ 
      cumulativeResourceBalance reserve (fun _=>0) (costStream (wholeTrace i m price width d u omega o plan)) k :=by
  have h:= (resourceViable_iff_cumulative_cost_le _ _ _).mp
    (actual_whole_p6 i m price width d u omega o plan H hplan cap reserve htariff hr) (k+1)
  simp only [Finset.sum_range_succ,Finset.sum_const_zero,add_zero] at h
  simp only [cumulativeResourceBalance,Finset.sum_const_zero,add_zero]
  linarith


/-- Exact actual training cost from ALL pre-registered normal/fault inputs.
This reads the original source word in the proof, not a selector noise oracle. -/
theorem actual_probe_cost_sum {n N : ℕ} (i : Fin n) (m : Mechanism) (o : ClockedOrganism n)
    (omega : Coordinate N→Bool×Bool) (js : List (Coordinate N)) :
    ((RegisterTimestampedBirthSource.trace i m o (RegisterFaultDynamicProbeClocked.probeEvents omega js)).map
      (fun r=>r.expenditure)).sum=
      ((js.countP (fun j=>(omega j).1) : ℕ) : ℝ)*m.writeCost :=by
  induction js generalizing o with
  | nil=>simp [RegisterTimestampedBirthSource.trace,RegisterFaultDynamicProbeClocked.probeEvents]
  | cons j js ih=>
    simp only [RegisterFaultDynamicProbeClocked.probeEvents,List.map_cons,
      RegisterTimestampedBirthSource.trace,List.map_cons,List.sum_cons]
    rw [show RegisterTimestampedBirthSource.trace i m
        (RegisterTimestampedBirthSource.step i m o (some j.1) (omega j).1 (omega j).2).parentAfter
        (List.map (fun j=>(some j.1,(omega j).1,(omega j).2)) js)=
      RegisterTimestampedBirthSource.trace i m
        (RegisterTimestampedBirthSource.step i m o (some j.1) (omega j).1 (omega j).2).parentAfter
        (RegisterFaultDynamicProbeClocked.probeEvents omega js) from rfl,ih]
    cases hm : (omega j).1 <;>
      simp [RegisterTimestampedBirthSource.step,modeRecordStep,RegisterJointRecord.recordStep,cost,
        hm,Nat.cast_add,Nat.cast_one]
    all_goals ring

/-- The original all-natural-index ledger at the finite run's end is exactly
its actual fee list. No prospective extra transactions have been inserted. -/
theorem costStream_total {n : ℕ} (rs : List (Option (ClockedRecord n))) :
    (∑k∈Finset.range rs.length,costStream rs k)=(rs.map fee).sum :=by
  induction rs with
  | nil=>simp [costStream,recordAt,fee]
  | cons r rs ih=>
    simp only [List.length_cons,Finset.sum_range_succ',costStream,recordAt,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.join_some,List.map_cons,List.sum_cons]
    simp only [costStream,recordAt] at ih
    rw [ih]
    ring

/-- Fixed three-position protocol, with the original whole future word. -/
def historyPlan (w : Fin 3→Bool×Bool) : List (ℕ×Bool×Bool) :=
  [(0,(w 0).1,(w 0).2),(0,(w 1).1,(w 1).2),(1,(w 2).1,(w 2).2)]

/-- P6 and PREPAY on the SAME unconditioned complete training×future3 source;
accepted, UNKNOWN, no-child and invalid-address outcomes are all retained. -/
theorem same_training_future_source_p6 {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon ≤ 1) (price width d u : ℚ) (o : ClockedOrganism n)
    (cap reserve : ℝ) (htariff : (m.writeCost : ℝ) ≤ cap)
    (hr : ((2*N+3 : ℕ) : ℝ)*cap ≤ reserve) :
    ∀ᵐ z ∂ RegisterFaultDynamicProbeHistoryPrice.experimentLaw noise epsilon he N,
      ResourceViable reserve (fun _=>0) (costStream (wholeTrace i m price width d u z.1 o (historyPlan z.2))) ∧
      ∀k,costStream (wholeTrace i m price width d u z.1 o (historyPlan z.2)) k ≤
        cumulativeResourceBalance reserve (fun _=>0) (costStream (wholeTrace i m price width d u z.1 o (historyPlan z.2))) k :=by
  apply ae_of_all
  intro z
  exact ⟨actual_whole_p6 i m price width d u z.1 o (historyPlan z.2) 3 (by rfl) cap reserve htariff hr,
    actual_whole_prepay i m price width d u z.1 o (historyPlan z.2) 3 (by rfl) cap reserve htariff hr⟩

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationFiniteEpisodeResource
