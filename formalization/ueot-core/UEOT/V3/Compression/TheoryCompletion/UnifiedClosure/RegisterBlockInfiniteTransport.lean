import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterBlockFormationTransport
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterRotatingBodyP10

/-!
Original promise: book11/C4 actual directed continuation must carry the SAME formed/retained parent and complete records on a genuine ongoing source.
Existing source: exact literal block formation/binding/finite trace and single-round product transport; original k-body Returns/P10 provides its own genuine countable execution.
Premise reduced: derive the missing countable-source/record/event transport from actual repeated embedded sweeps and native product pushforward, not a finite-prefix assertion renamed infinite.
Model/boundary: original compiler, injective e:Fin k into Fin n, exactly k actual transactions per round; embedded k-sweep is NOT original all-n sweep, unvisited coordinates persist from the actual initial seed.
Consumer: original k-body infinite records/law, measurable events, return-tail and P10; no extra action, reset, hidden-memory policy descent, GOD, resource or discount-unit change.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterBlockInfiniteTransport
open MeasureTheory ProbabilityTheory Set Filter
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultJointRecord
open RegisterRotatingBodySource RegisterRotatingBodyReturns RegisterBlockFormationTransport
open scoped NNReal ENNReal Topology
noncomputable section

/-- SAME registered source coordinate at every round, with no retry. -/
def stream {k n : ℕ} (e : Fin k ↪ Fin n) (w : RoundStream n) : RoundStream k:=fun r=>raw e (w r)

@[fun_prop] theorem measurable_stream {k n : ℕ} (e : Fin k ↪ Fin n) : Measurable (stream e) :=
  measurable_pi_lambda _ (fun r=>(measurable_of_finite (raw e)).comp (measurable_pi_apply r))

theorem source_law {k n : ℕ} (e : Fin k ↪ Fin n) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon ≤ 1) :
    (infiniteLaw n noise epsilon he).map (stream e)=infiniteLaw k noise epsilon he :=by
  unfold infiniteLaw stream
  rw [Measure.infinitePi_map_pi _ (fun _=>measurable_of_finite (raw e))]
  simp only [raw_source_law]

/-- Literal repeated embedded sweep, executed on the preceding actual parent. -/
def parentAt {k n : ℕ} (e : Fin k ↪ Fin n) (b : Bool) (fee : NNReal) (o : Organism n) (w : RoundStream n) : ℕ→Organism n
  | 0=>o
  | r+1=>runPorts b fee (w r) (parentAt e b fee o w r) ((List.finRange k).map e)

@[simp] theorem parent_program {k n : ℕ} (e : Fin k ↪ Fin n) (b : Bool) (fee : NNReal) (o : Organism n) (w : RoundStream n) (r : ℕ) :
    (parentAt e b fee o w r).program=o.program :=by
  induction r with
  | zero=>rfl
  | succ r ih=>simp only [parentAt,runPorts_program,ih]
@[simp] theorem parent_history {k n : ℕ} (e : Fin k ↪ Fin n) (b : Bool) (fee : NNReal) (o : Organism n) (w : RoundStream n) (r : ℕ) :
    (parentAt e b fee o w r).history=o.history :=by
  induction r with
  | zero=>rfl
  | succ r ih=>simp only [parentAt,runPorts_history,ih]

/-- Actual source dynamics preserves every unexecuted register, forever. -/
theorem unvisited_preserved {k n : ℕ} (e : Fin k ↪ Fin n) (b : Bool) (fee : NNReal) (o : Organism n)
    (w : RoundStream n) (r : ℕ) (l : Fin n) (hl : l∉Set.range e) :
    (parentAt e b fee o w r).physical l=o.physical l :=by
  have hmem : l∉(List.finRange k).map e :=by simpa only [List.mem_map,List.mem_finRange,true_and,Set.mem_range,not_exists] using hl
  induction r with
  | zero=>rfl
  | succ r ih=>rw [parentAt,runPorts_physical,if_neg hmem,ih]

/-- Projection of THIS actual retained parent, at EVERY macro clock. -/
theorem parent_transport {k n : ℕ} (e : Fin k ↪ Fin n) (b : Bool) (fee : NNReal) (o : Organism n) (w : RoundStream n) (r : ℕ) :
    organism e (parentAt e b fee o w r)=RegisterRotatingBodyReturns.parentAt b fee (organism e o) (stream e w) r :=by
  induction r with
  | zero=>rfl
  | succ r ih=>rw [parentAt,run_transport,ih];rfl

/-- Derived closed form, used ONLY to prove finite-factor measurability.
The execution above always runs the actual retained parent; no reset is run. -/
def closedParent {k n : ℕ} (e : Fin k ↪ Fin n) (b : Bool) (z : RoundRaw n) (o : Organism n) : Organism n:=
  ⟨o.history,fun l=>if l∈(List.finRange k).map e then bodyState b z l else o.physical l,o.program⟩

theorem actual_parent_closed {k n : ℕ} (e : Fin k ↪ Fin n) (b : Bool) (fee : NNReal) (o : Organism n) (w : RoundStream n) (r : ℕ) :
    parentAt e b fee o w (r+1)=closedParent e b (w r) o :=by
  have hH:=parent_history e b fee o w (r+1)
  have hP:=parent_program e b fee o w (r+1)
  have hF : (parentAt e b fee o w (r+1)).physical=(closedParent e b (w r) o).physical :=by
    ext l
    rw [parentAt,runPorts_physical]
    change (if l∈(List.finRange k).map e then _ else _)=if l∈(List.finRange k).map e then _ else _
    by_cases hl : l∈(List.finRange k).map e
    · simp only [if_pos hl,bodyState]
    · have hnot : l∉Set.range e :=by simpa only [List.mem_map,List.mem_finRange,true_and,Set.mem_range,not_exists] using hl
      simp only [if_neg hl,unvisited_preserved e b fee o w r l hnot]
  cases hp : parentAt e b fee o w (r+1) with
  | mk history physical program=>
    simp only [hp] at hH hP hF
    subst history
    subst program
    subst physical
    rfl

/-- Complete chronological finite prefix; every failed/fault record remains. -/
def recordsThrough {k n : ℕ} (e : Fin k ↪ Fin n) (b : Bool) (fee : NNReal) (o : Organism n) (w : RoundStream n) : ℕ→List (ModeRecord n)
  | 0=>[]
  | r+1=>recordsThrough e b fee o w r++tracePorts b fee (w r) (parentAt e b fee o w r) ((List.finRange k).map e)

theorem actual_prefix_length {k n : ℕ} (e : Fin k ↪ Fin n) (b : Bool) (fee : NNReal) (o : Organism n) (w : RoundStream n) (r : ℕ) :
    (recordsThrough e b fee o w r).length=k*r :=by
  induction r with
  | zero=>rfl
  | succ r ih=>rw [recordsThrough,List.length_append,ih,trace_length,List.length_map,List.length_finRange];simp only [Nat.mul_succ]

theorem prefix_transport {k n : ℕ} (e : Fin k ↪ Fin n) (b : Bool) (fee : NNReal) (o : Organism n) (w : RoundStream n) (r : ℕ) :
    (recordsThrough e b fee o w r).map (modeRecord e)=
      RegisterRotatingBodyReturns.recordsThrough b fee (organism e o) (stream e w) r :=by
  induction r with
  | zero=>rfl
  | succ r ih=>simp only [recordsThrough,List.map_append,ih,trace_transport,parent_transport];rfl

/-- No default/padding: k0 has no Fin k index and no actual transaction. -/
def recordAt {k n : ℕ} (e : Fin k ↪ Fin n) (b : Bool) (fee : NNReal) (o : Organism n) (r : ℕ) (j : Fin k) (w : RoundStream n) : ModeRecord n:=
  (tracePorts b fee (w r) (parentAt e b fee o w r) ((List.finRange k).map e)).get
    ⟨j,by simpa only [trace_length,List.length_map,List.length_finRange] using j.isLt⟩

local instance {n : ℕ} : MeasurableSpace (ModeRecord n):=⊤
local instance {n : ℕ} : MeasurableSingletonClass (ModeRecord n):=⟨fun _=>trivial⟩

/-- A real finite source factor, not a measurability assumption on arbitrary
uncountable record tuples mapped to discrete Lists. -/
theorem measurable_recordAt {k n : ℕ} (e : Fin k ↪ Fin n) (b : Bool) (fee : NNReal) (o : Organism n) (r : ℕ) (j : Fin k) :
    Measurable (recordAt e b fee o r j) :=by
  cases r with
  | zero=>
    let F : RoundRaw n→ModeRecord n:=fun z=>(tracePorts b fee z o ((List.finRange k).map e)).get
      ⟨j,by simpa only [trace_length,List.length_map,List.length_finRange] using j.isLt⟩
    exact (measurable_of_finite F).comp (measurable_pi_apply 0)
  | succ r=>
    let F : RoundRaw n×RoundRaw n→ModeRecord n:=fun z=>(tracePorts b fee z.2 (closedParent e b z.1 o) ((List.finRange k).map e)).get
      ⟨j,by simpa only [trace_length,List.length_map,List.length_finRange] using j.isLt⟩
    have heq : recordAt e b fee o (r+1) j=fun w=>F (w r,w (r+1)) :=by
      funext w
      let G : Organism n→ModeRecord n:=fun p=>(tracePorts b fee (w (r+1)) p ((List.finRange k).map e)).get
        ⟨j,by simpa only [trace_length,List.length_map,List.length_finRange] using j.isLt⟩
      exact congrArg G (actual_parent_closed e b fee o w r)
    rw [heq]
    exact (measurable_of_finite F).comp ((measurable_pi_apply r).prodMk (measurable_pi_apply (r+1)))

theorem actual_round_records {k n : ℕ} (e : Fin k ↪ Fin n) (b : Bool) (fee : NNReal) (o : Organism n) (w : RoundStream n) (r : ℕ) :
    List.ofFn (fun j : Fin k=>recordAt e b fee o r j w)=
      tracePorts b fee (w r) (parentAt e b fee o w r) ((List.finRange k).map e) :=by
  apply List.ext_getElem
  · simp only [List.length_ofFn,trace_length,List.length_map,List.length_finRange]
  · intros; simp only [List.getElem_ofFn];rfl

/-- Every actual record coordinate projects; the child and retained-parent
fields are the literal ones certified by the finite source theorem. -/
theorem record_transport {k n : ℕ} (e : Fin k ↪ Fin n) (b : Bool) (fee : NNReal) (o : Organism n) (w : RoundStream n) (r : ℕ) (j : Fin k) :
    modeRecord e (recordAt e b fee o r j w)=
      RegisterRotatingBodyReturns.recordAt b fee (organism e o) r j (stream e w) :=by
  have hh:=trace_transport e b fee (w r) (parentAt e b fee o w r) (List.finRange k)
  rw [←actual_round_records,List.map_ofFn,parent_transport] at hh
  change List.ofFn (fun j=>modeRecord e (recordAt e b fee o r j w))=
    roundTrace b fee ((stream e w) r) (RegisterRotatingBodyReturns.parentAt b fee (organism e o) (stream e w) r) at hh
  rw [←RegisterRotatingBodyReturns.actual_round_records] at hh
  have hi:=congrArg (fun rs : List (ModeRecord k)=>rs[j.val]?) hh
  simpa only [List.getElem?_ofFn,dif_pos j.isLt,Option.some.injEq] using hi

/-- GENUINE ongoing complete fine records, exactly k micro-transactions/round. -/
def infiniteRecords {k n : ℕ} (e : Fin k ↪ Fin n) (b : Bool) (fee : NNReal) (o : Organism n) (w : RoundStream n) : ℕ→Fin k→ModeRecord n:=
  fun r j=>recordAt e b fee o r j w

@[fun_prop] theorem measurable_infiniteRecords {k n : ℕ} (e : Fin k ↪ Fin n) (b : Bool) (fee : NNReal) (o : Organism n) :
    Measurable (infiniteRecords e b fee o) :=
  measurable_pi_lambda _ (fun r=>measurable_pi_lambda _ (fun j=>measurable_recordAt e b fee o r j))

def recordPathLaw {k n : ℕ} (e : Fin k ↪ Fin n) (b : Bool) (fee : NNReal) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon ≤ 1) (o : Organism n) :
    Measure (ℕ→Fin k→ModeRecord n):=(infiniteLaw n noise epsilon he).map (infiniteRecords e b fee o)
instance recordPathLaw_probability {k n : ℕ} (e : Fin k ↪ Fin n) (b : Bool) (fee : NNReal) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon ≤ 1) (o : Organism n) :
    IsProbabilityMeasure (recordPathLaw e b fee noise epsilon he o):=
  Measure.isProbabilityMeasure_map (measurable_infiniteRecords e b fee o).aemeasurable

/-- Pointwise record projection; unlike arbitrary tuple-to-List maps this
is measurable in the original countable product record sigma algebra. -/
def projectedRecords {k n : ℕ} (e : Fin k ↪ Fin n) (rs : ℕ→Fin k→ModeRecord n) : ℕ→Fin k→ModeRecord k:=
  fun r j=>modeRecord e (rs r j)
@[fun_prop] theorem measurable_projectedRecords {k n : ℕ} (e : Fin k ↪ Fin n) : Measurable (projectedRecords e) :=
  measurable_pi_lambda _ (fun r=>measurable_pi_lambda _ (fun j=>
    (show Measurable (modeRecord e) from fun _ _=>trivial).comp ((measurable_pi_apply j).comp (measurable_pi_apply r))))

/-- Exact countable complete-record law, proved from actual parent/prefix
recursion and native source-law pushforward; not inferred from a finite field. -/
theorem countable_record_transport {k n : ℕ} (e : Fin k ↪ Fin n) (b : Bool) (fee : NNReal) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon ≤ 1) (o : Organism n) :
    (recordPathLaw e b fee noise epsilon he o).map (projectedRecords e)=
      RegisterRotatingBodyReturns.recordPathLaw b fee noise epsilon he (organism e o) :=by
  rw [recordPathLaw,Measure.map_map (measurable_projectedRecords e) (measurable_infiniteRecords e b fee o)]
  have hf : (projectedRecords e∘infiniteRecords e b fee o)=
      (fun w r j=>RegisterRotatingBodyReturns.recordAt b fee (organism e o) r j (stream e w)) :=by
    funext w r j
    exact record_transport e b fee o w r j
  rw [hf]
  change (infiniteLaw n noise epsilon he).map ((fun w r j=>RegisterRotatingBodyReturns.recordAt b fee (organism e o) r j w)∘stream e)=_
  rw [←Measure.map_map (measurable_pi_lambda _ (fun r=>measurable_pi_lambda _ (fun j=>RegisterRotatingBodyReturns.measurable_recordAt b fee (organism e o) r j)))
    (measurable_stream e),source_law]
  rfl


/-- Arbitrary measurable countable record events, not just finite cylinders. -/
theorem record_event_transport {k n : ℕ} (e : Fin k ↪ Fin n) (b : Bool) (fee : NNReal) (noise : PMF Bool)
    (epsilon : NNReal) (he : epsilon ≤ 1) (o : Organism n) (S : Set (ℕ→Fin k→ModeRecord k)) (hS : MeasurableSet S) :
    recordPathLaw e b fee noise epsilon he o (projectedRecords e ⁻¹' S)=
      RegisterRotatingBodyReturns.recordPathLaw b fee noise epsilon he (organism e o) S :=by
  rw [←Measure.map_apply (measurable_projectedRecords e) hS,countable_record_transport]

/-- The same native source event pushforward, for the actual round stream. -/
theorem raw_event_transport {k n : ℕ} (e : Fin k ↪ Fin n) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon ≤ 1)
    (S : Set (RoundStream k)) (hS : MeasurableSet S) :
    infiniteLaw n noise epsilon he (stream e ⁻¹' S)=infiniteLaw k noise epsilon he S :=by
  rw [←Measure.map_apply (measurable_stream e) hS,source_law]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterBlockInfiniteTransport
