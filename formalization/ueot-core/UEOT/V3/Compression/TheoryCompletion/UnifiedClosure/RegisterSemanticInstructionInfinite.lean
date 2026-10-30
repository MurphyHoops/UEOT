import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterSemanticInstructionScale

/-!
Original promise: THIS submitted literal program and its actual synthesized coarse program must explain the same continuing complete-record execution.
Existing result: exact semantic synthesis derives the full finite-word record projection and original P9 validity, but no AST-source infinite readout was constructed.
Reduced premise: construct the retained-parent recursion on the SAME primitive stream, derive every literal finite prefix, measurable probability law and countable projection.
Family/boundary: all original finite Bool-register Instructions accepted by synthesize; arbitrary correlated Bool mode/label stream law, unchanged actions/observations/initial organism.
Consumer: the SAME returned AST, actual full infinite record law/event probabilities and original P9 validity; no padding, infinite descendant population, new resource port or all-six-semantics claim.

Measurability factors each coordinate through its FINITE primitive domain. It
never assumes List.ofFn into the discrete space of real-cost records is
measurable on an arbitrary uncountable record tuple. The local record sigma
algebra and countable product interface are those of RegisterFaultInfiniteRecord.
All faults, failed births, paid writes, protected programs and parent histories
are retained. This stream adapter imposes no iid/Markov condition on its law.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterSemanticInstructionInfinite
open MeasureTheory Function
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose
open RegisterFaultJointRecord RegisterActuatorScaleSource RegisterInstructionScaleSource
open RegisterSemanticInstructionScale
noncomputable section

abbrev Primitive := Bool × Bool
abbrev Stream := ℕ → Primitive
abbrev FiniteRaw (N : ℕ) := Fin N → Primitive

/-- Exactly the first N actual mode/label outcomes; neither actions nor
successful births are resampled or filtered. -/
def rawPrefix (N : ℕ) (w : Stream) : List Primitive := List.ofFn (fun j : Fin N => w j)
def finiteRaw (N : ℕ) (w : Stream) : FiniteRaw N := fun j => w j

@[fun_prop] theorem measurable_finiteRaw (N : ℕ) : Measurable (finiteRaw N) :=
  measurable_pi_lambda _ (fun j => measurable_pi_apply (j : ℕ))

/-- Each step retains the actual parent produced by the previous transaction.
The original submitted AST is reinterpreted on that parent's physical state. -/
def parentAt {n : ℕ} (i : Fin n) (m : Mechanism) (p : Instruction n)
    (o : Organism n) (w : Stream) : ℕ → Organism n
  | 0 => o
  | t+1 =>
    let parent := parentAt i m p o w t
    (modeRecordStep i m parent (interpret p parent.physical) (w t).1 (w t).2).transaction.parentAfter

def recordAt {n : ℕ} (i : Fin n) (m : Mechanism) (p : Instruction n)
    (o : Organism n) (w : Stream) (t : ℕ) : ModeRecord n :=
  let parent := parentAt i m p o w t
  modeRecordStep i m parent (interpret p parent.physical) (w t).1 (w t).2

@[simp] theorem parentAt_succ {n : ℕ} (i : Fin n) (m : Mechanism) (p : Instruction n)
    (o : Organism n) (w : Stream) (t : ℕ) :
    parentAt i m p o w (t+1)=(recordAt i m p o w t).transaction.parentAfter := rfl

private theorem parentAt_shift {n : ℕ} (i : Fin n) (m : Mechanism) (p : Instruction n)
    (o : Organism n) (w : Stream) (t : ℕ) :
    parentAt i m p (recordAt i m p o w 0).transaction.parentAfter (fun k => w (k+1)) t=
      parentAt i m p o w (t+1) := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [parentAt,ih]

private theorem recordAt_shift {n : ℕ} (i : Fin n) (m : Mechanism) (p : Instruction n)
    (o : Organism n) (w : Stream) (t : ℕ) :
    recordAt i m p (recordAt i m p o w 0).transaction.parentAfter (fun k => w (k+1)) t=
      recordAt i m p o w (t+1) := by
  change modeRecordStep i m
    (parentAt i m p (recordAt i m p o w 0).transaction.parentAfter (fun k => w (k+1)) t)
    (interpret p (parentAt i m p (recordAt i m p o w 0).transaction.parentAfter (fun k => w (k+1)) t).physical)
    (w (t+1)).1 (w (t+1)).2 = _
  rw [parentAt_shift]
  rfl

/-- Literal complete prefixes of the continuing recursion are exactly the
old programRecords for the SAME primitive word, at every N. -/
theorem actual_finite_prefix {n : ℕ} (i : Fin n) (m : Mechanism) (p : Instruction n)
    (o : Organism n) (w : Stream) (N : ℕ) :
    List.ofFn (fun j : Fin N => recordAt i m p o w j)=programRecords i m p o (rawPrefix N w) := by
  induction N generalizing o w with
  | zero => rfl
  | succ N ih =>
    simp only [rawPrefix,List.ofFn_succ,programRecords]
    change recordAt i m p o w 0 :: _ = recordAt i m p o w 0 :: _
    congr 1
    change List.ofFn (fun j : Fin N => recordAt i m p o w (j+1)) =
      programRecords i m p (recordAt i m p o w 0).transaction.parentAfter (rawPrefix N (fun k => w (k+1)))
    rw [← ih (recordAt i m p o w 0).transaction.parentAfter (fun k => w (k+1))]
    congr 1
    funext j
    exact (recordAt_shift i m p o w j).symm

/-- The finite-word source theorem binds the actual returned q at every
coordinate of the SAME primitive stream, with no new choice of program. -/
theorem actual_record_projection {n : ℕ} (i : Fin n) (m : Mechanism)
    (p : Instruction n) (q : Instruction 1) (hs : synthesize i p=some q)
    (o : Organism n) (w : Stream) (t : ℕ) :
    projectModeRecord i (recordAt i m p o w t)=
      recordAt (0 : Fin 1) m q (projectOrganism i o) w t := by
  have h:=actual_complete_records i m p q hs o (rawPrefix (t+1) w)
  rw [← actual_finite_prefix,← actual_finite_prefix,List.map_ofFn] at h
  have ht:=congrArg (fun rs => rs[t]?) h
  simpa only [List.getElem?_ofFn,dif_pos (Nat.lt_succ_self t),Option.some.injEq,Function.comp_apply] using ht

local instance {n : ℕ} : MeasurableSpace (ModeRecord n) := ⊤
local instance {n : ℕ} : MeasurableSingletonClass (ModeRecord n) := ⟨fun _ => trivial⟩

/-- Finite-domain execution adapter. The default is unreachable at j<N;
actual_finite_prefix proves that no default/padding enters the actual path. -/
def finiteRecords {n : ℕ} (i : Fin n) (m : Mechanism) (p : Instruction n)
    (o : Organism n) (N : ℕ) (v : FiniteRaw N) (j : Fin N) : ModeRecord n :=
  ((programRecords i m p o (List.ofFn v))[j.val]?).getD
    (modeRecordStep i m o none false false)

theorem actual_finite_factor {n : ℕ} (i : Fin n) (m : Mechanism) (p : Instruction n)
    (o : Organism n) (N : ℕ) (w : Stream) (j : Fin N) :
    finiteRecords i m p o N (finiteRaw N w) j=recordAt i m p o w j := by
  unfold finiteRecords finiteRaw
  change ((programRecords i m p o (rawPrefix N w))[j.val]?).getD _=_
  rw [← actual_finite_prefix]
  simp only [List.getElem?_ofFn,dif_pos j.isLt,Option.getD_some]

@[fun_prop] theorem measurable_recordAt {n : ℕ} (i : Fin n) (m : Mechanism) (p : Instruction n)
    (o : Organism n) (t : ℕ) : Measurable (fun w => recordAt i m p o w t) := by
  let F : FiniteRaw (t+1) → ModeRecord n := fun v => finiteRecords i m p o (t+1) v ⟨t,Nat.lt_succ_self t⟩
  have hf : (fun w => recordAt i m p o w t)=F ∘ finiteRaw (t+1) := by
    funext w
    exact (actual_finite_factor i m p o (t+1) w ⟨t,Nat.lt_succ_self t⟩).symm
  rw [hf]
  exact (measurable_of_finite F).comp (measurable_finiteRaw _)

@[fun_prop] theorem measurable_recordPath {n : ℕ} (i : Fin n) (m : Mechanism) (p : Instruction n)
    (o : Organism n) : Measurable (recordAt i m p o) :=
  measurable_pi_lambda _ (fun t => measurable_recordAt i m p o t)

/-- Actual measure of the continuing complete-record process. μ may have
arbitrary temporal/row correlation. Probability normalization is inherited
from its registered source law through a proved measurable actual readout. -/
def recordPathLaw {n : ℕ} (i : Fin n) (m : Mechanism) (p : Instruction n)
    (o : Organism n) (μ : Measure Stream) : Measure (ℕ → ModeRecord n) :=
  μ.map (recordAt i m p o)

instance recordPathLaw_probability {n : ℕ} (i : Fin n) (m : Mechanism) (p : Instruction n)
    (o : Organism n) (μ : Measure Stream) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (recordPathLaw i m p o μ) :=
  Measure.isProbabilityMeasure_map (measurable_recordPath i m p o).aemeasurable

/-- The path's actual finite tuple law is precisely execution of the old
finite word on the source's actual finite restriction. There is no arbitrary
List.ofFn map from an uncountable record tuple into a discrete list space. -/
theorem actual_prefix_law {n : ℕ} (i : Fin n) (m : Mechanism) (p : Instruction n)
    (o : Organism n) (μ : Measure Stream) (N : ℕ) :
    (recordPathLaw i m p o μ).map (fun rs (j : Fin N) => rs j)=
      (μ.map (finiteRaw N)).map (finiteRecords i m p o N) := by
  rw [recordPathLaw,Measure.map_map (by fun_prop) (measurable_recordPath i m p o),
    Measure.map_map (measurable_of_finite _) (measurable_finiteRaw _)]
  congr 1
  funext w j
  exact (actual_finite_factor i m p o N w j).symm

/-- The same complete-record countable projection interface as the original
actuator source, now for the actual semantically synthesized literal AST. -/
def projectPath {n : ℕ} (i : Fin n) (rs : ℕ → ModeRecord n) : ℕ → ModeRecord 1 :=
  fun t => projectModeRecord i (rs t)

@[fun_prop] theorem measurable_projectPath {n : ℕ} (i : Fin n) : Measurable (projectPath i) := by
  apply measurable_pi_lambda
  intro t
  have h : Measurable (projectModeRecord i) := by intro s hs; trivial
  exact h.comp (measurable_pi_apply t)

theorem actual_countable_path_law {n : ℕ} (i : Fin n) (m : Mechanism)
    (p : Instruction n) (q : Instruction 1) (hs : synthesize i p=some q)
    (o : Organism n) (μ : Measure Stream) :
    (recordPathLaw i m p o μ).map (projectPath i)=
      recordPathLaw (0 : Fin 1) m q (projectOrganism i o) μ := by
  rw [recordPathLaw,Measure.map_map (measurable_projectPath i) (measurable_recordPath i m p o)]
  unfold recordPathLaw
  congr 1
  funext w t
  exact actual_record_projection i m p q hs o w t

theorem actual_event_probability {n : ℕ} (i : Fin n) (m : Mechanism)
    (p : Instruction n) (q : Instruction 1) (hs : synthesize i p=some q)
    (o : Organism n) (μ : Measure Stream) (S : Set (ℕ → ModeRecord 1)) (hS : MeasurableSet S) :
    recordPathLaw i m p o μ ((projectPath i) ⁻¹' S)=
      recordPathLaw (0 : Fin 1) m q (projectOrganism i o) μ S := by
  rw [← Measure.map_apply (measurable_projectPath i) hS,actual_countable_path_law i m p q hs]

/-- One actual consumer binds the submitted AST, SAME returned AST, original
P9 preservation property and its complete infinite operational law. -/
theorem actual_p9_countable_consumer {n : ℕ} (i : Fin n) (b : Bool) (m : Mechanism)
    (pq : Accepted i) (hp : ValidProgram i b pq.val.1) (o : Organism n) (μ : Measure Stream) :
    ValidProgram (0 : Fin 1) b pq.val.2 ∧
      (recordPathLaw i m pq.val.1 o μ).map (projectPath i)=
        recordPathLaw (0 : Fin 1) m pq.val.2 (projectOrganism i o) μ :=
  ⟨p9_actual_returned_program i b pq hp,actual_countable_path_law i m _ _ pq.property o μ⟩

/-- The protected inherited program belongs to the SAME retained parent at
all actual times; no reinstallation or changing seed is used. -/
theorem actual_protected_program {n : ℕ} (i : Fin n) (m : Mechanism) (p : Instruction n)
    (o : Organism n) (w : Stream) (t : ℕ) : (parentAt i m p o w t).program=o.program := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [parentAt_succ]
    change (modeRecordStep i m _ _ _ _).transaction.parentAfter.program=_
    rw [step_program]
    exact ih

/-- A genuinely continuing primitive stream. Its first three transactions
are the registered repair/fault/repair word; later stages are real executions. -/
def witnessStream : Stream
  | 0 => (true,true)
  | 1 => (false,false)
  | _ => (true,false)

@[simp] theorem witness_prefix : rawPrefix 3 witnessStream=actualWord := by decide

/-- Static rejection of the harmless hidden test remains unchanged, while
semantic synthesis supplies THIS coarse program's complete countable law/P9. -/
theorem benign_p9_countable (hidden : Bool) (μ : Measure Stream) [IsProbabilityMeasure μ] :
    ValidProgram (0 : Fin 1) true (compile 0 true) ∧
    IsProbabilityMeasure (recordPathLaw (0 : Fin 2) ⟨true,1⟩ benignHidden (passiveInitial hidden) μ) ∧
    (recordPathLaw (0 : Fin 2) ⟨true,1⟩ benignHidden (passiveInitial hidden) μ).map (projectPath 0)=
      recordPathLaw (0 : Fin 1) ⟨true,1⟩ (compile 0 true)
        (projectOrganism 0 (passiveInitial hidden)) μ := by
  let pq : Accepted (0 : Fin 2) := ⟨(benignHidden,compile 0 true),benign_static_rejects_semantic_accepts.2⟩
  have h:=actual_p9_countable_consumer 0 true ⟨true,1⟩ pq benign_actual_valid (passiveInitial hidden) μ
  exact ⟨h.1,inferInstance,h.2⟩

/-- Full failure/fee/birth prefix of the actual ongoing recursion, obtained
from the original finite source theorem, rather than hardcoded dynamics. -/
theorem benign_continuing_failed_paid :
    let rs := List.ofFn (fun j : Fin 3 => recordAt (0 : Fin 2) ⟨true,1⟩ benignHidden
      (passiveInitial true) witnessStream j)
    rs.map (fun r => r.transaction.expenditure)=[1,0,1] ∧
      rs.map (fun r => r.transaction.child.isSome)=[true,false,true] := by
  change (List.ofFn _).map _ = _ ∧ (List.ofFn _).map _ = _
  rw [actual_finite_prefix,witness_prefix]
  exact benign_actual_failed_paid

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterSemanticInstructionInfinite
