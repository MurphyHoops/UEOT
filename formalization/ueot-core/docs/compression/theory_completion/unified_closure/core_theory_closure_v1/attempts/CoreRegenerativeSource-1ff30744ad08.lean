import Mathlib
import UEOT.V3.Compression.Objecthood.EndogenousRepairRank

/-!
# A finite, paid, damageable regenerative source

`Body` contains executable data, not a program label, fitness, expected offspring,
or a success certificate.  The two physical rows are repetition codes.  The
trusted bootstrap reads their majority and performs charged writes; it has no
argument specifying the intended program.  The main gate and active code cells
are causally necessary for unmediated execution.

This is a census source.  Each old organism brings one unit and receives five
explicit units from the environment.  Continuation reserves two possible output
endowments before reading its local noise.  A rejected request preserves the old
organism and refunds the five environmental units.  Stop has zero outputs.  The
population wrapper gives retained and newborn records their distinct identities
and runs newborns only at the next census.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeSource

open scoped BigOperators

abbrev Kind := Bool

inductive Action where
  | care | bloom | stop
  deriving DecidableEq, Repr

instance : Fintype Action := ⟨{.care, .bloom, .stop}, by
  intro a
  cases a <;> simp⟩

structure Triple where
  active : Bool
  backup1 : Bool
  backup2 : Bool
  deriving DecidableEq, Fintype, Repr

def majority (x : Triple) : Bool :=
  (x.active && x.backup1) || (x.active && x.backup2) || (x.backup1 && x.backup2)

def repeatBit (a : Bool) : Triple := ⟨a, a, a⟩

def flipActive (x : Triple) : Triple := { x with active := !x.active }

def tripleCost (x : Triple) : ℕ :=
  (if x.active = majority x then 0 else 1) +
  (if x.backup1 = majority x then 0 else 1) +
  (if x.backup2 = majority x then 0 else 1)

@[simp] theorem majority_repeat (a : Bool) : majority (repeatBit a) = a := by
  cases a <;> rfl

@[simp] theorem majority_flip_repeat (a : Bool) :
    majority (flipActive (repeatBit a)) = a := by
  cases a <;> rfl

@[simp] theorem tripleCost_repeat (a : Bool) : tripleCost (repeatBit a) = 0 := by
  cases a <;> decide

@[simp] theorem tripleCost_flip_repeat (a : Bool) :
    tripleCost (flipActive (repeatBit a)) = 1 := by
  cases a <;> decide

structure Body where
  rowH : Triple
  rowD : Triple
  gate : Bool
  bootstrap : Bool
  tag : Bool
  deriving DecidableEq, Fintype, Repr

def decode (x : Body) : Bool × Bool := (majority x.rowH, majority x.rowD)

def encode (h d tag : Bool) : Body :=
  ⟨repeatBit h, repeatBit d, true, true, tag⟩

def damageBody (x : Body) (damaged : Bool) : Body :=
  if damaged then
    { x with
      rowH := flipActive x.rowH
      rowD := flipActive x.rowD
      gate := false }
  else x

/-- The declared diagnostic sensor reads physical cells and the main gate. -/
def diagnostic (x : Body) : Kind :=
  !x.gate || !(x.rowH.active == x.rowH.backup1) ||
  !(x.rowH.backup1 == x.rowH.backup2) ||
  !(x.rowD.active == x.rowD.backup1) || !(x.rowD.backup1 == x.rowD.backup2)

/-- A code-independent write primitive.  Availability and payment are checked by `step`. -/
def restore (x : Body) : Body :=
  { x with
    rowH := repeatBit (majority x.rowH)
    rowD := repeatBit (majority x.rowD)
    gate := true }

def repairCost (x : Body) : ℕ :=
  tripleCost x.rowH + tripleCost x.rowD + if x.gate then 0 else 1

def selectedTriple (x : Body) (i : Kind) : Triple := if i then x.rowD else x.rowH

def bitAction (b : Bool) : Action := if b then .bloom else .care

/-- This function actually reads an active code cell and the execution gate. -/
def rawExecute (x : Body) (originalDiagnostic : Kind) : Option Action :=
  if x.gate then some (bitAction (selectedTriple x originalDiagnostic).active) else none

/-- Internal program request, based only on its allowed physical diagnostic. -/
def requestOf (x : Body) : Action :=
  bitAction (majority (selectedTriple x (diagnostic x)))

def programBody (theta i tag : Bool) : Body := damageBody (encode theta false tag) i

def programAction (theta i : Bool) : Action :=
  if i then .care else if theta then .bloom else .care

@[simp] theorem decode_programBody (theta i tag : Bool) :
    decode (programBody theta i tag) = (theta, false) := by
  cases theta <;> cases i <;> rfl

@[simp] theorem diagnostic_programBody (theta i tag : Bool) :
    diagnostic (programBody theta i tag) = i := by
  cases theta <;> cases i <;> rfl

@[simp] theorem restore_programBody (theta i tag : Bool) :
    restore (programBody theta i tag) = encode theta false tag := by
  cases theta <;> cases i <;> rfl

@[simp] theorem repairCost_programBody (theta i tag : Bool) :
    repairCost (programBody theta i tag) = if i then 3 else 0 := by
  cases theta <;> cases i <;> cases tag <;> decide

@[simp] theorem requestOf_programBody (theta i tag : Bool) :
    requestOf (programBody theta i tag) = programAction theta i := by
  cases theta <;> cases i <;> rfl

/-- The request is realized by the same restored raw program, at its original diagnostic. -/
theorem actual_program_reads_restored_code (theta i tag : Bool) :
    rawExecute (restore (programBody theta i tag))
      (diagnostic (programBody theta i tag)) = some (programAction theta i) := by
  cases theta <;> cases i <;> rfl

theorem main_gate_is_causal (h d tag i : Bool) :
    rawExecute { encode h d tag with gate := false } i = none := rfl

theorem active_code_is_causal (tag : Bool) :
    rawExecute (encode true false tag) false = some .bloom ∧
    rawExecute { encode true false tag with rowH := flipActive (repeatBit true) }
      false = some .care := by constructor <;> rfl

theorem copied_code_faithful (theta i tag newDamage : Bool) :
    damageBody (restore (programBody theta i tag)) newDamage =
      programBody theta newDamage tag := by
  rw [restore_programBody]
  rfl

theorem copied_decode_faithful (theta i tag newDamage : Bool) :
    decode (damageBody (restore (programBody theta i tag)) newDamage) =
      (theta, false) := by
  rw [copied_code_faithful, decode_programBody]

/-- Total erasure collapses different source programs to the same physical state. -/
def eraseCode (x : Body) : Body :=
  { x with rowH := repeatBit false, rowD := repeatBit false, gate := false }

theorem erased_programs_indistinguishable (tag : Bool) :
    eraseCode (programBody false false tag) =
      eraseCode (programBody true false tag) := rfl

theorem erased_bloom_cannot_be_restored (tag : Bool) :
    decode (restore (eraseCode (programBody true false tag))) ≠ (true, false) := by
  cases tag <;> decide

/-- No deterministic physical decoder can recover both erased original programs. -/
theorem no_decoder_recovers_both_erased (f : Body → Bool) (tag : Bool) :
    ¬ (f (eraseCode (programBody false false tag)) = false ∧
       f (eraseCode (programBody true false tag)) = true) := by
  rintro ⟨h0, h1⟩
  rw [← erased_programs_indistinguishable] at h1
  exact Bool.false_ne_true (h0.symm.trans h1)

def operationCost : Action → ℕ
  | .care => 1 | .bloom => 2 | .stop => 0

def requestCap (x : Body) (a : Action) : ℕ :=
  if a = .stop then 0 else repairCost x + operationCost a + 2

def canExecute (x : Body) (a : Action) : Bool :=
  (x.bootstrap || decide (repairCost x = 0)) && decide (requestCap x a ≤ 6)

@[simp] theorem requestCap_program_care (theta i tag : Bool) :
    requestCap (programBody theta i tag) .care = if i then 6 else 3 := by
  cases i <;> simp [requestCap, operationCost]

@[simp] theorem requestCap_program_bloom (theta i tag : Bool) :
    requestCap (programBody theta i tag) .bloom = if i then 7 else 4 := by
  cases i <;> simp [requestCap, operationCost]

theorem program_request_affordable (theta i tag : Bool) :
    canExecute (programBody theta i tag) (programAction theta i) = true := by
  cases theta <;> cases i <;> cases tag <;> decide

theorem damaged_bloom_rejected (theta tag : Bool) :
    canExecute (programBody theta true tag) .bloom = false := by
  cases theta <;> cases tag <;> decide

theorem bootstrap_cut_blocks_recovery (theta tag : Bool) :
    canExecute { programBody theta true tag with bootstrap := false } .care = false := by
  cases theta <;> cases tag <;> decide

/-- Primitive noise: common survival/birth categories plus independent output damage. -/
abbrev Noise := (Fin 3 × Fin 3) × (Bool × Bool)

def retains (a : Action) (z : Noise) : Bool :=
  match a with
  | .care => decide (z.1.1 = 1 ∨ z.1.1 = 2)
  | .bloom => decide (z.1.1 = 2)
  | .stop => false

def births (a : Action) (z : Noise) : Bool :=
  match a with
  | .care => decide (z.1.2 = 2)
  | .bloom => decide (z.1.2 = 1 ∨ z.1.2 = 2)
  | .stop => false

def eventCount (a : Action) (z : Noise) (j : Kind) : ℕ :=
  (if retains a z && decide (z.2.1 = j) then 1 else 0) +
  (if births a z && decide (z.2.2 = j) then 1 else 0)

def retainedCount (a : Action) (z : Noise) (j : Kind) : ℕ :=
  if retains a z && decide (z.2.1 = j) then 1 else 0

def newbornCount (a : Action) (z : Noise) (j : Kind) : ℕ :=
  if births a z && decide (z.2.2 = j) then 1 else 0

inductive Status where
  | executed | rejected | stopped
  deriving DecidableEq, Repr

structure LocalResult where
  retained : Option Body
  newborn : Option Body
  repairPaid : ℕ
  operationPaid : ℕ
  refund : ℕ
  status : Status
  deriving DecidableEq, Repr

def optionCount (x : Option Body) : ℕ := if x.isSome then 1 else 0

def outputCapital (r : LocalResult) : ℕ := optionCount r.retained + optionCount r.newborn

def executedResult (x : Body) (a : Action) (z : Noise) : LocalResult :=
  let r := if retains a z then some (damageBody (restore x) z.2.1) else none
  let b := if births a z then some (damageBody (restore x) z.2.2) else none
  ⟨r, b, repairCost x, operationCost a,
    6 - (repairCost x + operationCost a + optionCount r + optionCount b), .executed⟩

/-- A real request port.  Only accepted non-stop requests inspect the noise atom. -/
def step (x : Body) (a : Action) (z : Noise) : LocalResult :=
  if a = .stop then ⟨none, none, 0, 0, 6, .stopped⟩
  else if canExecute x a then executedResult x a z
  else ⟨some x, none, 0, 0, 5, .rejected⟩

def programStep (x : Body) (z : Noise) : LocalResult := step x (requestOf x) z

theorem optionCount_le_one (x : Option Body) : optionCount x ≤ 1 := by
  cases x <;> simp [optionCount]

theorem outputCapital_le_two (r : LocalResult) : outputCapital r ≤ 2 := by
  have h1 := optionCount_le_one r.retained
  have h2 := optionCount_le_one r.newborn
  simp only [outputCapital]
  omega

theorem step_budget (x : Body) (a : Action) (z : Noise) :
    (step x a z).repairPaid + (step x a z).operationPaid +
      outputCapital (step x a z) + (step x a z).refund = 1 + 5 := by
  by_cases hs : a = .stop
  · simp [step, hs, outputCapital, optionCount]
  · by_cases he : canExecute x a = true
    · have hcap : repairCost x + operationCost a + 2 ≤ 6 := by
        have hc : requestCap x a ≤ 6 := by
          by_contra h
          simp [canExecute, h] at he
        simpa [requestCap, hs] using hc
      have hr := optionCount_le_one
        (if retains a z then some (damageBody (restore x) z.2.1) else none)
      have hb := optionCount_le_one
        (if births a z then some (damageBody (restore x) z.2.2) else none)
      simp only [step, hs, ↓reduceIte, he, executedResult, outputCapital]
      omega
    · have hf : canExecute x a = false := Bool.eq_false_iff.mpr he
      simp [step, hs, hf, outputCapital, optionCount]

theorem stop_is_zero (x : Body) (z : Noise) :
    step x .stop z = ⟨none, none, 0, 0, 6, .stopped⟩ := by simp [step]

theorem rejection_retains_without_free_newborn (x : Body) (a : Action) (z : Noise)
    (hs : a ≠ .stop) (he : canExecute x a = false) :
    step x a z = ⟨some x, none, 0, 0, 5, .rejected⟩ := by simp [step, hs, he]

theorem program_step_executes (theta i tag : Bool) (z : Noise) :
    programStep (programBody theta i tag) z =
      executedResult (programBody theta i tag) (programAction theta i) z := by
  have hs : programAction theta i ≠ .stop := by
    cases theta <;> cases i <;> decide
  simp [programStep, step, program_request_affordable, hs]

theorem executed_retained_faithful (theta i tag : Bool) (a : Action) (z : Noise)
    (hr : retains a z = true) :
    (executedResult (programBody theta i tag) a z).retained =
      some (programBody theta z.2.1 tag) := by
  simp only [executedResult, hr, ↓reduceIte, restore_programBody]
  rfl

theorem executed_newborn_faithful (theta i tag : Bool) (a : Action) (z : Noise)
    (hb : births a z = true) :
    (executedResult (programBody theta i tag) a z).newborn =
      some (programBody theta z.2.2 tag) := by
  simp only [executedResult, hb, ↓reduceIte, restore_programBody]
  rfl

structure Parameters where
  survival : ℝ
  careOnly : ℝ
  commonBirth : ℝ
  bloomOnly : ℝ
  damage : ℝ

/-- An open, nonzero-noise, supercritical class; these are primitive probability parameters. -/
structure Valid (p : Parameters) : Prop where
  careOnly_pos : 0 < p.careOnly
  careOnly_lt_survival : p.careOnly < p.survival
  survival_lt_one : p.survival < 1
  commonBirth_pos : 0 < p.commonBirth
  birth_sum_lt_one : p.commonBirth + p.bloomOnly < 1
  advantage : p.careOnly < p.bloomOnly
  damage_pos : 0 < p.damage
  damage_lt_one : p.damage < 1
  supercritical : 1 < p.survival + p.commonBirth

def survivalWeight (p : Parameters) (u : Fin 3) : ℝ :=
  if u = 0 then 1 - p.survival else if u = 1 then p.careOnly
  else p.survival - p.careOnly

def birthWeight (p : Parameters) (v : Fin 3) : ℝ :=
  if v = 0 then 1 - p.commonBirth - p.bloomOnly else if v = 1 then p.bloomOnly
  else p.commonBirth

def damageWeight (p : Parameters) (j : Bool) : ℝ := if j then p.damage else 1 - p.damage

def noiseWeight (p : Parameters) (z : Noise) : ℝ :=
  survivalWeight p z.1.1 * birthWeight p z.1.2 *
    damageWeight p z.2.1 * damageWeight p z.2.2

def survivalRate (p : Parameters) : Action → ℝ
  | .care => p.survival | .bloom => p.survival - p.careOnly | .stop => 0

def birthRate (p : Parameters) : Action → ℝ
  | .care => p.commonBirth | .bloom => p.commonBirth + p.bloomOnly | .stop => 0

def countRate (p : Parameters) (a : Action) : ℝ := survivalRate p a + birthRate p a

def row (p : Parameters) (a : Action) (j : Kind) : ℝ := countRate p a * damageWeight p j

def eventMean (p : Parameters) (a : Action) (j : Kind) : ℝ :=
  ∑ z : Noise, noiseWeight p z * (eventCount a z j : ℝ)

def retainedMean (p : Parameters) (a : Action) (j : Kind) : ℝ :=
  ∑ z : Noise, noiseWeight p z * (retainedCount a z j : ℝ)

def newbornMean (p : Parameters) (a : Action) (j : Kind) : ℝ :=
  ∑ z : Noise, noiseWeight p z * (newbornCount a z j : ℝ)

theorem noiseWeight_sum (p : Parameters) : ∑ z : Noise, noiseWeight p z = 1 := by
  simp [Noise, noiseWeight, survivalWeight, birthWeight, damageWeight,
    Fintype.sum_prod_type, Fin.sum_univ_succ]
  ring

theorem noiseWeight_pos (p : Parameters) (hp : Valid p) (z : Noise) :
    0 < noiseWeight p z := by
  have hs : 0 < survivalWeight p z.1.1 := by
    unfold survivalWeight
    split_ifs <;> linarith [hp.survival_lt_one, hp.careOnly_pos, hp.careOnly_lt_survival]
  have hb : 0 < birthWeight p z.1.2 := by
    unfold birthWeight
    split_ifs <;> linarith [hp.birth_sum_lt_one, hp.advantage, hp.careOnly_pos,
      hp.commonBirth_pos]
  have hd : ∀ j, 0 < damageWeight p j := by
    intro j
    cases j <;> simp [damageWeight] <;> linarith [hp.damage_pos, hp.damage_lt_one]
  exact mul_pos (mul_pos (mul_pos hs hb) (hd _)) (hd _)

/-- These means are calculated from the 36 primitive atoms and actual retained events. -/
theorem retainedMean_eq (p : Parameters) (a : Action) (j : Kind) :
    retainedMean p a j = survivalRate p a * damageWeight p j := by
  cases a <;> cases j <;>
    simp [retainedMean, retainedCount, Noise, noiseWeight, survivalWeight, birthWeight,
      damageWeight, survivalRate, retains, Fintype.sum_prod_type, Fin.sum_univ_succ] <;> ring

/-- These means are calculated from actual newborn events, separate from retention. -/
theorem newbornMean_eq (p : Parameters) (a : Action) (j : Kind) :
    newbornMean p a j = birthRate p a * damageWeight p j := by
  cases a <;> cases j <;>
    simp [newbornMean, newbornCount, Noise, noiseWeight, survivalWeight, birthWeight,
      damageWeight, birthRate, births, Fintype.sum_prod_type, Fin.sum_univ_succ] <;> ring

theorem eventMean_eq_row (p : Parameters) (a : Action) (j : Kind) :
    eventMean p a j = row p a j := by
  have he : eventMean p a j = retainedMean p a j + newbornMean p a j := by
    simp [eventMean, eventCount, retainedMean, newbornMean, retainedCount, newbornCount,
      Nat.cast_add, mul_add, Finset.sum_add_distrib]
  rw [he, retainedMean_eq, newbornMean_eq]
  simp [row, countRate, add_mul]

def programRow (p : Parameters) (theta i j : Bool) : ℝ := row p (programAction theta i) j

/-- Repeated unaffordable requests are represented by the actual identity row. -/
def realizedRow (p : Parameters) (i : Kind) (a : Action) (j : Kind) : ℝ :=
  if i && decide (a = .bloom) then (if i = j then 1 else 0) else row p a j

@[simp] theorem realizedRow_reject (p : Parameters) (j : Kind) :
    realizedRow p true .bloom j = if true = j then 1 else 0 := by
  simp [realizedRow]

@[simp] theorem realizedRow_program (p : Parameters) (theta i j : Bool) :
    realizedRow p i (programAction theta i) j = programRow p theta i j := by
  cases theta <;> cases i <;> rfl

/-- Count actual local records by their physically observable body diagnostic. -/
def bodyCount (x : Option Body) (j : Kind) : ℕ :=
  match x with
  | none => 0
  | some b => if diagnostic b = j then 1 else 0

def resultCount (r : LocalResult) (j : Kind) : ℕ :=
  bodyCount r.retained j + bodyCount r.newborn j

@[simp] theorem canExecute_program_care (theta i tag : Bool) :
    canExecute (programBody theta i tag) .care = true := by
  cases theta <;> cases i <;> cases tag <;> decide

@[simp] theorem canExecute_program_bloom (theta i tag : Bool) :
    canExecute (programBody theta i tag) .bloom = !i := by
  cases theta <;> cases i <;> cases tag <;> decide

/-- The event counters are exactly the counters of the physical output records. -/
theorem executedResult_count (theta i tag : Bool) (a : Action) (z : Noise) (j : Kind) :
    resultCount (executedResult (programBody theta i tag) a z) j = eventCount a z j := by
  simp only [resultCount, executedResult, restore_programBody]
  change bodyCount (if retains a z then some (programBody theta z.2.1 tag) else none) j +
    bodyCount (if births a z then some (programBody theta z.2.2 tag) else none) j = _
  cases hr : retains a z <;> cases hb : births a z <;>
    simp [bodyCount, eventCount, hr, hb]

def realizedCount (i : Kind) (a : Action) (z : Noise) (j : Kind) : ℕ :=
  if i && decide (a = .bloom) then (if i = j then 1 else 0) else eventCount a z j

theorem step_resultCount (theta i tag : Bool) (a : Action) (z : Noise) (j : Kind) :
    resultCount (step (programBody theta i tag) a z) j = realizedCount i a z j := by
  cases a with
  | care =>
      simp [step, realizedCount, canExecute_program_care, executedResult_count]
  | bloom =>
      cases i
      · simp [step, realizedCount, canExecute_program_bloom, executedResult_count]
      · simp [step, realizedCount, canExecute_program_bloom, resultCount, bodyCount]
  | stop =>
      simp [step, realizedCount, resultCount, bodyCount, eventCount, retains, births]

def realizedMean (p : Parameters) (theta i tag : Bool) (a : Action) (j : Kind) : ℝ :=
  ∑ z : Noise, noiseWeight p z * (resultCount (step (programBody theta i tag) a z) j : ℝ)

/-- Full source bridge, including zero stop and identity rejection; no mean premise. -/
theorem realizedMean_eq (p : Parameters) (theta i tag : Bool) (a : Action) (j : Kind) :
    realizedMean p theta i tag a j = realizedRow p i a j := by
  simp only [realizedMean, step_resultCount]
  by_cases hr : (i && decide (a = .bloom)) = true
  · by_cases hj : i = j
    · simp [realizedCount, realizedRow, hr, hj, noiseWeight_sum]
    · simp [realizedCount, realizedRow, hr, hj]
  · have hf : (i && decide (a = .bloom)) = false := Bool.eq_false_iff.mpr hr
    simpa [realizedCount, realizedRow, hf, eventMean] using eventMean_eq_row p a j

theorem program_realizedMean (p : Parameters) (theta i tag j : Bool) :
    realizedMean p theta i tag (programAction theta i) j = programRow p theta i j := by
  rw [realizedMean_eq, realizedRow_program]

def growthRate (p : Parameters) (theta : Bool) : ℝ :=
  (1 - p.damage) * countRate p (programAction theta false) +
    p.damage * countRate p (programAction theta true)

noncomputable def concreteParameters : Parameters := ⟨3/4, 1/8, 3/8, 1/4, 1/3⟩

theorem concreteParameters_valid : Valid concreteParameters := by
  constructor <;> norm_num [concreteParameters]

theorem concrete_growth_rates :
    growthRate concreteParameters false = 9/8 ∧
    growthRate concreteParameters true = 29/24 := by
  norm_num [growthRate, programAction, countRate, survivalRate, birthRate, concreteParameters]

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeSource
