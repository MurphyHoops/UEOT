import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeSource

/-!
# A lawful physical quotient of the actual regenerative transaction

Only the silent physical tag is erased.  Code cells, gate, bootstrap, requests,
payments, refunds and the two marked output slots are retained.  The central
equality is pointwise in the same raw noise atom, so it preserves the complete
joint record law, not merely its first moment.  Permanent identities belong to
the population wrapper and are never quotient coordinates.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeQuotient

open CoreRegenerativeSource
open scoped BigOperators

abbrev Observation := Triple × Triple × Bool × Bool

def observe (x : Body) : Observation := (x.rowH, x.rowD, x.gate, x.bootstrap)

def eraseTag (x : Body) : Body := { x with tag := false }

@[simp] theorem observe_eraseTag (x : Body) : observe (eraseTag x) = observe x := rfl
@[simp] theorem eraseTag_idempotent (x : Body) : eraseTag (eraseTag x) = eraseTag x := rfl
@[simp] theorem diagnostic_eraseTag (x : Body) : diagnostic (eraseTag x) = diagnostic x := rfl
@[simp] theorem repairCost_eraseTag (x : Body) : repairCost (eraseTag x) = repairCost x := rfl
@[simp] theorem requestOf_eraseTag (x : Body) : requestOf (eraseTag x) = requestOf x := rfl
@[simp] theorem canExecute_eraseTag (x : Body) (a : Action) :
    canExecute (eraseTag x) a = canExecute x a := rfl
@[simp] theorem restore_eraseTag (x : Body) :
    restore (eraseTag x) = eraseTag (restore x) := rfl

@[simp] theorem damageBody_eraseTag (x : Body) (d : Bool) :
    damageBody (eraseTag x) d = eraseTag (damageBody x d) := by cases d <;> rfl

def eraseResult (r : LocalResult) : LocalResult :=
  { r with retained := r.retained.map eraseTag, newborn := r.newborn.map eraseTag }

theorem optionCount_map_eraseTag (o : Option Body) :
    optionCount (o.map eraseTag) = optionCount o := by cases o <;> rfl

theorem executedResult_eraseTag (x : Body) (a : Action) (z : Noise) :
    executedResult (eraseTag x) a z = eraseResult (executedResult x a z) := by
  cases hr : retains a z <;> cases hb : births a z <;>
    simp [executedResult, eraseResult, hr, hb, optionCount]

/-- Stronger than a matrix equality: the same atom gives the same full projected receipt. -/
theorem step_joint_record_commutes (x : Body) (a : Action) (z : Noise) :
    step (eraseTag x) a z = eraseResult (step x a z) := by
  by_cases hs : a = .stop
  · subst a
    simp [step, eraseResult]
  · cases he : canExecute x a <;>
      simp [step, hs, he, eraseResult, executedResult_eraseTag]

theorem programStep_joint_record_commutes (x : Body) (z : Noise) :
    programStep (eraseTag x) z = eraseResult (programStep x z) := by
  rw [programStep_eq_step, programStep_eq_step, requestOf_eraseTag]
  exact step_joint_record_commutes x (requestOf x) z

def ReducedBody := {x : Body // x.tag = false}

def quotient (x : Body) : ReducedBody := ⟨eraseTag x, rfl⟩

theorem quotient_surjective : Function.Surjective quotient := by
  intro x
  refine ⟨x.val, ?_⟩
  apply Subtype.ext
  cases x with
  | mk x hx =>
    cases x
    simp only [quotient, eraseTag, Body.mk.injEq, true_and]
    exact hx.symm

theorem quotient_is_noninjective : ¬ Function.Injective quotient := by
  intro hinj
  have h : quotient (encode false false false) = quotient (encode false false true) := rfl
  have he := hinj h
  have ht := congrArg Body.tag he
  exact Bool.false_ne_true ht

theorem observed_request_descends (policy : Observation → Action) (x : Body) :
    policy (observe (quotient x).val) = policy (observe x) := rfl

theorem observed_history_descends (policy : List Observation → Action) (xs : List Body) :
    policy ((xs.map eraseTag).map observe) = policy (xs.map observe) := by
  simp only [List.map_map]
  rfl

/-- Both representations have exactly the same observation history, so the
same action kernel is its own lift in both directions.  Private random arguments
can be included in `M`; they are not inferred from the erased tag. -/
theorem history_kernel_two_way {M : Type*}
    (kernel : M → List Observation → Action → ℝ) (seed : M) (xs : List Body) :
    kernel seed ((xs.map eraseTag).map observe) = kernel seed (xs.map observe) := by
  simp only [List.map_map]
  rfl

/-- All real-weight test functions of the projected complete receipt are preserved. -/
theorem joint_law_test (p : Parameters) (x : Body) (a : Action)
    (F : LocalResult → ℝ) :
    (∑ z : Noise, noiseWeight p z * F (step (eraseTag x) a z)) =
    ∑ z : Noise, noiseWeight p z * F (eraseResult (step x a z)) := by
  simp_rw [step_joint_record_commutes]

/-- The two physical tags are a genuine duplicated type coordinate.  Tag is
faithfully carried, not independently resampled for a convenient matrix. -/
abbrev RawKind := Kind × Bool

def expanded (M : Matrix Kind Kind ℝ) : Matrix RawKind RawKind ℝ :=
  fun i j => if i.2 = j.2 then M i.1 j.1 else 0

def incidence : Matrix RawKind Kind ℝ := fun i j => if i.1 = j then 1 else 0

theorem expanded_intertwining (M : Matrix Kind Kind ℝ) :
    expanded M * incidence = incidence * M := by
  ext i j
  rcases i with ⟨i, tag⟩
  cases i <;> cases tag <;> cases j <;>
    simp [Matrix.mul_apply, expanded, incidence, Fintype.sum_prod_type]

/-- Retention and birth intertwine separately, so marked genealogy is not lost. -/
theorem source_L_B_M_intertwining (p : Parameters) (theta : Bool) :
    expanded (fun i j => retainedMean p (programAction theta i) j) * incidence =
      incidence * (show Matrix Kind Kind ℝ from fun i j => retainedMean p (programAction theta i) j) ∧
    expanded (fun i j => newbornMean p (programAction theta i) j) * incidence =
      incidence * (show Matrix Kind Kind ℝ from fun i j => newbornMean p (programAction theta i) j) ∧
    expanded (programRow p theta) * incidence =
      incidence * (show Matrix Kind Kind ℝ from programRow p theta) := by
  exact ⟨expanded_intertwining _, expanded_intertwining _, expanded_intertwining _⟩

/-- Erasing the damage diagnostic instead would erase a real affordability distinction. -/
theorem dropping_diagnostic_is_not_lawful (theta tag : Bool) :
    canExecute (programBody theta false tag) .bloom = true ∧
    canExecute (programBody theta true tag) .bloom = false := by
  cases theta <;> cases tag <;> decide

/-- An unchanged code prediction does not preserve the physical execution port. -/
theorem code_only_prediction_loses_execution (tag : Bool) :
    decode (encode true false tag) = decode { encode true false tag with gate := false } ∧
    rawExecute (encode true false tag) false = some .bloom ∧
    rawExecute { encode true false tag with gate := false } false = none := by
  exact ⟨rfl, rfl, rfl⟩

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeQuotient
