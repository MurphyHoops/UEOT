import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RationalConditionedSource
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteConditionalStability

/-!
# Computed certificates rechecked by the Lean kernel

Generated from frozen finite input tables by emit_lean_witness.py.
Targets are recomputed from their original source. Candidate weights
and separators acquire a conclusion only after kernel `decide` and
the same-source full-path consumer have been checked.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionCertificateWitnessCheck

open MeasureTheory UEOT.V3.PathError UEOT.V3.FiniteDiscountedControl
open UEOT.V3.CoreOperationalAssembly FiniteActionCertificateCheck
open RationalConditionedSourceCheck ConditionedActionTransportCheck
open FiniteActionRealizabilityCheck SameSourceFiniteWindowCheck
open scoped BigOperators

set_option maxRecDepth 16384

local instance : MeasurableSpace (Fin 1) := ⊤
local instance : MeasurableSpace (Fin 2) := ⊤
local instance : MeasurableSpace (Fin 3) := ⊤

namespace case_0

private def P : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![(3 / 8), (3 / 8), (1 / 4)]], ![![(1 / 8), (1 / 8), (3 / 4)]], ![![0, 0, 1]]]
private def base : Fin 1 → Fin 1 → ℚ := ![![1]]
private def q : Fin 3 → Fin 1 := ![0, 0, 0]
private def p0 : Fin 3 → ℚ := ![(1 / 2), (1 / 2), 0]
private def deployed : Fin 3 → ℚ := ![(3 / 4), (1 / 4), 0]
private def safe : Fin 3 → Bool := ![true, true, false]
private def T : ℕ := 1
private def B := baselineRow P q base
private def mu := sourceInitial B p0 safe T
private def R := sourceTarget B safe T

private theorem source_rows : ∀ x a, ValidRow (P x a) := by decide +kernel
private theorem baseline_rows : ∀ y, ValidRow (base y) := by decide +kernel
private theorem initial_row : ValidRow p0 := by decide +kernel
private theorem deployed_row : ValidRow deployed := by decide +kernel

private theorem source_positive : 0 < sourceMass B p0 safe T := by decide +kernel
private theorem target_initial_valid : ValidRow mu :=
  sourceInitial_valid B (baselineRow_nonneg P source_rows q base baseline_rows)
    p0 initial_row.1 safe T source_positive
private theorem target_rows_valid : ∀ t x, ValidRow (R t x) :=
  sourceTarget_valid B (baselineRow_nonneg P source_rows q base baseline_rows) safe T

private theorem target_is_actual :
    targetPath (rowPMF mu target_initial_valid)
        (fun t x => rowPMF (R t x) (target_rows_valid t x)) T =
      actualConditionedPrefix (rationalModel P source_rows) q
        (fun y => rowPMF (base y) (baseline_rows y)) (rowPMF p0 initial_row)
        {x | safe x = true} T 0
        (actualSource_pos P source_rows q base baseline_rows p0 initial_row safe T source_positive) :=
  sourceTargetPath_eq_actual P source_rows q base baseline_rows p0 initial_row safe T source_positive

private def separator : Separation (Fin 3) (Fin 1) where
  time := 0
  observation := 0
  coefficient := ![![0, 0, 0], ![0, 0, -1], ![0, 0, 0]]
  bound := (-3 / 4)
  gap := (3 / 4)
private theorem rejected : checkNegative mu P R q T separator = true := by decide +kernel

private theorem full_path_no_go (p : PMF (Fin 3)) :
    ¬ ∃ sigma : ℕ → Fin 1 → PMF (Fin 1),
      (causalLaw p (riskMicroControlKernel q
        (fun _ => (rationalModel P source_rows).transitionPMF)
        (timeObservationPolicy sigma)) T).map
        (SourcePolicyPathBridgeCheck.eraseActionHistory T) =
      targetPath (rowPMF mu target_initial_valid)
        (fun t x => rowPMF (R t x) (target_rows_valid t x)) T :=
  checkNegative_path_no_go mu P R q T separator target_initial_valid source_rows
    target_rows_valid (rationalModel P source_rows)
    (rationalModel_transitionPMF P source_rows) rejected p

/-- The checked separator rules out the original conditional full state path. -/
theorem conditional_path_no_go (p : PMF (Fin 3)) :
    ¬ ∃ sigma : ℕ → Fin 1 → PMF (Fin 1),
      (causalLaw p (riskMicroControlKernel q
        (fun _ => (rationalModel P source_rows).transitionPMF)
        (timeObservationPolicy sigma)) T).map
        (SourcePolicyPathBridgeCheck.eraseActionHistory T) =
      actualConditionedPrefix (rationalModel P source_rows) q
        (fun y => rowPMF (base y) (baseline_rows y)) (rowPMF p0 initial_row)
        {x | safe x = true} T 0
        (actualSource_pos P source_rows q base baseline_rows p0 initial_row safe T source_positive) := by
  rintro ⟨sigma, hpath⟩
  exact full_path_no_go p ⟨sigma, hpath.trans target_is_actual.symm⟩

end case_0


namespace case_1

private def P : Fin 3 → Fin 3 → Fin 3 → ℚ := ![![![(3 / 8), (3 / 8), (1 / 4)], ![1, 0, 0], ![0, 1, 0]], ![![(1 / 8), (1 / 8), (3 / 4)], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, 1], ![1, 0, 0], ![0, 1, 0]]]
private def base : Fin 1 → Fin 3 → ℚ := ![![1, 0, 0]]
private def q : Fin 3 → Fin 1 := ![0, 0, 0]
private def p0 : Fin 3 → ℚ := ![(1 / 2), (1 / 2), 0]
private def deployed : Fin 3 → ℚ := ![(3 / 4), (1 / 4), 0]
private def safe : Fin 3 → Bool := ![true, true, false]
private def T : ℕ := 2
private def B := baselineRow P q base
private def mu := sourceInitial B p0 safe T
private def R := sourceTarget B safe T

private theorem source_rows : ∀ x a, ValidRow (P x a) := by decide +kernel
private theorem baseline_rows : ∀ y, ValidRow (base y) := by decide +kernel
private theorem initial_row : ValidRow p0 := by decide +kernel
private theorem deployed_row : ValidRow deployed := by decide +kernel

private theorem source_positive : 0 < sourceMass B p0 safe T := by decide +kernel
private theorem target_initial_valid : ValidRow mu :=
  sourceInitial_valid B (baselineRow_nonneg P source_rows q base baseline_rows)
    p0 initial_row.1 safe T source_positive
private theorem target_rows_valid : ∀ t x, ValidRow (R t x) :=
  sourceTarget_valid B (baselineRow_nonneg P source_rows q base baseline_rows) safe T

private theorem target_is_actual :
    targetPath (rowPMF mu target_initial_valid)
        (fun t x => rowPMF (R t x) (target_rows_valid t x)) T =
      actualConditionedPrefix (rationalModel P source_rows) q
        (fun y => rowPMF (base y) (baseline_rows y)) (rowPMF p0 initial_row)
        {x | safe x = true} T 0
        (actualSource_pos P source_rows q base baseline_rows p0 initial_row safe T source_positive) :=
  sourceTargetPath_eq_actual P source_rows q base baseline_rows p0 initial_row safe T source_positive

private def weights : Fin T → Fin 1 → Fin 3 → ℚ := ![![![0, (3 / 4), (1 / 4)]], ![![0, (1 / 2), (1 / 2)]]]
private theorem accepted : checkPositive deployed mu P R q T weights = true := by decide +kernel

private theorem output_path :
    (causalLaw (rowPMF deployed deployed_row)
      (riskMicroControlKernel q (fun _ => (rationalModel P source_rows).transitionPMF)
        (timeObservationPolicy (policy weights
          (acceptedWeights deployed mu P R q T weights accepted) 0))) T).map
        (SourcePolicyPathBridgeCheck.eraseActionHistory T) =
      targetPath (rowPMF mu target_initial_valid)
        (fun t x => rowPMF (R t x) (target_rows_valid t x)) T :=
  checkPositive_sound deployed mu P R q T weights deployed_row target_initial_valid
    source_rows target_rows_valid 0 (rationalModel P source_rows)
    (rationalModel_transitionPMF P source_rows) accepted

/-- The actual returned table implements the original conditional state path. -/
theorem output_actual_path :
    (causalLaw (rowPMF deployed deployed_row)
      (riskMicroControlKernel q (fun _ => (rationalModel P source_rows).transitionPMF)
        (timeObservationPolicy (policy weights
          (acceptedWeights deployed mu P R q T weights accepted) 0))) T).map
        (SourcePolicyPathBridgeCheck.eraseActionHistory T) =
      actualConditionedPrefix (rationalModel P source_rows) q
        (fun y => rowPMF (base y) (baseline_rows y)) (rowPMF p0 initial_row)
        {x | safe x = true} T 0
        (actualSource_pos P source_rows q base baseline_rows p0 initial_row safe T source_positive) :=
  output_path.trans target_is_actual

end case_1


namespace case_2

private def P : Fin 3 → Fin 3 → Fin 3 → ℚ := ![![![(3 / 8), (3 / 8), (1 / 4)], ![1, 0, 0], ![0, 1, 0]], ![![(1 / 8), (1 / 8), (3 / 4)], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, 1], ![1, 0, 0], ![0, 1, 0]]]
private def base : Fin 1 → Fin 3 → ℚ := ![![1, 0, 0]]
private def q : Fin 3 → Fin 1 := ![0, 0, 0]
private def p0 : Fin 3 → ℚ := ![(1 / 2), (1 / 2), 0]
private def deployed : Fin 3 → ℚ := ![(1 / 2), (1 / 2), 0]
private def safe : Fin 3 → Bool := ![true, true, false]
private def T : ℕ := 2
private def B := baselineRow P q base
private def mu := sourceInitial B p0 safe T
private def R := sourceTarget B safe T

private theorem source_rows : ∀ x a, ValidRow (P x a) := by decide +kernel
private theorem baseline_rows : ∀ y, ValidRow (base y) := by decide +kernel
private theorem initial_row : ValidRow p0 := by decide +kernel
private theorem deployed_row : ValidRow deployed := by decide +kernel

private theorem source_positive : 0 < sourceMass B p0 safe T := by decide +kernel
private theorem target_initial_valid : ValidRow mu :=
  sourceInitial_valid B (baselineRow_nonneg P source_rows q base baseline_rows)
    p0 initial_row.1 safe T source_positive
private theorem target_rows_valid : ∀ t x, ValidRow (R t x) :=
  sourceTarget_valid B (baselineRow_nonneg P source_rows q base baseline_rows) safe T

private theorem target_is_actual :
    targetPath (rowPMF mu target_initial_valid)
        (fun t x => rowPMF (R t x) (target_rows_valid t x)) T =
      actualConditionedPrefix (rationalModel P source_rows) q
        (fun y => rowPMF (base y) (baseline_rows y)) (rowPMF p0 initial_row)
        {x | safe x = true} T 0
        (actualSource_pos P source_rows q base baseline_rows p0 initial_row safe T source_positive) :=
  sourceTargetPath_eq_actual P source_rows q base baseline_rows p0 initial_row safe T source_positive

private theorem initial_mismatch : deployed ≠ mu := by decide +kernel

private theorem initial_pmf_mismatch : rowPMF deployed deployed_row ≠ rowPMF mu target_initial_valid := by
  intro heq
  apply initial_mismatch
  funext x
  have h := congrArg (fun p : PMF (Fin 3) => (p x).toReal) heq
  simp only [rowPMF_toReal] at h
  exact_mod_cast h

/-- Future actions cannot replace the required initial preparation. -/
theorem conditional_path_no_go :
    ¬ ∃ sigma : ℕ → Fin 1 → PMF (Fin 3),
      (causalLaw (rowPMF deployed deployed_row) (riskMicroControlKernel q
        (fun _ => (rationalModel P source_rows).transitionPMF)
        (timeObservationPolicy sigma)) T).map
        (SourcePolicyPathBridgeCheck.eraseActionHistory T) =
      actualConditionedPrefix (rationalModel P source_rows) q
        (fun y => rowPMF (base y) (baseline_rows y)) (rowPMF p0 initial_row)
        {x | safe x = true} T 0
        (actualSource_pos P source_rows q base baseline_rows p0 initial_row safe T source_positive) := by
  rintro ⟨sigma, hpath⟩
  have htarget := hpath.trans target_is_actual.symm
  exact initial_pmf_mismatch ((FinitePolicyPathCheck.specified_policy_path_iff
    (rationalModel P source_rows) q sigma (rowPMF deployed deployed_row)
    (rowPMF mu target_initial_valid) (fun t x => rowPMF (R t x) (target_rows_valid t x)) T).mp htarget).1

end case_2


namespace case_3

private def P : Fin 3 → Fin 2 → Fin 3 → ℚ := ![![![1, 0, 0], ![0, 0, 1]], ![![0, 0, 1], ![0, 1, 0]], ![![0, 0, 1], ![0, 0, 1]]]
private def base : Fin 1 → Fin 2 → ℚ := ![![(1 / 2), (1 / 2)]]
private def q : Fin 3 → Fin 1 := ![0, 0, 0]
private def p0 : Fin 3 → ℚ := ![(1 / 2), (1 / 2), 0]
private def deployed : Fin 3 → ℚ := ![(1 / 2), (1 / 2), 0]
private def safe : Fin 3 → Bool := ![true, true, false]
private def T : ℕ := 1
private def B := baselineRow P q base
private def mu := sourceInitial B p0 safe T
private def R := sourceTarget B safe T

private theorem source_rows : ∀ x a, ValidRow (P x a) := by decide +kernel
private theorem baseline_rows : ∀ y, ValidRow (base y) := by decide +kernel
private theorem initial_row : ValidRow p0 := by decide +kernel
private theorem deployed_row : ValidRow deployed := by decide +kernel

private theorem source_positive : 0 < sourceMass B p0 safe T := by decide +kernel
private theorem target_initial_valid : ValidRow mu :=
  sourceInitial_valid B (baselineRow_nonneg P source_rows q base baseline_rows)
    p0 initial_row.1 safe T source_positive
private theorem target_rows_valid : ∀ t x, ValidRow (R t x) :=
  sourceTarget_valid B (baselineRow_nonneg P source_rows q base baseline_rows) safe T

private theorem target_is_actual :
    targetPath (rowPMF mu target_initial_valid)
        (fun t x => rowPMF (R t x) (target_rows_valid t x)) T =
      actualConditionedPrefix (rationalModel P source_rows) q
        (fun y => rowPMF (base y) (baseline_rows y)) (rowPMF p0 initial_row)
        {x | safe x = true} T 0
        (actualSource_pos P source_rows q base baseline_rows p0 initial_row safe T source_positive) :=
  sourceTargetPath_eq_actual P source_rows q base baseline_rows p0 initial_row safe T source_positive

private def separator : Separation (Fin 3) (Fin 1) where
  time := 0
  observation := 0
  coefficient := ![![0, 0, -1], ![0, 0, -1], ![0, 0, 0]]
  bound := -1
  gap := 1
private theorem rejected : checkNegative mu P R q T separator = true := by decide +kernel

private theorem full_path_no_go (p : PMF (Fin 3)) :
    ¬ ∃ sigma : ℕ → Fin 1 → PMF (Fin 2),
      (causalLaw p (riskMicroControlKernel q
        (fun _ => (rationalModel P source_rows).transitionPMF)
        (timeObservationPolicy sigma)) T).map
        (SourcePolicyPathBridgeCheck.eraseActionHistory T) =
      targetPath (rowPMF mu target_initial_valid)
        (fun t x => rowPMF (R t x) (target_rows_valid t x)) T :=
  checkNegative_path_no_go mu P R q T separator target_initial_valid source_rows
    target_rows_valid (rationalModel P source_rows)
    (rationalModel_transitionPMF P source_rows) rejected p

/-- The checked separator rules out the original conditional full state path. -/
theorem conditional_path_no_go (p : PMF (Fin 3)) :
    ¬ ∃ sigma : ℕ → Fin 1 → PMF (Fin 2),
      (causalLaw p (riskMicroControlKernel q
        (fun _ => (rationalModel P source_rows).transitionPMF)
        (timeObservationPolicy sigma)) T).map
        (SourcePolicyPathBridgeCheck.eraseActionHistory T) =
      actualConditionedPrefix (rationalModel P source_rows) q
        (fun y => rowPMF (base y) (baseline_rows y)) (rowPMF p0 initial_row)
        {x | safe x = true} T 0
        (actualSource_pos P source_rows q base baseline_rows p0 initial_row safe T source_positive) := by
  rintro ⟨sigma, hpath⟩
  exact full_path_no_go p ⟨sigma, hpath.trans target_is_actual.symm⟩

end case_3


namespace case_4

private def P : Fin 3 → Fin 3 → Fin 3 → ℚ := ![![![(3 / 8), (3 / 8), (1 / 4)], ![1, 0, 0], ![0, 1, 0]], ![![(1 / 8), (1 / 8), (3 / 4)], ![1, 0, 0], ![0, 1, 0]], ![![1, 0, 0], ![1, 0, 0], ![1, 0, 0]]]
private def base : Fin 1 → Fin 3 → ℚ := ![![1, 0, 0]]
private def q : Fin 3 → Fin 1 := ![0, 0, 0]
private def p0 : Fin 3 → ℚ := ![(1 / 2), (1 / 2), 0]
private def deployed : Fin 3 → ℚ := ![(3 / 4), (1 / 4), 0]
private def safe : Fin 3 → Bool := ![true, true, false]
private def T : ℕ := 2
private def B := baselineRow P q base
private def mu := sourceInitial B p0 safe T
private def R := sourceTarget B safe T

private theorem source_rows : ∀ x a, ValidRow (P x a) := by decide +kernel
private theorem baseline_rows : ∀ y, ValidRow (base y) := by decide +kernel
private theorem initial_row : ValidRow p0 := by decide +kernel
private theorem deployed_row : ValidRow deployed := by decide +kernel

private theorem source_positive : 0 < sourceMass B p0 safe T := by decide +kernel
private theorem target_initial_valid : ValidRow mu :=
  sourceInitial_valid B (baselineRow_nonneg P source_rows q base baseline_rows)
    p0 initial_row.1 safe T source_positive
private theorem target_rows_valid : ∀ t x, ValidRow (R t x) :=
  sourceTarget_valid B (baselineRow_nonneg P source_rows q base baseline_rows) safe T

private theorem target_is_actual :
    targetPath (rowPMF mu target_initial_valid)
        (fun t x => rowPMF (R t x) (target_rows_valid t x)) T =
      actualConditionedPrefix (rationalModel P source_rows) q
        (fun y => rowPMF (base y) (baseline_rows y)) (rowPMF p0 initial_row)
        {x | safe x = true} T 0
        (actualSource_pos P source_rows q base baseline_rows p0 initial_row safe T source_positive) :=
  sourceTargetPath_eq_actual P source_rows q base baseline_rows p0 initial_row safe T source_positive

private def weights : Fin T → Fin 1 → Fin 3 → ℚ := ![![![0, (3 / 4), (1 / 4)]], ![![0, (1 / 2), (1 / 2)]]]
private theorem accepted : checkPositive deployed mu P R q T weights = true := by decide +kernel

private theorem output_path :
    (causalLaw (rowPMF deployed deployed_row)
      (riskMicroControlKernel q (fun _ => (rationalModel P source_rows).transitionPMF)
        (timeObservationPolicy (policy weights
          (acceptedWeights deployed mu P R q T weights accepted) 0))) T).map
        (SourcePolicyPathBridgeCheck.eraseActionHistory T) =
      targetPath (rowPMF mu target_initial_valid)
        (fun t x => rowPMF (R t x) (target_rows_valid t x)) T :=
  checkPositive_sound deployed mu P R q T weights deployed_row target_initial_valid
    source_rows target_rows_valid 0 (rationalModel P source_rows)
    (rationalModel_transitionPMF P source_rows) accepted

/-- The actual returned table implements the original conditional state path. -/
theorem output_actual_path :
    (causalLaw (rowPMF deployed deployed_row)
      (riskMicroControlKernel q (fun _ => (rationalModel P source_rows).transitionPMF)
        (timeObservationPolicy (policy weights
          (acceptedWeights deployed mu P R q T weights accepted) 0))) T).map
        (SourcePolicyPathBridgeCheck.eraseActionHistory T) =
      actualConditionedPrefix (rationalModel P source_rows) q
        (fun y => rowPMF (base y) (baseline_rows y)) (rowPMF p0 initial_row)
        {x | safe x = true} T 0
        (actualSource_pos P source_rows q base baseline_rows p0 initial_row safe T source_positive) :=
  output_path.trans target_is_actual

end case_4


namespace case_5

private def P : Fin 3 → Fin 3 → Fin 3 → ℚ := ![![![(3 / 8), (3 / 8), (1 / 4)], ![1, 0, 0], ![0, 1, 0]], ![![(1 / 8), (1 / 8), (3 / 4)], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, 1], ![1, 0, 0], ![0, 1, 0]]]
private def base : Fin 1 → Fin 3 → ℚ := ![![0, (1 / 3), (2 / 3)]]
private def q : Fin 3 → Fin 1 := ![0, 0, 0]
private def p0 : Fin 3 → ℚ := ![(1 / 2), (1 / 2), 0]
private def deployed : Fin 3 → ℚ := ![(1 / 2), (1 / 2), 0]
private def safe : Fin 3 → Bool := ![true, true, false]
private def T : ℕ := 2
private def B := baselineRow P q base
private def mu := sourceInitial B p0 safe T
private def R := sourceTarget B safe T

private theorem source_rows : ∀ x a, ValidRow (P x a) := by decide +kernel
private theorem baseline_rows : ∀ y, ValidRow (base y) := by decide +kernel
private theorem initial_row : ValidRow p0 := by decide +kernel
private theorem deployed_row : ValidRow deployed := by decide +kernel

private theorem source_positive : 0 < sourceMass B p0 safe T := by decide +kernel
private theorem target_initial_valid : ValidRow mu :=
  sourceInitial_valid B (baselineRow_nonneg P source_rows q base baseline_rows)
    p0 initial_row.1 safe T source_positive
private theorem target_rows_valid : ∀ t x, ValidRow (R t x) :=
  sourceTarget_valid B (baselineRow_nonneg P source_rows q base baseline_rows) safe T

private theorem target_is_actual :
    targetPath (rowPMF mu target_initial_valid)
        (fun t x => rowPMF (R t x) (target_rows_valid t x)) T =
      actualConditionedPrefix (rationalModel P source_rows) q
        (fun y => rowPMF (base y) (baseline_rows y)) (rowPMF p0 initial_row)
        {x | safe x = true} T 0
        (actualSource_pos P source_rows q base baseline_rows p0 initial_row safe T source_positive) :=
  sourceTargetPath_eq_actual P source_rows q base baseline_rows p0 initial_row safe T source_positive

private def weights : Fin T → Fin 1 → Fin 3 → ℚ := ![![![0, (1 / 3), (2 / 3)]], ![![0, (1 / 3), (2 / 3)]]]
private theorem accepted : checkPositive deployed mu P R q T weights = true := by decide +kernel

private theorem output_path :
    (causalLaw (rowPMF deployed deployed_row)
      (riskMicroControlKernel q (fun _ => (rationalModel P source_rows).transitionPMF)
        (timeObservationPolicy (policy weights
          (acceptedWeights deployed mu P R q T weights accepted) 0))) T).map
        (SourcePolicyPathBridgeCheck.eraseActionHistory T) =
      targetPath (rowPMF mu target_initial_valid)
        (fun t x => rowPMF (R t x) (target_rows_valid t x)) T :=
  checkPositive_sound deployed mu P R q T weights deployed_row target_initial_valid
    source_rows target_rows_valid 0 (rationalModel P source_rows)
    (rationalModel_transitionPMF P source_rows) accepted

/-- The actual returned table implements the original conditional state path. -/
theorem output_actual_path :
    (causalLaw (rowPMF deployed deployed_row)
      (riskMicroControlKernel q (fun _ => (rationalModel P source_rows).transitionPMF)
        (timeObservationPolicy (policy weights
          (acceptedWeights deployed mu P R q T weights accepted) 0))) T).map
        (SourcePolicyPathBridgeCheck.eraseActionHistory T) =
      actualConditionedPrefix (rationalModel P source_rows) q
        (fun y => rowPMF (base y) (baseline_rows y)) (rowPMF p0 initial_row)
        {x | safe x = true} T 0
        (actualSource_pos P source_rows q base baseline_rows p0 initial_row safe T source_positive) :=
  output_path.trans target_is_actual

end case_5


namespace case_6

private def P : Fin 3 → Fin 3 → Fin 3 → ℚ := ![![![(3 / 8), (3 / 8), (1 / 4)], ![1, 0, 0], ![0, 1, 0]], ![![(1 / 8), (1 / 8), (3 / 4)], ![1, 0, 0], ![0, 1, 0]], ![![0, 0, 1], ![1, 0, 0], ![0, 1, 0]]]
private def base : Fin 1 → Fin 3 → ℚ := ![![1, 0, 0]]
private def q : Fin 3 → Fin 1 := ![0, 0, 0]
private def p0 : Fin 3 → ℚ := ![(1 / 2), (1 / 2), 0]
private def deployed : Fin 3 → ℚ := ![(1 / 2), (1 / 2), 0]
private def safe : Fin 3 → Bool := ![true, true, false]
private def T : ℕ := 0
private def B := baselineRow P q base
private def mu := sourceInitial B p0 safe T
private def R := sourceTarget B safe T

private theorem source_rows : ∀ x a, ValidRow (P x a) := by decide +kernel
private theorem baseline_rows : ∀ y, ValidRow (base y) := by decide +kernel
private theorem initial_row : ValidRow p0 := by decide +kernel
private theorem deployed_row : ValidRow deployed := by decide +kernel

private theorem source_positive : 0 < sourceMass B p0 safe T := by decide +kernel
private theorem target_initial_valid : ValidRow mu :=
  sourceInitial_valid B (baselineRow_nonneg P source_rows q base baseline_rows)
    p0 initial_row.1 safe T source_positive
private theorem target_rows_valid : ∀ t x, ValidRow (R t x) :=
  sourceTarget_valid B (baselineRow_nonneg P source_rows q base baseline_rows) safe T

private theorem target_is_actual :
    targetPath (rowPMF mu target_initial_valid)
        (fun t x => rowPMF (R t x) (target_rows_valid t x)) T =
      actualConditionedPrefix (rationalModel P source_rows) q
        (fun y => rowPMF (base y) (baseline_rows y)) (rowPMF p0 initial_row)
        {x | safe x = true} T 0
        (actualSource_pos P source_rows q base baseline_rows p0 initial_row safe T source_positive) :=
  sourceTargetPath_eq_actual P source_rows q base baseline_rows p0 initial_row safe T source_positive

private def weights : Fin T → Fin 1 → Fin 3 → ℚ := Fin.elim0
private theorem accepted : checkPositive deployed mu P R q T weights = true := by decide +kernel

private theorem output_path :
    (causalLaw (rowPMF deployed deployed_row)
      (riskMicroControlKernel q (fun _ => (rationalModel P source_rows).transitionPMF)
        (timeObservationPolicy (policy weights
          (acceptedWeights deployed mu P R q T weights accepted) 0))) T).map
        (SourcePolicyPathBridgeCheck.eraseActionHistory T) =
      targetPath (rowPMF mu target_initial_valid)
        (fun t x => rowPMF (R t x) (target_rows_valid t x)) T :=
  checkPositive_sound deployed mu P R q T weights deployed_row target_initial_valid
    source_rows target_rows_valid 0 (rationalModel P source_rows)
    (rationalModel_transitionPMF P source_rows) accepted

/-- The actual returned table implements the original conditional state path. -/
theorem output_actual_path :
    (causalLaw (rowPMF deployed deployed_row)
      (riskMicroControlKernel q (fun _ => (rationalModel P source_rows).transitionPMF)
        (timeObservationPolicy (policy weights
          (acceptedWeights deployed mu P R q T weights accepted) 0))) T).map
        (SourcePolicyPathBridgeCheck.eraseActionHistory T) =
      actualConditionedPrefix (rationalModel P source_rows) q
        (fun y => rowPMF (base y) (baseline_rows y)) (rowPMF p0 initial_row)
        {x | safe x = true} T 0
        (actualSource_pos P source_rows q base baseline_rows p0 initial_row safe T source_positive) :=
  output_path.trans target_is_actual

end case_6


namespace case_7

private def P : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![(3 / 8), (3 / 8), (1 / 4)]], ![![(1 / 8), (1 / 8), (3 / 4)]], ![![0, 0, 1]]]
private def base : Fin 1 → Fin 1 → ℚ := ![![1]]
private def q : Fin 3 → Fin 1 := ![0, 0, 0]
private def p0 : Fin 3 → ℚ := ![(1 / 2), (1 / 2), 0]
private def deployed : Fin 3 → ℚ := ![(3 / 4), (1 / 4), 0]
private def safe : Fin 3 → Bool := ![false, false, false]
private def T : ℕ := 1
private def B := baselineRow P q base
private def mu := sourceInitial B p0 safe T
private def R := sourceTarget B safe T

private theorem source_rows : ∀ x a, ValidRow (P x a) := by decide +kernel
private theorem baseline_rows : ∀ y, ValidRow (base y) := by decide +kernel
private theorem initial_row : ValidRow p0 := by decide +kernel
private theorem deployed_row : ValidRow deployed := by decide +kernel

private theorem conditioning_undefined : sourceMass B p0 safe T = 0 := by decide +kernel

/-- The original source's safety event has exact mass zero. -/
theorem zero_survival_event :
    actualSurvivalMass (rationalModel P source_rows) q
      (fun y => rowPMF (base y) (baseline_rows y)) (rowPMF p0 initial_row)
      {x | safe x = true} T = 0 := by
  rw [← sourceMass_eq_actual P source_rows q base baseline_rows p0 initial_row safe T]
  exact_mod_cast conditioning_undefined

end case_7


end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionCertificateWitnessCheck
