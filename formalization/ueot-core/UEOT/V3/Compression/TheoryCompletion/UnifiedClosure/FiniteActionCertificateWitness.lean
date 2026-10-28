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

namespace original_actions

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

end original_actions


namespace two_step_added_actions

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

end two_step_added_actions


namespace unprepared_initial

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

end unprepared_initial


namespace same_source_alias

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

end same_source_alias


namespace unreachable_fallback

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

end unreachable_fallback


namespace independent_baseline_variant

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

end independent_baseline_variant


namespace zero_horizon

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

end zero_horizon


namespace zero_survival

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

end zero_survival

/-! Registered checks appended to the generated witness in its outer namespace.
Closed numeric checks stay private; the full causal initial-TV obstacle is public. -/

open UEOT.V3.TotalVariation FiniteConditionalStability

namespace two_step_added_actions

private theorem recomputed_reference :
    sourceMass B p0 safe T = 1/4 ∧ mu = ![3/4, 1/4, 0] ∧
    R 0 0 = ![3/4, 1/4, 0] ∧ R 1 0 = ![1/2, 1/2, 0] := by decide +kernel

private def staticWeights : Fin T → Fin 1 → Fin 3 → ℚ := fun _ _ => ![0, 3/4, 1/4]

private theorem static_table_rejected :
    checkPositive deployed mu P R q T staticWeights = false := by decide +kernel

private theorem invalid_weights_rejected :
    checkPositive deployed mu P R q T (fun _ _ => ![-1, 1, 1]) = false := by decide +kernel

end two_step_added_actions

namespace same_source_alias

private def individualWeights (x : Fin 2) : Fin 2 → ℚ := fun a => if a = x then 1 else 0

private theorem individually_feasible : ∀ x : Fin 2,
    ValidRow (individualWeights x) ∧ ∀ z,
      ∑ a, individualWeights x a * P x.castSucc a z = R 0 x.castSucc z := by decide +kernel

private theorem both_safe_rows_occupied : occupied mu R 0 0 ∧ occupied mu R 0 1 := by decide +kernel

private theorem zero_gap_rejected :
    checkNegative mu P R q T {separator with gap := 0} = false := by decide +kernel

private theorem outside_horizon_rejected :
    checkNegative mu P R q T {separator with time := T} = false := by decide +kernel

private theorem forged_score_rejected :
    checkNegative mu P R q T {separator with coefficient := fun _ _ => 0} = false := by decide +kernel

end same_source_alias

namespace unreachable_fallback

private theorem unreachable_at_all_constraint_times :
    ¬ occupied mu R 0 2 ∧ ¬ occupied mu R 1 2 := by decide +kernel

private theorem unoccupied_fallback_not_implementable (sigma : PMF (Fin 3)) :
    FiniteActionRealizabilityCheck.actionMixture
      (fun a => rowPMF (P 2 a) (source_rows 2 a)) sigma ≠
      rowPMF (R 0 2) (target_rows_valid 0 2) := by
  intro heq
  have hz := congrArg (fun p : PMF (Fin 3) => (p 2).toReal) heq
  change FiniteActionRealizabilityCheck.realRow
    (FiniteActionRealizabilityCheck.actionMixture
      (fun a => rowPMF (P 2 a) (source_rows 2 a)) sigma) 2 = _ at hz
  rw [FiniteActionRealizabilityCheck.realRow_actionMixture] at hz
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    FiniteActionRealizabilityCheck.realRow, rowPMF_toReal] at hz
  have hzero : ∀ a, P 2 a 2 = 0 := by decide +kernel
  have hone : R 0 2 2 = 1 := by decide +kernel
  simp [hzero, hone] at hz

end unreachable_fallback

namespace unprepared_initial

private theorem mu_computed : mu = ![3/4, 1/4, 0] := by decide +kernel

private theorem initial_tv :
    tvDist (rowPMF p0 initial_row).toMeasure (rowPMF mu target_initial_valid).toMeasure = 1/4 := by
  rw [tvDist_eq_one_sub_pmfCommonMass]
  have hp (x : Fin 3) : p0 x = if x = 0 then 1/2 else if x = 1 then 1/2 else 0 := by
    fin_cases x <;> decide +kernel
  have hm (x : Fin 3) : mu x = if x = 0 then 3/4 else if x = 1 then 1/4 else 0 := by
    fin_cases x <;> decide +kernel
  simp only [pmfCommonMass, Fin.sum_univ_succ, rowPMF_toReal, hp, hm]
  have h20 : (2 : Fin 3) ≠ 0 := by decide +kernel
  have h21 : (2 : Fin 3) ≠ 1 := by decide +kernel
  norm_num [h20, h21]

/-- Any future causal state kernel retains the original initial marginal, so
the original two-step conditional state path costs at least 1/4 in TV. -/
theorem every_causal_path_tv_obstacle
    (K : ∀ n, CausalHistory (Fin 3) (Fin 3) n → PMF (Fin 3)) :
    1/4 ≤ tvDist (causalLaw (rowPMF p0 initial_row) K T).toMeasure
      (actualConditionedPrefix (rationalModel P source_rows) q
        (fun y => rowPMF (base y) (baseline_rows y)) (rowPMF p0 initial_row)
        {x | safe x = true} T 0
        (actualSource_pos P source_rows q base baseline_rows p0 initial_row safe T source_positive)).toMeasure := by
  rw [← target_is_actual]
  have h := initial_tv_le_path_tv (rowPMF p0 initial_row) K T
    (targetPath (rowPMF mu target_initial_valid)
      (fun t x => rowPMF (R t x) (target_rows_valid t x)) T)
  have hmarg : (targetPath (rowPMF mu target_initial_valid)
      (fun t x => rowPMF (R t x) (target_rows_valid t x)) T).map (initialRecord T) =
      rowPMF mu target_initial_valid :=
    causalLaw_initial_marginal (rowPMF mu target_initial_valid) _ T
  rw [hmarg, initial_tv] at h
  exact h

end unprepared_initial


end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionCertificateWitnessCheck
