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
local instance : MeasurableSpace (Fin 3) := ⊤

namespace case_0

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

end case_0


end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionCertificateWitnessCheck
