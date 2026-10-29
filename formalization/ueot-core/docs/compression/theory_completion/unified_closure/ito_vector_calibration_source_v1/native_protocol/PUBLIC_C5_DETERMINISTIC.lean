import UEOT

-- Public-root consumer of the actual source; retained original independent discriminator.
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open DualDriveNoisyOperationalCalibration
namespace ActualNoisyCalibrationConsumer
noncomputable section
open scoped BigOperators
/-- Same actual regular data, literal checked inverse, exact returned vector. -/
theorem actual_returned_noisy_coefficient :
    coefficients regularInverse (regularQueries true)=(20/21 : ℝ) • unit (1 : Fin 2) := by
  ext i
  fin_cases i <;>
    norm_num [coefficients,regularInverse,regularQueries,regularDecoder,regularEncoder,regularInputs,
      diagonal_apply,unit]

theorem actual_nonzero_reconstruction_error :
    ‖coefficients regularInverse (regularQueries true)-unit (1 : Fin 2)‖=(1/21 : ℝ) := by
  have h : coefficients regularInverse (regularQueries true)-unit (1 : Fin 2)=
      ((20/21 : ℝ)-1) • unit (1 : Fin 2) := by
    rw [actual_returned_noisy_coefficient,sub_smul,one_smul]
  rw [h,norm_smul,norm_unit,mul_one,Real.norm_eq_abs]
  norm_num

/-- Both inverse equations refer to the matrix constructed FROM actual samples. -/
example (z : Coordinate 2) : regularChecked.symm (columns regularSamples z)=z :=
  regular_left z
example (z : Coordinate 2) : columns regularSamples (regularChecked.symm z)=z :=
  regular_right z
/-- Actual original rank consumer, same allowed actions, independent evaluation. -/
example : regularEvaluation (regularEncoder (regularInputs false)) <
    regularEvaluation (regularEncoder (regularInputs true)) :=
  regular_noisy_action_ranking false (by decide)

/-- Exact/no-noise fixture uses ACTUAL exact measured columns and a literal
candidate inverse, not another unknown true inverse used by the selector. -/
def exactSamples (i : Fin 2) : Coordinate 2 := regularDecoder (unit i)
def exactCandidate : Coordinate 2 →L[ℝ] Coordinate 2 := diagonal (fun _ => 1/2)
private theorem exact_left (z : Coordinate 2) : exactCandidate (columns exactSamples z)=z := by
  change exactCandidate (columns (fun i => regularDecoder (unit i)) z)=z
  rw [columns_of_map]
  ext i
  norm_num [exactCandidate,regularDecoder,diagonal_apply]
  ring
private theorem exact_right (z : Coordinate 2) : columns exactSamples (exactCandidate z)=z := by
  change columns (fun i => regularDecoder (unit i)) (exactCandidate z)=z
  rw [columns_of_map]
  ext i
  norm_num [exactCandidate,regularDecoder,diagonal_apply]
  ring

theorem actual_exact_reconstruction : coefficients exactCandidate (regularQueries true)=unit (1 : Fin 2) := by
  have h := actual_coefficient_error regularEncoder regularDecoder regularBasis (@unit 2)
    (fun _ => rfl) exactSamples 0 (le_refl 0)
    (fun i => by simp [exactSamples,regularEncoder]) exactCandidate exact_left (unit 1) (regularQueries true) 0
    (by simp [regularQueries,regularInputs,regularEncoder])
  have hz : ‖coefficients exactCandidate (regularQueries true)-unit (1 : Fin 2)‖ ≤ 0 := by
    simpa [regularBasis,regularEncoder] using h
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hz (norm_nonneg _)))

/-- Nondegenerate near-singular SAME measurement contract at exact t=1/100. -/
example :
    ‖nearDecoder (1/100) (unit 1)-nearDecoder (1/100) (0 : Coordinate 2)‖=(1/100 : ℝ) ∧
    ‖coefficients (nearInverse (1/100)) (nearDecoder (1/100) (unit 1))-(0 : Coordinate 2)‖=1 :=
  near_actual_query_contract (1/100) (by norm_num)
example : (100 : ℝ) ≤ ‖nearInverse (1/100)‖ := by
  have h := near_required_conditioning (1/100) (by norm_num)
  nlinarith
example (z : Coordinate 2) : (nearChecked (1/100) (by norm_num)).symm
    (columns (nearSamples (1/100)) z)=z := near_left _ (by norm_num) z
#print axioms actual_nonzero_reconstruction_error
#print axioms actual_exact_reconstruction
end
end ActualNoisyCalibrationConsumer

namespace IndependentSingularMeasuredTable
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DualDriveNoisyOperationalCalibration
example (R : Coordinate 2 →L[ℝ] Coordinate 2) :
    ¬ ∀ z, R (columns (fun _ : Fin 2 => (0 : Coordinate 2)) z) = z := by
  intro h
  have h0 := congrArg (fun z : Coordinate 2 => z 0) (h (unit (0 : Fin 2)))
  simp [columns_apply,unit] at h0
#print axioms actual_action_gap
#print axioms no_uniform_condition_free_reconstruction
end IndependentSingularMeasuredTable
