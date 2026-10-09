import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.TwoStageFormationTransport
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteFormationBoundary
import Mathlib.Tactic

/-!
# UMC-03 exact two-stage nonvacuity fixture

The physical microstate flips twice, and both sensor/parent fingerprints
are transported by the SAME normalized Boolean coordinate-permutation
channel. No independent free-form hWorld or hParent oracle is assumed:
their zero-error equalities are proven by cases.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

/-- A permutation channel on Boolean sensor coordinates. -/
noncomputable def flipSensorChannel : FiniteResponseChannel Bool Bool where
  weight := fun j i => if i = !j then 1 else 0
  nonneg := by
    intro j i
    split_ifs <;> norm_num
  row_sum_one := by
    intro j
    cases j <;> norm_num [Fintype.sum_bool]

/-- The channel sends the complete sensor fingerprint of x exactly to
the fingerprint of its next state T(x)=!x. -/
theorem flip_sensor_response_commutes (x j : Bool) :
    flipStateFingerprint (flipStep x ()) j =
      ∑ i : Bool, flipSensorChannel.weight j i *
        flipStateFingerprint x i := by
  cases x <;> cases j <;>
    norm_num [flipStateFingerprint, flipStep, flipSensorChannel,
      Fintype.sum_bool]

/-- Each step's real world and parent channels agree by CONSTRUCTION
with the same underlying flip, not merely through an assumed diagram. -/
theorem flip_sensor_zero_residual (x : Bool) (j : Bool) :
    |flipStateFingerprint (flipStep x ()) j -
      ∑ i : Bool, flipSensorChannel.weight j i *
        flipStateFingerprint x i| ≤ (0 : ℝ) := by
  rw [flip_sensor_response_commutes]
  simp

/-- Exact stage-zero formation is nonempty: physical false matches
the registered false source. -/
theorem flip_source_initially_formed :
    FormedByResponse flipStateFingerprint flipStateFingerprint 0
      false false := by
  intro i
  simp [flipStateFingerprint]

/-- Two independently verified zero-error transports of the SAME T
give a zero-tolerance final formation certificate from the generic
UMC-03 composition theorem, not via direct final-state matching. -/
theorem flip_two_stage_formation_computed :
    FormedByResponse flipStateFingerprint flipStateFingerprint 0
      (flipStep (flipStep false ()) ())
      (flipStep (flipStep false ()) ()) := by
  have h := two_stage_formation_budget
    flipSensorChannel flipSensorChannel
    flipStateFingerprint flipStateFingerprint flipStateFingerprint
    flipStateFingerprint flipStateFingerprint flipStateFingerprint
    (fun x => flipStep x ()) (fun x => flipStep x ())
    (fun p => flipStep p ()) (fun p => flipStep p ())
    0 0 0 0 0
    (fun x j => flip_sensor_zero_residual x j)
    (fun p j => flip_sensor_zero_residual p j)
    (fun x j => flip_sensor_zero_residual x j)
    (fun p j => flip_sensor_zero_residual p j)
    false false flip_source_initially_formed
  simpa using h

/-- The actual common-process double-flip has its same identity label
after two steps, and its final fingerprint identifies that label
uniquely among the two candidates. This is operational identity under
a declared label, not P8 ontic persistence or autopoiesis. -/
theorem flip_double_step_operational_identity_and_uniqueness :
    flipStep (flipStep false ()) () = false ∧
    (∀ q : Bool,
      FormedByResponse flipStateFingerprint flipStateFingerprint 0
        (flipStep (flipStep false ()) ()) q → q = false) := by
  constructor
  · rfl
  · intro q hq
    have hFormed := flip_two_stage_formation_computed
    have hsep : LocalResponseGap flipStateFingerprint 0 false := by
      intro candidate hne
      cases candidate
      · exact False.elim (hne rfl)
      · refine ⟨false, ?_⟩
        norm_num [flipStateFingerprint]
    have hu := unique_formed_target_of_local_gap
      flipStateFingerprint flipStateFingerprint 0
      (flipStep (flipStep false ()) ())
      (flipStep (flipStep false ()) ()) hFormed (by simpa [flipStep] using hsep)
      q hq
    simpa [flipStep] using hu

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
