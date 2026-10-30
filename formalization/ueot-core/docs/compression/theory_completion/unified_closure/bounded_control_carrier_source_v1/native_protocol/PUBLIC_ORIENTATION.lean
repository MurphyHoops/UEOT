import UEOT
namespace UEOTPositiveOrientationIndependent
open MeasureTheory ProbabilityTheory
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open DualDriveFiniteNoisyCalibration DualDriveAdaptiveReadCalibration DualDrivePersistentReadCounterexample
open DualDrivePositiveOrientationCalibration
noncomputable section
example {N : ℕ} (p : Parameters) (hp : Valid p) (mu : Measure (Raw N)) := any_law_joint_error_zero p hp mu
example (m K : ℕ) (route : Router) (p : Parameters) (hp : Valid p) (mu : Measure (Raw (m+K))) :=
  any_route_law_joint_error_zero m K route p hp mu
-- SAME actual persistent source/cache, distinct declared policies; old error retained.
example (m K : ℕ) (hm : 0 < m) (route : Router) :
    DualDriveAdaptiveReadCalibration.returned m K route
      (sourceData fragileParameters (repeatRaw (N:=m+K) shockWord))=some false ∧
    DualDrivePositiveOrientationCalibration.returned m K route
      (sourceData fragileParameters (repeatRaw (N:=m+K) shockWord))=some true :=
  ⟨adaptive_repeat_selects_wrong m K hm route,adaptive_repeat_oriented_true m K hm route⟩
example := actual_registered_cache_outputs
example := original_registered_outputs
example (m K : ℕ) (hm : 0 < m) (route : Router) := persistent_new_correct_acceptance_ge m K hm route
example (data : Data 0) := DualDrivePositiveOrientationCalibration.zero_budget_reject data
-- Strict extra boundary: Valid does NOT imply all raw words accept.
-- No new observation/action/threshold is introduced; use a legal weak gain
-- and a persistent common sign at every row/read.
def weak : Parameters := ⟨![1,1/100],fun a => if a then 1 else 0⟩
theorem weak_valid : Valid weak := by
  constructor
  · intro i; fin_cases i <;> norm_num [weak]
  · constructor
    · intro a; cases a <;> norm_num [weak]
    · norm_num [weak]
theorem weak_repeated_rejects (N : ℕ) (hN : 0 < N) :
    orient (sourceData weak (repeatRaw (N:=N) (fun _ => true)))=none := by
  have hn : N≠0 := Nat.ne_of_gt hN
  simp only [orient,select,conditioning,estimate]
  simp_rw [mean_repeat N hN]
  norm_num [hn,sensor,trueMean,weak,bit,Fin.ext_iff]
#print axioms accepted_oriented_correct
#print axioms any_route_law_joint_error_zero
#print axioms regular_any_raw_output
#print axioms actual_registered_cache_outputs
#print axioms weak_repeated_rejects
end
end UEOTPositiveOrientationIndependent
