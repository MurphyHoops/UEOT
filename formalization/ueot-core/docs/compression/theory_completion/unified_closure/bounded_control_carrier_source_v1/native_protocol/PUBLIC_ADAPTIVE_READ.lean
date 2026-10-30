import UEOT
open MeasureTheory ProbabilityTheory Set
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open DualDriveFiniteNoisyCalibration DualDriveFiniteCalibrationCoverage
open DualDriveAdaptiveReadCalibration DualDrivePersistentReadCounterexample
open scoped ENNReal

-- All inputs supplied to select come from actually read prefixes, with literal data binding.
example (m K : ℕ) (route : Router) (p : Parameters) (omega : Raw (m+K)) :=
  decoded_source_prefix m K route p omega
example (m K : ℕ) (route : Router) (data : Data (m+K)) := run_trace m K route data
example (m K : ℕ) (route : Router) (data : Data (m+K)) (r : Read)
    (hr : r ∈ (run m K route data).trace) := run_all_reads_actual m K route data r hr
example (m K : ℕ) (route : Router) (data : Data (m+K)) :
    (run m K route data).trace.length=4*m+K := run_trace_length m K route data
example (m K : ℕ) (hm : 0 < m) (route : Router) (p : Parameters) (hp : Valid p) :
    (rawLaw (m+K)).real {omega | ActualWrong m K route p omega} ≤
      8*((K+1 : ℕ) : ℝ)*Real.exp (-(m : ℝ)/8) := actual_joint_risk_le m K hm route p hp
example (m K : ℕ) (hm : 0 < m) (route : Router) (p : Parameters)
    (hg : ∀ i, 1 ≤ p.gain i) (best : Bool) (hgap : (1/2 : ℚ) ≤ p.latent best-p.latent (!best)) :=
  actual_best_accept_probability_ge m K hm route p hg best hgap
example : 0 < (rawLaw (adaptiveWarmup+adaptiveExtra)).real
    {omega | returned adaptiveWarmup adaptiveExtra (feedbackRouter adaptiveWarmup)
      (sourceData regularParameters omega)=some true} := adaptive_registered_positive_acceptance

-- THIS common-shock family keeps the exact per-coordinate sensor marginals.
example (N : ℕ) (q : Index N) := persistent_coordinate_law N q
example (m K : ℕ) (hm : 0 < m) :
    (rawLaw 1).real {z | repeatRaw (N:=m+K) z ∈ AllGood m K}=0 :=
  persistent_allGood_probability_zero m K hm
example (m K : ℕ) (hm : 0 < m) (route : Router) :
    (1/16 : ℝ) ≤ (rawLaw 1).real
      {z | ActualWrong m K route fragileParameters (repeatRaw (N:=m+K) z)} :=
  adaptive_persistent_joint_risk_ge m K hm route
example : (1/16 : ℝ) ≤ (rawLaw 1).real
    {z | ActualWrong adaptiveWarmup adaptiveExtra (feedbackRouter adaptiveWarmup)
      fragileParameters (repeatRaw (N:=adaptiveWarmup+adaptiveExtra) z)} :=
  adaptive_persistent_joint_risk_ge _ _ (by decide) _

#check DualDriveAdaptiveReadCalibration.Read.mk
#check DualDriveAdaptiveReadCalibration.ReadState.mk
#check persistentLaw_probability
#print axioms decoded_source_prefix
#print axioms actual_joint_risk_le
#print axioms adaptive_registered_positive_acceptance
#print axioms persistent_coordinate_law
#print axioms persistentLaw_probability
#print axioms adaptive_persistent_joint_risk_ge

-- Extra NONAUTHOR boundary: zero adaptive reads returns exactly the initial
-- common data prefix; the computed count is not a separately supplied count.
namespace UEOTAdaptiveReadIndependent
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open DualDriveFiniteNoisyCalibration DualDriveAdaptiveReadCalibration DualDrivePersistentReadCounterexample
example (m : ℕ) (route : Router) (data : Data (m+0)) :
    minCount (run m 0 route data)=m := by
  simp [run,adaptive,minCount,warmup_count]
-- Actual shock encoding is row0 OR row3 true. This also checks that the
-- mathematical error witness is not the wrong all-false-anchor transcription.
example : shockWord ⟨0,0⟩=true ∧ shockWord ⟨1,0⟩=false ∧
    shockWord ⟨2,0⟩=false ∧ shockWord ⟨3,0⟩=true := by decide
-- Real actual reader under arbitrary routing: repeated source prefix means
-- no amount of fresh indices turns one shock into independent evidence.
example (K : ℕ) (route : Router) :
    returned 1 K route (sourceData fragileParameters (repeatRaw shockWord))=some false :=
  adaptive_repeat_selects_wrong 1 K (by decide) route
#print axioms run_all_reads_actual
#print axioms adaptive_repeat_selects_wrong
end UEOTAdaptiveReadIndependent
