import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataJoint
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataCertifiedConsumer

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataRuntimeCertificate

open MeasureTheory UEOT.V3.PathError UEOT.V3.TotalVariation
open UEOT.V3.FiniteDiscountedControl UEOT.V3.CoreOperationalAssembly
open FiniteDataSource FiniteDataLiteral FiniteActionCertificateCheck
open SameSourceFiniteWindowCheck FiniteDataNumericalBounds
open ConditionedActionTransportCheck FiniteDataPathBounds
open scoped BigOperators
noncomputable section
local instance : MeasurableSpace State := ⊤
local instance : MeasurableSpace Bool := ⊤

def horizon : ℕ := 10
def counts : Fin 4 → ℕ := ![196842, 65524, 13028, 13237]
def qEstimate : Fin 4 → ℚ := fun j => (counts j : ℚ) / 262144
def estimate : Param := ⟨(qEstimate 0 : ℝ), (qEstimate 1 : ℝ),
  (qEstimate 2 : ℝ), (qEstimate 3 : ℝ)⟩
theorem counts_legal : ∀ j, counts j ≤ 262144 := by decide +kernel
theorem estimate_legal : Admissible estimate := by
  norm_num [Admissible, estimate, qEstimate, counts, Matrix.cons_val_two, Matrix.cons_val_three]

def lower : ℚ := (508503921308057449804690046268799397576852333174027222538784149147751 / 1361129467683753853853498429727072845824000000000000000000000000000000)
theorem lower_identity : 1-(1-dataFailureFloor estimate.e0 estimate.e1)^horizon = (lower : ℝ) := by
  norm_num [dataFailureFloor, estimate, qEstimate, counts, horizon, lower, Matrix.cons_val_two, Matrix.cons_val_three]
theorem strict_obstacle : (1/5 : ℝ) < lower := by norm_num [lower]

/-- A statistical, Good-conditional obstacle; no hidden true value is read. -/
theorem statistical_no_go (p : Param) (hb : Box p)
    (hg : Good p estimate (1/250))
    (sigma : ∀ n, CausalHistory State State n → PMF Action) (p0 : PMF State) :
    (1/5 : ℝ) < tvDist (causalLaw p0
      (FiniteDataObstacles.allowedKernel p (box_admissible hb) sigma) horizon).toMeasure
      (actualConditionedPrefix (model p (box_admissible hb)) observe baseline initial
        FiniteDataConditioned.safe horizon 0
        (FiniteDataConditioned.source_positive p (box_admissible hb) horizon)).toMeasure := by
  rw [← FiniteDataConditioned.target_eq_actual p (box_admissible hb) horizon]
  have h := FiniteDataObstacles.statistical_path_floor p estimate hb hg sigma p0 horizon
  rw [lower_identity] at h
  exact strict_obstacle.trans_le h

/-- Joint Accept∩Fail bound for the actual ideal training-selection-deployment law.
It is not a conditional-on-acceptance or observed-Good assertion. -/
theorem registered_training_joint_risk (p : Param) (hp : Admissible p) :
    (FiniteDataJoint.jointLaw p hp horizon).toMeasure.real
      {z | z.2 ∈ FiniteDataJoint.acceptedFailure z.1 horizon} ≤ 76/375 :=
  FiniteDataJoint.registered_joint_failure_le p hp horizon (by decide)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataRuntimeCertificate
