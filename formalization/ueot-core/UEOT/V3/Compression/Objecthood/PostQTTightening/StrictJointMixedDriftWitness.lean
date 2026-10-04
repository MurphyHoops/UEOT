import UEOT.V3.Compression.Objecthood.PostQTTightening.CanonicalJointMixedDrift
import UEOT.V3.Compression.Objecthood.Homeostasis.CanonicalBurden.LeastFaultBurden

/-!
# Post-QT tightening — strict joint mixed-drift witness

A three-state finite system demonstrates that direct canonicalization of the
mixed drift is genuinely sharper than separately canonicalizing the fault
burden.  The repair and fault worst cases are anti-correlated across states:
repair slack exactly absorbs the only positive fault excess in the actual
mixture.
-/

namespace UEOT.V3.Compression.Objecthood

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators ProbabilityTheory

noncomputable section

inductive JointMixedDriftWitnessState
  | low
  | nominal
  | damaged
  deriving DecidableEq

local instance jointWitnessFintype : Fintype JointMixedDriftWitnessState where
  elems := {JointMixedDriftWitnessState.low,
    JointMixedDriftWitnessState.nominal,
    JointMixedDriftWitnessState.damaged}
  complete := by
    intro z
    cases z <;> simp

open JointMixedDriftWitnessState

local instance jointWitnessMeasurableSpace : MeasurableSpace JointMixedDriftWitnessState := ⊤
local instance jointWitnessMeasurableSingleton :
    MeasurableSingletonClass JointMixedDriftWitnessState :=
  ⟨fun _ => by change True; trivial⟩

noncomputable def jointMixedDriftStrictWitnessSystem :
    RecurrentHomeostasisSystem JointMixedDriftWitnessState where
  legitimate := {low, nominal}
  carrier := Set.univ
  repairKernel
    | low => PMF.pure low
    | nominal => PMF.pure low
    | damaged => PMF.pure nominal
  faultKernel
    | low => PMF.pure low
    | nominal => PMF.pure damaged
    | damaged => PMF.pure damaged
  faultHazard := 1 / 2
  faultHazard_le_one := by norm_num
  potential
    | low => 0
    | nominal => 1
    | damaged => 2
  repairDrift := 1
  repairDrift_ne_zero := by norm_num
  repairDrift_ne_top := by simp
  legitimate_subset_carrier := Set.subset_univ _
  repair_stays_carrier := by
    intro z hz y hy
    trivial
  fault_stays_carrier := by
    intro z hz y hy
    trivial

/-- The witness satisfies the same repair-side drift premise used by RH2. -/
theorem jointMixedDriftStrictWitness_repair_budget :
    ∀ z, z ∈ jointMixedDriftStrictWitnessSystem.carrier →
      homeostaticENNExpectation
          (jointMixedDriftStrictWitnessSystem.repairKernel z)
          jointMixedDriftStrictWitnessSystem.potential +
        jointMixedDriftStrictWitnessSystem.damagePenalty z ≤
      jointMixedDriftStrictWitnessSystem.potential z := by
  intro z hz
  cases z <;>
    simp [jointMixedDriftStrictWitnessSystem,
      RecurrentHomeostasisSystem.damagePenalty,
      homeostaticENNExpectation, lintegral_fintype] <;>
    norm_num

/-- A unit RH1 fault certificate for the witness. -/
noncomputable def jointMixedDriftStrictWitnessUnitFaultCertificate :
    FaultBurdenCertificate jointMixedDriftStrictWitnessSystem where
  burden := 1
  burden_ne_top := by simp
  fault_expectation_bound := by
    intro z hz
    cases z <;>
      simp [jointMixedDriftStrictWitnessSystem, lintegral_fintype] <;>
      norm_num

/-- The separately canonicalized QT fault burden is exactly one. -/
theorem jointMixedDriftStrictWitness_canonicalFaultBurden_eq_one :
    canonicalFaultBurden jointMixedDriftStrictWitnessSystem = 1 := by
  apply le_antisymm
  · exact canonicalFaultBurden_le_certificate
      jointMixedDriftStrictWitnessSystem
      jointMixedDriftStrictWitnessUnitFaultCertificate
  · have h := faultExcess_le_canonicalFaultBurden
      jointMixedDriftStrictWitnessSystem
      (z := nominal) (by simp [jointMixedDriftStrictWitnessSystem])
    have hex : faultExcess jointMixedDriftStrictWitnessSystem nominal = 1 := by
      simp [faultExcess, jointMixedDriftStrictWitnessSystem, lintegral_fintype]
      change (2 : ENNReal) - 1 = 1
      calc
        (2 : ENNReal) - 1 = (1 + 1) - 1 := by norm_num
        _ = 1 := by simpa using add_tsub_cancel_right (1 : ENNReal) 1
    rw [hex] at h
    exact h

/-- At the RH damaged-occupation coefficient, the actual mixed drift has zero
uniform residual in the same witness. -/
theorem jointMixedDriftStrictWitness_jointResidual_eq_zero :
    canonicalJointMixedDriftResidual jointMixedDriftStrictWitnessSystem
      (((1 - jointMixedDriftStrictWitnessSystem.faultHazard : NNReal) : ENNReal) *
        jointMixedDriftStrictWitnessSystem.repairDrift) = 0 := by
  apply le_antisymm
  · apply canonicalJointMixedDriftResidual_le_of_bound
    intro z hz
    cases z with
    | low =>
        unfold homeostaticENNExpectation
        rw [RecurrentHomeostasisSystem.mixedKernel, recurrentFaultMix_lintegral]
        simp [jointMixedDriftStrictWitnessSystem, lintegral_fintype,
          damagedIndicatorENNReal]
    | nominal =>
        unfold homeostaticENNExpectation
        rw [RecurrentHomeostasisSystem.mixedKernel, recurrentFaultMix_lintegral]
        simp [jointMixedDriftStrictWitnessSystem, lintegral_fintype,
          damagedIndicatorENNReal]
    | damaged =>
        unfold homeostaticENNExpectation
        rw [RecurrentHomeostasisSystem.mixedKernel, recurrentFaultMix_lintegral]
        simp [jointMixedDriftStrictWitnessSystem, lintegral_fintype,
          damagedIndicatorENNReal]
        have hmul : (2 : ENNReal)⁻¹ * 2 = 1 := by
          rw [ENNReal.inv_mul_cancel]
          · norm_num
          · simp
        rw [hmul]
        have heq : (2 : ENNReal)⁻¹ + 1 + (2 : ENNReal)⁻¹ = 2 := by
          calc
            (2 : ENNReal)⁻¹ + 1 + (2 : ENNReal)⁻¹ =
                ((2 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹) + 1 := by ac_rfl
            _ = 1 + 1 := by rw [ENNReal.inv_two_add_inv_two]
            _ = 2 := by norm_num
        exact heq.le
  · exact bot_le

/-- Strict separation from QT: the state-coupled joint residual is strictly
smaller than the canonical separated fault envelope. -/
theorem jointMixedDriftStrictWitness_strict :
    canonicalJointMixedDriftResidual jointMixedDriftStrictWitnessSystem
        (((1 - jointMixedDriftStrictWitnessSystem.faultHazard : NNReal) : ENNReal) *
          jointMixedDriftStrictWitnessSystem.repairDrift) <
      (jointMixedDriftStrictWitnessSystem.faultHazard : ENNReal) *
        canonicalFaultBurden jointMixedDriftStrictWitnessSystem := by
  rw [jointMixedDriftStrictWitness_jointResidual_eq_zero,
    jointMixedDriftStrictWitness_canonicalFaultBurden_eq_one]
  norm_num [jointMixedDriftStrictWitnessSystem]

end
end UEOT.V3.Compression.Objecthood
