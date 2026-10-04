import UEOT.V3.Compression.Objecthood.Homeostasis.CanonicalBurden.CanonicalFaultBurden

namespace UEOT.V3.Compression.Objecthood

open Set MeasureTheory ProbabilityTheory
open UEOT.V3.ViabilityKernel
open scoped ENNReal BigOperators ProbabilityTheory

universe uZ

noncomputable section

variable {Z : Type uZ} [Fintype Z]
variable [MeasurableSpace Z] [MeasurableSingletonClass Z]
local instance leastFaultBurdenDecidableEq : DecidableEq Z := Classical.decEq Z

theorem canonicalFaultBurden_le_certificate
    (S : RecurrentHomeostasisSystem Z)
    (C : FaultBurdenCertificate S) :
    canonicalFaultBurden S ≤ C.burden := by
  classical
  unfold canonicalFaultBurden
  apply Finset.sup_le
  intro z hzuniv
  by_cases hz : z ∈ S.carrier
  · simp only [hz, if_true]
    unfold faultExcess
    rw [tsub_le_iff_right]
    simpa [add_comm] using C.fault_expectation_bound hz
  · simp [hz]

theorem canonicalFaultBurdenCertificate_minimal
    (S : RecurrentHomeostasisSystem Z)
    (hW : ∀ w, w ∈ S.carrier → S.potential w ≠ ∞)
    (C : FaultBurdenCertificate S) :
    (canonicalFaultBurdenCertificate S hW).burden ≤ C.burden := by
  exact canonicalFaultBurden_le_certificate S C

noncomputable def canonicalBurdenStrictWitnessSystem :
    RecurrentHomeostasisSystem Bool where
  legitimate := Set.univ
  carrier := Set.univ
  repairKernel := fun z => PMF.pure z
  faultKernel := fun z => PMF.pure z
  faultHazard := 1 / 2
  faultHazard_le_one := by norm_num
  potential := fun z => if z then 1 else 0
  repairDrift := 1
  repairDrift_ne_zero := by norm_num
  repairDrift_ne_top := by simp
  legitimate_subset_carrier := Set.Subset.rfl
  repair_stays_carrier := by
    intro z hz y hy
    trivial
  fault_stays_carrier := by
    intro z hz y hy
    trivial

theorem canonicalBurdenStrictWitness_canonical_eq_zero :
    canonicalFaultBurden canonicalBurdenStrictWitnessSystem = 0 := by
  classical
  simp [canonicalFaultBurden, faultExcess,
    canonicalBurdenStrictWitnessSystem, lintegral_fintype]

noncomputable def canonicalBurdenStrictWitnessOldCertificate :
    FaultBurdenCertificate canonicalBurdenStrictWitnessSystem :=
  faultBurdenCertificateOfUniformBound
    canonicalBurdenStrictWitnessSystem
    1
    (by simp)
    (by
      intro z hz
      cases z <;> simp [canonicalBurdenStrictWitnessSystem])

@[simp] theorem canonicalBurdenStrictWitnessOldCertificate_burden :
    canonicalBurdenStrictWitnessOldCertificate.burden = 1 := by
  rfl

theorem canonicalBurdenStrictWitness_strict :
    (canonicalFaultBurdenCertificate canonicalBurdenStrictWitnessSystem
      (by
        intro z hz
        cases z <;> simp [canonicalBurdenStrictWitnessSystem])).burden <
      canonicalBurdenStrictWitnessOldCertificate.burden := by
  change canonicalFaultBurden canonicalBurdenStrictWitnessSystem < 1
  rw [canonicalBurdenStrictWitness_canonical_eq_zero]
  norm_num

end
end UEOT.V3.Compression.Objecthood
