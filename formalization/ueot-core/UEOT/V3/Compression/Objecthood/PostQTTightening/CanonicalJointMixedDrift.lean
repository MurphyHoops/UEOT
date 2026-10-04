import UEOT.V3.Compression.Objecthood.Homeostasis.FiniteHorizonHomeostasis
import UEOT.V3.Compression.Objecthood.Homeostasis.CanonicalBurden.CanonicalFaultBurden

/-!
# Post-QT tightening — canonical joint mixed-drift residual

RH/QT first bound repair and fault contributions separately and then combine the
resulting worst-case constants.  The finite-horizon telescope, however, only
needs one statewise mixed-kernel drift inequality.  This module therefore
canonicalizes that actual mixed inequality directly.

For a fixed damaged-occupation coefficient `kappa`, the canonical residual is

the largest positive statewise excess

`E_{mixed(z)} W + kappa * 1_damaged(z) - W(z)`

over the declared carrier.  It is the least uniform `lambda` that makes the
mixed-drift inequality valid on that carrier.
-/

namespace UEOT.V3.Compression.Objecthood

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators ProbabilityTheory

universe uZ

noncomputable section

variable {Z : Type uZ} [Fintype Z]
variable [MeasurableSpace Z] [MeasurableSingletonClass Z]
local instance canonicalJointMixedDriftDecidableEq : DecidableEq Z := Classical.decEq Z

/-- Positive part of the actual one-step mixed-drift excess at one state for a
chosen damaged-occupation coefficient `kappa`. -/
noncomputable def jointMixedDriftExcess
    (S : RecurrentHomeostasisSystem Z) (kappa : ENNReal) (z : Z) : ENNReal :=
  (homeostaticENNExpectation (S.mixedKernel z) S.potential +
      kappa * damagedIndicatorENNReal S.legitimate z) - S.potential z

/-- Least uniform residual for the fixed-`kappa` mixed-drift inequality on the
system's declared carrier. -/
noncomputable def canonicalJointMixedDriftResidual
    (S : RecurrentHomeostasisSystem Z) (kappa : ENNReal) : ENNReal := by
  classical
  exact Finset.univ.sup (fun z =>
    if z ∈ S.carrier then jointMixedDriftExcess S kappa z else 0)

omit [MeasurableSingletonClass Z] in
/-- Every carrier-state excess is dominated by the canonical residual. -/
theorem jointMixedDriftExcess_le_canonical
    (S : RecurrentHomeostasisSystem Z) (kappa : ENNReal)
    {z : Z} (hz : z ∈ S.carrier) :
    jointMixedDriftExcess S kappa z ≤
      canonicalJointMixedDriftResidual S kappa := by
  classical
  unfold canonicalJointMixedDriftResidual
  have h := Finset.le_sup
    (s := Finset.univ)
    (f := fun z => if z ∈ S.carrier then jointMixedDriftExcess S kappa z else 0)
    (Finset.mem_univ z)
  simpa [hz] using h

omit [MeasurableSingletonClass Z] in
/-- The canonical residual itself certifies the mixed-drift inequality. -/
theorem mixedDrift_le_potential_add_canonicalJointResidual
    (S : RecurrentHomeostasisSystem Z) (kappa : ENNReal)
    {z : Z} (hz : z ∈ S.carrier) :
    homeostaticENNExpectation (S.mixedKernel z) S.potential +
        kappa * damagedIndicatorENNReal S.legitimate z ≤
      S.potential z + canonicalJointMixedDriftResidual S kappa := by
  let lhs := homeostaticENNExpectation (S.mixedKernel z) S.potential +
    kappa * damagedIndicatorENNReal S.legitimate z
  have hbase : lhs ≤ S.potential z + (lhs - S.potential z) := le_add_tsub
  have hex : lhs - S.potential z ≤ canonicalJointMixedDriftResidual S kappa := by
    simpa [lhs, jointMixedDriftExcess] using
      jointMixedDriftExcess_le_canonical S kappa hz
  exact hbase.trans (by
    simpa [add_comm] using add_le_add_left hex (S.potential z))

omit [MeasurableSingletonClass Z] in
/-- Minimality: any uniform residual satisfying the same fixed-`kappa`
carrier-wise mixed-drift inequality is at least the canonical residual. -/
theorem canonicalJointMixedDriftResidual_le_of_bound
    (S : RecurrentHomeostasisSystem Z) (kappa lambda : ENNReal)
    (hbound : ∀ z, z ∈ S.carrier →
      homeostaticENNExpectation (S.mixedKernel z) S.potential +
          kappa * damagedIndicatorENNReal S.legitimate z ≤
        S.potential z + lambda) :
    canonicalJointMixedDriftResidual S kappa ≤ lambda := by
  classical
  unfold canonicalJointMixedDriftResidual
  apply Finset.sup_le
  intro z hzuniv
  by_cases hz : z ∈ S.carrier
  · simp only [hz, if_true]
    unfold jointMixedDriftExcess
    rw [tsub_le_iff_right]
    simpa [add_comm] using hbound z hz
  · simp [hz]

/-- If the potential is finite on the carrier and `kappa` is finite, then the
canonical joint residual is finite as well. -/
theorem canonicalJointMixedDriftResidual_ne_top
    (S : RecurrentHomeostasisSystem Z) (kappa : ENNReal)
    (hW : ∀ z, z ∈ S.carrier → S.potential z ≠ ∞)
    (hkappa : kappa ≠ ∞) :
    canonicalJointMixedDriftResidual S kappa ≠ ∞ := by
  rw [← lt_top_iff_ne_top]
  unfold canonicalJointMixedDriftResidual
  rw [Finset.sup_lt_iff (by simp)]
  intro z hzuniv
  by_cases hz : z ∈ S.carrier
  · simp only [hz, if_true]
    rw [lt_top_iff_ne_top]
    unfold jointMixedDriftExcess
    apply ENNReal.sub_ne_top
    apply ENNReal.add_ne_top.2
    constructor
    · exact homeostaticENNExpectation_ne_top_of_staysIn
        (S.mixedKernel z) S.carrier S.potential
        (S.mixed_stays_carrier hz) hW
    · apply ENNReal.mul_ne_top hkappa
      classical
      by_cases hleg : z ∈ S.legitimate <;>
        simp [damagedIndicatorENNReal, hleg]
  · simp [hz]

/-- The old RH2 separated repair/fault certificate is a feasible point of the
new fixed-`kappa` problem.  Therefore direct mixed-drift canonicalization can
never produce a larger residual. -/
theorem canonicalJointMixedDriftResidual_le_faultCertificateEnvelope
    (S : RecurrentHomeostasisSystem Z)
    (C : FaultBurdenCertificate S)
    (hQ : ∀ z, z ∈ S.carrier →
      homeostaticENNExpectation (S.repairKernel z) S.potential +
          S.damagePenalty z ≤ S.potential z) :
    canonicalJointMixedDriftResidual S
        (((1 - S.faultHazard : NNReal) : ENNReal) * S.repairDrift) ≤
      (S.faultHazard : ENNReal) * C.burden := by
  apply canonicalJointMixedDriftResidual_le_of_bound
  intro z hz
  exact mixedHomeostaticDrift_indicator S C hz (hQ z hz)

/-- In particular, direct mixed-drift canonicalization is no worse than the
already canonical QT fault-burden envelope. -/
theorem canonicalJointMixedDriftResidual_le_canonicalFaultEnvelope
    (S : RecurrentHomeostasisSystem Z)
    (hW : ∀ z, z ∈ S.carrier → S.potential z ≠ ∞)
    (hQ : ∀ z, z ∈ S.carrier →
      homeostaticENNExpectation (S.repairKernel z) S.potential +
          S.damagePenalty z ≤ S.potential z) :
    canonicalJointMixedDriftResidual S
        (((1 - S.faultHazard : NNReal) : ENNReal) * S.repairDrift) ≤
      (S.faultHazard : ENNReal) * canonicalFaultBurden S := by
  simpa [canonicalFaultBurdenCertificate] using
    canonicalJointMixedDriftResidual_le_faultCertificateEnvelope
      S (canonicalFaultBurdenCertificate S hW) hQ

end
end UEOT.V3.Compression.Objecthood
