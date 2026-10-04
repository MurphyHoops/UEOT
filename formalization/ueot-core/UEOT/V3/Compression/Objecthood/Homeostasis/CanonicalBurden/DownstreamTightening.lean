import UEOT.V3.Compression.Objecthood.Homeostasis.CanonicalBurden.LeastFaultBurden
import UEOT.V3.Compression.Objecthood.Homeostasis.CertifiedHomeostaticMargin

namespace UEOT.V3.Compression.Objecthood

open scoped ENNReal

universe uZ

noncomputable section

variable {Z : Type uZ} [Fintype Z]
variable [MeasurableSpace Z] [MeasurableSingletonClass Z]

/-- The canonical certificate's real burden is no larger than any admissible
fault-burden certificate after ENNReal-to-real conversion. -/
theorem canonicalFaultBurden_toReal_le_certificate
    (S : RecurrentHomeostasisSystem Z)
    (hW : ∀ z, z ∈ S.carrier → S.potential z ≠ ∞)
    (C : FaultBurdenCertificate S) :
    (canonicalFaultBurdenCertificate S hW).burden.toReal ≤ C.burden.toReal := by
  exact ENNReal.toReal_mono C.burden_ne_top
    (canonicalFaultBurden_le_certificate S C)

/-- Canonical burden never increases the certified real fault load. -/
theorem canonical_faultLoadReal_le
    (S : RecurrentHomeostasisSystem Z)
    (hW : ∀ z, z ∈ S.carrier → S.potential z ≠ ∞)
    (C : FaultBurdenCertificate S) :
    faultLoadReal S.faultHazard (canonicalFaultBurdenCertificate S hW).burden ≤
      faultLoadReal S.faultHazard C.burden := by
  unfold faultLoadReal
  exact mul_le_mul_of_nonneg_left
    (canonicalFaultBurden_toReal_le_certificate S hW C)
    (by positivity)

/-- Under positive repair capacity, the canonical certificate never increases
the homeostatic load ratio. -/
theorem homeostaticLoadRatioReal_canonical_le
    (S : RecurrentHomeostasisSystem Z)
    (hW : ∀ z, z ∈ S.carrier → S.potential z ≠ ∞)
    (C : FaultBurdenCertificate S)
    (hhazard : S.faultHazard < 1) :
    homeostaticLoadRatioReal S.faultHazard S.repairDrift
        (canonicalFaultBurdenCertificate S hW).burden ≤
      homeostaticLoadRatioReal S.faultHazard S.repairDrift C.burden := by
  unfold homeostaticLoadRatioReal
  exact div_le_div_of_nonneg_right
    (canonical_faultLoadReal_le S hW C)
    (le_of_lt (repairCapacityReal_pos S.faultHazard S.repairDrift
      hhazard S.repairDrift_ne_zero S.repairDrift_ne_top))

/-- Canonical burden can only improve the certified homeostatic margin. -/
theorem homeostaticMarginReal_le_canonical
    (S : RecurrentHomeostasisSystem Z)
    (hW : ∀ z, z ∈ S.carrier → S.potential z ≠ ∞)
    (C : FaultBurdenCertificate S) :
    homeostaticMarginReal S.faultHazard S.repairDrift C.burden ≤
      homeostaticMarginReal S.faultHazard S.repairDrift
        (canonicalFaultBurdenCertificate S hW).burden := by
  unfold homeostaticMarginReal
  have hload := canonical_faultLoadReal_le S hW C
  linarith

/-- Any positive margin already certified by an arbitrary burden remains
positive after replacing it by the canonical least burden. -/
theorem canonical_homeostaticMarginReal_pos_of_certificate
    (S : RecurrentHomeostasisSystem Z)
    (hW : ∀ z, z ∈ S.carrier → S.potential z ≠ ∞)
    (C : FaultBurdenCertificate S)
    (hpos : 0 < homeostaticMarginReal
      S.faultHazard S.repairDrift C.burden) :
    0 < homeostaticMarginReal S.faultHazard S.repairDrift
      (canonicalFaultBurdenCertificate S hW).burden := by
  exact lt_of_lt_of_le hpos (homeostaticMarginReal_le_canonical S hW C)

/-- The exact real ratio appearing in RH3/RH4 damaged-occupation bounds is
monotone in the fault burden, hence canonicalization never worsens it. -/
theorem canonical_rhCertifiedRatio_le
    (S : RecurrentHomeostasisSystem Z)
    (hW : ∀ z, z ∈ S.carrier → S.potential z ≠ ∞)
    (C : FaultBurdenCertificate S) :
    ((S.faultHazard : ENNReal) *
        (canonicalFaultBurdenCertificate S hW).burden).toReal /
        (((1 - S.faultHazard : NNReal) : ENNReal) * S.repairDrift).toReal ≤
      ((S.faultHazard : ENNReal) * C.burden).toReal /
        (((1 - S.faultHazard : NNReal) : ENNReal) * S.repairDrift).toReal := by
  have hburden :
      (canonicalFaultBurdenCertificate S hW).burden ≤ C.burden :=
    canonicalFaultBurden_le_certificate S C
  have hnum :
      (S.faultHazard : ENNReal) *
          (canonicalFaultBurdenCertificate S hW).burden ≤
        (S.faultHazard : ENNReal) * C.burden :=
    mul_le_mul_of_nonneg_left hburden bot_le
  have hnumTop :
      (S.faultHazard : ENNReal) * C.burden ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) C.burden_ne_top
  have hnumReal :
      ((S.faultHazard : ENNReal) *
          (canonicalFaultBurdenCertificate S hW).burden).toReal ≤
        ((S.faultHazard : ENNReal) * C.burden).toReal :=
    ENNReal.toReal_mono hnumTop hnum
  exact div_le_div_of_nonneg_right hnumReal ENNReal.toReal_nonneg

end
end UEOT.V3.Compression.Objecthood
