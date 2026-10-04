import UEOT.V3.Compression.Objecthood.Homeostasis.CanonicalBurden.DownstreamTightening

/-!
# Post-QT tightening — canonical RH certificate optimality

QT proved that the canonical fault burden is least among all RH1
`FaultBurdenCertificate`s for one fixed recurrent-homeostasis system and fixed
potential. This module closes the immediate order-theoretic consequences at the
actual homeostatic-margin interface.

The result is deliberately certificate-relative: it does not optimize over
repair potentials, repair laws, carriers, fault kernels, or parent selection.
-/

namespace UEOT.V3.Compression.Objecthood

open Set
open scoped ENNReal

universe uZ

noncomputable section

/-- For a fixed recurrent-homeostasis system and fixed potential, the canonical
certificate detects exactly whether the existing RH1 certificate class can
certify a strictly positive homeostatic margin. -/
theorem canonical_homeostaticMarginReal_pos_iff_exists_certificate
    {Z : Type uZ} [Fintype Z]
    [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (S : RecurrentHomeostasisSystem Z)
    (hW : ∀ z, z ∈ S.carrier → S.potential z ≠ ∞) :
    0 < homeostaticMarginReal S.faultHazard S.repairDrift
        (canonicalFaultBurdenCertificate S hW).burden ↔
      ∃ C : FaultBurdenCertificate S,
        0 < homeostaticMarginReal S.faultHazard S.repairDrift C.burden := by
  constructor
  · intro h
    exact ⟨canonicalFaultBurdenCertificate S hW, h⟩
  · rintro ⟨C, hC⟩
    exact canonical_homeostaticMarginReal_pos_of_certificate S hW C hC

/-- The canonical certificate attains the greatest certified homeostatic margin
inside the existing RH1 certificate class for the same system and potential. -/
theorem canonical_homeostaticMarginReal_isGreatest
    {Z : Type uZ} [Fintype Z]
    [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (S : RecurrentHomeostasisSystem Z)
    (hW : ∀ z, z ∈ S.carrier → S.potential z ≠ ∞) :
    IsGreatest
      {m : ℝ | ∃ C : FaultBurdenCertificate S,
        m = homeostaticMarginReal S.faultHazard S.repairDrift C.burden}
      (homeostaticMarginReal S.faultHazard S.repairDrift
        (canonicalFaultBurdenCertificate S hW).burden) := by
  constructor
  · exact ⟨canonicalFaultBurdenCertificate S hW, rfl⟩
  · intro m hm
    rcases hm with ⟨C, rfl⟩
    exact homeostaticMarginReal_le_canonical S hW C

end
end UEOT.V3.Compression.Objecthood
