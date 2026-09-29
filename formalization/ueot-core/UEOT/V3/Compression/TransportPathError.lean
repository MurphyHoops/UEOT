import UEOT.V3.Compression.TransportCertificate
import UEOT.V3.PathError

/-!
# P-DYN-03 specialization of the transport/certificate calculus

This file keeps the domain-specific finite-PMF/common-mass bridge out of the
generic transport meta layer.  The sharp path-TV product bound is reconstructed
by specializing `multiplicative_chain_lower_bound`; all coupling/TV facts remain
explicit source adapters.
-/

namespace UEOT.V3.Compression.TransportCertificate

open scoped BigOperators

universe uHist

/-- Full frozen P-DYN-03 product-plus-union-bound statement reconstructed
through the generic multiplicative certificate recurrence.

The compression layer contributes only the abstract product recurrence.
Finite-PMF common mass, the one-step TV-to-overlap estimate, the exact
TV/common-mass identity, and the product-to-sum union bound remain explicit
domain adapters from the source layer.  No source assumption is strengthened. -/
theorem p_dyn_03_via_multiplicative_chain
    {H₀ Z : Type uHist}
    [Fintype H₀] [Fintype Z]
    [MeasurableSpace H₀] [MeasurableSingletonClass H₀]
    [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (p₀ : PMF H₀)
    (K L : ∀ n, UEOT.V3.PathError.CausalHistory H₀ Z n → PMF Z)
    (ε : ℕ → ℝ)
    (hε0 : ∀ n, 0 ≤ ε n)
    (hε1 : ∀ n, ε n ≤ 1)
    (hTV : ∀ n h,
      UEOT.V3.TotalVariation.tvDist (K n h).toMeasure (L n h).toMeasure ≤ ε n) :
    ∀ T,
      UEOT.V3.TotalVariation.tvDist
          (UEOT.V3.PathError.causalLaw p₀ K T).toMeasure
          (UEOT.V3.PathError.causalLaw p₀ L T).toMeasure
        ≤ 1 - (∏ i ∈ Finset.range T, (1 - ε i)) ∧
      1 - (∏ i ∈ Finset.range T, (1 - ε i))
        ≤ ∑ i ∈ Finset.range T, ε i := by
  intro T
  constructor
  · rw [UEOT.V3.PathError.tvDist_eq_one_sub_pmfCommonMass]
    have hcommon :
        (∏ i ∈ Finset.range T, (1 - ε i)) ≤
          UEOT.V3.PathError.pmfCommonMass
            (UEOT.V3.PathError.causalLaw p₀ K T)
            (UEOT.V3.PathError.causalLaw p₀ L T) := by
      apply multiplicative_chain_lower_bound
        (factor := fun n => 1 - ε n)
        (survival := fun n =>
          UEOT.V3.PathError.pmfCommonMass
            (UEOT.V3.PathError.causalLaw p₀ K n)
            (UEOT.V3.PathError.causalLaw p₀ L n))
      · intro n
        exact sub_nonneg.mpr (hε1 n)
      · change 1 ≤ UEOT.V3.PathError.pmfCommonMass p₀ p₀
        rw [UEOT.V3.PathError.pmfCommonMass_self]
      · intro n
        change
          UEOT.V3.PathError.pmfCommonMass
              (UEOT.V3.PathError.causalLaw p₀ K n)
              (UEOT.V3.PathError.causalLaw p₀ L n) *
              (1 - ε n) ≤
            UEOT.V3.PathError.pmfCommonMass
              (UEOT.V3.PathError.pmfExtend
                (UEOT.V3.PathError.causalLaw p₀ K n) (K n))
              (UEOT.V3.PathError.pmfExtend
                (UEOT.V3.PathError.causalLaw p₀ L n) (L n))
        exact
          UEOT.V3.PathError.pmfCommonMass_extend_of_tv
            (UEOT.V3.PathError.causalLaw p₀ K n)
            (UEOT.V3.PathError.causalLaw p₀ L n)
            (K n) (L n)
            (hε0 n) (hε1 n) (hTV n)
    exact sub_le_sub_left hcommon 1
  · exact
      UEOT.V3.PathError.one_sub_prod_one_sub_le_sum ε hε0 hε1 T

end UEOT.V3.Compression.TransportCertificate
