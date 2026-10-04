import UEOT.V3.Compression.Objecthood.Homeostasis.FaultBurden

namespace UEOT.V3.Compression.Objecthood

open Set MeasureTheory ProbabilityTheory
open UEOT.V3.ViabilityKernel
open scoped ENNReal BigOperators ProbabilityTheory

universe uZ
noncomputable section

variable {Z : Type uZ} [Fintype Z]
variable [MeasurableSpace Z] [MeasurableSingletonClass Z]
local instance canonicalFaultBurdenDecidableEq : DecidableEq Z := Classical.decEq Z

noncomputable def faultExcess
    (S : RecurrentHomeostasisSystem Z) (z : Z) : ENNReal :=
  (∫⁻ w, S.potential w ∂(S.faultKernel z).toMeasure) - S.potential z

noncomputable def canonicalFaultBurden
    (S : RecurrentHomeostasisSystem Z) : ENNReal := by
  classical
  exact Finset.univ.sup (fun z =>
    if z ∈ S.carrier then faultExcess S z else 0)

theorem faultExpectation_ne_top_of_carrierPotentialFinite
    (S : RecurrentHomeostasisSystem Z)
    (hW : ∀ w, w ∈ S.carrier → S.potential w ≠ ∞)
    {z : Z} (hz : z ∈ S.carrier) :
    (∫⁻ w, S.potential w ∂(S.faultKernel z).toMeasure) ≠ ∞ := by
  rw [lintegral_fintype, ENNReal.sum_ne_top]
  intro w hw
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton w)]
  by_cases hwB : w ∈ S.carrier
  · exact ENNReal.mul_ne_top (hW w hwB) (PMF.apply_ne_top (S.faultKernel z) w)
  · have hwNS : w ∉ (S.faultKernel z).support :=
      fun hws => hwB (S.fault_stays_carrier hz hws)
    have hw0 : S.faultKernel z w = 0 := by
      simpa [PMF.mem_support_iff] using hwNS
    simp [hw0]

theorem faultExcess_ne_top_of_carrierPotentialFinite
    (S : RecurrentHomeostasisSystem Z)
    (hW : ∀ w, w ∈ S.carrier → S.potential w ≠ ∞)
    {z : Z} (hz : z ∈ S.carrier) :
    faultExcess S z ≠ ∞ := by
  unfold faultExcess
  exact ENNReal.sub_ne_top
    (faultExpectation_ne_top_of_carrierPotentialFinite S hW hz)

theorem canonicalFaultBurden_ne_top_of_carrierPotentialFinite
    (S : RecurrentHomeostasisSystem Z)
    (hW : ∀ w, w ∈ S.carrier → S.potential w ≠ ∞) :
    canonicalFaultBurden S ≠ ∞ := by
  rw [← lt_top_iff_ne_top]
  unfold canonicalFaultBurden
  rw [Finset.sup_lt_iff (by simp)]
  intro z hzuniv
  by_cases hz : z ∈ S.carrier
  · simp only [hz, if_true]
    exact (lt_top_iff_ne_top).2
      (faultExcess_ne_top_of_carrierPotentialFinite S hW hz)
  · simp [hz]

omit [MeasurableSingletonClass Z] in
theorem faultExcess_le_canonicalFaultBurden
    (S : RecurrentHomeostasisSystem Z) {z : Z}
    (hz : z ∈ S.carrier) :
    faultExcess S z ≤ canonicalFaultBurden S := by
  classical
  unfold canonicalFaultBurden
  have h := Finset.le_sup
    (s := Finset.univ)
    (f := fun z => if z ∈ S.carrier then faultExcess S z else 0)
    (Finset.mem_univ z)
  simpa [hz] using h

omit [MeasurableSingletonClass Z] in
theorem faultExpectation_le_potential_add_canonicalFaultBurden
    (S : RecurrentHomeostasisSystem Z) {z : Z}
    (hz : z ∈ S.carrier) :
    (∫⁻ w, S.potential w ∂(S.faultKernel z).toMeasure) ≤
      S.potential z + canonicalFaultBurden S := by
  have hbase :
      (∫⁻ w, S.potential w ∂(S.faultKernel z).toMeasure) ≤
        S.potential z +
          ((∫⁻ w, S.potential w ∂(S.faultKernel z).toMeasure) -
            S.potential z) := le_add_tsub
  have hex :
      ((∫⁻ w, S.potential w ∂(S.faultKernel z).toMeasure) -
          S.potential z) ≤ canonicalFaultBurden S := by
    simpa [faultExcess] using faultExcess_le_canonicalFaultBurden S hz
  exact hbase.trans (by
    simpa [add_comm] using add_le_add_left hex (S.potential z))

noncomputable def canonicalFaultBurdenCertificate
    (S : RecurrentHomeostasisSystem Z)
    (hW : ∀ w, w ∈ S.carrier → S.potential w ≠ ∞) :
    FaultBurdenCertificate S where
  burden := canonicalFaultBurden S
  burden_ne_top :=
    canonicalFaultBurden_ne_top_of_carrierPotentialFinite S hW
  fault_expectation_bound := by
    intro z hz
    exact faultExpectation_le_potential_add_canonicalFaultBurden S hz


end
end UEOT.V3.Compression.Objecthood
