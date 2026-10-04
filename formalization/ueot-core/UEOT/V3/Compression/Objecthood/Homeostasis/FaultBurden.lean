import UEOT.V3.Compression.Objecthood.Homeostasis.RecurrentFaultSystem

/-!
# Track O / RH1 — finite fault-burden certificate

Fault-side burden is isolated from repair mixing and long-run occupation.
-/

namespace UEOT.V3.Compression.Objecthood

open Set MeasureTheory ProbabilityTheory
open UEOT.V3.ViabilityKernel
open UEOT.V3.Compression.CrossTrack
open scoped ENNReal BigOperators ProbabilityTheory

universe uZ uX uA
noncomputable section

/-- RH1 fault-side burden certificate.  It deliberately contains no repair
mixture or long-run conclusion. -/
structure FaultBurdenCertificate
    {Z : Type uZ} [Fintype Z]
    [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (S : RecurrentHomeostasisSystem Z) where
  burden : ENNReal
  burden_ne_top : burden ≠ ∞
  fault_expectation_bound :
    ∀ ⦃z : Z⦄, z ∈ S.carrier →
      (∫⁻ w, S.potential w ∂(S.faultKernel z).toMeasure) ≤
        S.potential z + burden

/-- A uniform finite carrier bound yields a valid finite fault burden for every
fault kernel whose support stays in the carrier. -/
noncomputable def faultBurdenCertificateOfUniformBound
    {Z : Type uZ} [Fintype Z]
    [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (S : RecurrentHomeostasisSystem Z)
    (M : ENNReal) (hMtop : M ≠ ∞)
    (hM : ∀ z, z ∈ S.carrier → S.potential z ≤ M) :
    FaultBurdenCertificate S where
  burden := M
  burden_ne_top := hMtop
  fault_expectation_bound := by
    intro z hz
    have hExp :
        (∫⁻ w, S.potential w ∂(S.faultKernel z).toMeasure) ≤ M := by
      rw [lintegral_fintype]
      simp_rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]
      calc
        (∑ w, S.potential w * S.faultKernel z w) ≤
            ∑ w, M * S.faultKernel z w := by
          apply Finset.sum_le_sum
          intro w hw
          by_cases hwB : w ∈ S.carrier
          · exact mul_le_mul_of_nonneg_right (hM w hwB) bot_le
          · have hwNS : w ∉ (S.faultKernel z).support :=
              fun hws => hwB (S.fault_stays_carrier hz hws)
            have hw0 : S.faultKernel z w = 0 := by
              simpa [PMF.mem_support_iff] using hwNS
            simp [hw0]
        _ = M * ∑ w, S.faultKernel z w := by
          rw [Finset.mul_sum]
        _ = M := by
          have hsum : ∑ w, S.faultKernel z w = 1 := by
            simpa [tsum_fintype] using PMF.tsum_coe (S.faultKernel z)
          rw [hsum, mul_one]
    exact le_trans hExp (le_add_left (le_refl M))

/-- The GCR homeostatic carrier admits one finite uniform bound on the existing
autonomous repair potential. -/
theorem exists_finite_uniform_gcrHomeostaticPotential_bound
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K) :
    ∃ M : ENNReal, M ≠ ∞ ∧
      ∀ z : ConstitutiveState X A,
        z ∈ gcrHomeostaticCarrier P K →
          autonomousRepairPotential P K
            (maximalStationaryRepairCertificate P K) z ≤ M := by
  classical
  let W : ConstitutiveState X A → ENNReal :=
    autonomousRepairPotential P K (maximalStationaryRepairCertificate P K)
  let B : Set (ConstitutiveState X A) := gcrHomeostaticCarrier P K
  let M : ENNReal := ∑ z : ConstitutiveState X A, if z ∈ B then W z else 0
  refine ⟨M, ?_, ?_⟩
  · unfold M
    rw [ENNReal.sum_ne_top]
    intro z hzuniv
    by_cases hzB : z ∈ B
    · simp only [hzB, if_true]
      exact autonomousRepairPotential_ne_top_on_gcrHomeostaticCarrier
        P K hfix hzB
    · simp [hzB]
  · intro z hz
    unfold M
    have hterm :
        (if z ∈ B then W z else 0) ≤
          ∑ y : ConstitutiveState X A, if y ∈ B then W y else 0 := by
      exact Finset.single_le_sum
        (s := Finset.univ)
        (f := fun y : ConstitutiveState X A => if y ∈ B then W y else 0)
        (fun y hy =>
          (show (0 : ENNReal) ≤ (if y ∈ B then W y else 0) from bot_le))
        (Finset.mem_univ z)
    simpa [hz, W, B] using hterm

/-- Every recurrent-fault Objecthood system satisfying RH0 fault-support closure
has a finite RH1 fault-burden certificate. -/
theorem nonempty_objecthoodFaultBurdenCertificate
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (F : ConstitutiveState X A → PMF (ConstitutiveState X A))
    (epsilon : NNReal) (hepsilon : epsilon ≤ 1)
    (hF : ∀ ⦃z : ConstitutiveState X A⦄,
      z ∈ gcrHomeostaticCarrier P K →
        StaysIn (F z) (gcrHomeostaticCarrier P K)) :
    Nonempty (FaultBurdenCertificate
      (objecthoodRecurrentHomeostasisSystem
        P K hfix F epsilon hepsilon hF)) := by
  obtain ⟨M, hMtop, hM⟩ :=
    exists_finite_uniform_gcrHomeostaticPotential_bound P K hfix
  let S := objecthoodRecurrentHomeostasisSystem
    P K hfix F epsilon hepsilon hF
  exact ⟨faultBurdenCertificateOfUniformBound S M hMtop (by
    intro z hz
    exact hM z hz)⟩


end
end UEOT.V3.Compression.Objecthood
