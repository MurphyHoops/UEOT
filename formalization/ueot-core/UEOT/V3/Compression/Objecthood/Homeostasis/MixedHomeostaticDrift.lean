import UEOT.V3.Compression.Objecthood.Homeostasis.FaultBurden

/-!
# Track O / RH2 — mixed homeostatic drift

This stage combines the explicit RH0 repair/fault PMF mixture with the RH1
finite fault-burden certificate.  No finite-horizon or asymptotic occupation
claim is made here.
-/

namespace UEOT.V3.Compression.Objecthood

open Set MeasureTheory ProbabilityTheory
open UEOT.V3.ViabilityKernel
open UEOT.V3.ViabilityTrajectory
open UEOT.V3.Compression.CrossTrack
open scoped ENNReal BigOperators ProbabilityTheory

universe uZ uX uA
noncomputable section

/-- RH2 damaged-state repair penalty. -/
noncomputable def RecurrentHomeostasisSystem.damagePenalty
    {Z : Type uZ} [Fintype Z]
    (S : RecurrentHomeostasisSystem Z) (z : Z) : ENNReal := by
  classical
  exact if z ∈ S.legitimate then 0 else S.repairDrift

/-- Exact ENNReal expectation decomposition under the explicit repair/fault
mixture. -/
theorem recurrentFaultMix_lintegral
    {Z : Type uZ} [Fintype Z]
    [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (Q F : PMF Z) (epsilon : NNReal) (hepsilon : epsilon ≤ 1)
    (W : Z → ENNReal) :
    (∫⁻ z, W z ∂(recurrentFaultMix Q F epsilon hepsilon).toMeasure) =
      ((1 - epsilon : NNReal) : ENNReal) * (∫⁻ z, W z ∂Q.toMeasure) +
      (epsilon : ENNReal) * (∫⁻ z, W z ∂F.toMeasure) := by
  simp_rw [lintegral_fintype]
  simp_rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]
  simp_rw [recurrentFaultMix_apply]
  rw [Finset.mul_sum, Finset.mul_sum]
  simp_rw [mul_add, ← mul_assoc]
  rw [Finset.sum_add_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro z hz <;> ac_rfl

/-- Generic RH2 mixture theorem.  It assumes only the repair-side one-step drift
budget and the RH1 fault-burden certificate. -/
theorem mixedHomeostaticDrift
    {Z : Type uZ} [Fintype Z]
    [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (S : RecurrentHomeostasisSystem Z)
    (C : FaultBurdenCertificate S)
    {z : Z} (hz : z ∈ S.carrier)
    (hQ :
      (∫⁻ w, S.potential w ∂(S.repairKernel z).toMeasure) +
          S.damagePenalty z ≤ S.potential z) :
    (∫⁻ w, S.potential w ∂(S.mixedKernel z).toMeasure) +
        ((1 - S.faultHazard : NNReal) : ENNReal) * S.damagePenalty z ≤
      S.potential z + (S.faultHazard : ENNReal) * C.burden := by
  rw [RecurrentHomeostasisSystem.mixedKernel]
  rw [recurrentFaultMix_lintegral]
  have hq :
      ((1 - S.faultHazard : NNReal) : ENNReal) *
          ((∫⁻ w, S.potential w ∂(S.repairKernel z).toMeasure) +
            S.damagePenalty z) ≤
        ((1 - S.faultHazard : NNReal) : ENNReal) * S.potential z :=
    mul_le_mul_of_nonneg_left hQ bot_le
  have hf :
      (S.faultHazard : ENNReal) *
          (∫⁻ w, S.potential w ∂(S.faultKernel z).toMeasure) ≤
        (S.faultHazard : ENNReal) * (S.potential z + C.burden) :=
    mul_le_mul_of_nonneg_left (C.fault_expectation_bound hz) bot_le
  calc
    ((1 - S.faultHazard : NNReal) : ENNReal) *
          (∫⁻ w, S.potential w ∂(S.repairKernel z).toMeasure) +
        (S.faultHazard : ENNReal) *
          (∫⁻ w, S.potential w ∂(S.faultKernel z).toMeasure) +
        ((1 - S.faultHazard : NNReal) : ENNReal) * S.damagePenalty z
        =
      ((1 - S.faultHazard : NNReal) : ENNReal) *
          ((∫⁻ w, S.potential w ∂(S.repairKernel z).toMeasure) +
            S.damagePenalty z) +
        (S.faultHazard : ENNReal) *
          (∫⁻ w, S.potential w ∂(S.faultKernel z).toMeasure) := by
            rw [mul_add]
            ac_rfl
    _ ≤ ((1 - S.faultHazard : NNReal) : ENNReal) * S.potential z +
          (S.faultHazard : ENNReal) * (S.potential z + C.burden) :=
      add_le_add hq hf
    _ = S.potential z + (S.faultHazard : ENNReal) * C.burden := by
      rw [mul_add]
      have he :
          ((1 - S.faultHazard : NNReal) : ENNReal) +
              (S.faultHazard : ENNReal) = 1 := by
        rw [ENNReal.coe_sub]
        exact tsub_add_cancel_of_le (by exact_mod_cast S.faultHazard_le_one)
      calc
        ((1 - S.faultHazard : NNReal) : ENNReal) * S.potential z +
            ((S.faultHazard : ENNReal) * S.potential z +
              (S.faultHazard : ENNReal) * C.burden) =
          ((((1 - S.faultHazard : NNReal) : ENNReal) +
              (S.faultHazard : ENNReal)) * S.potential z) +
            (S.faultHazard : ENNReal) * C.burden := by
              rw [add_mul]
              ac_rfl
        _ = S.potential z + (S.faultHazard : ENNReal) * C.burden := by
          rw [he, one_mul]

/-- Objecthood repair-side damaged penalty used by RH2. -/
noncomputable def autonomousRepairDamagePenalty
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X)
    (z : ConstitutiveState X A) : ENNReal := by
  classical
  exact if z ∈ legitimateConstitutiveDomain P K then 0
    else (maximalStationaryRepairCertificate P K).drift

/-- The existing O5 autonomous repair dynamics satisfies a global repair-side
budget: outside legitimacy this is O5 drift, while on legitimate states Q stays
legitimate and W is identically zero. -/
theorem autonomousRepair_global_drift_budget
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (z : ConstitutiveState X A) :
    let R := maximalStationaryRepairCertificate P K
    let Q := autonomousRepairLift P K hfix R z ()
    let W := autonomousRepairPotential P K R
    (∫⁻ w, W w ∂Q.toMeasure) +
        autonomousRepairDamagePenalty P K z ≤ W z := by
  classical
  let R := maximalStationaryRepairCertificate P K
  let Q := autonomousRepairLift P K hfix R z ()
  let W := autonomousRepairPotential P K R
  by_cases hzLeg : z ∈ legitimateConstitutiveDomain P K
  · have hstay := autonomousRepairLift_staysIn_legitimate P K hfix R hzLeg
    have hzero : (∫⁻ w, W w ∂Q.toMeasure) = 0 := by
      rw [lintegral_fintype]
      apply Finset.sum_eq_zero
      intro w hw
      rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton w)]
      by_cases hQw : Q w = 0
      · simp [hQw]
      · have hws : w ∈ Q.support := (PMF.mem_support_iff _ _).2 hQw
        have hwLeg := hstay hws
        have hW0 : W w = 0 := by
          exact autonomousRepairPotential_eq_zero_of_legitimate P K R hwLeg
        simp [hW0]
    have hWz : W z = 0 :=
      autonomousRepairPotential_eq_zero_of_legitimate P K R hzLeg
    change (∫⁻ w, W w ∂Q.toMeasure) +
      autonomousRepairDamagePenalty P K z ≤ W z
    simp [autonomousRepairDamagePenalty, hzLeg, hzero, hWz]
  · have h := autonomousRepair_drift P K hfix R z hzLeg
    change
      (∫⁻ w, W w ∂Q.toMeasure) +
        autonomousRepairDamagePenalty P K z ≤ W z
    simpa [autonomousRepairDamagePenalty, hzLeg, Q, W,
      stationaryKernel_apply] using h

/-- RH2 Objecthood specialization. -/
theorem objecthood_mixedHomeostaticDrift
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
        StaysIn (F z) (gcrHomeostaticCarrier P K))
    (C : FaultBurdenCertificate
      (objecthoodRecurrentHomeostasisSystem
        P K hfix F epsilon hepsilon hF))
    {z : ConstitutiveState X A}
    (hz : z ∈ gcrHomeostaticCarrier P K) :
    let S := objecthoodRecurrentHomeostasisSystem
      P K hfix F epsilon hepsilon hF
    (∫⁻ w, S.potential w ∂(S.mixedKernel z).toMeasure) +
        ((1 - epsilon : NNReal) : ENNReal) * S.damagePenalty z ≤
      S.potential z + (epsilon : ENNReal) * C.burden := by
  let S := objecthoodRecurrentHomeostasisSystem
    P K hfix F epsilon hepsilon hF
  apply mixedHomeostaticDrift S C hz
  have hpen :
      S.damagePenalty z = autonomousRepairDamagePenalty P K z := by
    classical
    simp [S, RecurrentHomeostasisSystem.damagePenalty,
      objecthoodRecurrentHomeostasisSystem,
      autonomousRepairDamagePenalty]
  rw [hpen]
  change
    (∫⁻ w,
      autonomousRepairPotential P K (maximalStationaryRepairCertificate P K) w
        ∂(autonomousRepairLift P K hfix
          (maximalStationaryRepairCertificate P K) z ()).toMeasure) +
      autonomousRepairDamagePenalty P K z ≤
    autonomousRepairPotential P K (maximalStationaryRepairCertificate P K) z
  exact autonomousRepair_global_drift_budget P K hfix z


end
end UEOT.V3.Compression.Objecthood
