import UEOT.V3.Compression.Objecthood.Homeostasis.MixedHomeostaticDrift
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Track O / RH3 — finite-horizon and mean damaged occupation

Carrier-aware PMF marginals turn the RH2 one-step drift budget into a
finite-horizon occupation telescope and an asymptotic mean damaged-occupation
bound. No invariant-law, irreducibility, or mixing assumption is used here.
-/

namespace UEOT.V3.Compression.Objecthood

open Set MeasureTheory ProbabilityTheory Filter Topology
open UEOT.V3.ViabilityKernel
open UEOT.V3.Compression.CrossTrack
open scoped ENNReal BigOperators ProbabilityTheory

universe uZ uX uA
noncomputable section

variable {Z : Type uZ} [Fintype Z]
variable [MeasurableSpace Z] [MeasurableSingletonClass Z]

noncomputable def homeostaticENNExpectation
    (p : PMF Z) (W : Z → ENNReal) : ENNReal :=
  ∫⁻ y, W y ∂p.toMeasure

theorem homeostaticENNExpectation_eq_sum
    (p : PMF Z) (W : Z → ENNReal) :
    homeostaticENNExpectation p W = ∑ y, W y * p y := by
  unfold homeostaticENNExpectation
  rw [lintegral_countable', tsum_fintype]
  apply Finset.sum_congr rfl
  intro y _
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton y)]

theorem homeostaticENNExpectation_bind
    (mu : PMF Z) (H : Z → PMF Z) (W : Z → ENNReal) :
    homeostaticENNExpectation (mu.bind H) W =
      ∑ z, mu z * homeostaticENNExpectation (H z) W := by
  rw [homeostaticENNExpectation_eq_sum]
  simp_rw [PMF.bind_apply, tsum_fintype]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [homeostaticENNExpectation_eq_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

noncomputable def damagedIndicatorENNReal
    (L : Set Z) (z : Z) : ENNReal := by
  classical
  exact if z ∈ L then 0 else 1

theorem homeostaticENNExpectation_damagedIndicator
    (mu : PMF Z) (L : Set Z) :
    homeostaticENNExpectation mu (damagedIndicatorENNReal L) =
      mu.toMeasure Lᶜ := by
  classical
  have hL : MeasurableSet L := (Set.toFinite L).measurableSet
  unfold homeostaticENNExpectation damagedIndicatorENNReal
  have hfun : (fun z : Z => if z ∈ L then (0 : ENNReal) else 1) =
      Lᶜ.indicator (fun _z : Z => (1 : ENNReal)) := by
    funext z
    by_cases hz : z ∈ L <;> simp [hz]
  rw [hfun, lintegral_indicator hL.compl]
  simp

/-- Integrate a pointwise drift inequality that is required only on the support
carrier of the current PMF. -/
theorem pmf_oneStep_drift_on_carrier
    (mu : PMF Z) (H : Z → PMF Z) (B : Set Z)
    (W damaged : Z → ENNReal) (kappa lambda : ENNReal)
    (hmu : StaysIn mu B)
    (hpoint : ∀ z, z ∈ B →
      homeostaticENNExpectation (H z) W + kappa * damaged z ≤
        W z + lambda) :
    homeostaticENNExpectation (mu.bind H) W +
        kappa * homeostaticENNExpectation mu damaged ≤
      homeostaticENNExpectation mu W + lambda := by
  rw [homeostaticENNExpectation_bind]
  rw [homeostaticENNExpectation_eq_sum, homeostaticENNExpectation_eq_sum]
  have hmass : ∑ z, mu z = 1 := by
    simpa [tsum_fintype] using PMF.tsum_coe mu
  have hsum :
      ∑ z, mu z *
          (homeostaticENNExpectation (H z) W + kappa * damaged z) ≤
        ∑ z, mu z * (W z + lambda) := by
    apply Finset.sum_le_sum
    intro z hz
    by_cases hzB : z ∈ B
    · exact mul_le_mul_of_nonneg_left (hpoint z hzB) bot_le
    · have hzNS : z ∉ mu.support := fun hzs => hzB (hmu hzs)
      have hzero : mu z = 0 := by
        simpa [PMF.mem_support_iff] using hzNS
      simp [hzero]
  calc
    (∑ z, mu z * homeostaticENNExpectation (H z) W) +
        kappa * (∑ z, damaged z * mu z) =
      (∑ z, mu z * homeostaticENNExpectation (H z) W) +
        ∑ z, mu z * (kappa * damaged z) := by
          apply congrArg₂ (· + ·) rfl
          calc
            kappa * ∑ z, damaged z * mu z =
                ∑ z, kappa * (damaged z * mu z) := by rw [Finset.mul_sum]
            _ = ∑ z, mu z * (kappa * damaged z) := by
              apply Finset.sum_congr rfl
              intro z hz
              ring
    _ = ∑ z, (mu z * homeostaticENNExpectation (H z) W +
        mu z * (kappa * damaged z)) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ z, mu z *
        (homeostaticENNExpectation (H z) W + kappa * damaged z) := by
          apply Finset.sum_congr rfl
          intro z hz
          ring
    _ ≤ ∑ z, mu z * (W z + lambda) := hsum
    _ = (∑ z, W z * mu z) + lambda := by
      rw [show (∑ z, mu z * (W z + lambda)) =
          (∑ z, mu z * W z) + ∑ z, mu z * lambda by
            simp_rw [mul_add]
            rw [Finset.sum_add_distrib]]
      have hW : ∑ z, mu z * W z = ∑ z, W z * mu z := by
        apply Finset.sum_congr rfl
        intro z hz
        ac_rfl
      rw [hW]
      calc
        (∑ z, W z * mu z) + ∑ z, mu z * lambda =
            (∑ z, W z * mu z) + (∑ z, mu z) * lambda := by
              rw [Finset.sum_mul]
        _ = (∑ z, W z * mu z) + lambda := by rw [hmass, one_mul]

noncomputable def homeostaticMarginal
    (H : Z → PMF Z) (mu0 : PMF Z) (n : ℕ) : PMF Z :=
  stationaryStateLaw (fun z (_ : Unit) => H z) (fun _ => ()) mu0 n

@[simp] theorem homeostaticMarginal_zero
    (H : Z → PMF Z) (mu0 : PMF Z) :
    homeostaticMarginal H mu0 0 = mu0 := rfl

@[simp] theorem homeostaticMarginal_succ
    (H : Z → PMF Z) (mu0 : PMF Z) (n : ℕ) :
    homeostaticMarginal H mu0 (n + 1) =
      (homeostaticMarginal H mu0 n).bind H := by
  simp [homeostaticMarginal, stationaryStateLaw_succ]

theorem homeostaticMarginal_staysIn
    (H : Z → PMF Z) (mu0 : PMF Z) (B : Set Z)
    (hmu0 : StaysIn mu0 B)
    (hH : ∀ z ∈ B, StaysIn (H z) B) :
    ∀ n, StaysIn (homeostaticMarginal H mu0 n) B := by
  intro n
  simpa [homeostaticMarginal] using
    (stationaryStateLaw_staysIn
      (P := fun z (_ : Unit) => H z) (π := fun _ => ())
      B mu0 hmu0 (by
        intro z hz
        simpa using hH z hz) n)

/-- No-subtraction ENNReal telescope retaining the terminal potential. -/
theorem ennreal_homeostatic_drift_telescope
    (V D : ℕ → ENNReal) (kappa lambda : ENNReal)
    (hstep : ∀ n, V (n + 1) + kappa * D n ≤ V n + lambda) :
    ∀ N, V N + kappa * (∑ n ∈ Finset.range N, D n) ≤
      V 0 + (N : ENNReal) * lambda := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      have hs := hstep N
      rw [Finset.sum_range_succ]
      calc
        V (N + 1) + kappa * (∑ n ∈ Finset.range N, D n + D N) =
          (V (N + 1) + kappa * D N) +
            kappa * (∑ n ∈ Finset.range N, D n) := by ring
        _ ≤ (V N + lambda) + kappa * (∑ n ∈ Finset.range N, D n) :=
          add_le_add hs (le_refl _)
        _ = (V N + kappa * (∑ n ∈ Finset.range N, D n)) + lambda := by ring
        _ ≤ (V 0 + (N : ENNReal) * lambda) + lambda :=
          add_le_add ih (le_refl lambda)
        _ = V 0 + ((N + 1 : ℕ) : ENNReal) * lambda := by
          push_cast
          ring

/-- Carrier-aware finite-horizon damaged-occupation bound. -/
theorem finiteHorizonDamagedOccupation_on_carrier
    (H : Z → PMF Z) (mu0 : PMF Z) (B L : Set Z)
    (W : Z → ENNReal) (kappa lambda : ENNReal)
    (hmu0 : StaysIn mu0 B)
    (hH : ∀ z ∈ B, StaysIn (H z) B)
    (hpoint : ∀ z, z ∈ B →
      homeostaticENNExpectation (H z) W +
          kappa * damagedIndicatorENNReal L z ≤ W z + lambda)
    (N : ℕ) :
    kappa * (∑ n ∈ Finset.range N,
        (homeostaticMarginal H mu0 n).toMeasure Lᶜ) ≤
      homeostaticENNExpectation mu0 W + (N : ENNReal) * lambda := by
  let V : ℕ → ENNReal :=
    fun n => homeostaticENNExpectation (homeostaticMarginal H mu0 n) W
  let D : ℕ → ENNReal :=
    fun n => (homeostaticMarginal H mu0 n).toMeasure Lᶜ
  have hstep : ∀ n, V (n + 1) + kappa * D n ≤ V n + lambda := by
    intro n
    have hmuN := homeostaticMarginal_staysIn H mu0 B hmu0 hH n
    have h := pmf_oneStep_drift_on_carrier
      (homeostaticMarginal H mu0 n) H B W
      (damagedIndicatorENNReal L) kappa lambda hmuN hpoint
    rw [← homeostaticMarginal_succ H mu0 n] at h
    rw [homeostaticENNExpectation_damagedIndicator] at h
    exact h
  have htel := ennreal_homeostatic_drift_telescope V D kappa lambda hstep N
  have hdrop :
      kappa * (∑ n ∈ Finset.range N, D n) ≤
        V N + kappa * (∑ n ∈ Finset.range N, D n) := by
    exact le_add_self
  exact hdrop.trans (by simpa [V, D] using htel)

theorem damagePenalty_eq_repairDrift_mul_indicator
    (S : RecurrentHomeostasisSystem Z) (z : Z) :
    S.damagePenalty z =
      S.repairDrift * damagedIndicatorENNReal S.legitimate z := by
  classical
  by_cases hz : z ∈ S.legitimate <;>
    simp [RecurrentHomeostasisSystem.damagePenalty,
      damagedIndicatorENNReal, hz]

theorem mixedHomeostaticDrift_indicator
    (S : RecurrentHomeostasisSystem Z)
    (C : FaultBurdenCertificate S)
    {z : Z} (hz : z ∈ S.carrier)
    (hQ :
      homeostaticENNExpectation (S.repairKernel z) S.potential +
          S.damagePenalty z ≤ S.potential z) :
    homeostaticENNExpectation (S.mixedKernel z) S.potential +
        (((1 - S.faultHazard : NNReal) : ENNReal) * S.repairDrift) *
          damagedIndicatorENNReal S.legitimate z ≤
      S.potential z + (S.faultHazard : ENNReal) * C.burden := by
  have h := mixedHomeostaticDrift S C hz hQ
  rw [damagePenalty_eq_repairDrift_mul_indicator S z] at h
  simpa [homeostaticENNExpectation, mul_assoc] using h

theorem RecurrentHomeostasisSystem.finiteHorizonDamagedOccupation
    (S : RecurrentHomeostasisSystem Z)
    (C : FaultBurdenCertificate S)
    (mu0 : PMF Z) (hmu0 : StaysIn mu0 S.carrier)
    (hQ : ∀ z, z ∈ S.carrier →
      homeostaticENNExpectation (S.repairKernel z) S.potential +
          S.damagePenalty z ≤ S.potential z)
    (N : ℕ) :
    (((1 - S.faultHazard : NNReal) : ENNReal) * S.repairDrift) *
        (∑ n ∈ Finset.range N,
          (homeostaticMarginal S.mixedKernel mu0 n).toMeasure
            S.legitimateᶜ) ≤
      homeostaticENNExpectation mu0 S.potential +
        (N : ENNReal) * ((S.faultHazard : ENNReal) * C.burden) := by
  apply finiteHorizonDamagedOccupation_on_carrier
    S.mixedKernel mu0 S.carrier S.legitimate S.potential
    (((1 - S.faultHazard : NNReal) : ENNReal) * S.repairDrift)
    ((S.faultHazard : ENNReal) * C.burden)
    hmu0
    (fun z hz => S.mixed_stays_carrier hz)
    (fun z hz => mixedHomeostaticDrift_indicator S C hz (hQ z hz))
    N


/-- Finite expectation follows from support inside a carrier on which the
potential is pointwise finite. -/
theorem homeostaticENNExpectation_ne_top_of_staysIn
    (mu : PMF Z) (B : Set Z) (W : Z → ENNReal)
    (hmu : StaysIn mu B)
    (hW : ∀ z, z ∈ B → W z ≠ ∞) :
    homeostaticENNExpectation mu W ≠ ∞ := by
  rw [homeostaticENNExpectation_eq_sum, ENNReal.sum_ne_top]
  intro z hz
  by_cases hzB : z ∈ B
  · exact ENNReal.mul_ne_top (hW z hzB) (PMF.apply_ne_top mu z)
  · have hzNS : z ∉ mu.support := fun hzs => hzB (hmu hzs)
    have hzero : mu z = 0 := by
      simpa [PMF.mem_support_iff] using hzNS
    simp [hzero]

/-- RH3 Objecthood specialization on the full GCR-complete carrier. -/
theorem objecthood_finiteHorizonDamagedOccupation
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
    (mu0 : PMF (ConstitutiveState X A))
    (hmu0 : StaysIn mu0 (gcrHomeostaticCarrier P K))
    (N : ℕ) :
    let S := objecthoodRecurrentHomeostasisSystem
      P K hfix F epsilon hepsilon hF
    (((1 - epsilon : NNReal) : ENNReal) * S.repairDrift) *
        (∑ n ∈ Finset.range N,
          (homeostaticMarginal S.mixedKernel mu0 n).toMeasure
            S.legitimateᶜ) ≤
      homeostaticENNExpectation mu0 S.potential +
        (N : ENNReal) * ((epsilon : ENNReal) * C.burden) := by
  let S := objecthoodRecurrentHomeostasisSystem
    P K hfix F epsilon hepsilon hF
  apply S.finiteHorizonDamagedOccupation C mu0 hmu0
  intro z hz
  have hpen :
      S.damagePenalty z = autonomousRepairDamagePenalty P K z := by
    classical
    simp [S, RecurrentHomeostasisSystem.damagePenalty,
      objecthoodRecurrentHomeostasisSystem,
      autonomousRepairDamagePenalty]
  rw [hpen]
  change
    homeostaticENNExpectation
        (autonomousRepairLift P K hfix
          (maximalStationaryRepairCertificate P K) z ())
        (autonomousRepairPotential P K
          (maximalStationaryRepairCertificate P K)) +
      autonomousRepairDamagePenalty P K z ≤
    autonomousRepairPotential P K
      (maximalStationaryRepairCertificate P K) z
  simpa [homeostaticENNExpectation] using
    autonomousRepair_global_drift_budget P K hfix z

/-- Real finite-horizon mean bound extracted from an ENNReal occupation budget. -/
theorem real_average_bound_of_ennreal_homeostatic_budget
    (D : ℕ → ENNReal) (kappa lambda V0 : ENNReal)
    (hDtop : ∀ n, D n ≠ ∞)
    (hk0 : kappa ≠ 0) (hktop : kappa ≠ ∞)
    (hlamtop : lambda ≠ ∞) (hVtop : V0 ≠ ∞)
    (N : ℕ) (hN : 0 < N)
    (hbound : kappa * (∑ n ∈ Finset.range N, D n) ≤
      V0 + (N : ENNReal) * lambda) :
    ((N : ℝ)⁻¹) * (∑ n ∈ Finset.range N, (D n).toReal) ≤
      V0.toReal / ((N : ℝ) * kappa.toReal) +
        lambda.toReal / kappa.toReal := by
  have hsumtop : (∑ n ∈ Finset.range N, D n) ≠ ∞ := by
    rw [ENNReal.sum_ne_top]
    intro n hn
    exact hDtop n
  have hlefttop : kappa * (∑ n ∈ Finset.range N, D n) ≠ ∞ :=
    ENNReal.mul_ne_top hktop hsumtop
  have hNtop : ((N : ENNReal) ≠ ∞) := by simp
  have hNlamtop : (N : ENNReal) * lambda ≠ ∞ :=
    ENNReal.mul_ne_top hNtop hlamtop
  have hrighttop : V0 + (N : ENNReal) * lambda ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨hVtop, hNlamtop⟩
  have hreal :
      (kappa * (∑ n ∈ Finset.range N, D n)).toReal ≤
        (V0 + (N : ENNReal) * lambda).toReal :=
    (ENNReal.toReal_le_toReal hlefttop hrighttop).2 hbound
  rw [ENNReal.toReal_mul] at hreal
  rw [ENNReal.toReal_sum (fun n hn => hDtop n)] at hreal
  rw [ENNReal.toReal_add hVtop hNlamtop] at hreal
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hreal
  have hkpos : 0 < kappa.toReal := ENNReal.toReal_pos hk0 hktop
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hNkpos : 0 < (N : ℝ) * kappa.toReal := mul_pos hNreal hkpos
  calc
    ((N : ℝ)⁻¹) * (∑ n ∈ Finset.range N, (D n).toReal) =
        (kappa.toReal * (∑ n ∈ Finset.range N, (D n).toReal)) /
          ((N : ℝ) * kappa.toReal) := by field_simp
    _ ≤ (V0.toReal + (N : ℝ) * lambda.toReal) /
          ((N : ℝ) * kappa.toReal) :=
      (div_le_div_iff_of_pos_right hNkpos).2 hreal
    _ = V0.toReal / ((N : ℝ) * kappa.toReal) +
          lambda.toReal / kappa.toReal := by field_simp

noncomputable def realDamageAverage
    (D : ℕ → ENNReal) (n : ℕ) : ℝ :=
  (((n + 1 : ℕ) : ℝ)⁻¹) *
    ∑ t ∈ Finset.range (n + 1), (D t).toReal

theorem mean_homeostasis_of_ennreal_budget
    (D : ℕ → ENNReal) (kappa lambda V0 : ENNReal)
    (hDtop : ∀ n, D n ≠ ∞)
    (hk0 : kappa ≠ 0) (hktop : kappa ≠ ∞)
    (hlamtop : lambda ≠ ∞) (hVtop : V0 ≠ ∞)
    (hbound : ∀ N, kappa * (∑ n ∈ Finset.range N, D n) ≤
      V0 + (N : ENNReal) * lambda) :
    ∀ eta > 0, ∀ᶠ n in atTop,
      realDamageAverage D n ≤ lambda.toReal / kappa.toReal + eta := by
  have hkpos : 0 < kappa.toReal := ENNReal.toReal_pos hk0 hktop
  have hden : Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * kappa.toReal)
      atTop atTop := by
    have hn : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
      exact (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
    exact hn.atTop_mul_const hkpos
  have hstartup : Tendsto
      (fun n : ℕ => V0.toReal /
        (((n + 1 : ℕ) : ℝ) * kappa.toReal))
      atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop hden V0.toReal
  intro eta heta
  have hev : ∀ᶠ n in atTop,
      V0.toReal / (((n + 1 : ℕ) : ℝ) * kappa.toReal) < eta :=
    hstartup.eventually (Iio_mem_nhds heta)
  filter_upwards [hev] with n hn
  have havg := real_average_bound_of_ennreal_homeostatic_budget
    D kappa lambda V0 hDtop hk0 hktop hlamtop hVtop
    (n + 1) (Nat.succ_pos n) (hbound (n + 1))
  change realDamageAverage D n ≤ lambda.toReal / kappa.toReal + eta
  unfold realDamageAverage
  exact havg.trans (by linarith)

/-- RH3 asymptotic mean occupation bound.  The strict hazard condition is used
only to make the certified repair capacity nonzero. -/
theorem RecurrentHomeostasisSystem.eventually_realDamageAverage_le
    (S : RecurrentHomeostasisSystem Z)
    (C : FaultBurdenCertificate S)
    (mu0 : PMF Z) (hmu0 : StaysIn mu0 S.carrier)
    (hQ : ∀ z, z ∈ S.carrier →
      homeostaticENNExpectation (S.repairKernel z) S.potential +
          S.damagePenalty z ≤ S.potential z)
    (hPotentialTop : ∀ z, z ∈ S.carrier → S.potential z ≠ ∞)
    (hhazard : S.faultHazard < 1) :
    let D : ℕ → ENNReal := fun n =>
      (homeostaticMarginal S.mixedKernel mu0 n).toMeasure S.legitimateᶜ
    let kappa : ENNReal :=
      ((1 - S.faultHazard : NNReal) : ENNReal) * S.repairDrift
    let lambda : ENNReal := (S.faultHazard : ENNReal) * C.burden
    ∀ eta > 0, ∀ᶠ n in atTop,
      realDamageAverage D n ≤ lambda.toReal / kappa.toReal + eta := by
  dsimp
  let D : ℕ → ENNReal := fun n =>
    (homeostaticMarginal S.mixedKernel mu0 n).toMeasure S.legitimateᶜ
  let kappa : ENNReal :=
    ((1 - S.faultHazard : NNReal) : ENNReal) * S.repairDrift
  let lambda : ENNReal := (S.faultHazard : ENNReal) * C.burden
  let V0 : ENNReal := homeostaticENNExpectation mu0 S.potential
  have hsubpos : 0 < (1 - S.faultHazard : NNReal) :=
    tsub_pos_iff_lt.mpr hhazard
  have hsub0 : ((1 - S.faultHazard : NNReal) : ENNReal) ≠ 0 := by
    exact_mod_cast (ne_of_gt hsubpos)
  have hk0 : kappa ≠ 0 := by
    exact mul_ne_zero hsub0 S.repairDrift_ne_zero
  have hktop : kappa ≠ ∞ := by
    exact ENNReal.mul_ne_top (by simp) S.repairDrift_ne_top
  have hlamtop : lambda ≠ ∞ := by
    exact ENNReal.mul_ne_top (by simp) C.burden_ne_top
  have hVtop : V0 ≠ ∞ := by
    exact homeostaticENNExpectation_ne_top_of_staysIn
      mu0 S.carrier S.potential hmu0 hPotentialTop
  have hDtop : ∀ n, D n ≠ ∞ := by
    intro n
    exact MeasureTheory.measure_ne_top _ _
  apply mean_homeostasis_of_ennreal_budget
    D kappa lambda V0 hDtop hk0 hktop hlamtop hVtop
  intro N
  simpa [D, kappa, lambda, V0] using
    S.finiteHorizonDamagedOccupation C mu0 hmu0 hQ N


/-- RH3 Objecthood mean-homeostasis corollary. The only extra scalar condition
is epsilon < 1, ensuring strictly positive certified repair capacity. -/
theorem objecthood_eventually_realDamageAverage_le
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (F : ConstitutiveState X A → PMF (ConstitutiveState X A))
    (epsilon : NNReal) (hepsilon : epsilon ≤ 1) (hepsilon_lt : epsilon < 1)
    (hF : ∀ ⦃z : ConstitutiveState X A⦄,
      z ∈ gcrHomeostaticCarrier P K →
        StaysIn (F z) (gcrHomeostaticCarrier P K))
    (C : FaultBurdenCertificate
      (objecthoodRecurrentHomeostasisSystem
        P K hfix F epsilon hepsilon hF))
    (mu0 : PMF (ConstitutiveState X A))
    (hmu0 : StaysIn mu0 (gcrHomeostaticCarrier P K)) :
    let S := objecthoodRecurrentHomeostasisSystem
      P K hfix F epsilon hepsilon hF
    let D : ℕ → ENNReal := fun n =>
      (homeostaticMarginal S.mixedKernel mu0 n).toMeasure S.legitimateᶜ
    let kappa : ENNReal := ((1 - epsilon : NNReal) : ENNReal) * S.repairDrift
    let lambda : ENNReal := (epsilon : ENNReal) * C.burden
    ∀ eta > 0, ∀ᶠ n in atTop,
      realDamageAverage D n ≤ lambda.toReal / kappa.toReal + eta := by
  let S := objecthoodRecurrentHomeostasisSystem
    P K hfix F epsilon hepsilon hF
  apply S.eventually_realDamageAverage_le C mu0 hmu0
  · intro z hz
    have hpen :
        S.damagePenalty z = autonomousRepairDamagePenalty P K z := by
      classical
      simp [S, RecurrentHomeostasisSystem.damagePenalty,
        objecthoodRecurrentHomeostasisSystem,
        autonomousRepairDamagePenalty]
    rw [hpen]
    change
      homeostaticENNExpectation
          (autonomousRepairLift P K hfix
            (maximalStationaryRepairCertificate P K) z ())
          (autonomousRepairPotential P K
            (maximalStationaryRepairCertificate P K)) +
        autonomousRepairDamagePenalty P K z ≤
      autonomousRepairPotential P K
        (maximalStationaryRepairCertificate P K) z
    simpa [homeostaticENNExpectation] using
      autonomousRepair_global_drift_budget P K hfix z
  · intro z hz
    exact autonomousRepairPotential_ne_top_on_gcrHomeostaticCarrier
      P K hfix hz
  · simpa [S, objecthoodRecurrentHomeostasisSystem] using hepsilon_lt


end
end UEOT.V3.Compression.Objecthood
