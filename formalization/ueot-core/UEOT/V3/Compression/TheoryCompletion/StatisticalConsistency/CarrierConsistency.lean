import UEOT.V3.Compression.TheoryCompletion.StatisticalConsistency.PredictiveConsistency
import UEOT.V3.CoreOperationalAssembly
import Mathlib.Tactic

namespace UEOT.V3.Compression.TheoryCompletion.StatisticalConsistency

open Filter Topology MeasureTheory
open UEOT.V3.TotalVariation
open UEOT.V3.StatisticalDefect
open UEOT.V3.CoreOperationalAssembly

universe uV uH uI uR uY

noncomputable def positiveDefectFallback
    {V : Type uV} (e : Finset V → ℝ) (S : Finset V) : ℝ :=
  if e S = 0 then 1 else e S

noncomputable def canonicalPositiveDefectGap
    {V : Type uV} [Fintype V] (e : Finset V → ℝ) : ℝ :=
  (Finset.univ : Finset (Finset V)).inf'
    ⟨∅, Finset.mem_univ ∅⟩
    (positiveDefectFallback e)

theorem positiveDefectFallback_pos
    {V : Type uV} (e : Finset V → ℝ)
    (hnonneg : ∀ S, 0 ≤ e S) (S : Finset V) :
    0 < positiveDefectFallback e S := by
  unfold positiveDefectFallback
  split_ifs with hz
  · norm_num
  · exact lt_of_le_of_ne (hnonneg S) (Ne.symm hz)

theorem canonicalPositiveDefectGap_pos
    {V : Type uV} [Fintype V]
    (e : Finset V → ℝ) (hnonneg : ∀ S, 0 ≤ e S) :
    0 < canonicalPositiveDefectGap e := by
  classical
  unfold canonicalPositiveDefectGap
  obtain ⟨S, _hS, hmin⟩ := Finset.exists_mem_eq_inf'
    (show (Finset.univ : Finset (Finset V)).Nonempty from
      ⟨∅, Finset.mem_univ ∅⟩)
    (positiveDefectFallback e)
  rw [hmin]
  exact positiveDefectFallback_pos e hnonneg S

theorem canonicalPositiveDefectGap_le_of_pos
    {V : Type uV} [Fintype V]
    (e : Finset V → ℝ) {S : Finset V} (hS : 0 < e S) :
    canonicalPositiveDefectGap e ≤ e S := by
  classical
  have hle : canonicalPositiveDefectGap e ≤ positiveDefectFallback e S := by
    unfold canonicalPositiveDefectGap
    exact Finset.inf'_le _ (Finset.mem_univ S)
  have hne : e S ≠ 0 := ne_of_gt hS
  simpa [positiveDefectFallback, hne] using hle

theorem eventually_exact_carrier_recovery
    {V : Type uV} [Fintype V] [DecidableEq V]
    {H : Type uH} [Nonempty H]
    {I : Type uI} [Nonempty I]
    {R : Type uR} {Y : Type uY} [MeasurableSpace Y]
    (readout : Finset V → H → R)
    (p : H → I → Measure Y)
    (pHat : ℕ → H → I → Measure Y)
    (hp : ∀ h i, IsProbabilityMeasure (p h i))
    (hpHat : ∀ n h i, IsProbabilityMeasure (pHat n h i))
    (η : ℕ → ℝ) (hη : Tendsto η atTop (𝓝 0))
    (hresp : ∀ n h i, tvDist (p h i) (pHat n h i) ≤ η n) :
    let Δ := canonicalPositiveDefectGap (responseDefect readout p)
    ∀ᶠ n in atTop,
      estimatedCarrierFamily readout (pHat n) (Δ / 2) =
        exactCarrierFamily readout p := by
  dsimp only
  let Δ := canonicalPositiveDefectGap (responseDefect readout p)
  have hnonneg : ∀ S, 0 ≤ responseDefect readout p S :=
    responseDefect_nonneg readout p hp
  have hΔ : 0 < Δ := canonicalPositiveDefectGap_pos _ hnonneg
  filter_upwards [eventually_two_mul_lt_half hη hΔ] with n hsmall
  have hdefect := p_stat_02 readout p (pHat n) hp (hpHat n) (η n) (hresp n)
  have hgap : ∀ S, 0 < responseDefect readout p S →
      Δ ≤ responseDefect readout p S := by
    intro S hS
    exact canonicalPositiveDefectGap_le_of_pos _ hS
  have hlower : 2 * η n < Δ / 2 := hsmall
  have hupper : Δ / 2 < Δ - 2 * η n := by linarith
  simpa [estimatedCarrierFamily, exactCarrierFamily, Δ] using
    (UEOT.V3.Threshold.exact_family
      (responseDefect readout p)
      (responseDefect readout (pHat n))
      Δ (Δ / 2) (η n)
      hnonneg hdefect hgap hlower hupper)

/-- Exact carrier recovery immediately transports the canonical blocker. -/
theorem eventually_exact_carrier_and_blocker_recovery
    {V : Type uV} [Fintype V] [DecidableEq V]
    {H : Type uH} [Nonempty H]
    {I : Type uI} [Nonempty I]
    {R : Type uR} {Y : Type uY} [MeasurableSpace Y]
    (readout : Finset V → H → R)
    (p : H → I → Measure Y)
    (pHat : ℕ → H → I → Measure Y)
    (hp : ∀ h i, IsProbabilityMeasure (p h i))
    (hpHat : ∀ n h i, IsProbabilityMeasure (pHat n h i))
    (η : ℕ → ℝ) (hη : Tendsto η atTop (𝓝 0))
    (hresp : ∀ n h i, tvDist (p h i) (pHat n h i) ≤ η n) :
    let Δ := canonicalPositiveDefectGap (responseDefect readout p)
    ∀ᶠ n in atTop,
      estimatedCarrierFamily readout (pHat n) (Δ / 2) =
          exactCarrierFamily readout p ∧
      UEOT.Blocker.blocker
          (estimatedCarrierFamily readout (pHat n) (Δ / 2)) =
        UEOT.Blocker.blocker (exactCarrierFamily readout p) := by
  dsimp only
  filter_upwards [eventually_exact_carrier_recovery
    readout p pHat hp hpHat η hη hresp] with n hcarrier
  exact ⟨hcarrier, congrArg UEOT.Blocker.blocker hcarrier⟩

/-- One-source asymptotic response closure.

For finite nonempty histories/protocols and a finite carrier universe, the true
response table canonically supplies both the predictive separation margin and
the positive carrier-defect gap.  Therefore a realized response estimator with
uniform TV error tending to zero eventually recovers predictive classes,
minimal exact carriers, and the corresponding blocker simultaneously. -/
theorem eventually_canonical_response_recovery
    {V : Type uV} [Fintype V] [DecidableEq V]
    {H : Type uH} [Fintype H] [Nonempty H]
    {I : Type uI} [Fintype I] [Nonempty I]
    {R : Type uR} {Y : Type uY} [MeasurableSpace Y]
    (readout : Finset V → H → R)
    (p : H → I → Measure Y)
    (pHat : ℕ → H → I → Measure Y)
    (hp : ∀ h i, IsProbabilityMeasure (p h i))
    (hpHat : ∀ n h i, IsProbabilityMeasure (pHat n h i))
    (η : ℕ → ℝ) (hη : Tendsto η atTop (𝓝 0))
    (hresp : ∀ n h i, tvDist (p h i) (pHat n h i) ≤ η n) :
    let γ := canonicalPredictiveGap p
    let Δ := canonicalPositiveDefectGap (responseDefect readout p)
    ∀ᶠ n in atTop,
      (∀ h h',
        UEOT.V3.PredictiveClassRecovery.protocolDistance (pHat n) h h' ≤ γ / 2 ↔
          UEOT.V3.PredictiveClassRecovery.trueEquivalent p h h') ∧
      estimatedCarrierFamily readout (pHat n) (Δ / 2) =
        exactCarrierFamily readout p ∧
      UEOT.Blocker.blocker
          (estimatedCarrierFamily readout (pHat n) (Δ / 2)) =
        UEOT.Blocker.blocker (exactCarrierFamily readout p) := by
  dsimp only
  let γ := canonicalPredictiveGap p
  let Δ := canonicalPositiveDefectGap (responseDefect readout p)
  have hγ : 0 < γ := canonicalPredictiveGap_pos p hp
  have hnonneg : ∀ S, 0 ≤ responseDefect readout p S :=
    responseDefect_nonneg readout p hp
  have hΔ : 0 < Δ := canonicalPositiveDefectGap_pos _ hnonneg
  filter_upwards
      [eventually_two_mul_lt_half hη hγ,
       eventually_two_mul_lt_half hη hΔ] with n hpredSmall hcarrierSmall
  have hcarrierGap : ∀ S, 0 < responseDefect readout p S →
      Δ ≤ responseDefect readout p S := by
    intro S hS
    exact canonicalPositiveDefectGap_le_of_pos _ hS
  have hupper : Δ / 2 < Δ - 2 * η n := by linarith
  exact response_recovery_on_good_event
    readout p (pHat n) hp (hpHat n)
    (η n) γ Δ (Δ / 2) (hresp n)
    (fun _ _ hne => canonicalPredictiveGap_le p hne)
    hpredSmall hcarrierGap hcarrierSmall hupper

end UEOT.V3.Compression.TheoryCompletion.StatisticalConsistency
