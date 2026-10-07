import UEOT.V3.FiniteCandidateDiscovery
import Mathlib.Tactic

/-!
# P4.1 — finite exact candidate recovery

P-STAT-08 gives an excess-risk bound for finite empirical-risk minimization.
Inverse Objecthood needs a stronger conclusion when the declared finite
candidate problem is identifiable: exact recovery of the unique true candidate.

For a finite candidate type and one strict true-risk minimizer, finiteness
itself supplies a canonical positive risk gap.  No independent finite gap is
assumed.  A uniform estimation radius smaller than half this canonical gap
then forces exact ERM selection.

The distinguished minimizer contributes a positive fallback value `1` to the
finite infimum.  This keeps the definition nonvacuous for singleton candidate
families while never strengthening a nontrivial true-risk gap.
-/

namespace UEOT.V3.Compression.TheoryCompletion.InverseObjecthood

open Filter Topology
open UEOT.V3.FiniteCandidateDiscovery

universe uF uOmega

noncomputable section

variable {F : Type uF} [Fintype F] [Nonempty F]
local instance inverseObjecthoodCandidateDecidableEq : DecidableEq F :=
  Classical.decEq F

/-- Canonical finite strict-risk gap around one declared true minimizer. -/
noncomputable def canonicalRiskGap (R : F → ℝ) (fStar : F) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun f => if f = fStar then 1 else R f - R fStar)

/-- A strict unique minimizer gives a strictly positive canonical finite gap. -/
theorem canonicalRiskGap_pos
    (R : F → ℝ) (fStar : F)
    (hStrict : ∀ f, f ≠ fStar → R fStar < R f) :
    0 < canonicalRiskGap R fStar := by
  unfold canonicalRiskGap
  obtain ⟨f, _hf, hmin⟩ := Finset.exists_mem_eq_inf'
    (Finset.univ_nonempty : (Finset.univ : Finset F).Nonempty)
    (fun g => if g = fStar then (1 : ℝ) else R g - R fStar)
  rw [hmin]
  by_cases h : f = fStar
  · simp [h]
  · simp [h, sub_pos.mpr (hStrict f h)]

/-- The canonical gap lower-bounds every non-minimizer's true excess risk. -/
theorem canonicalRiskGap_le_excess
    (R : F → ℝ) (fStar f : F) (hne : f ≠ fStar) :
    canonicalRiskGap R fStar ≤ R f - R fStar := by
  have hle : canonicalRiskGap R fStar ≤
      (if f = fStar then (1 : ℝ) else R f - R fStar) := by
    unfold canonicalRiskGap
    exact Finset.inf'_le _ (Finset.mem_univ f)
  simpa [hne] using hle

/-- Uniform risk estimation upgrades ERM excess-risk control to exact candidate
recovery once twice the estimation radius is below the canonical finite gap. -/
theorem erm_eq_uniqueMinimizer_of_two_radius_lt_canonicalRiskGap
    (R Rhat : F → ℝ)
    (fHat fStar : F)
    (u : ℝ)
    (hERM : ∀ f, Rhat fHat ≤ Rhat f)
    (hStrict : ∀ f, f ≠ fStar → R fStar < R f)
    (hUniform : ∀ f, |Rhat f - R f| ≤ u)
    (hsmall : 2 * u < canonicalRiskGap R fStar) :
    fHat = fStar := by
  by_contra hne
  have hexcess : R fHat ≤ R fStar + 2 * u :=
    erm_excess_le_two_uniform R Rhat fHat fStar u hERM
      (fun f => by
        by_cases h : f = fStar
        · subst f
          exact le_rfl
        · exact (hStrict f h).le)
      hUniform
  have hgap := canonicalRiskGap_le_excess R fStar fHat hne
  linarith

/-- Pointwise data-dependent version: on one simultaneous uniform-risk good
event, the empirical minimizer is exactly the unique true minimizer. -/
theorem erm_event_eq_uniqueMinimizer
    {Omega : Type uOmega}
    (R : F → ℝ)
    (Rhat : Omega → F → ℝ)
    (fHat : Omega → F)
    (fStar : F)
    (u : ℝ)
    (hERM : ∀ omega f, Rhat omega (fHat omega) ≤ Rhat omega f)
    (hStrict : ∀ f, f ≠ fStar → R fStar < R f)
    {omega : Omega}
    (hUniform : ∀ f, |Rhat omega f - R f| ≤ u)
    (hsmall : 2 * u < canonicalRiskGap R fStar) :
    fHat omega = fStar := by
  exact erm_eq_uniqueMinimizer_of_two_radius_lt_canonicalRiskGap
    R (Rhat omega) (fHat omega) fStar u (hERM omega) hStrict hUniform hsmall

/-- Exact-recovery failure is contained in the simultaneous uniform-estimation
bad event.  This is the deterministic event bridge later consumed by P4.5. -/
theorem wrongCandidate_implies_uniformRiskFailure
    {Omega : Type uOmega}
    (R : F → ℝ)
    (Rhat : Omega → F → ℝ)
    (fHat : Omega → F)
    (fStar : F)
    (u : ℝ)
    (hERM : ∀ omega f, Rhat omega (fHat omega) ≤ Rhat omega f)
    (hStrict : ∀ f, f ≠ fStar → R fStar < R f)
    (hsmall : 2 * u < canonicalRiskGap R fStar)
    {omega : Omega}
    (hwrong : fHat omega ≠ fStar) :
    ∃ f, u < |Rhat omega f - R f| := by
  by_contra hnone
  push Not at hnone
  have hUniform : ∀ f, |Rhat omega f - R f| ≤ u := by
    intro f
    exact hnone f
  exact hwrong (erm_event_eq_uniqueMinimizer
    R Rhat fHat fStar u hERM hStrict hUniform hsmall)

/-- Sequence form: a finite unique true minimizer is eventually selected
exactly by ERM under a vanishing simultaneous uniform estimation radius. -/
theorem eventually_erm_eq_uniqueMinimizer
    (R : F → ℝ)
    (Rhat : ℕ → F → ℝ)
    (fHat : ℕ → F)
    (fStar : F)
    (u : ℕ → ℝ)
    (hu : Tendsto u atTop (𝓝 0))
    (hERM : ∀ n f, Rhat n (fHat n) ≤ Rhat n f)
    (hStrict : ∀ f, f ≠ fStar → R fStar < R f)
    (hUniform : ∀ n f, |Rhat n f - R f| ≤ u n) :
    ∀ᶠ n in atTop, fHat n = fStar := by
  have hgap : 0 < canonicalRiskGap R fStar :=
    canonicalRiskGap_pos R fStar hStrict
  have hsmall : ∀ᶠ n in atTop, 2 * u n < canonicalRiskGap R fStar := by
    have htwo : Tendsto (fun n => 2 * u n) atTop (𝓝 0) := by
      simpa using hu.const_mul (2 : ℝ)
    exact (tendsto_order.1 htwo).2 _ hgap
  filter_upwards [hsmall] with n hn
  exact erm_eq_uniqueMinimizer_of_two_radius_lt_canonicalRiskGap
    R (Rhat n) (fHat n) fStar (u n) (hERM n) hStrict (hUniform n) hn

end
end UEOT.V3.Compression.TheoryCompletion.InverseObjecthood
