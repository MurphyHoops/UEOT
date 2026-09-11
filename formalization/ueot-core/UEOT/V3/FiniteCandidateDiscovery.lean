import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith

/-!
# P-STAT-08 — finite-candidate discovery

The frozen source separates the statistical statement into two layers:

1. on a simultaneous uniform-risk event, empirical risk minimization has
   excess true risk at most twice the uniform estimation radius;
2. Hoeffding plus a finite union bound supplies that event with radius
   `sqrt (log (2m/alpha) / (2N))`.

This module starts with the deterministic ERM layer.  The sampling/concentration
layer is added separately so that the optimization argument cannot hide any
probabilistic assumption.
-/

namespace UEOT.V3.FiniteCandidateDiscovery

universe uF uΩ

/-- Deterministic ERM excess-risk lemma.  If every empirical risk differs from
its true risk by at most `u`, an empirical minimizer is within `2u` of any true
risk minimizer. -/
theorem erm_excess_le_two_uniform
    {F : Type uF}
    (R Rhat : F → ℝ)
    (fHat fStar : F)
    (u : ℝ)
    (hHat : ∀ f, Rhat fHat ≤ Rhat f)
    (hStar : ∀ f, R fStar ≤ R f)
    (hUniform : ∀ f, |Rhat f - R f| ≤ u) :
    R fHat ≤ R fStar + 2 * u := by
  have hHatErr := (abs_le.mp (hUniform fHat)).1
  have hStarErr := (abs_le.mp (hUniform fStar)).2
  have hERM := hHat fStar
  linarith

/-- Pointwise version for a data-dependent empirical minimizer.  This is the
exact deterministic step used after the simultaneous Hoeffding event in
P-STAT-08. -/
theorem erm_excess_le_two_uniform_event
    {F : Type uF} {Ω : Type uΩ}
    (R : F → ℝ)
    (Rhat : Ω → F → ℝ)
    (fHat : Ω → F)
    (fStar : F)
    (u : ℝ)
    (hERM : ∀ ω f, Rhat ω (fHat ω) ≤ Rhat ω f)
    (hStar : ∀ f, R fStar ≤ R f)
    {ω : Ω}
    (hUniform : ∀ f, |Rhat ω f - R f| ≤ u) :
    R (fHat ω) ≤ R fStar + 2 * u := by
  exact erm_excess_le_two_uniform R (Rhat ω) (fHat ω) fStar u
    (hERM ω) hStar hUniform

/-- Source-oriented minimum form: if `fStar` realizes the minimum true risk,
the deterministic conclusion can be stated directly against that minimum. -/
theorem erm_le_min_add_two_uniform
    {F : Type uF}
    (R Rhat : F → ℝ)
    (fHat fStar : F)
    (u : ℝ)
    (hHat : ∀ f, Rhat fHat ≤ Rhat f)
    (hStar : ∀ f, R fStar ≤ R f)
    (hUniform : ∀ f, |Rhat f - R f| ≤ u) :
    R fHat ≤ (sInf (Set.range R)) + 2 * u := by
  have hmain := erm_excess_le_two_uniform R Rhat fHat fStar u hHat hStar hUniform
  have hmin : sInf (Set.range R) = R fStar := by
    apply le_antisymm
    · exact csInf_le ⟨R fStar, ⟨fStar, rfl⟩⟩ ⟨fStar, rfl⟩
    · refine le_csInf ?_ ?_
      · exact ⟨R fStar, by rintro y ⟨f, rfl⟩; exact hStar f⟩
      · rintro y ⟨f, rfl⟩
        exact hStar f
  simpa [hmin] using hmain

end UEOT.V3.FiniteCandidateDiscovery
