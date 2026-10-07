import UEOT.V3.Compression.TheoryCompletion.InverseObjecthood.Identifiability
import UEOT.V3.InformationPacking
import Mathlib.Tactic

/-!
# P4.3 — interaction-evidence class recovery

For finite candidate spaces, inverse discovery should first target the quotient
class induced by the declared probe/intervention family.  Literal candidate
recovery is stronger and requires the probe family to separate candidate
labels.

This module constructs the canonical positive gap **between distinct evidence
classes**, proves exact class recovery from one sufficiently accurate observed
fingerprint, and then gives literal-candidate recovery only as the pairwise-
separating specialization.

The observation-triangle lemma is restated locally with its actual minimal
assumptions.  The older CrossTrack wrapper was defined inside a section that
leaks unrelated `MetricSpace`/`Nontrivial` candidate assumptions even though
the TV triangle argument itself needs neither.
-/

namespace UEOT.V3.Compression.TheoryCompletion.InverseObjecthood

open Filter Topology MeasureTheory
open UEOT.V3.TotalVariation
open UEOT.V3.Compression.CrossTrack

universe uA uI uY

noncomputable section

/-- Minimal observation triangle: two candidate fingerprints close to one
observed fingerprint are close to each other.  No metric on candidate labels is
used. -/
theorem fingerprintDist_le_observationErrors
    {A : Type uA} {I : Type uI} {Y : Type uY} [MeasurableSpace Y]
    (F : InteractionResponseFamily A I Y)
    (probes : Finset I) (hprobes : probes.Nonempty)
    (observed : I → Measure Y)
    (hobserved : ∀ i, IsProbabilityMeasure (observed i))
    (a b : A) :
    interactionFingerprintDist F probes hprobes a b ≤
      interactionObservationError F probes hprobes observed a +
        interactionObservationError F probes hprobes observed b := by
  unfold interactionFingerprintDist
  apply Finset.sup'_le hprobes
  intro i hi
  let _ : IsProbabilityMeasure (F.response a i) := F.probability a i
  let _ : IsProbabilityMeasure (F.response b i) := F.probability b i
  let _ : IsProbabilityMeasure (observed i) := hobserved i
  have htri := UEOT.V3.InformationPacking.tvDist_triangle
    (F.response a i) (observed i) (F.response b i)
  have hsym : tvDist (observed i) (F.response b i) =
      tvDist (F.response b i) (observed i) :=
    UEOT.V3.InformationPacking.tvDist_symm _ _
  rw [hsym] at htri
  have ha : tvDist (F.response a i) (observed i) ≤
      interactionObservationError F probes hprobes observed a := by
    unfold interactionObservationError
    exact Finset.le_sup'
      (fun j : I => (tvDist (F.response a j) (observed j) : ℝ)) hi
  have hb : tvDist (F.response b i) (observed i) ≤
      interactionObservationError F probes hprobes observed b := by
    unfold interactionObservationError
    exact Finset.le_sup'
      (fun j : I => (tvDist (F.response b j) (observed j) : ℝ)) hi
  exact htri.trans (add_le_add ha hb)

variable {A : Type uA} [Fintype A] [Nonempty A]
variable {I : Type uI} {Y : Type uY} [MeasurableSpace Y]
local instance inverseObjecthoodInteractionDecidableEq : DecidableEq A :=
  Classical.decEq A

/-- Canonical finite gap between distinct probe-relative interaction evidence
classes.  Pairs already in the same evidence class contribute the harmless
fallback `1`, so the definition stays positive even when every candidate lies
in one observational class. -/
noncomputable def canonicalInteractionEvidenceGap
    (F : InteractionResponseFamily A I Y)
    (probes : Finset I) (hprobes : probes.Nonempty) : ℝ := by
  classical
  exact (Finset.univ : Finset (A × A)).inf' Finset.univ_nonempty
    (fun p =>
      if InteractionEvidenceEquivalent F probes p.1 p.2 then 1
      else interactionFingerprintDist F probes hprobes p.1 p.2)

/-- Every finite interaction-evidence quotient has a strictly positive gap
between distinct evidence classes.  This does **not** say different candidate
labels are separated: multiple labels may occupy one evidence class. -/
theorem canonicalInteractionEvidenceGap_pos
    (F : InteractionResponseFamily A I Y)
    (probes : Finset I) (hprobes : probes.Nonempty) :
    0 < canonicalInteractionEvidenceGap F probes hprobes := by
  classical
  unfold canonicalInteractionEvidenceGap
  obtain ⟨p, _hp, hmin⟩ := Finset.exists_mem_eq_inf'
    (Finset.univ_nonempty : (Finset.univ : Finset (A × A)).Nonempty)
    (fun q =>
      if InteractionEvidenceEquivalent F probes q.1 q.2 then (1 : ℝ)
      else interactionFingerprintDist F probes hprobes q.1 q.2)
  rw [hmin]
  by_cases heq : InteractionEvidenceEquivalent F probes p.1 p.2
  · simp [heq]
  · simp only [heq, ↓reduceIte]
    have hne0 : interactionFingerprintDist F probes hprobes p.1 p.2 ≠ 0 := by
      intro hzero
      exact heq ((interactionEvidenceEquivalent_iff_fingerprintDist_eq_zero
        F probes hprobes p.1 p.2).2 hzero)
    exact lt_of_le_of_ne
      (interactionFingerprintDist_nonneg F probes hprobes p.1 p.2)
      (Ne.symm hne0)

/-- The canonical evidence-class gap lower-bounds every fingerprint distance
between two candidates in distinct evidence classes. -/
theorem canonicalInteractionEvidenceGap_le_distinctClass
    (F : InteractionResponseFamily A I Y)
    (probes : Finset I) (hprobes : probes.Nonempty)
    {a b : A} (hne : ¬ InteractionEvidenceEquivalent F probes a b) :
    canonicalInteractionEvidenceGap F probes hprobes ≤
      interactionFingerprintDist F probes hprobes a b := by
  classical
  have hle : canonicalInteractionEvidenceGap F probes hprobes ≤
      (if InteractionEvidenceEquivalent F probes a b then 1
       else interactionFingerprintDist F probes hprobes a b) := by
    unfold canonicalInteractionEvidenceGap
    exact Finset.inf'_le _ (Finset.mem_univ (a, b))
  simpa [hne] using hle

/-- Two candidates fitting one observed interaction fingerprint within `eta`
lie in the same evidence class once `2 eta` is below the canonical inter-class
gap. -/
theorem evidenceEquivalent_of_commonObservation
    (F : InteractionResponseFamily A I Y)
    (probes : Finset I) (hprobes : probes.Nonempty)
    (observed : I → Measure Y)
    (hobserved : ∀ i, IsProbabilityMeasure (observed i))
    (eta : ℝ)
    {a b : A}
    (ha : interactionObservationError F probes hprobes observed a ≤ eta)
    (hb : interactionObservationError F probes hprobes observed b ≤ eta)
    (hsmall : 2 * eta < canonicalInteractionEvidenceGap F probes hprobes) :
    InteractionEvidenceEquivalent F probes a b := by
  by_contra hne
  have hfp := fingerprintDist_le_observationErrors
    F probes hprobes observed hobserved a b
  have hfpEta : interactionFingerprintDist F probes hprobes a b ≤ 2 * eta := by
    linarith
  have hgap := canonicalInteractionEvidenceGap_le_distinctClass
    F probes hprobes hne
  linarith

/-- Pairwise separating probes upgrade exact evidence-class recovery to literal
candidate recovery. -/
theorem exactCandidate_of_commonObservation_of_pairwiseSeparating
    (F : InteractionResponseFamily A I Y)
    (probes : Finset I) (hprobes : probes.Nonempty)
    (hsep : PairwiseInteractionSeparating F probes)
    (observed : I → Measure Y)
    (hobserved : ∀ i, IsProbabilityMeasure (observed i))
    (eta : ℝ)
    {a b : A}
    (ha : interactionObservationError F probes hprobes observed a ≤ eta)
    (hb : interactionObservationError F probes hprobes observed b ≤ eta)
    (hsmall : 2 * eta < canonicalInteractionEvidenceGap F probes hprobes) :
    a = b := by
  have heq := evidenceEquivalent_of_commonObservation
    F probes hprobes observed hobserved eta ha hb hsmall
  exact (pairwiseSeparating_iff_evidenceEquivalent_implies_eq F probes).1
    hsep a b heq

/-- Vanishing common observation error eventually recovers the correct finite
interaction-evidence class. -/
theorem eventually_evidenceEquivalent_of_vanishingObservation
    (F : InteractionResponseFamily A I Y)
    (probes : Finset I) (hprobes : probes.Nonempty)
    (observed : ℕ → I → Measure Y)
    (hobserved : ∀ n i, IsProbabilityMeasure (observed n i))
    (eta : ℕ → ℝ) (heta : Tendsto eta atTop (𝓝 0))
    (aStar : A) (aHat : ℕ → A)
    (hobs : ∀ n,
      interactionObservationError F probes hprobes (observed n) aStar ≤ eta n ∧
      interactionObservationError F probes hprobes (observed n) (aHat n) ≤ eta n) :
    ∀ᶠ n in atTop,
      InteractionEvidenceEquivalent F probes aStar (aHat n) := by
  have hgap : 0 < canonicalInteractionEvidenceGap F probes hprobes :=
    canonicalInteractionEvidenceGap_pos F probes hprobes
  have hsmall : ∀ᶠ n in atTop,
      2 * eta n < canonicalInteractionEvidenceGap F probes hprobes := by
    have htwo : Tendsto (fun n => 2 * eta n) atTop (𝓝 0) := by
      simpa using heta.const_mul (2 : ℝ)
    exact (tendsto_order.1 htwo).2 _ hgap
  filter_upwards [hsmall] with n hn
  exact evidenceEquivalent_of_commonObservation
    F probes hprobes (observed n) (hobserved n) (eta n)
    (hobs n).1 (hobs n).2 hn

/-- Under pairwise separating probes, vanishing common observation error
upgrades eventual evidence-class recovery to eventual literal candidate
recovery. -/
theorem eventually_exactCandidate_of_vanishingObservation_of_pairwiseSeparating
    (F : InteractionResponseFamily A I Y)
    (probes : Finset I) (hprobes : probes.Nonempty)
    (hsep : PairwiseInteractionSeparating F probes)
    (observed : ℕ → I → Measure Y)
    (hobserved : ∀ n i, IsProbabilityMeasure (observed n i))
    (eta : ℕ → ℝ) (heta : Tendsto eta atTop (𝓝 0))
    (aStar : A) (aHat : ℕ → A)
    (hobs : ∀ n,
      interactionObservationError F probes hprobes (observed n) aStar ≤ eta n ∧
      interactionObservationError F probes hprobes (observed n) (aHat n) ≤ eta n) :
    ∀ᶠ n in atTop, aHat n = aStar := by
  have hclass := eventually_evidenceEquivalent_of_vanishingObservation
    F probes hprobes observed hobserved eta heta aStar aHat hobs
  filter_upwards [hclass] with n hn
  exact ((pairwiseSeparating_iff_evidenceEquivalent_implies_eq F probes).1
    hsep aStar (aHat n) hn).symm

end
end UEOT.V3.Compression.TheoryCompletion.InverseObjecthood
