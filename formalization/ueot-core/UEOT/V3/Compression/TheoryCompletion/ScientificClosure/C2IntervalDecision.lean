import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Scientific Closure C2 — abstaining interval certification

This module is deliberately deterministic.  Sampling theory supplies a good
event on which an estimate differs from the target by a declared statistical
radius plus a declared drift allowance.  C2 then turns that event into a
three-way decision without assuming a known separation gap.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure

/-- A scalar estimate with separate sampling and drift budgets. -/
structure IntervalCertificate where
  estimate : ℝ
  statisticalRadius : ℝ
  driftRadius : ℝ
  statisticalRadius_nonneg : 0 ≤ statisticalRadius
  driftRadius_nonneg : 0 ≤ driftRadius

namespace IntervalCertificate

/-- Total radius kept as two auditable contributions in the structure. -/
def totalRadius (C : IntervalCertificate) : ℝ :=
  C.statisticalRadius + C.driftRadius

/-- Lower endpoint; it is intentionally not truncated at zero so the interval
logic is valid for arbitrary scalar observables. -/
def lower (C : IntervalCertificate) : ℝ := C.estimate - C.totalRadius

/-- Upper endpoint. -/
def upper (C : IntervalCertificate) : ℝ := C.estimate + C.totalRadius

@[simp] theorem totalRadius_nonneg (C : IntervalCertificate) :
    0 ≤ C.totalRadius := by
  exact add_nonneg C.statisticalRadius_nonneg C.driftRadius_nonneg

/-- Any truth lying within the declared total error budget lies below the upper
endpoint. -/
theorem truth_le_upper (C : IntervalCertificate) {truth : ℝ}
    (hgood : |C.estimate - truth| ≤ C.totalRadius) :
    truth ≤ C.upper := by
  rw [abs_le] at hgood
  unfold upper
  linarith

/-- Symmetric lower-endpoint guarantee. -/
theorem lower_le_truth (C : IntervalCertificate) {truth : ℝ}
    (hgood : |C.estimate - truth| ≤ C.totalRadius) :
    C.lower ≤ truth := by
  rw [abs_le] at hgood
  unfold lower
  linarith

end IntervalCertificate

/-- Scientific decisions are intentionally ternary. -/
inductive CertificationDecision
  | certified
  | rejected
  | ambiguous
  deriving DecidableEq, Repr

open CertificationDecision

/-- Certify values at or below `threshold`, reject values strictly above it,
and abstain whenever the interval crosses the threshold. -/
noncomputable def decideAt
    (C : IntervalCertificate) (threshold : ℝ) : CertificationDecision :=
  if C.upper ≤ threshold then certified
  else if threshold < C.lower then rejected
  else ambiguous

/-- A certified decision is sound on the declared good event. -/
theorem decideAt_certified_sound
    (C : IntervalCertificate) (threshold truth : ℝ)
    (hgood : |C.estimate - truth| ≤ C.totalRadius)
    (h : decideAt C threshold = certified) :
    truth ≤ threshold := by
  unfold decideAt at h
  split at h <;> rename_i hupper
  · exact (C.truth_le_upper hgood).trans hupper
  · split at h <;> simp_all

/-- A rejected decision is sound on the declared good event. -/
theorem decideAt_rejected_sound
    (C : IntervalCertificate) (threshold truth : ℝ)
    (hgood : |C.estimate - truth| ≤ C.totalRadius)
    (h : decideAt C threshold = rejected) :
    threshold < truth := by
  unfold decideAt at h
  split at h <;> rename_i hupper
  · simp at h
  · split at h <;> rename_i hlower
    · exact lt_of_lt_of_le hlower (C.lower_le_truth hgood)
    · simp at h

/-- Ambiguity is exactly failure of both one-sided certification conditions. -/
theorem decideAt_ambiguous_iff
    (C : IntervalCertificate) (threshold : ℝ) :
    decideAt C threshold = ambiguous ↔
      ¬ C.upper ≤ threshold ∧ ¬ threshold < C.lower := by
  unfold decideAt
  by_cases hupper : C.upper ≤ threshold
  · simp [hupper]
  · by_cases hlower : threshold < C.lower
    · simp [hupper, hlower]
    · simp [hupper, hlower]

/-- On a linear order, an ambiguous decision means the threshold lies inside
(or at one edge of) the unresolved interval. -/
theorem decideAt_ambiguous_bounds
    (C : IntervalCertificate) (threshold : ℝ)
    (h : decideAt C threshold = ambiguous) :
    C.lower ≤ threshold ∧ threshold < C.upper := by
  have ha := (decideAt_ambiguous_iff C threshold).1 h
  constructor
  · exact le_of_not_gt ha.2
  · exact lt_of_not_ge ha.1

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure
