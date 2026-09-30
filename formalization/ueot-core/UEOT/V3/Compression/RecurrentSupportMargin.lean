import UEOT.V3.Compression.ApproximateRecurrentGaugeStability

/-!
# Recurrent support margins and class-structure lock

Small metric perturbation alone cannot preserve recurrent classes: a zero edge
can become an arbitrarily small positive edge and merge communicating classes.
This module isolates a sufficient support-separation condition under which that
failure mode is impossible.

The key ingredients are:

* every positive one-step transition of both kernels is separated from zero by
  one common margin `gamma`;
* every matrix entry moves by strictly less than `gamma`.

Those hypotheses force equality of the positive-edge support graph.  For
finite stochastic kernels, equality of one-step support then propagates to
every matrix power, finite-step reachability, communication, and recurrent
carriers.
-/

namespace UEOT.V3.Compression.RecurrentSupportMargin

open UEOT.V3
open UEOT.V3.Compression.RecurrentClassGaugeInvariance

universe uS

noncomputable section

variable {S : Type uS} [Fintype S] [DecidableEq S]

/-- Equality of positive one-step transition support. -/
def TransitionSupportEq (P Q : Matrix S S ℝ) : Prop :=
  ∀ x y, 0 < P x y ↔ 0 < Q x y

/-- A positive-support margin: every entry is either exactly zero or at least
`gamma`.  This is intentionally stronger than stochasticity and is the
zero-pattern separation needed to prevent tiny new edges. -/
def HasTransitionGap (P : Matrix S S ℝ) (gamma : ℝ) : Prop :=
  ∀ x y, P x y = 0 ∨ gamma ≤ P x y

/-- Two kernels that both have the same positive gap and are entrywise closer
than that gap have identical positive support. -/
theorem transitionSupportEq_of_gap
    (P Q : Matrix S S ℝ) (gamma : ℝ)
    (hgamma : 0 < gamma)
    (hPgap : HasTransitionGap P gamma)
    (hQgap : HasTransitionGap Q gamma)
    (hclose : ∀ x y, |Q x y - P x y| < gamma) :
    TransitionSupportEq P Q := by
  intro x y
  constructor
  · intro hPpos
    rcases hQgap x y with hQzero | hQlarge
    · have hPlarge : gamma ≤ P x y := by
        rcases hPgap x y with hPzero | hPlarge
        · rw [hPzero] at hPpos
          exact (lt_irrefl 0 hPpos).elim
        · exact hPlarge
      have hc := hclose x y
      rw [hQzero, zero_sub, abs_neg, abs_of_pos hPpos] at hc
      exact (not_lt_of_ge hPlarge hc).elim
    · exact hgamma.trans_le hQlarge
  · intro hQpos
    rcases hPgap x y with hPzero | hPlarge
    · have hQlarge : gamma ≤ Q x y := by
        rcases hQgap x y with hQzero | hQlarge
        · rw [hQzero] at hQpos
          exact (lt_irrefl 0 hQpos).elim
        · exact hQlarge
      have hc := hclose x y
      rw [hPzero, sub_zero, abs_of_pos hQpos] at hc
      exact (not_lt_of_ge hQlarge hc).elim
    · exact hgamma.trans_le hPlarge

/-- Equality of one-step positive support propagates to every finite matrix
power for nonnegative finite kernels. -/
theorem pow_pos_iff_of_transitionSupportEq
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (hsupp : TransitionSupportEq P Q) :
    ∀ n x y, 0 < (P ^ n) x y ↔ 0 < (Q ^ n) x y := by
  intro n
  induction n with
  | zero =>
      intro x y
      simp [Matrix.one_apply]
  | succ n ih =>
      intro x y
      rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
      have hsumP := Finset.sum_pos_iff_of_nonneg
        (s := (Finset.univ : Finset S))
        (f := fun z => (P ^ n) x z * P z y)
        (fun z _ => mul_nonneg
          (Matrix.pow_apply_nonneg hP.1 n x z) (hP.1 z y))
      have hsumQ := Finset.sum_pos_iff_of_nonneg
        (s := (Finset.univ : Finset S))
        (f := fun z => (Q ^ n) x z * Q z y)
        (fun z _ => mul_nonneg
          (Matrix.pow_apply_nonneg hQ.1 n x z) (hQ.1 z y))
      rw [hsumP, hsumQ]
      constructor
      · rintro ⟨z, _, hz⟩
        have hPpow : 0 < (P ^ n) x z := by
          by_contra hn
          have hz0 : (P ^ n) x z = 0 :=
            le_antisymm (le_of_not_gt hn) (Matrix.pow_apply_nonneg hP.1 n x z)
          simp [hz0] at hz
        have hPedge : 0 < P z y := by
          by_contra hn
          have hz0 : P z y = 0 :=
            le_antisymm (le_of_not_gt hn) (hP.1 z y)
          simp [hz0] at hz
        exact ⟨z, Finset.mem_univ z,
          mul_pos ((ih x z).1 hPpow) ((hsupp z y).1 hPedge)⟩
      · rintro ⟨z, _, hz⟩
        have hQpow : 0 < (Q ^ n) x z := by
          by_contra hn
          have hz0 : (Q ^ n) x z = 0 :=
            le_antisymm (le_of_not_gt hn) (Matrix.pow_apply_nonneg hQ.1 n x z)
          simp [hz0] at hz
        have hQedge : 0 < Q z y := by
          by_contra hn
          have hz0 : Q z y = 0 :=
            le_antisymm (le_of_not_gt hn) (hQ.1 z y)
          simp [hz0] at hz
        exact ⟨z, Finset.mem_univ z,
          mul_pos ((ih x z).2 hQpow) ((hsupp z y).2 hQedge)⟩

/-- Under support equality, finite-step reachability is identical. -/
theorem reachable_iff_of_transitionSupportEq
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (hsupp : TransitionSupportEq P Q)
    (x y : S) :
    Reachable Q x y ↔ Reachable P x y := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, (pow_pos_iff_of_transitionSupportEq P Q hP hQ hsupp n x y).2 hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, (pow_pos_iff_of_transitionSupportEq P Q hP hQ hsupp n x y).1 hn⟩

/-- Under support equality, communication is identical. -/
theorem communicates_iff_of_transitionSupportEq
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (hsupp : TransitionSupportEq P Q)
    (x y : S) :
    Communicates Q x y ↔ Communicates P x y := by
  simp only [Communicates]
  constructor
  · rintro ⟨hxy, hyx⟩
    exact ⟨
      (reachable_iff_of_transitionSupportEq P Q hP hQ hsupp x y).1 hxy,
      (reachable_iff_of_transitionSupportEq P Q hP hQ hsupp y x).1 hyx⟩
  · rintro ⟨hxy, hyx⟩
    exact ⟨
      (reachable_iff_of_transitionSupportEq P Q hP hQ hsupp x y).2 hxy,
      (reachable_iff_of_transitionSupportEq P Q hP hQ hsupp y x).2 hyx⟩

/-- Closed carriers are identical when one-step positive support is identical. -/
theorem closedCarrier_iff_of_transitionSupportEq
    (P Q : Matrix S S ℝ)
    (hsupp : TransitionSupportEq P Q)
    (A : Set S) :
    ClosedCarrier Q A ↔ ClosedCarrier P A := by
  constructor
  · intro hclosed x hx y hxy
    exact hclosed hx y ((hsupp x y).1 hxy)
  · intro hclosed x hx y hxy
    exact hclosed hx y ((hsupp x y).2 hxy)

/-- Recurrent carriers are locked when the positive support graph is locked. -/
theorem recurrentCarrier_iff_of_transitionSupportEq
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (hsupp : TransitionSupportEq P Q)
    (A : Set S) :
    RecurrentCarrier Q A ↔ RecurrentCarrier P A := by
  constructor
  · rintro ⟨hne, hcomm, hclosed⟩
    refine ⟨hne, ?_, (closedCarrier_iff_of_transitionSupportEq P Q hsupp A).1 hclosed⟩
    intro x hx y hy
    exact (communicates_iff_of_transitionSupportEq P Q hP hQ hsupp x y).1
      (hcomm hx hy)
  · rintro ⟨hne, hcomm, hclosed⟩
    refine ⟨hne, ?_, (closedCarrier_iff_of_transitionSupportEq P Q hsupp A).2 hclosed⟩
    intro x hx y hy
    exact (communicates_iff_of_transitionSupportEq P Q hP hQ hsupp x y).2
      (hcomm hx hy)

/-- The explicit transition-gap hypotheses imply full recurrent-carrier lock. -/
theorem recurrentCarrier_iff_of_gap
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hPgap : HasTransitionGap P gamma)
    (hQgap : HasTransitionGap Q gamma)
    (hclose : ∀ x y, |Q x y - P x y| < gamma)
    (A : Set S) :
    RecurrentCarrier Q A ↔ RecurrentCarrier P A := by
  exact recurrentCarrier_iff_of_transitionSupportEq P Q hP hQ
    (transitionSupportEq_of_gap P Q gamma hgamma hPgap hQgap hclose) A

/-- Support-margin lock followed by an exact state gauge: a recurrent carrier
of the source is exactly the relabeled recurrent carrier of the physical
target.  `Qaligned` is only a common-coordinate representative used to state
the small perturbation; its relabeling contributes no extra structural error. -/
theorem recurrentCarrier_image_iff_of_gap_gauge
    [Nonempty S]
    (P Qaligned Ptarget : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Qaligned ∈ Matrix.rowStochastic ℝ S)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hPgap : HasTransitionGap P gamma)
    (hQgap : HasTransitionGap Qaligned gamma)
    (hclose : ∀ x y, |Qaligned x y - P x y| < gamma)
    (e : S ≃ S)
    (hconj : ∀ s t, Qaligned s t = Ptarget (e s) (e t))
    (A : Set S) :
    RecurrentCarrier Ptarget (e '' A) ↔ RecurrentCarrier P A := by
  calc
    RecurrentCarrier Ptarget (e '' A) ↔ RecurrentCarrier Qaligned A :=
      recurrentCarrier_image_iff Qaligned Ptarget e hconj A
    _ ↔ RecurrentCarrier P A :=
      recurrentCarrier_iff_of_gap P Qaligned hP hQ
        gamma hgamma hPgap hQgap hclose A

end

end UEOT.V3.Compression.RecurrentSupportMargin
