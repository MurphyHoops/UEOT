import UEOT.V3.FiniteDiscountedExactQuotient
import UEOT.V3.FiniteDiscountedSelectorValue
import UEOT.V3.TVSpan
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic

/-!
# P-QUO-02 — approximate finite discounted control quotient

This module formalizes the frozen span-sensitive approximate quotient theorem.
The transition error is represented as genuine event-supremum total variation
between the pushed-forward finite micro row and the corresponding macro row.
The expectation error is then derived from P-MET-02; it is not assumed.
-/

namespace UEOT.V3.FiniteDiscountedControl

open Filter Topology
open CausalPolicy

universe uX uY uA uS

variable {X : Type uX} [Fintype X]
variable {Y : Type uY} [Fintype Y]
variable {A : X → Type uA} [∀ x, Fintype (A x)] [∀ x, Nonempty (A x)]
variable {Abar : Y → Type uA} [∀ y, Fintype (Abar y)] [∀ y, Nonempty (Abar y)]

namespace FiniteProbabilityRow

/-- Turn a finite nonnegative real row of total mass one into its exact PMF. -/
noncomputable def ofRealRow {S : Type uS} [Fintype S]
    (p : S → ℝ) (hp : ∀ s, 0 ≤ p s) (hsum : ∑ s, p s = 1) : PMF S :=
  PMF.ofFintype (fun s => ENNReal.ofReal (p s)) <| by
    calc
      (∑ s, ENNReal.ofReal (p s)) = ENNReal.ofReal (∑ s, p s) := by
        symm
        simpa using
          (ENNReal.ofReal_sum_of_nonneg
            (s := (Finset.univ : Finset S)) (f := p) (fun s _ => hp s))
      _ = 1 := by simp [hsum]

@[simp] theorem ofRealRow_apply_toReal {S : Type uS} [Fintype S]
    (p : S → ℝ) (hp : ∀ s, 0 ≤ p s) (hsum : ∑ s, p s = 1) (s : S) :
    ((ofRealRow p hp hsum) s).toReal = p s := by
  simp [ofRealRow, hp s]

/-- Event-supremum total variation of two finite PMFs, evaluated with the
canonical discrete measurable structure. -/
noncomputable def tvDist {S : Type uS} (p q : PMF S) : ℝ := by
  letI : MeasurableSpace S := ⊤
  exact UEOT.V3.TotalVariation.tvDist p.toMeasure q.toMeasure

/-- P-MET-02 specialized to finite PMFs.  This is the bridge from the genuine
TV premise used by P-QUO-02 to a continuation-value expectation error. -/
theorem abs_expectation_sub_le_span_tvDist {S : Type uS} [Fintype S]
    (p q : PMF S) (v : S → ℝ) :
    |(∑ s, (p s).toReal * v s) - (∑ s, (q s).toReal * v s)| ≤
      UEOT.V3.TVSpan.span v * tvDist p q := by
  classical
  letI : MeasurableSpace S := ⊤
  have h :=
    UEOT.V3.TVSpan.abs_integral_sub_le_span
      p.toMeasure q.toMeasure v Measurable.of_discrete
      (Finite.bddBelow_range v) (Finite.bddAbove_range v)
  rw [PMF.integral_eq_sum, PMF.integral_eq_sum] at h
  simpa [smul_eq_mul, tvDist] using h

/-- The span of a real function on a finite type is nonnegative, including the
empty-type case under Mathlib's real `sInf/sSup` convention. -/
theorem span_nonneg {S : Type uS} [Fintype S] (v : S → ℝ) :
    0 ≤ UEOT.V3.TVSpan.span v := by
  unfold UEOT.V3.TVSpan.span
  exact sub_nonneg.mpr <|
    Real.sInf_le_sSup (Set.range v)
      (Finite.bddBelow_range v) (Finite.bddAbove_range v)

end FiniteProbabilityRow

namespace Model

/-- Exact PMF associated with one finite controlled transition row. -/
noncomputable def transitionPMF (M : Model X A) (x : X) (a : A x) : PMF X :=
  FiniteProbabilityRow.ofRealRow (M.transition x a)
    (M.transition_nonneg x a) (M.transition_sum_one x a)

@[simp] theorem transitionPMF_apply_toReal (M : Model X A) (x : X) (a : A x) (y : X) :
    ((M.transitionPMF x a) y).toReal = M.transition x a y := by
  simp [transitionPMF]

end Model

/-- The finite pushforward mass of a probability row is nonnegative. -/
theorem fiberMass_nonneg (f : X → Y) (p : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (y : Y) :
    0 ≤ fiberMass f p y := by
  classical
  unfold fiberMass
  exact Finset.sum_nonneg fun x _ => by
    split <;> simp_all

/-- Summing pushed-forward fibre masses recovers the original total mass. -/
theorem sum_fiberMass (f : X → Y) (p : X → ℝ) :
    ∑ y, fiberMass f p y = ∑ x, p x := by
  classical
  unfold fiberMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp

/-- Exact finite PMF of the pushed-forward micro transition row. -/
noncomputable def pushforwardTransitionPMF
    (f : X → Y) (M : Model X A) (x : X) (a : A x) : PMF Y :=
  FiniteProbabilityRow.ofRealRow
    (fiberMass f (M.transition x a))
    (fiberMass_nonneg f (M.transition x a) (M.transition_nonneg x a))
    (by rw [sum_fiberMass, M.transition_sum_one x a])

@[simp] theorem pushforwardTransitionPMF_apply_toReal
    (f : X → Y) (M : Model X A) (x : X) (a : A x) (y : Y) :
    ((pushforwardTransitionPMF f M x a) y).toReal =
      fiberMass f (M.transition x a) y := by
  simp [pushforwardTransitionPMF]

/-- The pushed-forward PMF expectation is exactly the micro expectation of the
pulled-back function. -/
theorem pushforward_expect_eq
    (f : X → Y) (M : Model X A) (x : X) (a : A x) (v : Y → ℝ) :
    (∑ y, ((pushforwardTransitionPMF f M x a) y).toReal * v y) =
      M.expect x a (fun x' => v (f x')) := by
  classical
  simp only [pushforwardTransitionPMF_apply_toReal, Model.expect]
  calc
    (∑ y : Y, fiberMass f (M.transition x a) y * v y) =
        ∑ y : Y, ∑ x' : X,
          if f x' = y then M.transition x a x' * v y else 0 := by
      apply Finset.sum_congr rfl
      intro y hy
      simp only [fiberMass]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x' hx
      by_cases hxy : f x' = y <;> simp [hxy]
    _ = ∑ x' : X, ∑ y : Y,
          if f x' = y then M.transition x a x' * v y else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x' : X, M.transition x a x' * v (f x') := by
      apply Finset.sum_congr rfl
      intro x' hx
      simp

/-- Frozen-source data for an approximate finite discounted control quotient.
The TV field is an actual total-variation comparison of the all-action
pushed-forward micro row against the macro row. -/
structure ApproxControlQuotient (X : Type uX) [Fintype X]
    (Y : Type uY) [Fintype Y]
    (Abar : Y → Type uA) [∀ y, Fintype (Abar y)] [∀ y, Nonempty (Abar y)] where
  f : X → Y
  surjective : Function.Surjective f
  micro : Model X (fun x => Abar (f x))
  macroModel : Model Y Abar
  discount_eq : micro.discount = macroModel.discount
  epsilonReward : ℝ
  epsilonTransition : ℝ
  epsilonReward_nonneg : 0 ≤ epsilonReward
  epsilonTransition_nonneg : 0 ≤ epsilonTransition
  reward_approx : ∀ x (a : Abar (f x)),
    |micro.reward x a - macroModel.reward (f x) a| ≤ epsilonReward
  transition_tv_approx : ∀ x (a : Abar (f x)),
    FiniteProbabilityRow.tvDist
      (pushforwardTransitionPMF f micro x a)
      (macroModel.transitionPMF (f x) a) ≤ epsilonTransition

namespace ApproxControlQuotient

variable (Q : ApproxControlQuotient X Y Abar)

/-- Pull a macro value function to the micro state space. -/
def pullback (v : Y → ℝ) : X → ℝ := fun x => v (Q.f x)

@[simp] theorem pullback_apply (v : Y → ℝ) (x : X) :
    Q.pullback v x = v (Q.f x) := rfl

/-- The true TV premise implies the source span-sensitive continuation error. -/
theorem abs_expect_pullback_sub_le_span
    (x : X) (a : Abar (Q.f x)) (v : Y → ℝ) :
    |Q.micro.expect x a (Q.pullback v) -
      Q.macroModel.expect (Q.f x) a v| ≤
      UEOT.V3.TVSpan.span v * Q.epsilonTransition := by
  have htv := Q.transition_tv_approx x a
  have h :=
    FiniteProbabilityRow.abs_expectation_sub_le_span_tvDist
      (pushforwardTransitionPMF Q.f Q.micro x a)
      (Q.macroModel.transitionPMF (Q.f x) a) v
  rw [pushforward_expect_eq Q.f Q.micro x a v] at h
  simp only [Model.expect, Model.transitionPMF_apply_toReal] at h
  exact h.trans <|
    mul_le_mul_of_nonneg_left htv (FiniteProbabilityRow.span_nonneg v)

end ApproxControlQuotient

end UEOT.V3.FiniteDiscountedControl
