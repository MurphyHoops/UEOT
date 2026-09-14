import Mathlib

/-!
# P-REF-02 foundation — finite Bayes belief interface

This module implements the discrete-observation finite-model Bayes core used to
formalize Core 3 §27.2. It proves normalization of the predictive observation
law, exact positive-evidence Bayes updating, explicit model conflict on impossible
observations, and the one-step reward/continuation data needed by a belief-state
control reduction.

`Theta` and `X` are the finite latent parameter/state required by the frozen
source. This file currently also takes `Y` finite in order to express the
observation kernel by a probability-mass table. The final source-facing audit
must either justify that discrete observation reading of the displayed Bayes
formula or add the corresponding general-observation/disintegration interface
before P-REF-02 is counted.
-/

namespace UEOT.V3.FiniteBayesBelief

open Finset
open scoped BigOperators

universe uTheta uX uA uY

/-- Finite latent model with a discrete observation channel. -/
structure Model
    (Theta : Type uTheta) (X : Type uX) (A : Type uA) (Y : Type uY)
    [Fintype X] [Fintype Y] where
  transition : Theta → X → A → X → ℝ
  observation : Theta → X → A → Y → ℝ
  transition_nonneg : ∀ theta x a x', 0 ≤ transition theta x a x'
  observation_nonneg : ∀ theta x' a y, 0 ≤ observation theta x' a y
  transition_sum_one : ∀ theta x a, ∑ x' : X, transition theta x a x' = 1
  observation_sum_one : ∀ theta x' a, ∑ y : Y, observation theta x' a y = 1

/-- A normalized joint belief on the finite pair `(theta,x)`. -/
structure Belief
    (Theta : Type uTheta) (X : Type uX) [Fintype Theta] [Fintype X] where
  mass : Theta → X → ℝ
  nonneg : ∀ theta x, 0 ≤ mass theta x
  sum_one : ∑ theta : Theta, ∑ x : X, mass theta x = 1

/-- A normalized finite probability mass function. -/
structure FiniteLaw (T : Type*) [Fintype T] where
  mass : T → ℝ
  nonneg : ∀ t, 0 ≤ mass t
  sum_one : ∑ t : T, mass t = 1

variable {Theta : Type uTheta} {X : Type uX} {A : Type uA} {Y : Type uY}
variable [Fintype Theta] [Fintype X] [Fintype Y]

/-- Predicted joint mass of `(theta,x')` after applying action `a`. -/
def nextMass (M : Model Theta X A Y) (b : Belief Theta X)
    (a : A) (theta : Theta) (x' : X) : ℝ :=
  ∑ x : X, M.transition theta x a x' * b.mass theta x

/-- Joint mass of the next latent pair and the new observation. -/
def jointObservationMass (M : Model Theta X A Y) (b : Belief Theta X)
    (a : A) (y : Y) (theta : Theta) (x' : X) : ℝ :=
  M.observation theta x' a y * nextMass M b a theta x'

/-- Predictive probability of observation `y`; this is exactly the denominator
in the Bayes formula from frozen §27.2. -/
def evidence (M : Model Theta X A Y) (b : Belief Theta X)
    (a : A) (y : Y) : ℝ :=
  ∑ theta : Theta, ∑ x' : X, jointObservationMass M b a y theta x'

theorem nextMass_nonneg (M : Model Theta X A Y) (b : Belief Theta X)
    (a : A) (theta : Theta) (x' : X) :
    0 ≤ nextMass M b a theta x' := by
  unfold nextMass
  exact Finset.sum_nonneg fun x _ =>
    mul_nonneg (M.transition_nonneg theta x a x') (b.nonneg theta x)

theorem jointObservationMass_nonneg (M : Model Theta X A Y)
    (b : Belief Theta X) (a : A) (y : Y) (theta : Theta) (x' : X) :
    0 ≤ jointObservationMass M b a y theta x' := by
  exact mul_nonneg (M.observation_nonneg theta x' a y)
    (nextMass_nonneg M b a theta x')

theorem evidence_nonneg (M : Model Theta X A Y) (b : Belief Theta X)
    (a : A) (y : Y) : 0 ≤ evidence M b a y := by
  unfold evidence
  exact Finset.sum_nonneg fun theta _ =>
    Finset.sum_nonneg fun x' _ => jointObservationMass_nonneg M b a y theta x'

/-- Prediction preserves total joint probability mass. -/
theorem nextMass_sum_one (M : Model Theta X A Y) (b : Belief Theta X)
    (a : A) :
    ∑ theta : Theta, ∑ x' : X, nextMass M b a theta x' = 1 := by
  simp_rw [nextMass]
  calc
    (∑ theta : Theta, ∑ x' : X,
        ∑ x : X, M.transition theta x a x' * b.mass theta x) =
        ∑ theta : Theta, ∑ x : X,
          ∑ x' : X, M.transition theta x a x' * b.mass theta x := by
            apply Finset.sum_congr rfl
            intro theta htheta
            rw [Finset.sum_comm]
    _ = ∑ theta : Theta, ∑ x : X, b.mass theta x := by
          apply Finset.sum_congr rfl
          intro theta htheta
          apply Finset.sum_congr rfl
          intro x hx
          rw [← Finset.sum_mul, M.transition_sum_one, one_mul]
    _ = 1 := b.sum_one

/-- The predictive observation masses form a normalized law. -/
theorem evidence_sum_one (M : Model Theta X A Y) (b : Belief Theta X)
    (a : A) : ∑ y : Y, evidence M b a y = 1 := by
  simp_rw [evidence, jointObservationMass]
  calc
    (∑ y : Y, ∑ theta : Theta, ∑ x' : X,
        M.observation theta x' a y * nextMass M b a theta x') =
        ∑ theta : Theta, ∑ y : Y, ∑ x' : X,
          M.observation theta x' a y * nextMass M b a theta x' := by
            rw [Finset.sum_comm]
    _ = ∑ theta : Theta, ∑ x' : X, ∑ y : Y,
          M.observation theta x' a y * nextMass M b a theta x' := by
            apply Finset.sum_congr rfl
            intro theta htheta
            rw [Finset.sum_comm]
    _ = ∑ theta : Theta, ∑ x' : X, nextMass M b a theta x' := by
          apply Finset.sum_congr rfl
          intro theta htheta
          apply Finset.sum_congr rfl
          intro x' hx'
          rw [← Finset.sum_mul, M.observation_sum_one, one_mul]
    _ = 1 := nextMass_sum_one M b a

/-- The next-observation conditional law determined solely by `(b,a)`. -/
def observationLaw (M : Model Theta X A Y) (b : Belief Theta X)
    (a : A) : FiniteLaw Y where
  mass y := evidence M b a y
  nonneg y := evidence_nonneg M b a y
  sum_one := evidence_sum_one M b a

@[simp] theorem observationLaw_mass (M : Model Theta X A Y)
    (b : Belief Theta X) (a : A) (y : Y) :
    (observationLaw M b a).mass y = evidence M b a y := rfl

/-- Positive-evidence Bayes update. The denominator is an explicit proof
obligation; zero evidence is handled by `updateResult` below. -/
noncomputable def posterior (M : Model Theta X A Y) (b : Belief Theta X)
    (a : A) (y : Y) (h : evidence M b a y ≠ 0) : Belief Theta X where
  mass theta x' := jointObservationMass M b a y theta x' / evidence M b a y
  nonneg theta x' :=
    div_nonneg (jointObservationMass_nonneg M b a y theta x') (evidence_nonneg M b a y)
  sum_one := by
    let e : ℝ := evidence M b a y
    have he : e ≠ 0 := by simpa [e] using h
    calc
      (∑ theta : Theta,
          ∑ x' : X, jointObservationMass M b a y theta x' / e) =
          ∑ theta : Theta,
            (∑ x' : X, jointObservationMass M b a y theta x') / e := by
              apply Finset.sum_congr rfl
              intro theta htheta
              rw [Finset.sum_div]
      _ = (∑ theta : Theta,
            ∑ x' : X, jointObservationMass M b a y theta x') / e := by
              rw [Finset.sum_div]
      _ = e / e := by rfl
      _ = 1 := div_self he

@[simp] theorem posterior_mass (M : Model Theta X A Y) (b : Belief Theta X)
    (a : A) (y : Y) (h : evidence M b a y ≠ 0)
    (theta : Theta) (x' : X) :
    (posterior M b a y h).mass theta x' =
      jointObservationMass M b a y theta x' / evidence M b a y := rfl

/-- Explicit interface result required by the source for impossible observations. -/
inductive UpdateResult
    (Theta : Type uTheta) (X : Type uX) [Fintype Theta] [Fintype X] where
  | modelConflict
  | updated (belief : Belief Theta X)

/-- Return `modelConflict` exactly on a zero-denominator observation. -/
noncomputable def updateResult (M : Model Theta X A Y) (b : Belief Theta X)
    (a : A) (y : Y) : UpdateResult Theta X := by
  classical
  by_cases h : evidence M b a y = 0
  · exact .modelConflict
  · exact .updated (posterior M b a y h)

theorem updateResult_eq_modelConflict_iff
    (M : Model Theta X A Y) (b : Belief Theta X) (a : A) (y : Y) :
    updateResult M b a y = .modelConflict ↔ evidence M b a y = 0 := by
  classical
  unfold updateResult
  by_cases h : evidence M b a y = 0 <;> simp [h]

/-- One complete Bayes-interface step. Both the predictive observation law and
the deterministic posterior/conflict update are functions only of `(b,a)`. -/
structure BeliefStep (Theta : Type uTheta) (X : Type uX) (Y : Type uY)
    [Fintype Theta] [Fintype X] [Fintype Y] where
  observation : FiniteLaw Y
  update : Y → UpdateResult Theta X
  conflict_iff_zero : ∀ y, update y = .modelConflict ↔ observation.mass y = 0

noncomputable def beliefStep (M : Model Theta X A Y) (b : Belief Theta X)
    (a : A) : BeliefStep Theta X Y where
  observation := observationLaw M b a
  update := updateResult M b a
  conflict_iff_zero y := by
    simpa using updateResult_eq_modelConflict_iff M b a y

/-- Conditional expected immediate reward under belief `b` and action `a`.
This is the reward component of the belief-state control reduction. -/
def beliefReward (r : Theta → X → A → ℝ) (b : Belief Theta X) (a : A) : ℝ :=
  ∑ theta : Theta, ∑ x : X, b.mass theta x * r theta x a

/-- Belief expectation of a continuation value after the next observation.
Impossible observations contribute zero because their predictive mass is zero. -/
noncomputable def continuationExpectation
    (M : Model Theta X A Y) (b : Belief Theta X) (a : A)
    (V : Belief Theta X → ℝ) : ℝ :=
  ∑ y : Y, evidence M b a y *
    match updateResult M b a y with
    | .modelConflict => 0
    | .updated b' => V b'

/-- One-step discounted control quantity written entirely in belief coordinates.
For any continuation value `V`, it depends only on `(b,a)`. -/
noncomputable def beliefControlStep
    (M : Model Theta X A Y) (r : Theta → X → A → ℝ)
    (beta : ℝ) (V : Belief Theta X → ℝ)
    (b : Belief Theta X) (a : A) : ℝ :=
  beliefReward r b a + beta * continuationExpectation M b a V

/-- Complete one-step control interface required by belief-state dynamic
programming: observation law, deterministic Bayes update/model conflict, and
conditional expected reward are all functions of `(b,a)`. -/
structure BeliefControlStep
    (Theta : Type uTheta) (X : Type uX) (Y : Type uY)
    [Fintype Theta] [Fintype X] [Fintype Y] where
  bayes : BeliefStep Theta X Y
  reward : ℝ

noncomputable def controlStep
    (M : Model Theta X A Y) (r : Theta → X → A → ℝ)
    (b : Belief Theta X) (a : A) : BeliefControlStep Theta X Y where
  bayes := beliefStep M b a
  reward := beliefReward r b a

@[simp] theorem controlStep_reward
    (M : Model Theta X A Y) (r : Theta → X → A → ℝ)
    (b : Belief Theta X) (a : A) :
    (controlStep M r b a).reward = beliefReward r b a := rfl

end UEOT.V3.FiniteBayesBelief
