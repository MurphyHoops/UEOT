import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# P-DDH-03 — finite exponential-family I-projection

The frozen UEOT Core v3 §23.3 statement is finite-dimensional.  A strictly
positive baseline law `p0` on a finite state space `Γ`, a prescribed feature
map `F : Γ → ℝ^k`, and a finite natural parameter `theta : ℝ^k` determine
the exponential tilt

`q_theta ∝ p0 * exp(theta · F)`.

If a target moment `m` is actually represented by that finite parameter, then
the tilt uniquely minimizes `KL(q || p0)` over every probability law with the
same moment.  This module deliberately does not assert that boundary moments
have a finite-parameter representation.

The baseline is represented by a `PMF Γ`, while competitors are quantified
directly as arbitrary probability measures on `Γ`.  The proof uses Mathlib's
`Measure.tilted` and its log-likelihood-ratio identities.  Strict positivity
of `p0` makes every candidate law absolutely continuous with respect to the
baseline.
-/

namespace UEOT.V3.ExponentialFamilyIProjection

noncomputable section

open MeasureTheory InformationTheory Real Set
open scoped ENNReal NNReal BigOperators

universe uΓ uJ

variable {Γ : Type uΓ} [MeasurableSpace Γ]

/-- A full-support baseline PMF dominates every measure on the same measurable
space.  Finiteness itself is not needed for this bridge. -/
lemma measure_ac_pmf_of_pos
    (p : PMF Γ) (μ : Measure Γ) (hp : ∀ x, p x ≠ 0) :
    μ ≪ p.toMeasure := by
  refine Measure.AbsolutelyContinuous.mk ?_
  intro s hs hps
  have hdis : Disjoint p.support s :=
    (p.toMeasure_apply_eq_zero_iff hs).mp hps
  have hsup : p.support = Set.univ := by
    ext x
    simp [PMF.mem_support_iff, hp x]
  have hs0 : s = ∅ := by
    rw [hsup] at hdis
    simpa using hdis
  simp [hs0]

section Finite

variable [Fintype Γ] [MeasurableSingletonClass Γ]

/-- Every real-valued function on the finite state space is integrable against
every finite measure. -/
lemma finite_type_integrable
    (μ : Measure Γ) [IsFiniteMeasure μ] (f : Γ → ℝ) :
    Integrable f μ := by
  have h := IntegrableOn.of_finite
    (μ := μ) (f := f) (s := (Set.univ : Set Γ)) (Set.toFinite _)
  simpa only [IntegrableOn, Measure.restrict_univ] using h

/-- KL of the finite exponential tilt against its baseline, written in the
standard log-partition form. -/
lemma tilted_kl_toReal
    (p : PMF Γ) (f : Γ → ℝ) :
    (klDiv (p.toMeasure.tilted f) p.toMeasure).toReal =
      (∫ x, f x ∂(p.toMeasure.tilted f)) -
        log (∫ x, exp (f x) ∂p.toMeasure) := by
  have hExp : Integrable (fun x => exp (f x)) p.toMeasure :=
    finite_type_integrable _ _
  letI : IsProbabilityMeasure (p.toMeasure.tilted f) :=
    isProbabilityMeasure_tilted hExp
  have htp : p.toMeasure.tilted f ≪ p.toMeasure :=
    tilted_absolutelyContinuous _ _
  have hllrtp :
      Integrable
        (llr (p.toMeasure.tilted f) p.toMeasure)
        (p.toMeasure.tilted f) :=
    finite_type_integrable _ _
  rw [toReal_klDiv htp hllrtp]
  have hmeas : AEMeasurable f p.toMeasure :=
    (measurable_of_finite f).aemeasurable
  have hformula0 :
      llr (p.toMeasure.tilted f) p.toMeasure =ᵐ[p.toMeasure]
        (fun x =>
          f x - log (∫ z, exp (f z) ∂p.toMeasure) +
            llr p.toMeasure p.toMeasure x) := by
    simpa using
      (llr_tilted_left
        (μ := p.toMeasure) (ν := p.toMeasure) (f := f)
        (Measure.AbsolutelyContinuous.rfl) hExp hmeas)
  have hformula := htp.ae_eq hformula0
  have hself := htp.ae_eq (llr_self p.toMeasure)
  have hpoint :
      llr (p.toMeasure.tilted f) p.toMeasure =ᵐ[p.toMeasure.tilted f]
        (fun x => f x - log (∫ z, exp (f z) ∂p.toMeasure)) := by
    filter_upwards [hformula, hself] with x hx hs
    rw [hx, hs]
    simp only [Pi.zero_apply, add_zero]
  rw [integral_congr_ae hpoint]
  rw [integral_sub (finite_type_integrable _ _) (integrable_const _)]
  simp

/-- Finite-support KL Pythagorean identity for an exponential tilt.  The only
constraint needed here is equality of the score expectation. -/
lemma kl_pythagorean_toReal
    (p : PMF Γ) (Q : Measure Γ) [IsProbabilityMeasure Q]
    (hp : ∀ x, p x ≠ 0) (f : Γ → ℝ)
    (hsame :
      (∫ x, f x ∂Q) =
        ∫ x, f x ∂(p.toMeasure.tilted f)) :
    (klDiv Q p.toMeasure).toReal =
      (klDiv Q (p.toMeasure.tilted f)).toReal +
        (klDiv (p.toMeasure.tilted f) p.toMeasure).toReal := by
  have hExp : Integrable (fun x => exp (f x)) p.toMeasure :=
    finite_type_integrable _ _
  letI : IsProbabilityMeasure (p.toMeasure.tilted f) :=
    isProbabilityMeasure_tilted hExp
  have hQp : Q ≪ p.toMeasure :=
    measure_ac_pmf_of_pos p Q hp
  have hpt : p.toMeasure ≪ p.toMeasure.tilted f :=
    absolutelyContinuous_tilted hExp
  have hQt : Q ≪ p.toMeasure.tilted f :=
    hQp.trans hpt
  have hfQ : Integrable f Q :=
    finite_type_integrable _ _
  have hllrQp : Integrable (llr Q p.toMeasure) Q :=
    finite_type_integrable _ _
  have hllrQt :
      Integrable
        (llr Q (p.toMeasure.tilted f))
        Q :=
    finite_type_integrable _ _
  have hright :=
    integral_llr_tilted_right
      (μ := Q) (ν := p.toMeasure) (f := f)
      hQp hfQ hExp hllrQp
  have hKLQp :
      (klDiv Q p.toMeasure).toReal =
        ∫ x, llr Q p.toMeasure x ∂Q := by
    rw [toReal_klDiv hQp hllrQp]
    simp
  have hKLQt :
      (klDiv Q (p.toMeasure.tilted f)).toReal =
        ∫ x, llr Q (p.toMeasure.tilted f) x ∂Q := by
    rw [toReal_klDiv hQt hllrQt]
    simp
  rw [hKLQp, hKLQt, tilted_kl_toReal p f, hright, hsame]
  ring

variable {J : Type uJ} [Fintype J]

/-- Finite natural-parameter score `theta · F(γ)`. -/
def score (theta : J → ℝ) (F : Γ → J → ℝ) (γ : Γ) : ℝ :=
  ∑ j, theta j * F γ j

/-- Coordinate moment of a finite law. -/
def moment (μ : Measure Γ) (F : Γ → J → ℝ) (j : J) : ℝ :=
  ∫ γ, F γ j ∂μ

/-- The score expectation is the natural-parameter pairing with the vector
moment. -/
lemma integral_score_eq_sum_moment
    (μ : Measure Γ) [IsFiniteMeasure μ]
    (theta : J → ℝ) (F : Γ → J → ℝ) :
    (∫ γ, score theta F γ ∂μ) =
      ∑ j, theta j * moment μ F j := by
  unfold score moment
  rw [integral_finsetSum Finset.univ]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [integral_const_mul]
  · intro j hj
    exact finite_type_integrable _ _

/-- Equal vector moments imply equal score expectations for every finite
natural parameter. -/
lemma integral_score_eq_of_moment_eq
    (μ ν : Measure Γ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (theta : J → ℝ) (F : Γ → J → ℝ)
    (h : ∀ j, moment μ F j = moment ν F j) :
    (∫ γ, score theta F γ ∂μ) =
      ∫ γ, score theta F γ ∂ν := by
  rw [integral_score_eq_sum_moment μ theta F,
    integral_score_eq_sum_moment ν theta F]
  apply Finset.sum_congr rfl
  intro j hj
  rw [h j]

/-- Source-facing P-DDH-03.

For an arbitrary finite dimension `k`, let `m` be a target moment actually
represented by the finite parameter `theta`.  Then the corresponding
exponential tilt globally minimizes KL over every probability law with
that moment, and equality holds exactly for the tilt itself.

No full-rank, feature-independence, strict-convexity, positive-definite
covariance, or unique-parameter hypothesis is used.  In particular `k = 0`,
redundant features, constant features, and singular covariance remain allowed.
-/
theorem p_ddh_03
    {k : ℕ}
    (p0 : PMF Γ) (Q : Measure Γ) [IsProbabilityMeasure Q]
    (hp0 : ∀ γ, 0 < p0 γ)
    (F : Γ → Fin k → ℝ) (m : Fin k → ℝ) (theta : Fin k → ℝ)
    (htheta : ∀ j,
      moment (p0.toMeasure.tilted (score theta F)) F j = m j)
    (hQ : ∀ j, moment Q F j = m j) :
    klDiv (p0.toMeasure.tilted (score theta F)) p0.toMeasure ≤
        klDiv Q p0.toMeasure ∧
      (klDiv Q p0.toMeasure =
          klDiv (p0.toMeasure.tilted (score theta F)) p0.toMeasure ↔
        Q = p0.toMeasure.tilted (score theta F)) := by
  have hExp :
      Integrable
        (fun γ => exp (score theta F γ))
        p0.toMeasure :=
    finite_type_integrable _ _
  letI : IsProbabilityMeasure (p0.toMeasure.tilted (score theta F)) :=
    isProbabilityMeasure_tilted hExp
  have hmom : ∀ j,
      moment Q F j =
        moment (p0.toMeasure.tilted (score theta F)) F j := by
    intro j
    exact (hQ j).trans (htheta j).symm
  have hscore :
      (∫ γ, score theta F γ ∂Q) =
        ∫ γ, score theta F γ ∂(p0.toMeasure.tilted (score theta F)) :=
    integral_score_eq_of_moment_eq _ _ theta F hmom
  have hpy :=
    kl_pythagorean_toReal
      p0 Q (fun γ => (hp0 γ).ne') (score theta F) hscore
  have hQp : Q ≪ p0.toMeasure :=
    measure_ac_pmf_of_pos p0 Q (fun γ => (hp0 γ).ne')
  have htp :
      p0.toMeasure.tilted (score theta F) ≪ p0.toMeasure :=
    tilted_absolutelyContinuous _ _
  have hpt :
      p0.toMeasure ≪ p0.toMeasure.tilted (score theta F) :=
    absolutelyContinuous_tilted hExp
  have hQt :
      Q ≪ p0.toMeasure.tilted (score theta F) :=
    hQp.trans hpt
  have hllrQp :
      Integrable (llr Q p0.toMeasure) Q :=
    finite_type_integrable _ _
  have hllrtp :
      Integrable
        (llr (p0.toMeasure.tilted (score theta F)) p0.toMeasure)
        (p0.toMeasure.tilted (score theta F)) :=
    finite_type_integrable _ _
  have hllrQt :
      Integrable
        (llr Q (p0.toMeasure.tilted (score theta F)))
        Q :=
    finite_type_integrable _ _
  have hQp_ne :
      klDiv Q p0.toMeasure ≠ ∞ :=
    klDiv_ne_top hQp hllrQp
  have htp_ne :
      klDiv (p0.toMeasure.tilted (score theta F)) p0.toMeasure ≠ ∞ :=
    klDiv_ne_top htp hllrtp
  have hQt_ne :
      klDiv Q (p0.toMeasure.tilted (score theta F)) ≠ ∞ :=
    klDiv_ne_top hQt hllrQt
  constructor
  · apply (ENNReal.toReal_le_toReal htp_ne hQp_ne).mp
    have hnonneg :
        0 ≤
          (klDiv Q
            (p0.toMeasure.tilted (score theta F))).toReal :=
      ENNReal.toReal_nonneg
    linarith
  · constructor
    · intro heq
      have heqReal := congrArg ENNReal.toReal heq
      have hzReal :
          (klDiv Q
            (p0.toMeasure.tilted (score theta F))).toReal = 0 := by
        linarith
      have hz :
          klDiv Q
            (p0.toMeasure.tilted (score theta F)) = 0 := by
        rcases (ENNReal.toReal_eq_zero_iff _).mp hzReal with hz | hz
        · exact hz
        · exact (hQt_ne hz).elim
      exact (klDiv_eq_zero_iff).mp hz
    · intro hQeq
      rw [hQeq]

end Finite

end

end UEOT.V3.ExponentialFamilyIProjection
