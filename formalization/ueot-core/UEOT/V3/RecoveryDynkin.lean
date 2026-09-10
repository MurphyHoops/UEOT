import UEOT.V3.RecoveryContinuous

/-!
# P-REC-02 Dynkin-output interface

Core v3 does not license the recovery estimate from a symbolic generator
inequality alone.  The stochastic-process layer must first justify Dynkin's
formula, localization/integrability, and hence local absolute continuity of
m(t) = E[W(X_t)] together with the almost-everywhere identity between m' and
the expected generator drift.

This module formalizes exactly that output interface.  It does not postulate a
process-specific Dynkin theorem and therefore does not hide explosion/domain
issues.  A model-specific process theorem can discharge this certificate and
then reuse the source-regularity scalar Grönwall result.
-/

namespace UEOT.V3.RecoveryDynkin

open Set MeasureTheory
open UEOT.V3.RecoveryContinuous

/-- The analytic output that a valid Dynkin/localization argument must provide
on a compact time interval.  `ell t` represents E[(L W)(X_t)]. -/
structure DynkinExpectationCertificate
    (m ell : ℝ → ℝ) (T : ℝ) : Prop where
  ac : AbsolutelyContinuousOnInterval m 0 T
  deriv_eq :
    ∀ᵐ t ∂volume.restrict (Icc 0 T), deriv m t = ell t

/-- Once a valid Dynkin certificate identifies the derivative of the expected
Lyapunov energy with the expected generator drift, the v3 drift inequality
implies the exact exponential recovery estimate. -/
theorem expectation_recovery_of_dynkin
    (m ell : ℝ → ℝ) (a b T : ℝ)
    (ha : 0 < a) (hT : 0 ≤ T)
    (hDynkin : DynkinExpectationCertificate m ell T)
    (hdrift :
      ∀ᵐ t ∂volume.restrict (Icc 0 T),
        ell t ≤ -a * m t + b) :
    ∀ t ∈ Icc 0 T,
      m t ≤
        Real.exp (-a * t) * m 0 +
          (b / a) * (1 - Real.exp (-a * t)) := by
  apply exponential_recovery_bound_ac_ae m a b T ha hT hDynkin.ac
  filter_upwards [hDynkin.deriv_eq, hdrift] with t hder hle
  simpa [hder] using hle

/-- Final deterministic expectation-to-distance wrapper of P-REC-02.  The
pointwise Lyapunov lower bound enters the stochastic process layer through the
expected domination hypothesis `c * d2 t <= m t`; this theorem performs only
the logically subsequent division by c. -/
theorem meanSq_recovery_of_dynkin
    (m ell d2 : ℝ → ℝ) (W0 a b c T : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hT : 0 ≤ T)
    (hDynkin : DynkinExpectationCertificate m ell T)
    (hm0 : m 0 = W0)
    (hdrift :
      ∀ᵐ t ∂volume.restrict (Icc 0 T),
        ell t ≤ -a * m t + b)
    (hdom : ∀ t ∈ Icc 0 T, c * d2 t ≤ m t) :
    ∀ t ∈ Icc 0 T,
      d2 t ≤
        (Real.exp (-a * t) * W0 +
          (b / a) * (1 - Real.exp (-a * t))) / c := by
  intro t ht
  have hm := expectation_recovery_of_dynkin
    m ell a b T ha hT hDynkin hdrift t ht
  rw [hm0] at hm
  exact sqDistance_le_of_energy_bound hc (hdom t ht) hm

/-! ## Pointwise-to-expectation bridge required by the literal source -/

/-- A pointwise generator drift inequality integrates to the corresponding
expected drift inequality under any probability law, provided the two
quantities are integrable. -/
theorem expected_generator_drift_of_pointwise
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (W LW : X → ℝ) (a b : ℝ)
    (hW : Integrable W μ) (hLW : Integrable LW μ)
    (hpoint : ∀ x, LW x ≤ -a * W x + b) :
    (∫ x, LW x ∂μ) ≤ -a * (∫ x, W x ∂μ) + b := by
  have hscaled : Integrable (fun x => -a * W x) μ :=
    Integrable.const_mul hW (-a)
  have hrhs : Integrable (fun x => -a * W x + b) μ :=
    hscaled.add (integrable_const _)
  calc
    (∫ x, LW x ∂μ) ≤ ∫ x, (-a * W x + b) ∂μ :=
      integral_mono hLW hrhs hpoint
    _ = -a * (∫ x, W x ∂μ) + b := by
      rw [integral_add hscaled (integrable_const _), integral_const_mul,
        integral_const, probReal_univ]
      simp

/-- The pointwise Lyapunov domination `c*d² <= W` integrates to the exact
expected domination used by the scalar recovery theorem. -/
theorem expected_distance_domination_of_pointwise
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X)
    (W d2 : X → ℝ) (c : ℝ)
    (hW : Integrable W μ) (hd2 : Integrable d2 μ)
    (hpoint : ∀ x, c * d2 x ≤ W x) :
    c * (∫ x, d2 x ∂μ) ≤ ∫ x, W x ∂μ := by
  have hscaled : Integrable (fun x => c * d2 x) μ :=
    Integrable.const_mul hd2 c
  calc
    c * (∫ x, d2 x ∂μ) = ∫ x, c * d2 x ∂μ := by
      rw [integral_const_mul]
    _ ≤ ∫ x, W x ∂μ := integral_mono hscaled hW hpoint

/-- Literal source-facing P-REC-02 wrapper.  The process-specific assumptions
"W is in the generator domain; Dynkin formula/localization/integrability are
valid" are represented by `hDynkin` together with the displayed integrability
hypotheses.  Unlike the lower-level theorem, this wrapper starts from the
source's pointwise generator inequality `LW <= -a W + b` and pointwise
Lyapunov domination `c*d² <= W`, and derives the needed expectation bounds. -/
theorem p_rec_02
    {X : Type*} [MeasurableSpace X]
    (law : ℝ → Measure X)
    (W LW d2 : X → ℝ) (x0 : X)
    (a b c T : ℝ)
    (ha : 0 < a) (_hb : 0 ≤ b) (hc : 0 < c) (hT : 0 ≤ T)
    (hprob : ∀ t ∈ Icc 0 T, IsProbabilityMeasure (law t))
    (hWint : ∀ t ∈ Icc 0 T, Integrable W (law t))
    (hLWint : ∀ t ∈ Icc 0 T, Integrable LW (law t))
    (hd2int : ∀ t ∈ Icc 0 T, Integrable d2 (law t))
    (hDynkin : DynkinExpectationCertificate
      (fun t => ∫ x, W x ∂law t)
      (fun t => ∫ x, LW x ∂law t) T)
    (hinit : (∫ x, W x ∂law 0) = W x0)
    (hgenerator : ∀ x, LW x ≤ -a * W x + b)
    (hdom : ∀ x, c * d2 x ≤ W x) :
    ∀ t ∈ Icc 0 T,
      (∫ x, d2 x ∂law t) ≤
        (Real.exp (-a * t) * W x0 +
          (b / a) * (1 - Real.exp (-a * t))) / c := by
  have hdrift :
      ∀ᵐ t ∂volume.restrict (Icc 0 T),
        (∫ x, LW x ∂law t) ≤ -a * (∫ x, W x ∂law t) + b := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    letI : IsProbabilityMeasure (law t) := hprob t ht
    exact expected_generator_drift_of_pointwise
      (law t) W LW a b (hWint t ht) (hLWint t ht) hgenerator
  have hdomExpected :
      ∀ t ∈ Icc 0 T,
        c * (∫ x, d2 x ∂law t) ≤ ∫ x, W x ∂law t := by
    intro t ht
    exact expected_distance_domination_of_pointwise
      (law t) W d2 c (hWint t ht) (hd2int t ht) hdom
  exact meanSq_recovery_of_dynkin
    (fun t => ∫ x, W x ∂law t)
    (fun t => ∫ x, LW x ∂law t)
    (fun t => ∫ x, d2 x ∂law t)
    (W x0) a b c T ha hc hT hDynkin hinit hdrift hdomExpected

end UEOT.V3.RecoveryDynkin
