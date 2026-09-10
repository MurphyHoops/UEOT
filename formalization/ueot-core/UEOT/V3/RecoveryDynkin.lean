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

end UEOT.V3.RecoveryDynkin
