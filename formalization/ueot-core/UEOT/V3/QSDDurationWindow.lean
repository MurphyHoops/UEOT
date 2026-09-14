import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.OrderClosed

/-!
# P-QSD-03 — same-initial quasi-stationary duration window

This file formalizes the analytic implication in frozen Core 3 §10.3. The
process-specific quantities are indexed by an initial law, so the theorem uses
the same `μ` for both conditional-stability and survival bounds. This prevents
silently splicing a mixing estimate for one initial law with a survival estimate
for another. The theorem then solves the two exponential bounds and intersects
the resulting time constraints exactly as in the source.
-/

namespace UEOT.V3.QSDDurationWindow

open Real

/-- Lower endpoint imposed by start time, nonnegative time, and conditional
mixing accuracy. -/
noncomputable def lowerEndpoint
    (t0 C ε γ : ℝ) : ℝ :=
  max (max t0 0) (Real.log (C / ε) / γ)

/-- Upper endpoint imposed by the survival-probability threshold. -/
noncomputable def upperEndpoint
    (c p lam : ℝ) : ℝ :=
  Real.log (c / p) / lam

/-- Solving the conditional-stability exponential inequality. -/
theorem decay_le_threshold
    {C ε γ t : ℝ}
    (hC : 0 < C) (hε : 0 < ε) (hγ : 0 < γ)
    (ht : Real.log (C / ε) / γ ≤ t) :
    C * Real.exp (-(γ * t)) ≤ ε := by
  have hratio : 0 < C / ε := div_pos hC hε
  have hlog : Real.log (C / ε) ≤ γ * t := by
    have h := (div_le_iff₀ hγ).mp ht
    nlinarith
  have hexp : C / ε ≤ Real.exp (γ * t) := by
    calc
      C / ε = Real.exp (Real.log (C / ε)) := by
        rw [Real.exp_log hratio]
      _ ≤ Real.exp (γ * t) := Real.exp_le_exp.mpr hlog
  have hmain : C ≤ ε * Real.exp (γ * t) := by
    have h := (div_le_iff₀ hε).mp hexp
    nlinarith [h, Real.exp_pos (γ * t)]
  calc
    C * Real.exp (-(γ * t)) = C / Real.exp (γ * t) := by
      rw [Real.exp_neg]
      ring
    _ ≤ ε := (div_le_iff₀ (Real.exp_pos (γ * t))).2 (by
      nlinarith [hmain, Real.exp_pos (γ * t)])

/-- Solving the survival exponential inequality. -/
theorem threshold_le_survival
    {c p lam t : ℝ}
    (hc : 0 < c) (hp : 0 < p) (hlam : 0 < lam)
    (ht : t ≤ Real.log (c / p) / lam) :
    p ≤ c * Real.exp (-(lam * t)) := by
  have hratio : 0 < c / p := div_pos hc hp
  have hlog : lam * t ≤ Real.log (c / p) := by
    have h := (le_div_iff₀ hlam).mp ht
    nlinarith
  have hexp : Real.exp (lam * t) ≤ c / p := by
    calc
      Real.exp (lam * t) ≤ Real.exp (Real.log (c / p)) :=
        Real.exp_le_exp.mpr hlog
      _ = c / p := Real.exp_log hratio
  have hmain : p * Real.exp (lam * t) ≤ c := by
    have h := (le_div_iff₀ hp).mp hexp
    nlinarith [h, Real.exp_pos (lam * t)]
  calc
    p ≤ c / Real.exp (lam * t) :=
      (le_div_iff₀ (Real.exp_pos (lam * t))).2 hmain
    _ = c * Real.exp (-(lam * t)) := by
      rw [Real.exp_neg]
      ring

/-- **P-QSD-03.** For one fixed initial law `μ`, every time in the frozen closed
duration window simultaneously satisfies the requested conditional-stability
and survival thresholds. Equality of the endpoints is allowed, yielding a
singleton window. -/
theorem p_qsd_03
    {Init : Type*}
    (condError survival : Init → ℝ → ℝ)
    (μ : Init)
    (t0 C c γ lam ε p : ℝ)
    (hC : 0 < C) (hc : 0 < c) (hγ : 0 < γ) (hlam : 0 < lam)
    (hε : 0 < ε) (hp : 0 < p) (_hpc : p ≤ c)
    (hmix : ∀ t, t0 ≤ t → condError μ t ≤ C * Real.exp (-(γ * t)))
    (hsurv : ∀ t, t0 ≤ t → c * Real.exp (-(lam * t)) ≤ survival μ t)
    (_hwindow : lowerEndpoint t0 C ε γ ≤ upperEndpoint c p lam) :
    ∀ t ∈ Set.Icc (lowerEndpoint t0 C ε γ) (upperEndpoint c p lam),
      condError μ t ≤ ε ∧ p ≤ survival μ t := by
  intro t ht
  have ht0 : t0 ≤ t := le_trans (le_max_left t0 0) (le_trans
    (le_max_left (max t0 0) (Real.log (C / ε) / γ)) ht.1)
  have hlogmix : Real.log (C / ε) / γ ≤ t :=
    le_trans (le_max_right (max t0 0) (Real.log (C / ε) / γ)) ht.1
  have hlogsurv : t ≤ Real.log (c / p) / lam := ht.2
  constructor
  · exact le_trans (hmix t ht0) (decay_le_threshold hC hε hγ hlogmix)
  · exact le_trans (threshold_le_survival hc hp hlam hlogsurv) (hsurv t ht0)

/-- Nonemptiness of the frozen interval is exactly the endpoint inequality. -/
theorem window_nonempty_iff
    (t0 C ε γ c p lam : ℝ) :
    (Set.Icc (lowerEndpoint t0 C ε γ) (upperEndpoint c p lam)).Nonempty ↔
      lowerEndpoint t0 C ε γ ≤ upperEndpoint c p lam := by
  simp

end UEOT.V3.QSDDurationWindow
