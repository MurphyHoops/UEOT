import UEOT.Core.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

/-! P-STAT-03/04 on the simultaneous response-error event.
The probability of this event belongs to P-STAT-01/02, not these claims. -/
namespace UEOT.V3.Threshold

theorem threshold_classification (e estimate δ ε : ℝ)
    (error : |estimate - e| ≤ ε) (margin : ε < |e - δ|) :
    estimate ≤ δ ↔ e ≤ δ := by
  have hlow := (abs_le.mp error).1
  have hupp := (abs_le.mp error).2
  constructor
  · intro h
    by_contra hn
    have he : δ < e := lt_of_not_ge hn
    rw [abs_of_pos (sub_pos.mpr he)] at margin
    linarith
  · intro h
    rw [abs_of_nonpos (sub_nonpos.mpr h)] at margin
    linarith

theorem approximate_family {V : Type*} (e estimate : Finset V → ℝ) (δ η : ℝ)
    (error : ∀ S, |estimate S - e S| ≤ 2 * η)
    (margin : ∀ S, 2 * η < |e S - δ|) :
    {S | Finite.Minimal (fun T => estimate T ≤ δ) S} =
      {S | Finite.Minimal (fun T => e T ≤ δ) S} := by
  have h : (fun T => estimate T ≤ δ) = (fun T => e T ≤ δ) := by
    funext T
    exact propext (threshold_classification _ _ _ _ (error T) (margin T))
  rw [h]

theorem zero_classification (e estimate Δ τ η : ℝ)
    (nonneg : 0 ≤ e) (error : |estimate - e| ≤ 2 * η)
    (gap : 0 < e → Δ ≤ e) (lower : 2 * η < τ) (upper : τ < Δ - 2 * η) :
    estimate ≤ τ ↔ e = 0 := by
  have hlow := (abs_le.mp error).1
  have hupp := (abs_le.mp error).2
  constructor
  · intro h
    by_contra hn
    have he : 0 < e := lt_of_le_of_ne nonneg (Ne.symm hn)
    have hg := gap he
    linarith
  · intro h
    subst e
    linarith

theorem exact_family {V : Type*} (e estimate : Finset V → ℝ) (Δ τ η : ℝ)
    (nonneg : ∀ S, 0 ≤ e S) (error : ∀ S, |estimate S - e S| ≤ 2 * η)
    (gap : ∀ S, 0 < e S → Δ ≤ e S)
    (lower : 2 * η < τ) (upper : τ < Δ - 2 * η) :
    {S | Finite.Minimal (fun T => estimate T ≤ τ) S} =
      {S | Finite.Minimal (fun T => e T = 0) S} := by
  have h : (fun T => estimate T ≤ τ) = (fun T => e T = 0) := by
    funext T
    exact propext (zero_classification _ _ _ _ _ (nonneg T) (error T) (gap T) lower upper)
  rw [h]

end UEOT.V3.Threshold
