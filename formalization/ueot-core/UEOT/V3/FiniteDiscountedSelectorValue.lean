import UEOT.V3.FiniteDiscountedSelector
import Mathlib.Tactic

/-!
# Generic stationary-selector fixed-point value

This module extends the selector infrastructure introduced for P-QUO-01 from
"selectors already known to be Bellman-optimal" to arbitrary stationary
deterministic selectors. It supplies the policy-evaluation fixed point and its
residual certificate needed by the approximate quotient theorem P-QUO-02.
-/

namespace UEOT.V3.FiniteDiscountedControl

open Filter Topology
open CausalPolicy

universe uX uA

variable {X : Type uX} [Fintype X]
variable {A : X → Type uA} [∀ x, Fintype (A x)] [∀ x, Nonempty (A x)]

namespace Model

/-- The unique discounted value fixed point of an arbitrary stationary
deterministic selector. -/
noncomputable def selectorValue (M : Model X A) (σ : ∀ x, A x) : X → ℝ :=
  ContractingWith.fixedPoint (M.selectorBellman σ) (M.selectorBellman_contracting σ)

/-- The selector value is a fixed point of its policy-evaluation Bellman map. -/
theorem selectorValue_fixed (M : Model X A) (σ : ∀ x, A x) :
    M.selectorBellman σ (M.selectorValue σ) = M.selectorValue σ :=
  (M.selectorBellman_contracting σ).fixedPoint_isFixedPt

/-- The selector policy-evaluation fixed point is unique. -/
theorem selectorValue_unique (M : Model X A) (σ : ∀ x, A x)
    {v : X → ℝ} (hv : M.selectorBellman σ v = v) :
    v = M.selectorValue σ :=
  (M.selectorBellman_contracting σ).fixedPoint_unique hv

/-- Policy-evaluation iteration converges from every initial value to the
selector's own value fixed point. -/
theorem selectorValueIteration_tendsto_fixedPoint
    (M : Model X A) (σ : ∀ x, A x) (v₀ : X → ℝ) :
    Tendsto (fun n => (M.selectorBellman σ)^[n] v₀)
      atTop (𝓝 (M.selectorValue σ)) := by
  simpa [selectorValue] using
    (M.selectorBellman_contracting σ).tendsto_iterate_fixedPoint v₀

/-- A-posteriori residual certificate for an arbitrary stationary selector:
`‖v - V^σ‖∞ ≤ ‖v - T_σ v‖∞ / (1 - β)`. -/
theorem selectorValueError_le_residual
    (M : Model X A) (σ : ∀ x, A x) (v : X → ℝ) :
    dist v (M.selectorValue σ) ≤
      dist v (M.selectorBellman σ v) / (1 - M.discount) := by
  simpa [selectorValue] using
    (M.selectorBellman_contracting σ).dist_fixedPoint_le v

end Model

/-- Finite-horizon values of an arbitrary stationary deterministic selector
converge to its selector fixed-point value. -/
theorem selector_truncatedValue_tendsto_selectorValue
    (M : Model X A) (σ : ∀ x, A x) {t : ℕ} (x : X) :
    Tendsto (fun n => truncatedValue (selectorPolicy σ) M n (t := t) x)
      atTop (𝓝 (M.selectorValue σ x)) := by
  have hfun :=
    M.selectorValueIteration_tendsto_fixedPoint σ (fun _ : X => (0 : ℝ))
  have hx := tendsto_pi_nhds.mp hfun x
  exact hx.congr' <| Eventually.of_forall fun n =>
    (selector_truncatedValue_eq_iterate M σ n t x).symm

/-- The causal-policy infinite value of a stationary deterministic selector is
exactly its policy-evaluation fixed point. -/
theorem selector_infiniteValue_eq_selectorValue
    (M : Model X A) (σ : ∀ x, A x) {t : ℕ} (x : X) :
    infiniteValue (selectorPolicy σ) M (t := t) x = M.selectorValue σ x := by
  exact tendsto_nhds_unique
    (truncatedValue_tendsto_infiniteValue (selectorPolicy σ) M (t := t) x)
    (selector_truncatedValue_tendsto_selectorValue M σ (t := t) x)

end UEOT.V3.FiniteDiscountedControl
