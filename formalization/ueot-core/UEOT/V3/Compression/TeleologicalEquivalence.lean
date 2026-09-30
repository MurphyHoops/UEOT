import UEOT.V3.DualDriveGauge
import UEOT.V3.RewardInfinite

/-!
# Experimental teleological-equivalence calculus

This module tests whether P-DDH-01 (dual-drive gauge freedom) and P-TEL-01
(discounted potential shaping) share a nontrivial compression core.

The candidate is deliberately stratified.  Numerically identical objectives,
positive-affine equivalent policy values, order-equivalent policy values, and
equal maximizer sets are not conflated.

The experiment is uncounted.  In particular, the existence of this hierarchy
does not itself show that either source theorem can be deleted: DDH still owns
the gauge algebra, while TEL still owns the telescoping and infinite-horizon
convergence analysis.
-/

namespace UEOT.V3.Compression.TeleologicalEquivalence

open Filter Topology
open UEOT.Reward

universe uP uX

/-- Strongest level: the two numerical value representations agree pointwise. -/
def ValueEqual {P : Type uP} (V W : P → ℝ) : Prop :=
  ∀ p, W p = V p

/-- Policy values differ by one common positive affine transformation. -/
def PositiveAffineEquivalent {P : Type uP} (V W : P → ℝ) : Prop :=
  ∃ a b : ℝ, 0 < a ∧ ∀ p, W p = a * V p + b

/-- The two value functions induce the same weak ordering on policies. -/
def OrderEquivalent {P : Type uP} (V W : P → ℝ) : Prop :=
  ∀ p q, W p ≤ W q ↔ V p ≤ V q

/-- The two value functions have exactly the same maximizers. -/
def MaximizerEquivalent {P : Type uP} (V W : P → ℝ) : Prop :=
  ∀ p, IsMaximizer W p ↔ IsMaximizer V p

theorem valueEqual_refl {P : Type uP} (V : P → ℝ) :
    ValueEqual V V := by
  intro p
  rfl

theorem valueEqual_to_positiveAffineEquivalent
    {P : Type uP} {V W : P → ℝ}
    (h : ValueEqual V W) :
    PositiveAffineEquivalent V W := by
  refine ⟨1, 0, zero_lt_one, ?_⟩
  intro p
  simpa using h p

theorem positiveAffineEquivalent_to_orderEquivalent
    {P : Type uP} {V W : P → ℝ}
    (h : PositiveAffineEquivalent V W) :
    OrderEquivalent V W := by
  rcases h with ⟨a, b, ha, hval⟩
  intro p q
  rw [hval p, hval q]
  constructor <;> intro hle <;> nlinarith

theorem orderEquivalent_to_maximizerEquivalent
    {P : Type uP} {V W : P → ℝ}
    (h : OrderEquivalent V W) :
    MaximizerEquivalent V W := by
  intro p
  constructor
  · intro hp q
    exact (h q p).mp (hp q)
  · intro hp q
    exact (h q p).mpr (hp q)

theorem positiveAffineEquivalent_to_maximizerEquivalent
    {P : Type uP} {V W : P → ℝ}
    (h : PositiveAffineEquivalent V W) :
    MaximizerEquivalent V W :=
  orderEquivalent_to_maximizerEquivalent
    (positiveAffineEquivalent_to_orderEquivalent h)

/-- Positive-affine teleological equivalence composes. -/
theorem positiveAffineEquivalent_trans
    {P : Type uP} {U V W : P → ℝ}
    (hUV : PositiveAffineEquivalent U V)
    (hVW : PositiveAffineEquivalent V W) :
    PositiveAffineEquivalent U W := by
  rcases hUV with ⟨a, b, ha, hV⟩
  rcases hVW with ⟨c, d, hc, hW⟩
  refine ⟨c * a, c * b + d, mul_pos hc ha, ?_⟩
  intro p
  rw [hW p, hV p]
  ring

/-! ## P-DDH-01 adapter -/

/-- Dual-drive gauge freedom gives the strongest equivalence level: the
combined objective is numerically identical pointwise. -/
theorem dualDriveGauge_valueEqual
    {X : Type uX}
    (piVal phiVal chiVal : X → ℝ) (lambdaVal : ℝ) :
    ValueEqual
      (fun x => piVal x - lambdaVal * phiVal x)
      (fun x =>
        (piVal x + lambdaVal * chiVal x) -
          lambdaVal * (phiVal x + chiVal x)) := by
  intro x
  exact UEOT.V3.DualDriveGauge.p_ddh_01_pointwise
    piVal phiVal chiVal lambdaVal x

/-- Consequently any policy/objective domain indexed by `X` has the same
maximizers after the DDH gauge transformation.  This is downstream of the
source algebraic identity, not a replacement for it. -/
theorem dualDriveGauge_maximizerEquivalent
    {X : Type uX}
    (piVal phiVal chiVal : X → ℝ) (lambdaVal : ℝ) :
    MaximizerEquivalent
      (fun x => piVal x - lambdaVal * phiVal x)
      (fun x =>
        (piVal x + lambdaVal * chiVal x) -
          lambdaVal * (phiVal x + chiVal x)) :=
  positiveAffineEquivalent_to_maximizerEquivalent
    (valueEqual_to_positiveAffineEquivalent
      (dualDriveGauge_valueEqual piVal phiVal chiVal lambdaVal))

/-! ## P-TEL-01 adapter -/

/-- The analytic shaping hypotheses of P-TEL-01 produce a positive-affine
relation between the policy-value functions. -/
theorem rewardShaping_positiveAffineEquivalent
    {P : Type uP}
    (β a c M ψ0 : ℝ)
    (r ψ : P → ℕ → ℝ)
    (V V' : P → ℝ)
    (hβ : |β| < 1)
    (ha : 0 < a)
    (hψ0 : ∀ p, ψ p 0 = ψ0)
    (hψ : ∀ p n, |ψ p n| ≤ M)
    (hr : ∀ p,
      Tendsto (fun n => discounted β (r p) n) atTop (𝓝 (V p)))
    (hr' : ∀ p,
      Tendsto
        (fun n => discounted β
          (fun t => a * r p t + β * ψ p (t + 1) - ψ p t + c) n)
        atTop (𝓝 (V' p))) :
    PositiveAffineEquivalent V V' := by
  refine ⟨a, -ψ0 + c * (1 - β)⁻¹, ha, ?_⟩
  intro p
  rw [UEOT.V3.RewardInfinite.shaping_limit_value
    β a c M (V p) (V' p) (r p) (ψ p)
    hβ (hψ p) (hr p) (hr' p), hψ0 p]
  ring

/-- Exact source-signature rederivation of the policy-value form of P-TEL-01
through the equivalence hierarchy.  The analytic work remains in
`shaping_limit_value`; the generic layer owns only the order/maximizer step. -/
theorem policy_values_affine_via_teleologicalEquivalence
    {P : Type uP}
    (β a c M ψ0 : ℝ)
    (r ψ : P → ℕ → ℝ)
    (V V' : P → ℝ)
    (hβ : |β| < 1)
    (ha : 0 < a)
    (hψ0 : ∀ p, ψ p 0 = ψ0)
    (hψ : ∀ p n, |ψ p n| ≤ M)
    (hr : ∀ p,
      Tendsto (fun n => discounted β (r p) n) atTop (𝓝 (V p)))
    (hr' : ∀ p,
      Tendsto
        (fun n => discounted β
          (fun t => a * r p t + β * ψ p (t + 1) - ψ p t + c) n)
        atTop (𝓝 (V' p))) :
    (∀ p, V' p = a * V p - ψ0 + c * (1 - β)⁻¹) ∧
      ∀ p, IsMaximizer V' p ↔ IsMaximizer V p := by
  have hval :
      ∀ p, V' p = a * V p - ψ0 + c * (1 - β)⁻¹ := by
    intro p
    rw [UEOT.V3.RewardInfinite.shaping_limit_value
      β a c M (V p) (V' p) (r p) (ψ p)
      hβ (hψ p) (hr p) (hr' p), hψ0 p]
  have hAff : PositiveAffineEquivalent V V' := by
    refine ⟨a, -ψ0 + c * (1 - β)⁻¹, ha, ?_⟩
    intro p
    rw [hval p]
    ring
  exact ⟨hval, positiveAffineEquivalent_to_maximizerEquivalent hAff⟩

end UEOT.V3.Compression.TeleologicalEquivalence
