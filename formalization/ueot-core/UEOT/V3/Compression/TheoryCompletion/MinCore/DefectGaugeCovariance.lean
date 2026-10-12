import UEOT.V3.Compression.TheoryCompletion.MinCore.CalibratedDefectComparison

/-!
# UEOT MINCORE — defect gauge covariance

This additive, uncounted research module sharpens the calibrated-defect
comparison into a structural covariance classification.

There are two distinct levels.

1. A general positive two-sided calibration
   `a * d <= d' <= b * d` preserves exact zero structure and finite budgets,
   but transports an exact triangle inequality only to a quasi-triangle
   inequality with explicit condition factor `b / a`.  Cross-stage
   contraction constants similarly acquire the target-upper/source-lower
   factor `b₁ / a₀`.

2. Positive stagewise scalar rescaling is a smaller genuine gauge class.
   Because every defect at one stage is multiplied by one common positive
   scalar, the exact triangle form is preserved.  The complete registered
   M-TC weighted-chain premise class therefore survives, with covariantly
   transformed coefficients
   `L'_n = (c_{n+1}/c_n) L_n` and
   `ε'_n = c_{n+1} ε_n`.

The distinction is deliberate: generic bi-Lipschitz calibration is not silently
identified with exact scalar gauge.  No frozen Core theorem or counted
compression generator is changed here.
-/

namespace UEOT.V3.Compression.TheoryCompletion.MinCore

open scoped BigOperators

universe u v

namespace DefectCalibration

variable {X : Type u}
variable {P Q : RelationDefectPresentation X}
variable {a b : ℝ}

/-- A general two-sided defect calibration transports an exact triangle bound
only as a quasi-triangle bound, with condition factor `b / a`.

This is a sufficient transported bound, not a claim that `b / a` is the
optimal quasi-triangle constant for a particular pair of presentations. -/
theorem triangle_quasi
    (C : DefectCalibration P Q a b)
    {x y z : X}
    (htri : P.defect x z ≤ P.defect x y + P.defect y z) :
    Q.defect x z ≤ (b / a) * (Q.defect x y + Q.defect y z) := by
  have hxy : P.defect x y ≤ Q.defect x y / a :=
    C.reverse_budget (hQ := le_rfl)
  have hyz : P.defect y z ≤ Q.defect y z / a :=
    C.reverse_budget (hQ := le_rfl)
  calc
    Q.defect x z ≤ b * P.defect x z := C.upper x z
    _ ≤ b * (P.defect x y + P.defect y z) :=
      mul_le_mul_of_nonneg_left htri C.b_nonneg
    _ ≤ b * (Q.defect x y / a + Q.defect y z / a) :=
      mul_le_mul_of_nonneg_left (add_le_add hxy hyz) C.b_nonneg
    _ = (b / a) * (Q.defect x y + Q.defect y z) := by ring

end DefectCalibration

/-- Cross-stage contraction constants transport under two independent
calibrations by the target upper/source lower ratio.

Unlike the scalar-gauge theorem below, this does not assert preservation of an
exact triangle premise. -/
theorem calibrated_cross_stage_contraction
    {A : Type u} {B : Type v}
    (P0 Q0 : RelationDefectPresentation A)
    (P1 Q1 : RelationDefectPresentation B)
    {a0 b0 a1 b1 L : ℝ}
    (C0 : DefectCalibration P0 Q0 a0 b0)
    (C1 : DefectCalibration P1 Q1 a1 b1)
    (hL : 0 ≤ L)
    {x y : A} {u v : B}
    (h : P1.defect u v ≤ L * P0.defect x y) :
    Q1.defect u v ≤ (b1 / a0) * L * Q0.defect x y := by
  have hrev : P0.defect x y ≤ Q0.defect x y / a0 :=
    C0.reverse_budget (hQ := le_rfl)
  calc
    Q1.defect u v ≤ b1 * P1.defect u v := C1.upper u v
    _ ≤ b1 * (L * P0.defect x y) :=
      mul_le_mul_of_nonneg_left h C1.b_nonneg
    _ ≤ b1 * (L * (Q0.defect x y / a0)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hrev hL) C1.b_nonneg
    _ = (b1 / a0) * L * Q0.defect x y := by ring

/-- Positive scalar gauge preserves the exact triangle form at one stage. -/
theorem rescale_triangle_preserved
    {X : Type u}
    (P : RelationDefectPresentation X)
    (c : ℝ) (hc : 0 < c)
    {x y z : X}
    (htri : P.defect x z ≤ P.defect x y + P.defect y z) :
    (P.rescale c hc).defect x z ≤
      (P.rescale c hc).defect x y +
        (P.rescale c hc).defect y z := by
  change c * P.defect x z ≤ c * P.defect x y + c * P.defect y z
  calc
    c * P.defect x z ≤ c * (P.defect x y + P.defect y z) :=
      mul_le_mul_of_nonneg_left htri (le_of_lt hc)
    _ = c * P.defect x y + c * P.defect y z := by ring

/-- Under positive scalar gauges at two adjacent stages, a contraction
coefficient transforms covariantly by `c₁ / c₀`. -/
theorem rescale_contraction_transformed
    {A : Type u} {B : Type v}
    (P0 : RelationDefectPresentation A)
    (P1 : RelationDefectPresentation B)
    (c0 c1 L : ℝ)
    (hc0 : 0 < c0) (hc1 : 0 < c1)
    {x y : A} {u v : B}
    (h : P1.defect u v ≤ L * P0.defect x y) :
    (P1.rescale c1 hc1).defect u v ≤
      ((c1 / c0) * L) *
        (P0.rescale c0 hc0).defect x y := by
  change c1 * P1.defect u v ≤
    ((c1 / c0) * L) * (c0 * P0.defect x y)
  calc
    c1 * P1.defect u v ≤ c1 * (L * P0.defect x y) :=
      mul_le_mul_of_nonneg_left h (le_of_lt hc1)
    _ = ((c1 / c0) * L) * (c0 * P0.defect x y) := by
      field_simp

/-- Positive scalar gauge transforms a local finite defect budget by the same
stage scalar. -/
theorem rescale_local_budget_transformed
    {X : Type u}
    (P : RelationDefectPresentation X)
    (c ε : ℝ) (hc : 0 < c)
    {x y : X}
    (h : P.defect x y ≤ ε) :
    (P.rescale c hc).defect x y ≤ c * ε := by
  change c * P.defect x y ≤ c * ε
  exact mul_le_mul_of_nonneg_left h (le_of_lt hc)

/-- Full M-TC covariance under positive stagewise scalar gauge.

The proof transports each registered M-TC premise and then reuses
`TransportCertificate.weighted_chain_bound` directly.  The exact triangle
premise is preserved, while contraction and local-defect coefficients transform
as

```text
L'_t = (c_{t+1} / c_t) * L_t,
ε'_t = c_{t+1} * ε_t.
```

Thus positive scalar rescaling is a genuine presentation gauge for the M-TC
premise class.  This theorem does not extend that claim to an arbitrary
two-sided calibration, for which only `DefectCalibration.triangle_quasi` has
been established. -/
theorem rescaled_weighted_chain_bound
    {A : ℕ → Type*}
    (P : ∀ n, RelationDefectPresentation (A n))
    (c : ℕ → ℝ)
    (hc : ∀ n, 0 < c n)
    (ideal actual : (n : ℕ) → A n)
    (step : ∀ n, A n → A (n + 1))
    (L ε : ℕ → ℝ)
    (hcontract : ∀ n,
      (P (n + 1)).defect (ideal (n + 1)) (step n (actual n)) ≤
        L n * (P n).defect (ideal n) (actual n))
    (htriangle : ∀ n,
      (P (n + 1)).defect (ideal (n + 1)) (actual (n + 1)) ≤
        (P (n + 1)).defect (ideal (n + 1)) (step n (actual n)) +
        (P (n + 1)).defect (step n (actual n)) (actual (n + 1)))
    (hlocal : ∀ n,
      (P (n + 1)).defect (step n (actual n)) (actual (n + 1)) ≤ ε n)
    (hL0 : ∀ n, 0 ≤ L n)
    (n : ℕ) :
    ((P n).rescale (c n) (hc n)).defect (ideal n) (actual n) ≤
      (∏ j ∈ Finset.range n, ((c (j + 1) / c j) * L j)) *
          ((P 0).rescale (c 0) (hc 0)).defect (ideal 0) (actual 0) +
        ∑ k ∈ Finset.range n,
          (c (k + 1) * ε k) *
            ∏ j ∈ Finset.Ico (k + 1) n,
              ((c (j + 1) / c j) * L j) := by
  apply TransportCertificate.weighted_chain_bound
    (defect := fun t => ((P t).rescale (c t) (hc t)).defect)
    (ideal := ideal)
    (actual := actual)
    (step := step)
    (L := fun t => (c (t + 1) / c t) * L t)
    (ε := fun t => c (t + 1) * ε t)
  · intro t
    exact rescale_contraction_transformed
      (P0 := P t)
      (P1 := P (t + 1))
      (c0 := c t)
      (c1 := c (t + 1))
      (L := L t)
      (hc0 := hc t)
      (hc1 := hc (t + 1))
      (hcontract t)
  · intro t
    exact rescale_triangle_preserved
      (P := P (t + 1))
      (c := c (t + 1))
      (hc := hc (t + 1))
      (htriangle t)
  · intro t
    exact rescale_local_budget_transformed
      (P := P (t + 1))
      (c := c (t + 1))
      (ε := ε t)
      (hc := hc (t + 1))
      (hlocal t)
  · intro t
    exact mul_nonneg
      (div_nonneg (le_of_lt (hc (t + 1))) (le_of_lt (hc t)))
      (hL0 t)

end UEOT.V3.Compression.TheoryCompletion.MinCore

