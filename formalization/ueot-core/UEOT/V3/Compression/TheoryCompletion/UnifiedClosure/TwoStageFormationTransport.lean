import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteFormationBoundary
import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCFiniteFormation
import Mathlib.Tactic

/-!
# UMC-03 — two-stage quantitative source-coherent formation certification

No formed target at step 1 or 2 is an assumption. Both intermediate and
final formed certificates are *derived* using the already proven normalized
positive response-channel theorem, and local separation is then combined
with SI-2 uniqueness. The source/parent transport types are explicitly
connected from stage 0 to stage 2 rather than being independent models.

This is a finite two-stage result; no arbitrary correlated-data or
general measurable-space assertion is included.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

universe uX0 uX1 uX2 uP0 uP1 uP2 uO0 uO1 uO2

/-- Both transformations are real, normalized positive response channels;
the intermediate state and parent are the outputs of the first stage. -/
theorem two_stage_formation_budget
    {X0 : Type uX0} {X1 : Type uX1} {X2 : Type uX2}
    {P0 : Type uP0} {P1 : Type uP1} {P2 : Type uP2}
    {O0 : Type uO0} {O1 : Type uO1} {O2 : Type uO2}
    [Fintype O0] [Fintype O1]
    (K01 : FiniteResponseChannel O0 O1)
    (K12 : FiniteResponseChannel O1 O2)
    (actual0 : X0 → O0 → ℝ) (actual1 : X1 → O1 → ℝ)
    (actual2 : X2 → O2 → ℝ)
    (predict0 : P0 → O0 → ℝ) (predict1 : P1 → O1 → ℝ)
    (predict2 : P2 → O2 → ℝ)
    (tx01 : X0 → X1) (tx12 : X1 → X2)
    (tp01 : P0 → P1) (tp12 : P1 → P2)
    (tau dw01 dp01 dw12 dp12 : ℝ)
    (hWorld01 : ∀ x j,
      |actual1 (tx01 x) j - ∑ i, K01.weight j i * actual0 x i| ≤ dw01)
    (hParent01 : ∀ p j,
      |predict1 (tp01 p) j - ∑ i, K01.weight j i * predict0 p i| ≤ dp01)
    (hWorld12 : ∀ x j,
      |actual2 (tx12 x) j - ∑ i, K12.weight j i * actual1 x i| ≤ dw12)
    (hParent12 : ∀ p j,
      |predict2 (tp12 p) j - ∑ i, K12.weight j i * predict1 p i| ≤ dp12)
    (x : X0) (p : P0)
    (hFormed0 : FormedByResponse actual0 predict0 tau x p) :
    FormedByResponse actual2 predict2
      (dw12 + (dw01 + tau + dp01) + dp12)
      (tx12 (tx01 x)) (tp12 (tp01 p)) := by
  have hFormed1 := finite_mechanism_preserves_formation
    K01 actual0 actual1 predict0 predict1 tx01 tp01
    tau dw01 dp01 hWorld01 hParent01 x p hFormed0
  exact finite_mechanism_preserves_formation
    K12 actual1 actual2 predict1 predict2 tx12 tp12
    (dw01 + tau + dp01) dw12 dp12
    hWorld12 hParent12 (tx01 x) (tp01 p) hFormed1

/-- Mechanically constructed two-stage response transport plus independent
final response separation implies a unique **operational** final parent
candidate. Uniqueness is a conclusion, not a supplied hUnique field. -/
theorem two_stage_formation_uniqueness_of_final_gap
    {X0 : Type uX0} {X1 : Type uX1} {X2 : Type uX2}
    {P0 : Type uP0} {P1 : Type uP1} {P2 : Type uP2}
    {O0 : Type uO0} {O1 : Type uO1} {O2 : Type uO2}
    [Fintype O0] [Fintype O1]
    (K01 : FiniteResponseChannel O0 O1)
    (K12 : FiniteResponseChannel O1 O2)
    (actual0 : X0 → O0 → ℝ) (actual1 : X1 → O1 → ℝ)
    (actual2 : X2 → O2 → ℝ)
    (predict0 : P0 → O0 → ℝ) (predict1 : P1 → O1 → ℝ)
    (predict2 : P2 → O2 → ℝ)
    (tx01 : X0 → X1) (tx12 : X1 → X2)
    (tp01 : P0 → P1) (tp12 : P1 → P2)
    (tau dw01 dp01 dw12 dp12 : ℝ)
    (hWorld01 : ∀ x j,
      |actual1 (tx01 x) j - ∑ i, K01.weight j i * actual0 x i| ≤ dw01)
    (hParent01 : ∀ p j,
      |predict1 (tp01 p) j - ∑ i, K01.weight j i * predict0 p i| ≤ dp01)
    (hWorld12 : ∀ x j,
      |actual2 (tx12 x) j - ∑ i, K12.weight j i * actual1 x i| ≤ dw12)
    (hParent12 : ∀ p j,
      |predict2 (tp12 p) j - ∑ i, K12.weight j i * predict1 p i| ≤ dp12)
    (x : X0) (p : P0)
    (hFormed0 : FormedByResponse actual0 predict0 tau x p)
    (hgap : LocalResponseGap predict2
      (dw12 + (dw01 + tau + dp01) + dp12) (tp12 (tp01 p))) :
    ∀ q : P2,
      FormedByResponse actual2 predict2
        (dw12 + (dw01 + tau + dp01) + dp12)
        (tx12 (tx01 x)) q → q = tp12 (tp01 p) := by
  exact unique_formed_target_of_local_gap
    actual2 predict2
    (dw12 + (dw01 + tau + dp01) + dp12)
    (tx12 (tx01 x)) (tp12 (tp01 p))
    (two_stage_formation_budget
      K01 K12 actual0 actual1 actual2 predict0 predict1 predict2
      tx01 tx12 tp01 tp12 tau dw01 dp01 dw12 dp12
      hWorld01 hParent01 hWorld12 hParent12 x p hFormed0) hgap

/-- Existing exact-error clone counterexample keeps the gap obligation
meaningful: transport certificates alone cannot identify object identity. -/
theorem zero_two_stage_error_does_not_force_parent_uniqueness :
    ∃ (actual : PUnit → PUnit → ℝ)
      (predicted : Bool → PUnit → ℝ),
      FormedByResponse actual predicted 0 PUnit.unit false ∧
      FormedByResponse actual predicted 0 PUnit.unit true ∧
      false ≠ true :=
  zero_formation_error_does_not_identify_parent

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
