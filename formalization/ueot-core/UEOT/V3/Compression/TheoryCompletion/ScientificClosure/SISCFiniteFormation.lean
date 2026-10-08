import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCUniqueSuccessor
import Mathlib.Tactic.Linarith

/-!
# SISC SI-3: derive formation coverage from finite lower response dynamics

This is a deliberately restricted constructive mechanism. The lower response
vector and the candidate parent response vector evolve under the *same*
registered positive normalized response channel, up to **separate** world and
parent residual budgets. This yields formation of the transported parent as a
theorem, rather than assuming C4's `DirectedFormationCoverage` directly.

It is a finite, protocol-fixed forward mechanism; it does not discover the
channel, identify ontic parents or establish universal identity.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

universe uOld uNew uX0 uX1 uP0 uP1 uD0 uD1

/-- A stochastic averaging channel on finite registered response coordinates.
New coordinates are positive, mass-one averages of old coordinates. -/
structure FiniteResponseChannel (Old : Type uOld) (New : Type uNew)
    [Fintype Old] where
  weight : New → Old → ℝ
  nonneg : ∀ j i, 0 ≤ weight j i
  row_sum_one : ∀ j, ∑ i, weight j i = 1

/-- Certificate of formation against **all** registered response coordinates. -/
def FormedByResponse {X : Type*} {P : Type*} {Obs : Type*}
    (actual : X → Obs → ℝ) (predicted : P → Obs → ℝ)
    (tau : ℝ) (x : X) (p : P) : Prop :=
  ∀ i, |actual x i - predicted p i| ≤ tau

/-- A normalized positive channel does not amplify uniform response error.
The direction follows from positivity, not an assumed transported formation
or a separately assumed `L = 1` oracle. -/
theorem finite_channel_error_nonexpansive
    {Old : Type uOld} {New : Type uNew} [Fintype Old]
    (K : FiniteResponseChannel Old New)
    (a b : Old → ℝ) (tau : ℝ)
    (h : ∀ i, |a i - b i| ≤ tau) (j : New) :
    |(∑ i, K.weight j i * a i) - (∑ i, K.weight j i * b i)| ≤ tau := by
  have hlow : -tau ≤ ∑ i, K.weight j i * (a i - b i) := by
    calc
      -tau = ∑ i, K.weight j i * (-tau) := by
        rw [← Finset.sum_mul, K.row_sum_one]
        ring
      _ ≤ ∑ i, K.weight j i * (a i - b i) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (abs_le.mp (h i)).1 (K.nonneg j i)
  have hupp : (∑ i, K.weight j i * (a i - b i)) ≤ tau := by
    calc
      (∑ i, K.weight j i * (a i - b i)) ≤
          ∑ i, K.weight j i * tau := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (abs_le.mp (h i)).2 (K.nonneg j i)
      _ = tau := by
        rw [← Finset.sum_mul, K.row_sum_one]
        ring
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  exact abs_le.mpr ⟨hlow, hupp⟩

/-- Derived formation-after-transport. The two error sources are
**independent residual tests**, not postulated successor matches. -/
theorem finite_mechanism_preserves_formation
    {Old : Type uOld} {New : Type uNew} [Fintype Old]
    {X0 : Type uX0} {X1 : Type uX1}
    {P0 : Type uP0} {P1 : Type uP1}
    (K : FiniteResponseChannel Old New)
    (actual0 : X0 → Old → ℝ) (actual1 : X1 → New → ℝ)
    (predict0 : P0 → Old → ℝ) (predict1 : P1 → New → ℝ)
    (tx : X0 → X1) (tp : P0 → P1)
    (tau deltaWorld deltaParent : ℝ)
    (hWorld : ∀ x j,
      |actual1 (tx x) j - ∑ i, K.weight j i * actual0 x i| ≤ deltaWorld)
    (hParent : ∀ p j,
      |predict1 (tp p) j - ∑ i, K.weight j i * predict0 p i| ≤ deltaParent)
    (x : X0) (p : P0)
    (hFormed : FormedByResponse actual0 predict0 tau x p) :
    FormedByResponse actual1 predict1
      (deltaWorld + tau + deltaParent) (tx x) (tp p) := by
  intro j
  let A := ∑ i, K.weight j i * actual0 x i
  let B := ∑ i, K.weight j i * predict0 p i
  have hw := hWorld x j
  have hp := hParent p j
  have hmid : |A - B| ≤ tau := by
    exact finite_channel_error_nonexpansive K (actual0 x) (predict0 p) tau hFormed j
  have ht1 := abs_sub_le (actual1 (tx x) j) A (predict1 (tp p) j)
  have ht2 := abs_sub_le A B (predict1 (tp p) j)
  have hp' : |B - predict1 (tp p) j| ≤ deltaParent := by
    simpa only [abs_sub_comm] using hp
  linarith

/-- A concrete positive finite-world model gives C4's *exact* directed
formation coverage (parent transport chosen as the witness). No `hCoverage`
appears among the assumptions. The formation tolerance itself expands by
the explicitly metered lower/parent mechanism residuals. -/
theorem finite_mechanism_derives_directed_coverage
    {Old : Type uOld} {New : Type uNew} [Fintype Old]
    {X0 : Type uX0} {X1 : Type uX1}
    {P0 : Type uP0} {P1 : Type uP1} [PseudoMetricSpace P1]
    (K : FiniteResponseChannel Old New)
    (actual0 : X0 → Old → ℝ) (actual1 : X1 → New → ℝ)
    (predict0 : P0 → Old → ℝ) (predict1 : P1 → New → ℝ)
    (tx : X0 → X1) (tp : P0 → P1)
    (tau deltaWorld deltaParent : ℝ)
    (hWorld : ∀ x j,
      |actual1 (tx x) j - ∑ i, K.weight j i * actual0 x i| ≤ deltaWorld)
    (hParent : ∀ p j,
      |predict1 (tp p) j - ∑ i, K.weight j i * predict0 p i| ≤ deltaParent) :
    DirectedFormationCoverage
      (FormedByResponse actual0 predict0 tau)
      (FormedByResponse actual1 predict1 (deltaWorld + tau + deltaParent))
      tx tp 0 := by
  apply exact_formation_implies_directed_coverage
  intro x p hp
  exact finite_mechanism_preserves_formation K actual0 actual1 predict0 predict1
    tx tp tau deltaWorld deltaParent hWorld hParent x p hp

/-- Assemble the mechanistically **derived** coverage with the already public
C4 FBT. This is an end-to-end conditional theorem, not a new object-identity
axiom. The particular finite model has parent-transport defect zero. -/
theorem finite_mechanism_to_fbt_continuation
    {Old : Type uOld} {New : Type uNew} [Fintype Old]
    {X0 : Type uX0} {X1 : Type uX1}
    {P0 : Type uP0} {P1 : Type uP1} [PseudoMetricSpace P1]
    {D0 : Type uD0} {D1 : Type uD1} [PseudoMetricSpace D1]
    (K : FiniteResponseChannel Old New)
    (actual0 : X0 → Old → ℝ) (actual1 : X1 → New → ℝ)
    (predict0 : P0 → Old → ℝ) (predict1 : P1 → New → ℝ)
    (tx : X0 → X1) (tp : P0 → P1)
    (B0 : P0 → D0) (B1 : P1 → D1) (td : D0 → D1)
    (tau deltaWorld deltaParent L epsB : ℝ) (hL : 0 ≤ L)
    (hWorld : ∀ x j,
      |actual1 (tx x) j - ∑ i, K.weight j i * actual0 x i| ≤ deltaWorld)
    (hParent : ∀ p j,
      |predict1 (tp p) j - ∑ i, K.weight j i * predict0 p i| ≤ deltaParent)
    (hbindingLip : ∀ p q, dist (B1 p) (B1 q) ≤ L * dist p q)
    (hbindingTransport : ∀ p,
      dist (B1 (tp p)) (td (B0 p)) ≤ epsB)
    (x : X0) (p : P0)
    (h0 : FormedByResponse actual0 predict0 tau x p) :
    ∃ p1,
      FormedByResponse actual1 predict1 (deltaWorld + tau + deltaParent)
        (tx x) p1 ∧
      RealizedStructuralContinuation B0 B1 td (L * 0 + epsB) p p1 := by
  exact directed_setValued_fbt
    (FormedByResponse actual0 predict0 tau)
    (FormedByResponse actual1 predict1 (deltaWorld + tau + deltaParent))
    tx tp B0 B1 td L 0 epsB hL
    (finite_mechanism_derives_directed_coverage K actual0 actual1
      predict0 predict1 tx tp tau deltaWorld deltaParent hWorld hParent)
    hbindingLip hbindingTransport x p h0

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
