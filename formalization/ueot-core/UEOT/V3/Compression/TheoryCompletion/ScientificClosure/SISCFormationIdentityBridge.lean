import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCFiniteFormation
import Mathlib.Tactic.Linarith

/-!
# SISC SI-2/3 bridge: mechanistic formation and discriminating successor

The baseline SI-3 produces a candidate `tp p` in a new formed fibre, but did
not establish uniqueness in that fibre. The theorem here supplies a separately
registered discrimination margin on *predicted response coordinates* and an
independent causal edge, and then derives unique formed operational successor.
Neither `SameObject` nor a unique-successor predicate is an assumption.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

universe uObs uX0 uX1 uP0 uP1

/-- Any two target candidates that both fit the same actual response within
`tau` cannot be distinguished by more than `2*tau` on any coordinate. -/
theorem formed_targets_close_at_each_coordinate
    {X P Obs : Type*}
    (actual : X → Obs → ℝ) (predicted : P → Obs → ℝ)
    (tau : ℝ) (x : X) (p q : P)
    (hp : FormedByResponse actual predicted tau x p)
    (hq : FormedByResponse actual predicted tau x q)
    (j : Obs) :
    |predicted p j - predicted q j| ≤ 2 * tau := by
  have h := abs_sub_le (predicted p j) (actual x j) (predicted q j)
  have ha : |predicted p j - actual x j| ≤ tau := by
    simpa only [abs_sub_comm] using hp j
  linarith [hq j]

/-- Local (source-conditioned) candidate separation. Unlike SI-2's global
pairwise condition, this only tests competitors against a single predicted
transported parent and permits clones to yield UNRESOLVED. -/
def LocalResponseGap {P Obs : Type*}
    (predicted : P → Obs → ℝ) (tau : ℝ) (target : P) : Prop :=
  ∀ q, q ≠ target → ∃ j, 2 * tau < |predicted target j - predicted q j|

/-- A registered target with local response separation is the unique formed
candidate. The conclusion uses no assumed uniqueness or identity map. -/
theorem unique_formed_target_of_local_gap
    {X P Obs : Type*}
    (actual : X → Obs → ℝ) (predicted : P → Obs → ℝ)
    (tau : ℝ) (x : X) (target : P)
    (htarget : FormedByResponse actual predicted tau x target)
    (hgap : LocalResponseGap predicted tau target) :
    ∀ q, FormedByResponse actual predicted tau x q → q = target := by
  intro q hq
  by_contra hne
  obtain ⟨j, hsep⟩ := hgap q hne
  have hsmall := formed_targets_close_at_each_coordinate
    actual predicted tau x target q htarget hq j
  exact (not_lt_of_ge hsmall) hsep

/-- SI-3→SI-2 scientific composition. A *finite normalized lower response
channel* and separately checked world/parent residuals construct target
formation; an independently observed causal edge and registered response gap
then certify one unique formed causal successor among the declared P1 space.
The candidate `tp p` is a model transport, not an inferred physical identity.
-/
theorem finite_mechanism_unique_formed_successor
    {Old : Type*} {New : Type*} [Fintype Old]
    {X0 : Type uX0} {X1 : Type uX1}
    {P0 : Type uP0} {P1 : Type uP1}
    (K : FiniteResponseChannel Old New)
    (actual0 : X0 → Old → ℝ) (actual1 : X1 → New → ℝ)
    (predict0 : P0 → Old → ℝ) (predict1 : P1 → New → ℝ)
    (tx : X0 → X1) (tp : P0 → P1)
    (edge : P0 → P1 → Prop)
    (tau deltaWorld deltaParent : ℝ)
    (hWorld : ∀ x j,
      |actual1 (tx x) j - ∑ i, K.weight j i * actual0 x i| ≤ deltaWorld)
    (hParent : ∀ p j,
      |predict1 (tp p) j - ∑ i, K.weight j i * predict0 p i| ≤ deltaParent)
    (x : X0) (p : P0)
    (hsource : FormedByResponse actual0 predict0 tau x p)
    (hcausal : edge p (tp p))
    (hgap : LocalResponseGap predict1 (deltaWorld + tau + deltaParent) (tp p)) :
    (edge p (tp p) ∧
        FormedByResponse actual1 predict1 (deltaWorld + tau + deltaParent)
          (tx x) (tp p)) ∧
    (∀ q, edge p q →
      FormedByResponse actual1 predict1 (deltaWorld + tau + deltaParent)
        (tx x) q → q = tp p) := by
  have htarget := finite_mechanism_preserves_formation
    K actual0 actual1 predict0 predict1 tx tp tau deltaWorld deltaParent
    hWorld hParent x p hsource
  refine ⟨⟨hcausal, htarget⟩, ?_⟩
  intro q _ hq
  exact unique_formed_target_of_local_gap actual1 predict1
    (deltaWorld + tau + deltaParent) (tx x) (tp p) htarget hgap q hq

/-- A clone counterexample to any automatic SI-3 uniqueness assertion:
two different parent tokens can both be perfectly formed under exactly the
same finite response and zero tolerance. -/
theorem zero_formation_error_does_not_identify_parent :
    ∃ (actual : PUnit → PUnit → ℝ)
      (predicted : Bool → PUnit → ℝ),
      FormedByResponse actual predicted 0 PUnit.unit false ∧
      FormedByResponse actual predicted 0 PUnit.unit true ∧
      false ≠ true := by
  refine ⟨(fun _ _ => 0), (fun _ _ => 0), ?_, ?_, Bool.false_ne_true⟩
  · intro i
    norm_num
  · intro i
    norm_num

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
