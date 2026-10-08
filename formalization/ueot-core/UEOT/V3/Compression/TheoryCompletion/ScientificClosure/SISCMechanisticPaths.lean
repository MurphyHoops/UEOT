import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCFinitePaths
import Mathlib.Tactic.Linarith

/-!
# SISC mechanism-to-path bridge

Unlike the generic SI-4 theorem, this construction does NOT assume each
source has an unnamed admissible successor. The *paired lower+parent* successor
is explicitly `(tx x, tp p)`; SI-3 response-channel inequalities prove that
the new pair remains formed and C4 binding transport controls the realized
path error. Nonzero response drift is accumulated rather than erased.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

universe uObs uX uP uD

def formationPathBudget (tau deltaWorld deltaParent : ℝ) : ℕ → ℝ
  | 0 => tau
  | n + 1 => deltaWorld + formationPathBudget tau deltaWorld deltaParent n + deltaParent

/-- The paired transport records actual lower state and model-parent history,
not an ontological same-object relation. -/
def PairedTransportEdge {X : Type uX} {P : Type uP}
    (tx : X → X) (tp : P → P) : (X × P) → (X × P) → Prop :=
  fun s t => t.1 = tx s.1 ∧ t.2 = tp s.2

/-- SI-3→SI-4 finite synthesis with *two* distinct accumulated budgets:
the source↔parent formation tolerance and the realized transport error.
Formation membership, including intermediate times, is part of the output.
No generic global `hStep` is supplied as a hidden premise. -/
theorem finite_channel_formed_history_with_realization_bound
    {Obs : Type uObs} [Fintype Obs]
    {X : Type uX} {P : Type uP} {D : Type uD} [PseudoMetricSpace D]
    (K : FiniteResponseChannel Obs Obs)
    (actual : X → Obs → ℝ) (predict : P → Obs → ℝ)
    (tx : X → X) (tp : P → P)
    (B : P → D) (T : D → D)
    (tau deltaWorld deltaParent deltaBind M : ℝ)
    (hM : 0 ≤ M)
    (hWorld : ∀ x j,
      |actual (tx x) j - ∑ i, K.weight j i * actual x i| ≤ deltaWorld)
    (hParent : ∀ p j,
      |predict (tp p) j - ∑ i, K.weight j i * predict p i| ≤ deltaParent)
    (hBind : ∀ p, dist (B (tp p)) (T (B p)) ≤ deltaBind)
    (hLip : ∀ d e, dist (T d) (T e) ≤ M * dist d e)
    (x : X) (p : P)
    (h0 : FormedByResponse actual predict tau x p) (n : ℕ) :
    ∃ s : X × P,
      DirectedFinitePath (PairedTransportEdge tx tp) n (x, p) s ∧
      FormedByResponse actual predict
        (formationPathBudget tau deltaWorld deltaParent n) s.1 s.2 ∧
      dist (B s.2) (iterateResponse T n (B p)) ≤
        accumulatedPathError deltaBind M n := by
  induction n with
  | zero =>
      refine ⟨(x, p), DirectedFinitePath.zero (x, p), ?_, ?_⟩
      · simpa only [formationPathBudget] using h0
      · simp [iterateResponse, accumulatedPathError]
  | succ n ih =>
      obtain ⟨s, hpath, hformed, herr⟩ := ih
      have hnext := finite_mechanism_preserves_formation K actual actual
        predict predict tx tp
        (formationPathBudget tau deltaWorld deltaParent n)
        deltaWorld deltaParent hWorld hParent s.1 s.2 hformed
      let t : X × P := (tx s.1, tp s.2)
      have hedge : PairedTransportEdge tx tp s t := ⟨rfl, rfl⟩
      refine ⟨t, DirectedFinitePath.append hpath hedge, ?_, ?_⟩
      · simpa only [formationPathBudget] using hnext
      · have htri := dist_triangle (B (tp s.2)) (T (B s.2))
          (T (iterateResponse T n (B p)))
        have htrans := hLip (B s.2) (iterateResponse T n (B p))
        have hbound : M * dist (B s.2) (iterateResponse T n (B p)) ≤
            M * accumulatedPathError deltaBind M n :=
          mul_le_mul_of_nonneg_left herr hM
        change dist (B (tp s.2)) (T (iterateResponse T n (B p))) ≤
          deltaBind + M * accumulatedPathError deltaBind M n
        linarith [hBind s.2]

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
