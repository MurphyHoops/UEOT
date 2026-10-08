import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCFiniteFormation
import Mathlib.Tactic.Linarith

/-!
# SISC SI-4: finite, selector-free directed path existence and error

One-step coverage gives *at least one* finite compatible chain, not a unique
history, a canonical path, a global measurable selector, or a `SameObject`
certificate. Split/merge witnesses explicitly refute those stronger claims.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

universe uP uD

/-- A proof-relevant finite history, including the intermediate successors.
The construction never assumes a designated global choice of successor. -/
inductive DirectedFinitePath {P : Type uP} (edge : P → P → Prop) :
    ℕ → P → P → Prop where
  | zero (p : P) : DirectedFinitePath edge 0 p p
  | append {n : ℕ} {p q r : P}
      (history : DirectedFinitePath edge n p q)
      (next : edge q r) : DirectedFinitePath edge (n + 1) p r

/-- Physical response transport iterated along a finite chain. -/
def iterateResponse {D : Type uD} (T : D → D) : ℕ → D → D
  | 0, d => d
  | n + 1, d => T (iterateResponse T n d)

/-- Error accumulation for a one-step envelope `delta` amplified by the
next transport's Lipschitz constant `M`. -/
def accumulatedPathError (delta M : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => delta + M * accumulatedPathError delta M n

/-- Every registered source has a successor, and every admissible edge obeys
a quantitative realized defect bound. The conclusion derives existence of a
full n-step history *and* a finite-time end-to-end error bound. -/
theorem finite_directed_history_with_bound
    {P : Type uP} {D : Type uD} [PseudoMetricSpace D]
    (edge : P → P → Prop) (B : P → D) (T : D → D)
    (delta M : ℝ) (hM : 0 ≤ M)
    (hStep : ∀ p, ∃ q, edge p q ∧ dist (B q) (T (B p)) ≤ delta)
    (hLip : ∀ d e, dist (T d) (T e) ≤ M * dist d e)
    (p : P) (n : ℕ) :
    ∃ q, DirectedFinitePath edge n p q ∧
      dist (B q) (iterateResponse T n (B p)) ≤ accumulatedPathError delta M n := by
  induction n with
  | zero =>
      refine ⟨p, DirectedFinitePath.zero p, ?_⟩
      simp [iterateResponse, accumulatedPathError]
  | succ n ih =>
      obtain ⟨q, hpq, hbq⟩ := ih
      obtain ⟨r, hqr, hbr⟩ := hStep q
      refine ⟨r, DirectedFinitePath.append hpq hqr, ?_⟩
      have htriangle := dist_triangle (B r) (T (B q))
        (T (iterateResponse T n (B p)))
      have htrans := hLip (B q) (iterateResponse T n (B p))
      have hprop : M * dist (B q) (iterateResponse T n (B p)) ≤
          M * accumulatedPathError delta M n :=
        mul_le_mul_of_nonneg_left hbq hM
      change dist (B r) (T (iterateResponse T n (B p))) ≤
        delta + M * accumulatedPathError delta M n
      linarith

/-- Split means one recorded parent has multiple distinct successors. -/
def SplitWitness {P : Type uP} (edge : P → P → Prop) : Prop :=
  ∃ p q r, edge p q ∧ edge p r ∧ q ≠ r

/-- Merge means one recorded target has multiple distinct predecessors. -/
def MergeWitness {P : Type uP} (edge : P → P → Prop) : Prop :=
  ∃ p q r, edge p r ∧ edge q r ∧ p ≠ q

/-- A finite relation can exhibit splitting and merging simultaneously;
neither outcome should be silently forced into a bijective identity mapping. -/
theorem split_and_merge_can_coexist :
    ∃ edge : Bool → Bool → Prop, SplitWitness edge ∧ MergeWitness edge := by
  refine ⟨fun _ _ => True, ?_, ?_⟩
  · exact ⟨false, false, true, trivial, trivial, Bool.false_ne_true⟩
  · exact ⟨false, true, false, trivial, trivial, Bool.false_ne_true⟩

/-- In the absence of a one-step existence premise, even an n=1 source
history need not exist. This is the finite-time loss/death boundary. -/
theorem without_coverage_one_step_path_may_fail :
    ∃ edge : PUnit → PUnit → Prop,
      ¬ ∃ q, DirectedFinitePath edge 1 PUnit.unit q := by
  refine ⟨fun _ _ => False, ?_⟩
  rintro ⟨q, h⟩
  cases h with
  | append _ hfalse => exact hfalse

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
