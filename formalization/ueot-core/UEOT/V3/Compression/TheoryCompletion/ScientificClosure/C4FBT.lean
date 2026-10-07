import UEOT.V3.Compression.CrossTrack.ParentBindingDynamic
import UEOT.V3.Compression.TheoryCompletion.ObjectScaleCalculus
import Mathlib.Tactic.Linarith

/-!
# Scientific Closure C4 — Formation / Binding / Transport coherence

This is the post-Core FBT synthesis surface.  Same-object identity is not an
input.  Exact set-valued formation naturality is kept separate from an
approximate representative-level theorem.  The approximate theorem combines a
formation transport defect, a realization Lipschitz bound and a binding-
transport defect into one end-to-end realized continuation bound.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure

universe uX0 uX1 uP0 uP1 uD0 uD1

/-- Set-valued formation relation: one lower-level state may support multiple
parent completions. -/
abbrev FormationRelation (X : Type uX0) (P : Type uP0) := X → P → Prop

/-- Exact naturality of a set-valued formation relation under a declared lower
and parent transport.  This is an interface condition, not itself an existence
theorem. -/
def FormationTransportCompatible
    {X0 : Type uX0} {X1 : Type uX1}
    {P0 : Type uP0} {P1 : Type uP1}
    (F0 : FormationRelation X0 P0)
    (F1 : FormationRelation X1 P1)
    (tx : X0 → X1) (tp : P0 → P1) : Prop :=
  ∀ x p, F0 x p → F1 (tx x) (tp p)

/-- Exact naturality of realization/binding under parent and realized-dynamics
transport. -/
def BindingTransportCompatible
    {P0 : Type uP0} {P1 : Type uP1}
    {D0 : Type uD0} {D1 : Type uD1}
    (B0 : P0 → D0) (B1 : P1 → D1)
    (tp : P0 → P1) (td : D0 → D1) : Prop :=
  ∀ p, B1 (tp p) = td (B0 p)

/-- Exact FBT composition preserves formation membership and commutes at the
realized layer.  The theorem makes explicit that these are two independent
compatibility obligations. -/
theorem exact_fbt_composition
    {X0 : Type uX0} {X1 : Type uX1}
    {P0 : Type uP0} {P1 : Type uP1}
    {D0 : Type uD0} {D1 : Type uD1}
    (F0 : FormationRelation X0 P0)
    (F1 : FormationRelation X1 P1)
    (tx : X0 → X1) (tp : P0 → P1)
    (B0 : P0 → D0) (B1 : P1 → D1) (td : D0 → D1)
    (hF : FormationTransportCompatible F0 F1 tx tp)
    (hB : BindingTransportCompatible B0 B1 tp td)
    {x : X0} {p : P0} (hformed : F0 x p) :
    F1 (tx x) (tp p) ∧ B1 (tp p) = td (B0 p) :=
  ⟨hF x p hformed, hB p⟩

/-- Operational, directed continuation at realized-dynamics tolerance `margin`.
This is deliberately not parent-token equality. -/
def RealizedStructuralContinuation
    {P0 : Type uP0} {P1 : Type uP1}
    {D0 : Type uD0} {D1 : Type uD1} [PseudoMetricSpace D1]
    (B0 : P0 → D0) (B1 : P1 → D1) (td : D0 → D1)
    (margin : ℝ) (p0 : P0) (p1 : P1) : Prop :=
  dist (B1 p1) (td (B0 p0)) ≤ margin

/-- **C4-04/05 quantitative FBT theorem.**

Formation representatives commute with parent transport up to `epsF`; the new
binding map is `L`-Lipschitz; and binding itself commutes with realized-dynamics
transport up to `epsB`.  Then the fully realized formation-after-transport path
and transport-after-realization path differ by at most `L*epsF + epsB`.

No same-object relation occurs as an assumption. -/
theorem approximate_fbt_realized_bound
    {X0 : Type uX0} {X1 : Type uX1}
    {P0 : Type uP0} {P1 : Type uP1} [PseudoMetricSpace P1]
    {D0 : Type uD0} {D1 : Type uD1} [PseudoMetricSpace D1]
    (f0 : X0 → P0) (f1 : X1 → P1)
    (tx : X0 → X1) (tp : P0 → P1)
    (B0 : P0 → D0) (B1 : P1 → D1) (td : D0 → D1)
    (L epsF epsB : ℝ)
    (hL : 0 ≤ L)
    (hformation : ∀ x,
      dist (tp (f0 x)) (f1 (tx x)) ≤ epsF)
    (hbindingLip : ∀ p q,
      dist (B1 p) (B1 q) ≤ L * dist p q)
    (hbindingTransport : ∀ p,
      dist (B1 (tp p)) (td (B0 p)) ≤ epsB)
    (x : X0) :
    dist (B1 (f1 (tx x))) (td (B0 (f0 x))) ≤ L * epsF + epsB := by
  calc
    dist (B1 (f1 (tx x))) (td (B0 (f0 x)))
        ≤ dist (B1 (f1 (tx x))) (B1 (tp (f0 x))) +
            dist (B1 (tp (f0 x))) (td (B0 (f0 x))) :=
          dist_triangle _ _ _
    _ ≤ L * dist (f1 (tx x)) (tp (f0 x)) + epsB := by
          gcongr
          · exact hbindingLip _ _
          · exact hbindingTransport _
    _ ≤ L * epsF + epsB := by
          have hf : dist (f1 (tx x)) (tp (f0 x)) ≤ epsF := by
            simpa [dist_comm] using hformation x
          gcongr

/-- **C4-06 certified structural continuation.**  If the independently derived
FBT error budget lies within the registered continuation margin, the transported
formed representative receives a directed realized-continuation certificate.
This is an operational identity-through-change certificate, not equality of
parent tokens. -/
theorem certified_structural_continuation
    {X0 : Type uX0} {X1 : Type uX1}
    {P0 : Type uP0} {P1 : Type uP1} [PseudoMetricSpace P1]
    {D0 : Type uD0} {D1 : Type uD1} [PseudoMetricSpace D1]
    (f0 : X0 → P0) (f1 : X1 → P1)
    (tx : X0 → X1) (tp : P0 → P1)
    (B0 : P0 → D0) (B1 : P1 → D1) (td : D0 → D1)
    (L epsF epsB margin : ℝ)
    (hL : 0 ≤ L)
    (hformation : ∀ x,
      dist (tp (f0 x)) (f1 (tx x)) ≤ epsF)
    (hbindingLip : ∀ p q,
      dist (B1 p) (B1 q) ≤ L * dist p q)
    (hbindingTransport : ∀ p,
      dist (B1 (tp p)) (td (B0 p)) ≤ epsB)
    (hmargin : L * epsF + epsB ≤ margin)
    (x : X0) :
    RealizedStructuralContinuation B0 B1 td margin
      (f0 x) (f1 (tx x)) := by
  exact (approximate_fbt_realized_bound
    f0 f1 tx tp B0 B1 td L epsF epsB
    hL hformation hbindingLip hbindingTransport x).trans hmargin

/-- **C4-06 formed structural continuation endpoint.**  The source and target
representatives must independently belong to their respective formation
relations; the realized continuation bound is then derived from FBT coherence.
No same-parent token/equality is assumed. -/
theorem certified_formed_structural_continuation
    {X0 : Type uX0} {X1 : Type uX1}
    {P0 : Type uP0} {P1 : Type uP1} [PseudoMetricSpace P1]
    {D0 : Type uD0} {D1 : Type uD1} [PseudoMetricSpace D1]
    (F0 : FormationRelation X0 P0) (F1 : FormationRelation X1 P1)
    (f0 : X0 → P0) (f1 : X1 → P1)
    (tx : X0 → X1) (tp : P0 → P1)
    (B0 : P0 → D0) (B1 : P1 → D1) (td : D0 → D1)
    (L epsF epsB margin : ℝ) (hL : 0 ≤ L)
    (hformed0 : ∀ x, F0 x (f0 x))
    (hformed1 : ∀ x, F1 (tx x) (f1 (tx x)))
    (hformation : ∀ x,
      dist (tp (f0 x)) (f1 (tx x)) ≤ epsF)
    (hbindingLip : ∀ p q,
      dist (B1 p) (B1 q) ≤ L * dist p q)
    (hbindingTransport : ∀ p,
      dist (B1 (tp p)) (td (B0 p)) ≤ epsB)
    (hmargin : L * epsF + epsB ≤ margin)
    (x : X0) :
    F0 x (f0 x) ∧
      F1 (tx x) (f1 (tx x)) ∧
      RealizedStructuralContinuation B0 B1 td margin
        (f0 x) (f1 (tx x)) := by
  exact ⟨hformed0 x, hformed1 x,
    certified_structural_continuation
      f0 f1 tx tp B0 B1 td L epsF epsB margin hL
      hformation hbindingLip hbindingTransport hmargin x⟩

/-- Formation naturality alone cannot force binding naturality.  This prevents
collapsing F and B into one unnamed compatibility assumption. -/
theorem formationTransport_does_not_imply_bindingTransport :
    ∃ (F0 F1 : FormationRelation Bool Bool)
      (tx tp : Bool → Bool)
      (B0 B1 td : Bool → Bool),
      FormationTransportCompatible F0 F1 tx tp ∧
      ¬ BindingTransportCompatible B0 B1 tp td := by
  refine ⟨(fun _ _ => True), (fun _ _ => True), id, id,
    (fun _ => false), (fun _ => true), id, ?_, ?_⟩
  · intro x p h
    trivial
  · intro h
    have := h false
    simp at this

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure
