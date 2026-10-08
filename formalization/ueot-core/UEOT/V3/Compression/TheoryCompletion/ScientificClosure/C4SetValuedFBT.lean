import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.C4FBT

/-!
# Scientific Closure C4 — directed set-valued FBT continuation

A quantitative extension of the registered-selector C4 endpoint.  It quantifies
across *all source formation completions*, retaining nonuniqueness.  Only a
forward matching witness is required; no measurable/continuous selector is
introduced.  This is a directed (not symmetric Hausdorff) statement: new target
components need not have ancestors, and source components must have a matched
successor.  No `SameObject` relation is assumed or constructed.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure

universe uX0 uX1 uX2 uP0 uP1 uP2 uD0 uD1 uD2

/-- Directed parent-formation coverage: every admitted source completion has
*some* admitted target completion whose parent transport defect is bounded.
Neither a unique nor a globally selected target is required. -/
def DirectedFormationCoverage
    {X0 : Type uX0} {X1 : Type uX1}
    {P0 : Type uP0} {P1 : Type uP1} [PseudoMetricSpace P1]
    (F0 : FormationRelation X0 P0) (F1 : FormationRelation X1 P1)
    (tx : X0 → X1) (tp : P0 → P1) (epsF : ℝ) : Prop :=
  ∀ x p0, F0 x p0 →
    ∃ p1, F1 (tx x) p1 ∧ dist (tp p0) p1 ≤ epsF

/-- Existing exact formation naturality is a zero-defect special case of
forward set-valued coverage. No selection theorem is hidden here. -/
theorem exact_formation_implies_directed_coverage
    {X0 : Type uX0} {X1 : Type uX1}
    {P0 : Type uP0} {P1 : Type uP1} [PseudoMetricSpace P1]
    (F0 : FormationRelation X0 P0) (F1 : FormationRelation X1 P1)
    (tx : X0 → X1) (tp : P0 → P1)
    (hF : FormationTransportCompatible F0 F1 tx tp) :
    DirectedFormationCoverage F0 F1 tx tp 0 := by
  intro x p0 hp0
  exact ⟨tp p0, hF x p0 hp0, by simp⟩

/-- Forward set-valued coverage propagates *formation nonemptiness* of a
source fibre, but makes no completeness statement about target births. -/
theorem directed_coverage_preserves_formed_existence
    {X0 : Type uX0} {X1 : Type uX1}
    {P0 : Type uP0} {P1 : Type uP1} [PseudoMetricSpace P1]
    (F0 : FormationRelation X0 P0) (F1 : FormationRelation X1 P1)
    (tx : X0 → X1) (tp : P0 → P1) (epsF : ℝ)
    (hF : DirectedFormationCoverage F0 F1 tx tp epsF)
    (x : X0) (h0 : ∃ p0, F0 x p0) :
    ∃ p1, F1 (tx x) p1 := by
  obtain ⟨p0, hp0⟩ := h0
  obtain ⟨p1, hp1, _⟩ := hF x p0 hp0
  exact ⟨p1, hp1⟩

/-- A selector-free quantitative FBT certificate for every source completion.
The output target may depend on the source parent. -/
theorem directed_setValued_fbt
    {X0 : Type uX0} {X1 : Type uX1}
    {P0 : Type uP0} {P1 : Type uP1} [PseudoMetricSpace P1]
    {D0 : Type uD0} {D1 : Type uD1} [PseudoMetricSpace D1]
    (F0 : FormationRelation X0 P0) (F1 : FormationRelation X1 P1)
    (tx : X0 → X1) (tp : P0 → P1)
    (B0 : P0 → D0) (B1 : P1 → D1) (td : D0 → D1)
    (L epsF epsB : ℝ) (hL : 0 ≤ L)
    (hF : DirectedFormationCoverage F0 F1 tx tp epsF)
    (hbindingLip : ∀ p q, dist (B1 p) (B1 q) ≤ L * dist p q)
    (hbindingTransport : ∀ p, dist (B1 (tp p)) (td (B0 p)) ≤ epsB)
    (x : X0) (p0 : P0) (h0 : F0 x p0) :
    ∃ p1, F1 (tx x) p1 ∧
      RealizedStructuralContinuation B0 B1 td (L * epsF + epsB) p0 p1 := by
  obtain ⟨p1, h1, hclose⟩ := hF x p0 h0
  refine ⟨p1, h1, ?_⟩
  dsimp [RealizedStructuralContinuation]
  calc
    dist (B1 p1) (td (B0 p0))
        ≤ dist (B1 p1) (B1 (tp p0)) +
          dist (B1 (tp p0)) (td (B0 p0)) := dist_triangle _ _ _
    _ ≤ L * dist p1 (tp p0) + epsB :=
      add_le_add (hbindingLip _ _) (hbindingTransport _)
    _ ≤ L * epsF + epsB := by
      exact add_le_add (mul_le_mul_of_nonneg_left (by simpa only [dist_comm] using hclose) hL) le_rfl

/-- Directed realized-set inclusion in a metric neighbourhood, without
selector choice or compactness/closedness assumptions.  This is the pointwise
witness form of a directed Hausdorff envelope; it makes no reverse claim. -/
theorem directed_realized_fibre_coverage
    {X0 : Type uX0} {X1 : Type uX1}
    {P0 : Type uP0} {P1 : Type uP1} [PseudoMetricSpace P1]
    {D0 : Type uD0} {D1 : Type uD1} [PseudoMetricSpace D1]
    (F0 : FormationRelation X0 P0) (F1 : FormationRelation X1 P1)
    (tx : X0 → X1) (tp : P0 → P1)
    (B0 : P0 → D0) (B1 : P1 → D1) (td : D0 → D1)
    (L epsF epsB : ℝ) (hL : 0 ≤ L)
    (hF : DirectedFormationCoverage F0 F1 tx tp epsF)
    (hbindingLip : ∀ p q, dist (B1 p) (B1 q) ≤ L * dist p q)
    (hbindingTransport : ∀ p, dist (B1 (tp p)) (td (B0 p)) ≤ epsB)
    (x : X0) (d : D1)
    (hd : ∃ p0, F0 x p0 ∧ d = td (B0 p0)) :
    ∃ d' : D1, (∃ p1, F1 (tx x) p1 ∧ d' = B1 p1) ∧
      dist d' d ≤ L * epsF + epsB := by
  obtain ⟨p0, hp0, rfl⟩ := hd
  obtain ⟨p1, hp1, hbound⟩ :=
    directed_setValued_fbt F0 F1 tx tp B0 B1 td L epsF epsB
      hL hF hbindingLip hbindingTransport x p0 hp0
  exact ⟨B1 p1, ⟨p1, hp1, rfl⟩, hbound⟩

/-- Directed set-valued continuation composes through a real intermediate
completion.  A Lipschitz bound on the *second realized transport* is necessary
to propagate the first error.  No same-parent or SameObject assertion occurs. -/
theorem directed_two_step_realized_continuation
    {X0 : Type uX0} {X1 : Type uX1} {X2 : Type uX2}
    {P0 : Type uP0} {P1 : Type uP1} {P2 : Type uP2}
    {D0 : Type uD0} {D1 : Type uD1} {D2 : Type uD2}
    [PseudoMetricSpace D1] [PseudoMetricSpace D2]
    (F0 : FormationRelation X0 P0) (F1 : FormationRelation X1 P1)
    (F2 : FormationRelation X2 P2)
    (tx01 : X0 → X1) (tx12 : X1 → X2)
    (B0 : P0 → D0) (B1 : P1 → D1) (B2 : P2 → D2)
    (td01 : D0 → D1) (td12 : D1 → D2)
    (delta01 delta12 M : ℝ) (hM : 0 ≤ M)
    (h01 : ∀ x p0, F0 x p0 →
      ∃ p1, F1 (tx01 x) p1 ∧
        dist (B1 p1) (td01 (B0 p0)) ≤ delta01)
    (h12 : ∀ x p1, F1 x p1 →
      ∃ p2, F2 (tx12 x) p2 ∧
        dist (B2 p2) (td12 (B1 p1)) ≤ delta12)
    (htransportLip : ∀ a b, dist (td12 a) (td12 b) ≤ M * dist a b)
    (x : X0) (p0 : P0) (hp0 : F0 x p0) :
    ∃ p1 p2,
      F1 (tx01 x) p1 ∧ F2 (tx12 (tx01 x)) p2 ∧
      dist (B2 p2) (td12 (td01 (B0 p0))) ≤ delta12 + M * delta01 := by
  obtain ⟨p1, hp1, hfirst⟩ := h01 x p0 hp0
  obtain ⟨p2, hp2, hsecond⟩ := h12 (tx01 x) p1 hp1
  refine ⟨p1, p2, hp1, hp2, ?_⟩
  calc
    dist (B2 p2) (td12 (td01 (B0 p0)))
        ≤ dist (B2 p2) (td12 (B1 p1)) +
          dist (td12 (B1 p1)) (td12 (td01 (B0 p0))) := dist_triangle _ _ _
    _ ≤ delta12 + M * dist (B1 p1) (td01 (B0 p0)) :=
      add_le_add hsecond (htransportLip _ _)
    _ ≤ delta12 + M * delta01 := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hfirst hM)

/-- Forward naturality allows a newly born target with no source predecessor;
therefore it cannot imply two-sided/Hausdorff correspondence. -/
theorem forward_formation_does_not_imply_reverse :
    ∃ (F0 F1 : FormationRelation Bool Bool) (tx tp : Bool → Bool),
      FormationTransportCompatible F0 F1 tx tp ∧
      ¬ (∀ x p1, F1 (tx x) p1 →
        ∃ p0, F0 x p0 ∧ tp p0 = p1) := by
  refine ⟨(fun _ p => p = false), (fun _ _ => True), id, id, ?_, ?_⟩
  · intro x p hp
    trivial
  · intro h
    obtain ⟨p0, h0, hmap⟩ := h false true (by trivial)
    change p0 = false at h0
    change p0 = true at hmap
    exact Bool.false_ne_true (h0.symm.trans hmap)

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure
