import UEOT.V3.CompositionMargin

/-!
# Parent Binding Mechanism — P-COMP diagnostic identifiability no-go

Forward stability of a composition diagnostic does not imply that the
diagnostic identifies the richer parent state.  This separates P-COMP-03's
Lipschitz margin theorem from the inverse/binding regularity needed by PB3.
-/

namespace UEOT.V3.Compression.CrossTrack

open UEOT.V3.CompositionMargin

noncomputable section

/-- One declared cut which simply returns the supplied parent state. -/
def pbDiagnosticIdentityCut : Unit → ℝ → ℝ := fun _ x => x

def pbDiagnosticLip : Unit → ℝ := fun _ => 1

theorem pbDiagnosticIdentityCut_lipschitz :
    ∀ i x y,
      dist (pbDiagnosticIdentityCut i x) (pbDiagnosticIdentityCut i y) ≤
        pbDiagnosticLip i * dist x y := by
  intro i x y
  simp [pbDiagnosticIdentityCut, pbDiagnosticLip]

/-- The P-COMP-03 composition margin is identically zero for the identity cut. -/
theorem pbDiagnostic_margin_zero (x : ℝ) :
    compositionMargin pbDiagnosticIdentityCut x = 0 := by
  unfold compositionMargin
  simp [pbDiagnosticIdentityCut]

/-- The genuine frozen P-COMP-03 forward-Lipschitz theorem applies to this
example. -/
theorem pbDiagnostic_p_comp_03_applies (x y : ℝ) :
    |compositionMargin pbDiagnosticIdentityCut x -
        compositionMargin pbDiagnosticIdentityCut y| ≤
      (1 + maxCutLipschitz pbDiagnosticLip) * dist x y := by
  exact p_comp_03
    pbDiagnosticIdentityCut pbDiagnosticLip
    pbDiagnosticIdentityCut_lipschitz x y

/-- **Diagnostic no-go.**

Two distinct richer parent states can have exactly the same P-COMP-03
composition margin even though that diagnostic satisfies the source-facing
forward Lipschitz theorem.  Therefore P-COMP-03 continuity alone cannot supply
an inverse parent-binding metric or a kernel-realization Lipschitz constant. -/
theorem p_comp_03_forward_stability_not_parent_identifiability :
    compositionMargin pbDiagnosticIdentityCut 0 =
        compositionMargin pbDiagnosticIdentityCut 1 ∧
    (0 : ℝ) ≠ 1 := by
  constructor
  · rw [pbDiagnostic_margin_zero, pbDiagnostic_margin_zero]
  · norm_num

end

end UEOT.V3.Compression.CrossTrack
