import UEOT.V3.Compression.CrossTrack.DualIsolationCanonical
import UEOT.V3.Compression.CrossTrack.ParentSemanticNoGo

/-!
# Dual Isolation — binding-identifiability no-go

The second isolation margin is not optional bookkeeping.  A diagnostic that
collapses distinct parent assemblies cannot have any positive binding-
isolation certificate, while the corresponding completions may still possess
individually unique but maximally separated long-run semantics.
-/

namespace UEOT.V3.Compression.CrossTrack

open UEOT.V3
open UEOT.V3.FiniteDobrushin

noncomputable section

/-- Two distinct richer parent completions represented as distinct assembly
points. -/
def dualIsolationNoGoAssembly : Bool → ℝ := fun p => if p then 1 else 0

/-- Completely uninformative lower-level diagnostic. -/
def dualIsolationConstantDiagnostic : ℝ → ℝ := fun _ => 0

/-- No positive binding-isolation margin exists for a constant diagnostic. -/
theorem dualIsolationConstantDiagnostic_no_isolation (beta : ℝ) :
    ¬ BindingIsolation dualIsolationConstantDiagnostic beta := by
  intro hiso
  have hinj := BindingIsolation.injective
    dualIsolationConstantDiagnostic beta hiso
  have heq : dualIsolationConstantDiagnostic 0 =
      dualIsolationConstantDiagnostic 1 := rfl
  have h01 : (0 : ℝ) = 1 := hinj heq
  norm_num at h01

/-- **Dual-isolation no-go.**

Same diagnostic evidence may coexist with maximally separated stable parent
semantics.  Therefore semantic isolation (`kappa > 0`) cannot substitute for
binding isolation (`beta > 0`). -/
theorem semanticIsolation_does_not_imply_bindingIsolation :
    dualIsolationConstantDiagnostic (dualIsolationNoGoAssembly false) =
        dualIsolationConstantDiagnostic (dualIsolationNoGoAssembly true) ∧
    dualIsolationNoGoAssembly false ≠ dualIsolationNoGoAssembly true ∧
    (∀ p : Bool, 0 <
      UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm.l1ResidualConorm
        (x1Kernel p)) ∧
    lawTV (x1Invariant false) (x1Invariant true) = 1 ∧
    (∀ beta : ℝ,
      ¬ BindingIsolation dualIsolationConstantDiagnostic beta) := by
  refine ⟨rfl, ?_, ?_, x1Invariant_distance,
    dualIsolationConstantDiagnostic_no_isolation⟩
  · norm_num [dualIsolationNoGoAssembly]
  intro p
  rw [x1Kernel_l1ResidualConorm_eq_one]
  norm_num

end

end UEOT.V3.Compression.CrossTrack
