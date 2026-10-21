import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteSupportViability

/-!
# Complete causal policies realized by autonomous memory

Initialization reads the first observation. The action distribution reads
only the current memory, and the update reads that memory, the recorded
action and the new observation. Neither output nor update receives time or
the remaining history. A finite instance on `M` therefore supplies a finite
memory implementation of the entire policy, including unsupported histories.

This representation supplies no certification conclusion: source support
and actual deployment occupancy must be proved separately.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open UEOT.V3.PathError

universe u

/-- An autonomous observation controller with explicit total memory. -/
structure FiniteMemoryController (M Y A : Type u) where
  initialize : Y → M
  action : M → PMF A
  update : M → A → Y → M

namespace FiniteMemoryController

/-- The actual memory obtained by replaying a complete observed record. -/
def memory {M Y A : Type u} (controller : FiniteMemoryController M Y A) :
    ∀ n, CausalHistory Y (A × Y) n → M
  | 0, y => controller.initialize y
  | n + 1, h => controller.update (controller.memory n h.1) h.2.1 h.2.2

/-- The complete history policy induced by the autonomous controller. -/
def policy {M Y A : Type u} (controller : FiniteMemoryController M Y A) :
    ∀ n, CausalHistory Y (A × Y) n → PMF A :=
  fun n h => controller.action (controller.memory n h)

end FiniteMemoryController
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
