import Mathlib

/-!
# RLSR0 — trusted repair substrate boundary

Repair-law self-reconstruction must stop an otherwise vacuous regress somewhere.
The trusted substrate is that explicit boundary.  It supplies only execution
semantics for an encoded repair program.  The repair program itself is *not*
stored here and may be corrupted as mutable object state in later stages.

This is a relative self-reconstruction theorem architecture: it does not claim
that the ambient mathematics, physical laws, or interpreter semantics reconstruct
themselves.
-/

namespace UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction

universe uX uA uP

/-- Immutable ambient semantics used to execute an object-level repair program.
The trusted substrate contains no distinguished "correct" program. -/
structure TrustedRepairSubstrate
    (Program : Type uP) (X : Type uX) (A : Type uA) where
  execute : Program → X → A

end UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
