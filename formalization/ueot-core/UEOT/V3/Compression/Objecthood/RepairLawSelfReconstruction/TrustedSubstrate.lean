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

universe uX uA uP uR

/-- Immutable ambient semantics used to execute an object-level repair program.
The trusted substrate contains no distinguished "correct" program. -/
structure TrustedRepairSubstrate
    (Program : Type uP) (X : Type uX) (A : Type uA) where
  execute : Program → X → A


/-- Immutable encode/decode semantics for a mutable repair-program representation.
The codec contains no distinguished correct program; it only specifies how a
representation is interpreted and how a program is canonically represented. -/
structure TrustedRepairCodec
    (Program : Type uP) (Representation : Type uR) where
  encode : Program → Representation
  decode : Representation → Program
  decode_encode : ∀ r, decode (encode r) = r

end UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
