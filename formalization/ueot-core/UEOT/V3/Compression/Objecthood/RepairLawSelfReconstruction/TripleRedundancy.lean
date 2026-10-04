import UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction.IdentifiabilityBoundary

/-!
# RLSR4 — finite triple-redundant repair-program reconstruction

The first constructive benchmark uses three mutable replicas of one executable
repair program.  Majority-by-equality corrects an arbitrary replacement of any
single replica.  A two-replica collision theorem records why literal two-copy
replication cannot solve the same exact reconstruction problem without extra
side information.
-/

namespace UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction

universe uP

section Triple

variable {Program : Type uP} [DecidableEq Program]

abbrev TripleProgramRepresentation (Program : Type uP) := Fin 3 → Program

/-- Three mutable copies of one executable repair program. -/
def tripleProgramEncode (r : Program) : TripleProgramRepresentation Program :=
  fun _ => r

/-- Trusted majority decoder for three replicas.  If replicas 0 and 1 agree,
use them; otherwise replica 2 must be one of the two surviving copies under the
single-replacement fault model. -/
def tripleProgramDecode (e : TripleProgramRepresentation Program) : Program :=
  if e 0 = e 1 then e 0 else e 2

/-- Replace exactly one replica by an arbitrary program. -/
def replaceProgramReplica
    (i : Fin 3) (bad : Program)
    (e : TripleProgramRepresentation Program) : TripleProgramRepresentation Program :=
  fun j => if j = i then bad else e j

@[simp] theorem tripleProgramDecode_encode (r : Program) :
    tripleProgramDecode (tripleProgramEncode r) = r := by
  simp [tripleProgramDecode, tripleProgramEncode]

/-- Exact correction of an arbitrary one-replica replacement. -/
theorem tripleProgramDecode_replace_encode
    (r bad : Program) (i : Fin 3) :
    tripleProgramDecode
      (replaceProgramReplica i bad (tripleProgramEncode r)) = r := by
  fin_cases i <;>
    simp [tripleProgramDecode, replaceProgramReplica, tripleProgramEncode]

/-- The entire single-replacement corruption class decodes to the source
program. -/
def SingleReplicaCorruptionOf
    (r : Program) (e : TripleProgramRepresentation Program) : Prop :=
  ∃ i : Fin 3, ∃ bad : Program,
    e = replaceProgramReplica i bad (tripleProgramEncode r)

theorem tripleProgramDecode_of_singleReplicaCorruption
    {r : Program} {e : TripleProgramRepresentation Program}
    (h : SingleReplicaCorruptionOf r e) :
    tripleProgramDecode e = r := by
  rcases h with ⟨i, bad, rfl⟩
  exact tripleProgramDecode_replace_encode r bad i

end Triple

section TwoReplicaBoundary

variable {Program : Type uP}

abbrev PairProgramRepresentation (Program : Type uP) := Fin 2 → Program

def pairProgramEncode (r : Program) : PairProgramRepresentation Program :=
  fun _ => r

def replacePairReplica
    (i : Fin 2) (bad : Program)
    (e : PairProgramRepresentation Program) : PairProgramRepresentation Program :=
  fun j => if j = i then bad else e j

/-- Two literal replicas have an exact single-replacement ambiguity: corrupting
copy 0 of `r₁` toward `r₂` produces the same observed pair as corrupting copy 1
of `r₂` toward `r₁`. -/
theorem twoReplica_singleReplacement_collision
    (r₁ r₂ : Program) :
    replacePairReplica 0 r₂ (pairProgramEncode r₁) =
      replacePairReplica 1 r₁ (pairProgramEncode r₂) := by
  funext j
  fin_cases j <;>
    simp [replacePairReplica, pairProgramEncode]

/-- Consequently, if `r₁ ≠ r₂`, no deterministic decoder can return the exact
source program for every one-replica replacement of both source codewords. -/
theorem no_exact_twoReplica_decoder_for_distinct_sources
    {r₁ r₂ : Program} (hne : r₁ ≠ r₂) :
    ¬ ∃ decode : PairProgramRepresentation Program → Program,
        (∀ i : Fin 2, decode (replacePairReplica i r₂ (pairProgramEncode r₁)) = r₁) ∧
        (∀ i : Fin 2, decode (replacePairReplica i r₁ (pairProgramEncode r₂)) = r₂) := by
  rintro ⟨decode, h₁, h₂⟩
  apply hne
  calc
    r₁ = decode (replacePairReplica 0 r₂ (pairProgramEncode r₁)) := (h₁ 0).symm
    _ = decode (replacePairReplica 1 r₁ (pairProgramEncode r₂)) := by
      rw [twoReplica_singleReplacement_collision]
    _ = r₂ := h₂ 1

end TwoReplicaBoundary

end UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
