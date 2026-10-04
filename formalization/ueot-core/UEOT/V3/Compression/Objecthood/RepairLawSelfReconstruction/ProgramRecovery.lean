import UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction.TripleRedundancy

/-!
# RLSR5 — autonomous repair-program reconstruction dynamics

The trusted decoder is lifted to a one-step PMF kernel on mutable redundant
program state.  The exact reconstruction basin is characterized by validity of
the decoded program, and the valid redundant target is absorbing/idempotent.
-/

namespace UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction

open Set
open UEOT.V3.Compression.Objecthood
open UEOT.V3.ViabilityKernel

universe uX uA uP

noncomputable section

variable {X : Type uX} {A : Type uA} {Program : Type uP}
variable [DecidableEq Program]

/-- Trusted one-step canonicalization of mutable program replicas.  Runtime
input is only the current redundant representation. -/
noncomputable def tripleProgramReconstructionKernel
    (e : TripleProgramRepresentation Program) :
    PMF (TripleProgramRepresentation Program) :=
  PMF.pure (tripleProgramEncode (tripleProgramDecode e))

/-- Fully reconstructed object-level repair organization: all replicas agree on
one behaviorally valid executable program. -/
def ValidRedundantRepairProgram
    (T : TrustedRepairSubstrate Program X A)
    (P : X → A → PMF X) (K : Set X) :
    Set (TripleProgramRepresentation Program) :=
  {e | ∃ r, e = tripleProgramEncode r ∧ RepairProgramValid T P K r}

/-- Exact basin for the one-step reconstruction kernel: the surviving
information decodes to a behaviorally valid program. -/
def ProgramReconstructionBasin
    (T : TrustedRepairSubstrate Program X A)
    (P : X → A → PMF X) (K : Set X) :
    Set (TripleProgramRepresentation Program) :=
  {e | RepairProgramValid T P K (tripleProgramDecode e)}

@[simp] theorem tripleProgramReconstructionKernel_encode
    (r : Program) :
    tripleProgramReconstructionKernel (tripleProgramEncode r) =
      PMF.pure (tripleProgramEncode r) := by
  simp [tripleProgramReconstructionKernel]

/-- A valid codeword is a fixed point of program reconstruction. -/
theorem tripleProgramReconstructionKernel_eq_pure_self_of_valid
    (T : TrustedRepairSubstrate Program X A)
    (P : X → A → PMF X) (K : Set X)
    {e : TripleProgramRepresentation Program}
    (he : e ∈ ValidRedundantRepairProgram T P K) :
    tripleProgramReconstructionKernel e = PMF.pure e := by
  rcases he with ⟨r, rfl, hr⟩
  exact tripleProgramReconstructionKernel_encode r

/-- Every representation in the decoded-valid basin enters the valid redundant
target in one step. -/
theorem reconstructionKernel_enters_valid_of_mem_basin
    (T : TrustedRepairSubstrate Program X A)
    (P : X → A → PMF X) (K : Set X)
    {e : TripleProgramRepresentation Program}
    (he : e ∈ ProgramReconstructionBasin T P K) :
    StaysIn (tripleProgramReconstructionKernel e)
      (ValidRedundantRepairProgram T P K) := by
  intro e' he'
  have heq : e' = tripleProgramEncode (tripleProgramDecode e) := by
    simpa [tripleProgramReconstructionKernel, PMF.mem_support_iff] using he'
  subst e'
  exact ⟨tripleProgramDecode e, rfl, he⟩

/-- Conversely, entering the valid target in one reconstruction step forces the
decoded program itself to be valid.  This makes the basin characterization
exact rather than merely sufficient. -/
theorem mem_programReconstructionBasin_of_kernel_enters_valid
    (T : TrustedRepairSubstrate Program X A)
    (P : X → A → PMF X) (K : Set X)
    {e : TripleProgramRepresentation Program}
    (hstay : StaysIn (tripleProgramReconstructionKernel e)
      (ValidRedundantRepairProgram T P K)) :
    e ∈ ProgramReconstructionBasin T P K := by
  have hsupp :
      tripleProgramEncode (tripleProgramDecode e) ∈
        (tripleProgramReconstructionKernel e).support := by
    simp [tripleProgramReconstructionKernel]
  rcases hstay hsupp with ⟨r, hcode, hr⟩
  have hdecoded : tripleProgramDecode e = r := by
    have h0 := congrFun hcode 0
    simpa [tripleProgramEncode] using h0
  simpa [ProgramReconstructionBasin, hdecoded] using hr

/-- Exact one-step basin characterization. -/
theorem reconstructionKernel_enters_valid_iff_mem_basin
    (T : TrustedRepairSubstrate Program X A)
    (P : X → A → PMF X) (K : Set X)
    (e : TripleProgramRepresentation Program) :
    StaysIn (tripleProgramReconstructionKernel e)
        (ValidRedundantRepairProgram T P K) ↔
      e ∈ ProgramReconstructionBasin T P K := by
  constructor
  · exact mem_programReconstructionBasin_of_kernel_enters_valid T P K
  · exact reconstructionKernel_enters_valid_of_mem_basin T P K

/-- Valid redundant repair organization is absorbing under reconstruction. -/
theorem reconstructionKernel_staysIn_valid_target
    (T : TrustedRepairSubstrate Program X A)
    (P : X → A → PMF X) (K : Set X)
    {e : TripleProgramRepresentation Program}
    (he : e ∈ ValidRedundantRepairProgram T P K) :
    StaysIn (tripleProgramReconstructionKernel e)
      (ValidRedundantRepairProgram T P K) := by
  rw [tripleProgramReconstructionKernel_eq_pure_self_of_valid T P K he]
  simpa [StaysIn, PMF.mem_support_iff] using he

/-- Any arbitrary single-replica replacement of a valid codeword lies in the
exact reconstruction basin. -/
theorem singleReplicaCorruption_mem_programReconstructionBasin
    (T : TrustedRepairSubstrate Program X A)
    (P : X → A → PMF X) (K : Set X)
    {r : Program} (hr : RepairProgramValid T P K r)
    (bad : Program) (i : Fin 3) :
    replaceProgramReplica i bad (tripleProgramEncode r) ∈
      ProgramReconstructionBasin T P K := by
  change RepairProgramValid T P K
    (tripleProgramDecode
      (replaceProgramReplica i bad (tripleProgramEncode r)))
  simpa [tripleProgramDecode_replace_encode] using hr

/-- Single-replica corruption is corrected *exactly* to the original codeword in
one runtime reconstruction step. -/
theorem reconstructionKernel_singleReplica_exact
    (r bad : Program) (i : Fin 3) :
    tripleProgramReconstructionKernel
      (replaceProgramReplica i bad (tripleProgramEncode r)) =
        PMF.pure (tripleProgramEncode r) := by
  simp [tripleProgramReconstructionKernel,
    tripleProgramDecode_replace_encode]

end
end UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
