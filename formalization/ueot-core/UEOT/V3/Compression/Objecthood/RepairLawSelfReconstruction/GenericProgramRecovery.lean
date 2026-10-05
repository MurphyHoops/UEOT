import UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction.ProgramSemantics

/-!
# RLSR-T8 — generic codec reconstruction and identity basins

RLSR5 originally instantiated program reconstruction directly with the triple
repetition code.  The post-audit architecture already has a generic trusted
codec, so this module lifts the recovery semantics to an arbitrary codec and
separates three different notions that should not be conflated:

* decoded-valid basin;
* exact source-program basin;
* dynamics-source basin modulo physical transition equivalence.
-/

namespace UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction

open Set
open UEOT.V3.ViabilityKernel
open UEOT.V3.Compression.Objecthood

universe uX uA uP uR uO

noncomputable section

variable {X : Type uX} {A : Type uA}
variable {Program : Type uP} {Representation : Type uR} {Obs : Type uO}

/-- Generic trusted one-step canonicalization of a mutable representation. -/
noncomputable def codecReconstructionKernel
    (codec : TrustedRepairCodec Program Representation)
    (e : Representation) : PMF Representation :=
  PMF.pure (codec.encode (codec.decode e))

/-- Canonical representations whose decoded program is behaviorally valid. -/
def CodecValidRepairTarget
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (P : X → A → PMF X) (K : Set X) : Set Representation :=
  {e | ∃ r, e = codec.encode r ∧ RepairProgramValid T P K r}

/-- Representations whose currently decoded program is valid.  This is a
*validity* basin, not yet a source-identity basin. -/
def CodecValidityBasin
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (P : X → A → PMF X) (K : Set X) : Set Representation :=
  {e | RepairProgramValid T P K (codec.decode e)}

/-- Exact source identity: decoding returns the designated source program. -/
def CodecExactSourceBasin
    (codec : TrustedRepairCodec Program Representation)
    (r : Program) : Set Representation :=
  {e | codec.decode e = r}

/-- Operational source identity: decoding need only return a program inducing
the same physical transition kernel on the object carrier. -/
def CodecDynamicsSourceBasin
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (P : X → A → PMF X) (K : Set X)
    (r : Program) : Set Representation :=
  {e | RepairProgramDynamicsEquivalentOn T P K (codec.decode e) r}

@[simp] theorem codecReconstructionKernel_encode
    (codec : TrustedRepairCodec Program Representation)
    (r : Program) :
    codecReconstructionKernel codec (codec.encode r) =
      PMF.pure (codec.encode r) := by
  simp [codecReconstructionKernel, codec.decode_encode]

/-- A canonical valid codeword is a fixed point of generic reconstruction. -/
theorem codecReconstructionKernel_eq_pure_self_of_valid
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (P : X → A → PMF X) (K : Set X)
    {e : Representation}
    (he : e ∈ CodecValidRepairTarget T codec P K) :
    codecReconstructionKernel codec e = PMF.pure e := by
  rcases he with ⟨r, rfl, hr⟩
  exact codecReconstructionKernel_encode codec r

/-- The generic validity basin is exactly the one-step preimage of the canonical
valid target. -/
theorem codecReconstructionKernel_enters_valid_iff_mem_validityBasin
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (P : X → A → PMF X) (K : Set X)
    (e : Representation) :
    StaysIn (codecReconstructionKernel codec e)
        (CodecValidRepairTarget T codec P K) ↔
      e ∈ CodecValidityBasin T codec P K := by
  constructor
  · intro hstay
    have hsupp : codec.encode (codec.decode e) ∈
        (codecReconstructionKernel codec e).support := by
      simp [codecReconstructionKernel]
    rcases hstay hsupp with ⟨r, hcode, hr⟩
    have hdecoded : codec.decode e = r := by
      have h := congrArg codec.decode hcode
      simpa [codec.decode_encode] using h
    simpa [CodecValidityBasin, hdecoded] using hr
  · intro he e' he'
    have heq : e' = codec.encode (codec.decode e) := by
      simpa [codecReconstructionKernel, PMF.mem_support_iff] using he'
    subst e'
    exact ⟨codec.decode e, rfl, he⟩

/-- Exact source recovery is stronger than dynamics-level source recovery. -/
theorem codecExactSourceBasin_subset_dynamicsSourceBasin
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (P : X → A → PMF X) (K : Set X)
    (r : Program) :
    CodecExactSourceBasin codec r ⊆
      CodecDynamicsSourceBasin T codec P K r := by
  intro e he x hx
  change codec.decode e = r at he
  rw [he]

/-- If the source program is valid, every representation decoding to a
dynamics-equivalent source behavior lies in the generic validity basin. -/
theorem codecDynamicsSourceBasin_subset_validityBasin_of_source_valid
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (P : X → A → PMF X) (K : Set X)
    {r : Program} (hr : RepairProgramValid T P K r) :
    CodecDynamicsSourceBasin T codec P K r ⊆
      CodecValidityBasin T codec P K := by
  intro e he
  exact repairProgramValid_of_dynamicsEquivalent T P K hr
    (fun x hx => (he x hx).symm)

/-- Exact source-basin membership reconstructs the designated source codeword in
one step. -/
theorem codecReconstructionKernel_exact_of_mem_sourceBasin
    (codec : TrustedRepairCodec Program Representation)
    {r : Program} {e : Representation}
    (he : e ∈ CodecExactSourceBasin codec r) :
    codecReconstructionKernel codec e = PMF.pure (codec.encode r) := by
  change codec.decode e = r at he
  simp [codecReconstructionKernel, he]

/-- General corruption-correction contract for a trusted codec. -/
def CodecCorrectsCorruption
    (codec : TrustedRepairCodec Program Representation)
    (Corrupt : Program → Representation → Prop) : Prop :=
  ∀ r e, Corrupt r e → codec.decode e = r

/-- Any corruption relation corrected by the codec is mapped exactly back to the
source codeword by the generic reconstruction kernel. -/
theorem codecReconstructionKernel_exact_of_corrects
    (codec : TrustedRepairCodec Program Representation)
    (Corrupt : Program → Representation → Prop)
    (hcorr : CodecCorrectsCorruption codec Corrupt)
    {r : Program} {e : Representation}
    (he : Corrupt r e) :
    codecReconstructionKernel codec e = PMF.pure (codec.encode r) := by
  exact codecReconstructionKernel_exact_of_mem_sourceBasin codec (hcorr r e he)

end
end UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
