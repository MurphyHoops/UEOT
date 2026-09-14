import UEOT.V3.ReflexiveStatePathUniqueness
import UEOT.V3.ReflexiveStateSpecialCases
import UEOT.V3.ReflexiveControlledClosure

/-!
# P-REF-01 — source-faithful theorem surface

This module assembles the three clauses frozen in the canonical UEOT Core 3
source without conflating them:

1. on the reflexive state `Z = X × S`, a Markov controlled kernel together with
   an arbitrary causal randomized policy generates one unique state path law;
2. a structural modification `S_{t+1}=F(S_t,X_t,a_t,ξ_t)` is realized as a
   special case of such a controlled Markov kernel, while the policy remains
   arbitrary and causal;
3. after a further compression `φ : Z → M`, controlled/Markov closure is a
   separate action-wise lumpability obligation.  Reflexive augmentation is not
   used as a proof of that obligation.
-/

namespace UEOT.V3.ReflexivePRef01

open MeasureTheory ProbabilityTheory
open UEOT.V3.ReflexiveStateAugmentation
open UEOT.V3.ReflexiveStatePathUniqueness
open UEOT.V3.ReflexiveStateSpecialCases
open UEOT.V3.ReflexiveControlledClosure
open UEOT.V3.DynamicsKernel
open scoped ProbabilityTheory

universe uX uS uA uXi uM

variable {X : Type uX} {S : Type uS} {A : Type uA} {Ξ : Type uXi}
variable [MeasurableSpace X] [MeasurableSpace S]
variable [MeasurableSpace A] [MeasurableSpace Ξ]

abbrev Z := ReflexiveState X S

/-- **P-REF-01, main clause.** On the measurable reflexive state `Z = X × S`,
an initial probability law, a controlled Markov kernel, and an arbitrary causal
randomized policy determine one unique reflexive-state path law.  No
Standard-Borel restriction is needed once the measurable Markov kernels are
supplied; this keeps the theorem at the generality of the frozen source. -/
theorem p_ref_01
    (mu0 : Measure (Z (X := X) (S := S)))
    (K : Kernel (Z (X := X) (S := S) × A) (Z (X := X) (S := S)))
    (pi : CausalPolicy (Z (X := X) (S := S)) A)
    [IsProbabilityMeasure mu0]
    [IsMarkovKernel K]
    [∀ n, IsMarkovKernel (pi n)] :
    ∃! rho : Measure (ℕ → Z (X := X) (S := S)),
      IsReflexivePathLaw mu0 K pi rho :=
  p_ref_01_pathlaw_unique mu0 K pi

/-- **P-REF-01, structural-modification specialization.** A measurable update
whose structural coordinate is literally
`F(S_t,X_t,a_t,ξ_t)` and whose exogenous noise is sampled by a Markov kernel is
an ordinary controlled Markov kernel on `X × S`.  Consequently the main
P-REF-01 path-law theorem applies with the *same arbitrary causal policy*.

This is the source's deterministic-modification special case; it is not a
restriction to deterministic policies. -/
theorem p_ref_01_structureModification
    (mu0 : Measure (Z (X := X) (S := S)))
    (noise : Kernel (Z (X := X) (S := S) × A) Ξ)
    (xNext : ((Z (X := X) (S := S) × A) × Ξ) → X)
    (F : (((S × X) × A) × Ξ) → S)
    (pi : CausalPolicy (Z (X := X) (S := S)) A)
    [IsProbabilityMeasure mu0]
    [IsMarkovKernel noise]
    [∀ n, IsMarkovKernel (pi n)]
    (hx : Measurable xNext)
    (hF : Measurable F) :
    ∃! rho : Measure (ℕ → Z (X := X) (S := S)),
      IsReflexivePathLaw mu0
        (structureModificationKernel noise xNext F) pi rho := by
  letI : IsMarkovKernel (structureModificationKernel noise xNext F) :=
    isMarkovKernel_structureModificationKernel noise xNext F hx hF
  exact p_ref_01 mu0 (structureModificationKernel noise xNext F) pi

/-- **P-REF-01, compression clause in one-step form.** A measurable compression
`φ : Z → M` closes to a controlled macro-kernel `Kbar` exactly when the
one-step pushed-forward transition agrees with `Kbar` for every microscopic
state and every allowed action.  This is a separate obligation after reflexive
augmentation. -/
theorem p_ref_01_compression_closure_iff_kernel
    {M : Type uM} [MeasurableSpace M]
    (K : Kernel (Z (X := X) (S := S) × A) (Z (X := X) (S := S)))
    (Kbar : Kernel (M × A) M)
    (φ : Z (X := X) (S := S) → M)
    (hφ : Measurable φ) :
    ControlledStrongLumpability K Kbar φ hφ ↔
      ∀ a : A, ∀ z : Z (X := X) (S := S),
        (K (z, a)).map φ = Kbar (φ z, a) :=
  controlledStrongLumpability_iff_apply K Kbar φ hφ

/-- **P-REF-01, compression clause in path-law form.** Under Markov-kernel
hypotheses, the same action-wise controlled closure condition is equivalent to
path-law closure for every frozen action, by the already proved P-DYN-01 bridge.
No implication from reflexivity to closure is assumed. -/
theorem p_ref_01_compression_closure_iff_pathLaw
    {M : Type uM} [MeasurableSpace M]
    (K : Kernel (Z (X := X) (S := S) × A) (Z (X := X) (S := S)))
    (Kbar : Kernel (M × A) M)
    [IsMarkovKernel K]
    [IsMarkovKernel Kbar]
    (φ : Z (X := X) (S := S) → M)
    (hφ : Measurable φ) :
    ControlledStrongLumpability K Kbar φ hφ ↔
      ∀ a : A,
        PathLawLumpability
          (fixedActionKernel K a)
          (fixedActionKernel Kbar a)
          φ hφ :=
  controlledStrongLumpability_iff_actionPathLaw K Kbar φ hφ

end UEOT.V3.ReflexivePRef01
