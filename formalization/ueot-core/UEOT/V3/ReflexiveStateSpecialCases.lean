import UEOT.V3.ReflexiveStateAugmentation

/-!
# P-REF-01 transition special cases

The frozen P-REF-01 source says that a structural update of the form

`S_{t+1} = F(S_t, X_t, a_t, ξ_t)`

is a special case of the controlled Markov-kernel formulation on the reflexive
state `Z = X × S`.  This file records that statement at the **transition-kernel**
level.  It is intentionally not a deterministic-policy statement.

A noise kernel first samples `ξ`; a measurable update map then turns
`(X_t,S_t,a_t,ξ_t)` into the next reflexive state.  Pushing the product kernel
through that update gives an ordinary Markov kernel on `Z`.  The zero-extra-
randomness case is the usual deterministic kernel.
-/

namespace UEOT.V3.ReflexiveStateSpecialCases

open MeasureTheory ProbabilityTheory
open UEOT.V3.ReflexiveStateAugmentation
open scoped ProbabilityTheory

universe uX uS uA uXi

variable {X : Type uX} {S : Type uS} {A : Type uA} {Ξ : Type uXi}
variable [MeasurableSpace X] [MeasurableSpace S]
variable [MeasurableSpace A] [MeasurableSpace Ξ]

abbrev Z := ReflexiveState X S

/-- Reorder the current reflexive state, action and noise into exactly the
source-facing argument order `(S_t, X_t, a_t, ξ_t)`. -/
def structureInput :
    ((Z (X := X) (S := S) × A) × Ξ) → (((S × X) × A) × Ξ) :=
  fun p => (((p.1.1.2, p.1.1.1), p.1.2), p.2)

theorem measurable_structureInput :
    Measurable (structureInput (X := X) (S := S) (A := A) (Ξ := Ξ)) := by
  unfold structureInput
  fun_prop

/-- A source-shaped reflexive update. `xNext` specifies the next physical
state while `F` is literally a measurable function of
`(S_t, X_t, a_t, ξ_t)` for the next structural state. -/
def structureModificationUpdate
    (xNext : ((Z (X := X) (S := S) × A) × Ξ) → X)
    (F : (((S × X) × A) × Ξ) → S) :
    ((Z (X := X) (S := S) × A) × Ξ) → Z (X := X) (S := S) :=
  fun p => (xNext p, F (structureInput p))

theorem measurable_structureModificationUpdate
    (xNext : ((Z (X := X) (S := S) × A) × Ξ) → X)
    (F : (((S × X) × A) × Ξ) → S)
    (hx : Measurable xNext) (hF : Measurable F) :
    Measurable (structureModificationUpdate xNext F) := by
  exact hx.prodMk (hF.comp measurable_structureInput)

@[simp]
theorem structureModificationUpdate_structure
    (xNext : ((Z (X := X) (S := S) × A) × Ξ) → X)
    (F : (((S × X) × A) × Ξ) → S)
    (p : ((Z (X := X) (S := S) × A) × Ξ)) :
    (structureModificationUpdate xNext F p).2 =
      F (((p.1.1.2, p.1.1.1), p.1.2), p.2) := rfl

/-- Noise-driven deterministic realization of a controlled reflexive
transition.  Given `(z,a)`, first sample `ξ ~ noise (z,a)` and then apply the
measurable deterministic update. -/
noncomputable def noiseDrivenReflexiveKernel
    (noise : Kernel (Z (X := X) (S := S) × A) Ξ)
    (update : ((Z (X := X) (S := S) × A) × Ξ) → Z (X := X) (S := S)) :
    Kernel (Z (X := X) (S := S) × A) (Z (X := X) (S := S)) :=
  (Kernel.id ×ₖ noise).map update

/-- A noise-driven measurable structural update is a Markov kernel whenever
the noise kernel is Markov.  This is a theorem rather than an instance because
measurability of `update` is an explicit proof obligation not recoverable by
typeclass synthesis from the kernel expression alone. -/
theorem isMarkovKernel_noiseDrivenReflexiveKernel
    (noise : Kernel (Z (X := X) (S := S) × A) Ξ)
    [IsMarkovKernel noise]
    (update : ((Z (X := X) (S := S) × A) × Ξ) → Z (X := X) (S := S))
    (hupdate : Measurable update) :
    IsMarkovKernel (noiseDrivenReflexiveKernel noise update) := by
  unfold noiseDrivenReflexiveKernel
  exact Kernel.IsMarkovKernel.map _ hupdate

/-- The exact source-shaped constructor
`S_{t+1}=F(S_t,X_t,a_t,ξ_t)` as an ordinary controlled Markov kernel. -/
noncomputable def structureModificationKernel
    (noise : Kernel (Z (X := X) (S := S) × A) Ξ)
    (xNext : ((Z (X := X) (S := S) × A) × Ξ) → X)
    (F : (((S × X) × A) × Ξ) → S) :
    Kernel (Z (X := X) (S := S) × A) (Z (X := X) (S := S)) :=
  noiseDrivenReflexiveKernel noise (structureModificationUpdate xNext F)

/-- The source-shaped structural-modification constructor is a Markov kernel.
The two measurability hypotheses remain explicit because they are mathematical
side conditions on the supplied update maps, not globally inferable instances. -/
theorem isMarkovKernel_structureModificationKernel
    (noise : Kernel (Z (X := X) (S := S) × A) Ξ)
    [IsMarkovKernel noise]
    (xNext : ((Z (X := X) (S := S) × A) × Ξ) → X)
    (F : (((S × X) × A) × Ξ) → S)
    (hx : Measurable xNext) (hF : Measurable F) :
    IsMarkovKernel (structureModificationKernel noise xNext F) := by
  unfold structureModificationKernel
  exact isMarkovKernel_noiseDrivenReflexiveKernel
    noise (structureModificationUpdate xNext F)
    (measurable_structureModificationUpdate xNext F hx hF)

/-- Zero-extra-randomness specialization: a measurable controlled update is
represented by the Dirac/`deterministic` Markov kernel. -/
noncomputable def deterministicReflexiveKernel
    (update : (Z (X := X) (S := S) × A) → Z (X := X) (S := S))
    (hupdate : Measurable update) :
    Kernel (Z (X := X) (S := S) × A) (Z (X := X) (S := S)) :=
  Kernel.deterministic update hupdate

instance isMarkovKernel_deterministicReflexiveKernel
    (update : (Z (X := X) (S := S) × A) → Z (X := X) (S := S))
    (hupdate : Measurable update) :
    IsMarkovKernel (deterministicReflexiveKernel update hupdate) := by
  unfold deterministicReflexiveKernel
  infer_instance

@[simp]
theorem deterministicReflexiveKernel_apply
    (update : (Z (X := X) (S := S) × A) → Z (X := X) (S := S))
    (hupdate : Measurable update)
    (za : Z (X := X) (S := S) × A) :
    deterministicReflexiveKernel update hupdate za = Measure.dirac (update za) := by
  exact Kernel.deterministic_apply hupdate za

end UEOT.V3.ReflexiveStateSpecialCases
