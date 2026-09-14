import UEOT.V3.ReflexiveStateAugmentation
import UEOT.V3.DynamicsKernel

/-!
# P-REF-01 controlled-compression closure

Reflexive state augmentation does not by itself imply that a lower-dimensional
compression is Markov.  The frozen P-REF-01 contract therefore reuses the
P-DYN-01 lumpability criterion and requires it separately for every allowed
action.

This file deliberately does not derive closure from reflexivity.  It exposes
the exact extra condition and transports the already-proved kernel/path-law
bridge action by action.
-/

namespace UEOT.V3.ReflexiveControlledClosure

open MeasureTheory ProbabilityTheory
open UEOT.V3.DynamicsKernel
open scoped ProbabilityTheory

universe uZ uM uA

variable {Z : Type uZ} {M : Type uM} {A : Type uA}
variable [MeasurableSpace Z] [MeasurableSpace M] [MeasurableSpace A]

/-- Freeze one action in a controlled kernel.  This is the ordinary homogeneous
state kernel whose trajectories describe repeated use of that action. -/
noncomputable def fixedActionKernel
    (K : Kernel (Z × A) Z) (a : A) : Kernel Z Z :=
  K.comap (fun z => (z, a)) (measurable_id.prodMk measurable_const)

instance isMarkovKernel_fixedActionKernel
    (K : Kernel (Z × A) Z) [IsMarkovKernel K] (a : A) :
    IsMarkovKernel (fixedActionKernel K a) := by
  unfold fixedActionKernel
  infer_instance

/-- Source-faithful controlled closure after a measurable compression `f`:
there must be one macroscopic controlled kernel `Kbar`, and strong lumpability
must hold for every allowed action.  A statement for only one passive policy is
strictly weaker and is not this definition. -/
def ControlledStrongLumpability
    (K : Kernel (Z × A) Z)
    (Kbar : Kernel (M × A) M)
    (f : Z → M) (hf : Measurable f) : Prop :=
  ∀ a : A,
    StrongLumpability
      (fixedActionKernel K a)
      (fixedActionKernel Kbar a)
      f hf

/-- Kernel-level form of controlled closure: for every microscopic state and
every allowed action, pushing the one-step microscopic law through the
compression agrees with the macroscopic controlled transition. -/
theorem controlledStrongLumpability_iff_apply
    (K : Kernel (Z × A) Z)
    (Kbar : Kernel (M × A) M)
    (f : Z → M) (hf : Measurable f) :
    ControlledStrongLumpability K Kbar f hf ↔
      ∀ a : A, ∀ z : Z,
        (K (z, a)).map f = Kbar (f z, a) := by
  constructor
  · intro h a z
    have hz :=
      (strongLumpability_iff_apply
        (fixedActionKernel K a)
        (fixedActionKernel Kbar a) f hf).1 (h a) z
    simpa [fixedActionKernel, Kernel.comap_apply] using hz
  · intro h a
    rw [strongLumpability_iff_apply]
    intro z
    simpa [fixedActionKernel, Kernel.comap_apply] using h a z

/-- Action-wise controlled closure is equivalent to the complete homogeneous
path-law closure for every frozen action.  This is exactly the P-DYN-01 bridge
reused at the reflexive-compression boundary; no new Markov assumption is
smuggled in through the reflexive-state construction. -/
theorem controlledStrongLumpability_iff_actionPathLaw
    (K : Kernel (Z × A) Z)
    (Kbar : Kernel (M × A) M)
    [IsMarkovKernel K] [IsMarkovKernel Kbar]
    (f : Z → M) (hf : Measurable f) :
    ControlledStrongLumpability K Kbar f hf ↔
      ∀ a : A,
        PathLawLumpability
          (fixedActionKernel K a)
          (fixedActionKernel Kbar a)
          f hf := by
  constructor
  · intro h a
    exact strongLumpability_implies_pathLaw
      (fixedActionKernel K a)
      (fixedActionKernel Kbar a)
      f hf (h a)
  · intro h a
    exact pathLaw_implies_strongLumpability
      (fixedActionKernel K a)
      (fixedActionKernel Kbar a)
      f hf (h a)

/-- Forward source-facing closure theorem: once the separate action-wise
lumpability condition has actually been verified, every fixed-action path law
closes on the compressed controlled state. -/
theorem controlledCompression_pathLaw
    (K : Kernel (Z × A) Z)
    (Kbar : Kernel (M × A) M)
    [IsMarkovKernel K] [IsMarkovKernel Kbar]
    (f : Z → M) (hf : Measurable f)
    (hclose : ControlledStrongLumpability K Kbar f hf)
    (a : A) :
    PathLawLumpability
      (fixedActionKernel K a)
      (fixedActionKernel Kbar a)
      f hf :=
  (controlledStrongLumpability_iff_actionPathLaw K Kbar f hf).1 hclose a

end UEOT.V3.ReflexiveControlledClosure
