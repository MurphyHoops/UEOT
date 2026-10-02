import UEOT.V3.Compression.CrossTrack.PCompParentSemantic
import UEOT.V3.Compression.CrossTrack.ParentSemanticNoGo

/-!
# Parent Binding Mechanism — PB0 no-go

P-COMP-06 carrier validity and common child binding do not by themselves
control parent dynamics or long-run semantics.
-/

namespace UEOT.V3.Compression.CrossTrack

open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.CompositionCarrierLift
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.Compression.TopologyChangingGoaFunctionalGraphClassification

noncomputable section

/-- Degenerate but genuine physical-carrier instance: the empty physical
carrier is the sole physical minimum.  Its unique minimal child coalition is
empty. -/
def pb0Regions : Unit → Finset Unit := fun _ => ∅

def pb0PhysicalMin : Set (Finset Unit) := {∅}

theorem pb0_empty_childMinimal :
    (∅ : Finset Unit) ∈ childMinimalFamily pb0Regions pb0PhysicalMin := by
  change UEOT.Finite.Minimal
    (childSufficient pb0Regions pb0PhysicalMin) ∅
  constructor
  · refine ⟨∅, ?_, ?_⟩
    · simp [pb0PhysicalMin]
    · simp [coalitionCovers]
  · intro T hT _hchild
    exact Finset.subset_empty.mp hT

/-- Both Boolean parent completions are P-COMP-06-valid and bind to exactly the
same child evidence.  The assembly certificate says nothing about their
dynamics. -/
def pb0Assembly :
    PCompCarrierAssemblyCertificate
      (P := Bool) (C := Unit) (I := Unit) (V := Unit)
      x1ChildProjection where
  child := ()
  regions := pb0Regions
  physicalMin := pb0PhysicalMin
  coalition := fun _ => ∅
  admissible := fun _ => True
  admissible_iff_childMinimal := by
    intro p
    constructor
    · intro _
      exact pb0_empty_childMinimal
    · intro _
      trivial
  child_binding := by
    intro p _
    rfl
  nonempty := ⟨false, trivial⟩

@[simp] theorem pb0_false_admissible : pb0Assembly.admissible false := by
  trivial

@[simp] theorem pb0_true_admissible : pb0Assembly.admissible true := by
  trivial

/-- The two P-COMP-valid completions can induce genuinely different parent
kernels. -/
theorem pb0_valid_completions_have_different_dynamics :
    x1Kernel false ≠ x1Kernel true := by
  intro h
  have hentry := congrFun (congrFun h false) false
  simp [x1Kernel, detKernel] at hentry

/-- **PB0 — P-COMP validity alone does not identify stable parent semantics.**

The same valid P-COMP-06 assembly certificate admits two richer parent
completions bound to the same child evidence.  Their dynamics differ, each has
an explicitly stationary unique long-run law, and those laws are maximally
separated in total variation.

Therefore the dynamics-defect premise used by Track X cannot be deleted or
derived from P-COMP-06 carrier validity alone. -/
theorem pb0_pcompValidity_does_not_control_parent_semantics :
    pb0Assembly.admissible false ∧
    pb0Assembly.admissible true ∧
    x1ChildProjection false = x1ChildProjection true ∧
    x1Kernel false ≠ x1Kernel true ∧
    x1Invariant false ∈
      invariantLawSet (x1Kernel false) (x1Kernel_stochastic false) ∧
    x1Invariant true ∈
      invariantLawSet (x1Kernel true) (x1Kernel_stochastic true) ∧
    lawTV (x1Invariant false) (x1Invariant true) = 1 := by
  exact ⟨by trivial, by trivial, rfl,
    pb0_valid_completions_have_different_dynamics,
    x1Invariant_mem false, x1Invariant_mem true, x1Invariant_distance⟩

end

end UEOT.V3.Compression.CrossTrack
