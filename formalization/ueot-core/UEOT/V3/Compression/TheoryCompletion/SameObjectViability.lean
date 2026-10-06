import UEOT.V3.Compression.TheoryCompletion.SameObjectGOAStability
import UEOT.V3.Compression.ContractiveFixedPoint

/-!
# P2.7 — Optimality versus object viability

Bellman optimality does not by itself imply self-preservation. This module
proves a concrete finite counterexample and then states the explicit
same-Objecthood persistence-compatibility gate required by P2.
-/

namespace UEOT.V3.Compression.TheoryCompletion

open Set MeasureTheory ProbabilityTheory
open UEOT.V3
open UEOT.V3.ViabilityKernel
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.CrossTrack
open UEOT.V3.Compression.Objecthood

/-! ## P2.7 no-go: an optimal action can leave a viable set -/

private noncomputable def viabilityBoundaryDynamics :
    Bool → Bool → PMF Bool :=
  fun _ a => PMF.pure a

private noncomputable def viabilityBoundaryModel :
    Model Bool (fun _ : Bool => Bool) where
  transition := fun _ a y => if y = a then 1 else 0
  reward := fun _ a => if a then 1 else 0
  rewardBound := 1
  discount := 1 / 2
  transition_nonneg := by
    intro _ a y
    by_cases h : y = a <;> simp [h]
  transition_sum_one := by
    intro _ a
    classical
    cases a <;> simp
  reward_abs_le := by
    intro _ a
    cases a <;> norm_num
  discount_pos := by norm_num
  discount_lt_one := by norm_num

private theorem viabilityBoundaryModel_optimalValue :
    viabilityBoundaryModel.optimalValue = fun _ : Bool => (2 : ℝ) := by
  have hfixed :
      viabilityBoundaryModel.bellman (fun _ : Bool => (2 : ℝ)) =
        (fun _ : Bool => (2 : ℝ)) := by
    funext x
    cases x <;>
      norm_num [Model.bellman, Model.qValue, Model.expect,
        viabilityBoundaryModel, Finset.sup'_eq_sup]
  exact
    (UEOT.V3.Compression.ContractiveFixedPoint.bellman_fixedPoint_unique_via_mcf
      viabilityBoundaryModel hfixed).symm

private theorem trueAction_isBellmanGOD_at_false :
    true ∈ BellmanGODCorrespondence viabilityBoundaryModel false := by
  rw [mem_bellmanGODCorrespondence_iff, viabilityBoundaryModel_optimalValue]
  norm_num [Model.qValue, Model.expect, viabilityBoundaryModel]

/-- Concrete P2.7 boundary: a Bellman-optimal local action can leave a declared
viability/persistence set with probability one. Hence "optimal" cannot be
silently upgraded to "self-preserving". -/
theorem bellmanGOD_does_not_imply_viability_preservation :
    true ∈ BellmanGODCorrespondence viabilityBoundaryModel false ∧
      ¬ StaysIn
        (viabilityBoundaryDynamics false true)
        ({false} : Set Bool) := by
  refine ⟨trueAction_isBellmanGOD_at_false, ?_⟩
  simp [StaysIn, viabilityBoundaryDynamics]

/-! ## Explicit same-Objecthood viability gate -/

universe uV uChild uH uProbe uR uY uE uZ uX uA uC uS uF

noncomputable section

variable {V : Type uV} {Child : Type uChild}
variable {H : Type uH} {Probe : Type uProbe}
variable {Rout : Type uR} {Y : Type uY} [MeasurableSpace Y]
variable {E : Type uE} {Z : Type uZ} [MeasurableSpace Z]
variable {X : Type uX} {A : Type uA}
variable [Fintype X] [Nonempty X] [Fintype A] [Nonempty A]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace (ConstitutiveState X A)]
variable [MeasurableSingletonClass (ConstitutiveState X A)]
variable {Csem : Type uC}
variable {Ssem : Type uS} [Fintype Ssem] [Nonempty Ssem]
variable {Future : Type uF}
noncomputable local instance sameObjectViabilitySemanticDecidableEq :
    DecidableEq Ssem :=
  Classical.decEq Ssem

namespace ObjecthoodTeleologicalControlSpec

variable [Fintype Child]
variable
    {readout : Finset V → H → Rout}
    {p : H → Probe → Measure Y}
    {regions : Child → Finset V}
    {response : Finset Child → E → Measure Z}
    {hprob : ∀ S e, IsProbabilityMeasure (response S e)}
    {probes : Finset E}
    {dynamics : FormedCandidate readout p regions → X → A → PMF X}
    {persistenceDomain : FormedCandidate readout p regions → Set X}
    {pi : FormedCandidate readout p regions → Csem}
    {semanticKernel : FormedCandidate readout p regions → Matrix Ssem Ssem ℝ}
    {hSemanticKernel : ∀ q, semanticKernel q ∈ Matrix.rowStochastic ℝ Ssem}
    (C : SemanticallyStableSelfRepairingOperationalParent
      readout p regions response hprob probes dynamics persistenceDomain
      pi semanticKernel hSemanticKernel)

/-- Explicit P2.7 compatibility certificate. The Bellman-greedy action of the
same-object induced control model must preserve the exact persistence kernel
already certified by Objecthood.

This is an additional condition, not a consequence of Bellman optimality. -/
def GreedyPreservesObjectPersistence
    (R : ObjecthoodTeleologicalControlSpec C Future) : Prop :=
  ∀ x ∈ C.repairing.operational.persistence.K,
    StaysIn
      (dynamics C.repairing.operational.parent x
        (((R.toParentRealization C).toControlModel dynamics).greedyAction x))
      C.repairing.operational.persistence.K

/-- Under the explicit P2.7 gate, the same selected parent is closed under its
Bellman-greedy physical dynamics throughout the Objecthood persistence kernel. -/
theorem greedyPhysicalDynamics_staysIn_persistence
    (R : ObjecthoodTeleologicalControlSpec C Future)
    (hviable : R.GreedyPreservesObjectPersistence C)
    {x : X} (hx : x ∈ C.repairing.operational.persistence.K) :
    StaysIn
      (dynamics C.repairing.operational.parent x
        (((R.toParentRealization C).toControlModel dynamics).greedyAction x))
      C.repairing.operational.persistence.K :=
  hviable x hx

end ObjecthoodTeleologicalControlSpec

end

end UEOT.V3.Compression.TheoryCompletion
