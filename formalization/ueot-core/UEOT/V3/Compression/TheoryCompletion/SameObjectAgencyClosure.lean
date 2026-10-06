import UEOT.V3.Compression.TheoryCompletion.BellmanTeleologicalFaithfulness
import UEOT.V3.Compression.TheoryCompletion.SameObjectRestoration

/-!
# P2.9 — layered same-object Agency / GOD / GOA closure

The terminal surface deliberately separates unconditional consequences from
certificate-gated upgrades.

Unconditional:
* the control parent is definitionally the canonical Objecthood selected parent;
* the induced transition is that parent's physical dynamics;
* the induced reward is the explicitly P1-contract-valid objective;
* Bellman GOD is nonempty and set-valued;
* the greedy closed loop has at least one invariant-law GOA.

Conditional:
* policy-level teleological maximality requires BellmanTeleologicalFaithfulness;
* viability requires GreedyPreservesObjectPersistence;
* GOA uniqueness/geometric mixing requires an explicit Dobrushin margin;
* RLSR restoration keeps its own trusted-substrate/program hypotheses and is
  exposed by SameObjectRestoration rather than hidden in this base theorem.
-/

namespace UEOT.V3.Compression.TheoryCompletion

open Set MeasureTheory ProbabilityTheory
open UEOT.V3
open UEOT.V3.ViabilityKernel
open UEOT.V3.FiniteDobrushin
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.AgencyGodGoaAssembly
open UEOT.V3.Compression.CrossTrack
open UEOT.V3.Compression.Objecthood

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
noncomputable local instance sameObjectAgencyClosureSemanticDecidableEq :
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

/-- P2.9 base closure. Every conjunct is unconditional at the P2 interface.
The theorem intentionally stops before uniqueness, mixing, viability, or
policy-level purpose faithfulness. -/
theorem sameObject_agency_god_goa_closure
    (R : ObjecthoodTeleologicalControlSpec C Future) :
    (R.toParentRealization C).parent =
        C.repairing.operational.parent ∧
    SemanticFiberIdentity
      pi (R.toParentRealization C).parent C.semantic.child ∧
    (∀ x a y,
      ((R.toParentRealization C).toControlModel dynamics).transition x a y =
        ((dynamics C.repairing.operational.parent x a) y).toReal) ∧
    (∀ x a,
      ((R.toParentRealization C).toControlModel dynamics).reward x a =
        R.objective (R.actionFuture x a)) ∧
    (∀ x,
      (BellmanGODCorrespondence
        ((R.toParentRealization C).toControlModel dynamics) x).Nonempty) ∧
    (R.greedyGOASet C).Nonempty := by
  refine ⟨rfl, R.selected_parent_semantic_identity C, ?_, ?_, ?_, ?_⟩
  · intro x a y
    exact R.toControlModel_transition_selectedParent C x a y
  · intro x a
    exact R.toControlModel_reward_selectedParent C x a
  · exact
      ParentTeleologicalControlRealization.sameParent_bellmanGOD_nonempty
        dynamics (R.toParentRealization C)
  · exact R.greedyGOASet_nonempty C

/-- Policy-level purpose upgrade. This is deliberately parameterized by the
extra Bellman-faithfulness certificate proved necessary by P2.4b. -/
theorem sameObject_greedyPolicy_contract_maximal
    (R : ObjecthoodTeleologicalControlSpec C Future)
    (F :
      ParentTeleologicalControlRealization.BellmanTeleologicalFaithfulness
        dynamics (R.toParentRealization C))
    (x : X) (π : StationaryPolicy (fun _ : X => A)) :
    R.contract.prefers
      (F.policyFuture x π)
      (F.policyFuture x
        (StationaryPolicy.ofSelector
          ((R.toParentRealization C).toControlModel dynamics).greedyAction)) := by
  simpa [toParentRealization] using
    ParentTeleologicalControlRealization.greedyPolicy_contract_maximal
      dynamics (R.toParentRealization C) F x π

/-- Viability upgrade. The no-go in SameObjectViability shows why this extra
gate cannot be dropped. -/
theorem sameObject_greedy_preserves_persistence
    (R : ObjecthoodTeleologicalControlSpec C Future)
    (hviable : R.GreedyPreservesObjectPersistence C)
    {x : X} (hx : x ∈ C.repairing.operational.persistence.K) :
    StaysIn
      (dynamics C.repairing.operational.parent x
        (((R.toParentRealization C).toControlModel dynamics).greedyAction x))
      C.repairing.operational.persistence.K :=
  R.greedyPhysicalDynamics_staysIn_persistence C hviable hx

/-- Stability upgrade. Existence is unconditional; uniqueness and geometric
mixing are available exactly when the explicit Dobrushin certificate holds. -/
theorem sameObject_greedyGOA_stable_of_dobrushin
    (R : ObjecthoodTeleologicalControlSpec C Future)
    (halpha :
      dobrushinAlpha
        (greedyClosedLoopMatrix
          ((R.toParentRealization C).toControlModel dynamics))
        (greedyClosedLoopMatrix_rowStochastic
          ((R.toParentRealization C).toControlModel dynamics)) < 1) :
    ∃ mustar : stdSimplex ℝ X,
      mustar ∈ R.greedyGOASet C ∧
      (∀ mu : stdSimplex ℝ X,
        mu ∈ R.greedyGOASet C → mu = mustar) ∧
      ∀ (mu : stdSimplex ℝ X) (n : ℕ),
        lawTV
            (((step
              (greedyClosedLoopMatrix
                ((R.toParentRealization C).toControlModel dynamics))
              (greedyClosedLoopMatrix_rowStochastic
                ((R.toParentRealization C).toControlModel dynamics)))^[n]) mu)
            mustar ≤
          dobrushinAlpha
              (greedyClosedLoopMatrix
                ((R.toParentRealization C).toControlModel dynamics))
              (greedyClosedLoopMatrix_rowStochastic
                ((R.toParentRealization C).toControlModel dynamics)) ^ n *
            lawTV mu mustar :=
  R.existsUnique_stable_greedyGOA C halpha

end ObjecthoodTeleologicalControlSpec

end

end UEOT.V3.Compression.TheoryCompletion
