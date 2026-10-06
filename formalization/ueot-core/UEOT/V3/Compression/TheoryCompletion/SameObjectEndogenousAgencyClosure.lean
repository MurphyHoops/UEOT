import UEOT.V3.Compression.TheoryCompletion.SameObjectAgencyClosure
import UEOT.V3.Compression.TheoryCompletion.SameObjectViableGOA
import UEOT.V3.Compression.TheoryCompletion.CausalBellmanTeleologicalFaithfulness

/-!
# P2 audit hardening — endogenous same-object Agency / GOD / GOA closure

The existing sameObject_agency_god_goa_closure is the unconditional base
surface. This module adds the conditional endpoint that the P2 audit actually
needs.

Under exactly the two semantic gates independently shown necessary in P2:

* Bellman teleological faithfulness, and
* greedy preservation of the canonical Objecthood persistence kernel,

the same selected object simultaneously has:

1. exact parent identity;
2. an own-history effective-state realization of that parent's dynamics;
3. contract-maximal stationary greedy policy semantics;
4. Bellman-GOD membership of the greedy action;
5. internalization of the greedy controller in the same Objecthood legitimate
   constitutive class; and
6. an invariant greedy GOA supported inside the exact persistence kernel.

No Dobrushin mixing, uniqueness, RLSR recovery, or causal-policy faithfulness is
silently assumed. Those remain stronger explicit upgrades.
-/

namespace UEOT.V3.Compression.TheoryCompletion

open Set MeasureTheory ProbabilityTheory
open UEOT.V3
open UEOT.V3.ViabilityKernel
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.AgencyGodGoaAssembly
open UEOT.V3.Compression.CrossTrack
open UEOT.V3.Compression.Objecthood

universe uV uChild uH uProbe uR uY uE uZ uX uA uC uS uF uHpi

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
noncomputable local instance sameObjectEndogenousAgencySemanticDecidableEq :
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

/-- The audited P2 terminal theorem.

The conclusion deliberately bundles consequences rather than packing desired
claims into a new certificate structure. The only extra hypotheses are the
independently motivated policy-order faithfulness and viability gates. -/
theorem endogenous_sameObject_agency_god_goa
    (R : ObjecthoodTeleologicalControlSpec C Future)
    (F :
      ParentTeleologicalControlRealization.BellmanTeleologicalFaithfulness
        dynamics (R.toParentRealization C))
    (hviable : R.GreedyPreservesObjectPersistence C) :
    (R.toParentRealization C).parent =
        C.repairing.operational.parent ∧
    SemanticFiberIdentity
      pi (R.toParentRealization C).parent C.semantic.child ∧
    Function.Surjective
      (OwnHistory.current :
        OwnHistory (R.toParentRealization C).parent X A → X) ∧
    UEOT.V3.Compression.RecursiveSufficientState.InputFiberCompatible
      (OwnHistory.current :
        OwnHistory (R.toParentRealization C).parent X A → X)
      (parentHistoryTransitionResponse
        dynamics (R.toParentRealization C).parent) ∧
    (∃! U : X → A → PMF X,
      ∀ h a,
        U h.current a =
          parentHistoryTransitionResponse
            dynamics (R.toParentRealization C).parent h a) ∧
    (∀ x (piPolicy : StationaryPolicy (fun _ : X => A)),
      R.contract.prefers
        (F.policyFuture x piPolicy)
        (F.policyFuture x
          (StationaryPolicy.ofSelector
            ((R.toParentRealization C).toControlModel dynamics).greedyAction))) ∧
    (∀ x,
      ((R.toParentRealization C).toControlModel dynamics).greedyAction x ∈
        BellmanGODCorrespondence
          ((R.toParentRealization C).toControlModel dynamics) x) ∧
    (∀ x ∈ C.repairing.operational.persistence.K,
      (x, ((R.toParentRealization C).toControlModel dynamics).greedyAction) ∈
        legitimateConstitutiveDomain
          (dynamics C.repairing.operational.parent)
          C.repairing.operational.persistence.K) ∧
    (R.persistenceSupportedGreedyGOASet C).Nonempty := by
  refine ⟨rfl, R.selected_parent_semantic_identity C,
    ownHistoryCurrent_surjective (R.toParentRealization C).parent,
    parentHistoryTransitionResponse_compatible
      dynamics (R.toParentRealization C).parent, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      existsUnique_parentDynamics_effectiveResponse
        dynamics (R.toParentRealization C).parent
  · intro x piPolicy
    exact R.sameObject_greedyPolicy_contract_maximal C F x piPolicy
  · intro x
    exact
      greedyAction_mem_bellmanGODCorrespondence
        ((R.toParentRealization C).toControlModel dynamics) x
  · intro x hx
    exact R.greedyConstitutiveState_mem_legitimate C hviable hx
  · exact R.persistenceSupportedGreedyGOASet_nonempty C hviable

/-- Optional causal-policy upgrade of the terminal surface. Pairwise causal
faithfulness is kept separate from the stationary terminal theorem because it
is strictly stronger semantic information, not a consequence of P2.4b. -/
theorem sameObject_greedyCausalPolicy_contract_maximal
    (R : ObjecthoodTeleologicalControlSpec C Future)
    (piPolicy :
      CausalPolicy.{uX, uA, uHpi} X (fun _ : X => A))
    (piFuture :
      ∀ {t : ℕ}, piPolicy.Memory t →
        AdmissibleFuture R.contract.admissible)
    (greedyFuture :
      X → AdmissibleFuture R.contract.admissible)
    (F :
      ParentTeleologicalControlRealization.CausalPolicyPairTeleologicalFaithfulness
        dynamics (R.toParentRealization C) piPolicy
          (selectorPolicy
            ((R.toParentRealization C).toControlModel dynamics).greedyAction)
          piFuture (fun x => greedyFuture x))
    {t : ℕ} (h : piPolicy.Memory t) :
    R.contract.prefers
      (piFuture h)
      (greedyFuture (piPolicy.current h)) := by
  exact
    ParentTeleologicalControlRealization.greedyCausalPolicy_contract_maximal
      dynamics (R.toParentRealization C) piPolicy piFuture greedyFuture F h

end ObjecthoodTeleologicalControlSpec

end

end UEOT.V3.Compression.TheoryCompletion
