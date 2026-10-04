import UEOT.V3.Compression.Objecthood.GeneralCausalRepairSynthesis
import UEOT.V3.Compression.Objecthood.StochasticRepairSynthesis

/-!
# Post-GCR tightening — general-causal Objecthood terminal closure

GCR6 proved equivalence between arbitrary randomized complete-history causal
almost-sure repairability and deterministic-stationary finite-expected repairability
for the finite controlled-PMF semantics. Existing AR7/O7 terminal APIs still
exposed the narrower deterministic-stationary premise. This module removes that
presentation gap without introducing any new repair dynamics.
-/

namespace UEOT.V3.Compression.Objecthood

open Set MeasureTheory ProbabilityTheory
open UEOT.V3.ViabilityTrajectory
open UEOT.V3.OmegaMinimalFailure
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.CrossTrack
open scoped ENNReal ProbabilityTheory

universe uV uChild uH uProbe uR uY uE uZout uX uA uC uS

noncomputable section

/-- The strongest existing same-parent semantic + eventual-permanent repair
endpoint accepts the full general-causal repairability premise. -/
theorem generalCausal_semantic_bound_and_eventually_always_same_parent_repair
    {V : Type uV} {Child : Type uChild}
    {H : Type uH} {Probe : Type uProbe}
    {Rout : Type uR} {Y : Type uY} [MeasurableSpace Y]
    {E : Type uE} {Zout : Type uZout} [MeasurableSpace Zout]
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    [Fintype Child]
    {readout : Finset V → H → Rout}
    {p : H → Probe → Measure Y}
    {regions : Child → Finset V}
    {response : Finset Child → E → Measure Zout}
    {hprob : ∀ T e, IsProbabilityMeasure (response T e)}
    {probes : Finset E}
    {dynamics : FormedCandidate readout p regions → X → A → PMF X}
    {persistenceDomain : FormedCandidate readout p regions → Set X}
    (C : OperationalFormedPersistentParent
      readout p regions response hprob probes dynamics persistenceDomain)
    {Csem : Type uC}
    {Ssem : Type uS} [Fintype Ssem] [Nonempty Ssem] [DecidableEq Ssem]
    {pi : FormedCandidate readout p regions → Csem}
    {semanticKernel : FormedCandidate readout p regions → Matrix Ssem Ssem ℝ}
    {hSemanticKernel : ∀ q, semanticKernel q ∈ Matrix.rowStochastic ℝ Ssem}
    (semantic : RobustParentSemanticCertificate pi semanticKernel hSemanticKernel)
    (hselected : pi C.parent = semantic.child)
    (hcard : 1 < Fintype.card Ssem)
    {q : FormedCandidate readout p regions}
    (hq : pi q = semantic.child)
    {z : ConstitutiveState X A}
    (hz : GeneralCausalAlmostSureRepairable
      (dynamics C.parent) C.persistence.K z.1) :
    lawTV (semantic.invariantLaw C.parent) (semantic.invariantLaw q) ≤
        semantic.epsilon / semantic.kappaMin ∧
      (∀ᵐ omega ∂stationaryTrajMeasure
          (autonomousRepairLift
            (dynamics C.parent) C.persistence.K C.persistence.source_fixed
            (maximalStationaryRepairCertificate
              (dynamics C.parent) C.persistence.K))
          noExternalControl (PMF.pure z),
        ∃ N : ℕ, ∀ m ≥ N,
          omega m ∈ legitimateConstitutiveDomain
            (dynamics C.parent) C.persistence.K) := by
  have hstationary : DeterministicStationaryFiniteExpectedRepairable
      (dynamics C.parent) C.persistence.K z.1 :=
    (generalCausalAlmostSureRepairable_iff_deterministicStationary
      (dynamics C.parent) C.persistence.K z.1).1 hz
  exact canonical_semantic_bound_and_eventually_always_same_parent_repair
    C semantic hselected hcard hq hstationary

/-- End-to-end Objecthood terminal closure: a failing deletion that is repairable
by any admissible randomized complete-history causal policy has a minimal
failure witness, retains the same-parent Track-X semantic guarantee, and is
almost surely eventually permanently restored by the unchanged canonical
stationary repair architecture. -/
theorem generalCausal_failingDeletion_semantic_and_eventuallyAlways_sameParent
    {V : Type uV} {Child : Type uChild}
    {H : Type uH} {Probe : Type uProbe}
    {Rout : Type uR} {Y : Type uY} [MeasurableSpace Y]
    {E : Type uE} {Zout : Type uZout} [MeasurableSpace Zout]
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    [Fintype Child]
    {readout : Finset V → H → Rout}
    {p : H → Probe → Measure Y}
    {regions : Child → Finset V}
    {response : Finset Child → E → Measure Zout}
    {hprob : ∀ T e, IsProbabilityMeasure (response T e)}
    {probes : Finset E}
    {dynamics : FormedCandidate readout p regions → X → A → PMF X}
    {persistenceDomain : FormedCandidate readout p regions → Set X}
    (C : OperationalFormedPersistentParent
      readout p regions response hprob probes dynamics persistenceDomain)
    {Csem : Type uC}
    {Ssem : Type uS} [Fintype Ssem] [Nonempty Ssem] [DecidableEq Ssem]
    {pi : FormedCandidate readout p regions → Csem}
    {semanticKernel : FormedCandidate readout p regions → Matrix Ssem Ssem ℝ}
    {hSemanticKernel : ∀ q, semanticKernel q ∈ Matrix.rowStochastic ℝ Ssem}
    (semantic : RobustParentSemanticCertificate pi semanticKernel hSemanticKernel)
    (hselected : pi C.parent = semantic.child)
    (hcard : 1 < Fintype.card Ssem)
    {q : FormedCandidate readout p regions}
    (hq : pi q = semantic.child)
    {Del : Type*}
    (Failure : Finset Del → Prop)
    (hmono : FailureMonotone Failure)
    (damage : Finset Del → ConstitutiveState X A)
    (D : Finset Del)
    (hfail : Failure D)
    (hrepair : GeneralCausalAlmostSureRepairable
      (dynamics C.parent) C.persistence.K (damage D).1) :
    ∃ Dmin, Dmin ∈ minimalFailures Failure ∧ Dmin ⊆ D ∧
      lawTV (semantic.invariantLaw C.parent) (semantic.invariantLaw q) ≤
        semantic.epsilon / semantic.kappaMin ∧
      (∀ᵐ omega ∂stationaryTrajMeasure
          (autonomousRepairLift
            (dynamics C.parent) C.persistence.K C.persistence.source_fixed
            (maximalStationaryRepairCertificate
              (dynamics C.parent) C.persistence.K))
          noExternalControl (PMF.pure (damage D)),
        ∃ N : ℕ, ∀ m ≥ N,
          omega m ∈ legitimateConstitutiveDomain
            (dynamics C.parent) C.persistence.K) := by
  have hstationary : DeterministicStationaryFiniteExpectedRepairable
      (dynamics C.parent) C.persistence.K (damage D).1 :=
    (generalCausalAlmostSureRepairable_iff_deterministicStationary
      (dynamics C.parent) C.persistence.K (damage D).1).1 hrepair
  obtain ⟨Dmin, hmin, hsub, hevent⟩ :=
    stationaryRepairable_failingDeletion_eventually_always_same_parent
      C Failure hmono damage D hfail hstationary
  refine ⟨Dmin, hmin, hsub, ?_, hevent⟩
  exact semantic.pairwise_bound
    pi semanticKernel hSemanticKernel hcard hselected hq

end
end UEOT.V3.Compression.Objecthood
