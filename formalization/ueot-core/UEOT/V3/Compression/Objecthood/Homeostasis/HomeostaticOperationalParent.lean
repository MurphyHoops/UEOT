import UEOT.V3.Compression.Objecthood.Homeostasis.SemanticHomeostasis
import UEOT.V3.Compression.Objecthood.FormedParentSelfRepairSynthesis

namespace UEOT.V3.Compression.Objecthood

open Set MeasureTheory ProbabilityTheory
open UEOT.V3.ViabilityKernel
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.CrossTrack
open scoped ENNReal ProbabilityTheory

universe uV uChild uH uProbe uR uY uE uZ uX uA uC uS

noncomputable section

variable {V : Type uV} {Child : Type uChild}
variable {H : Type uH} {Probe : Type uProbe}
variable {Rout : Type uR} {Y : Type uY} [MeasurableSpace Y]
variable {E : Type uE} {Z : Type uZ} [MeasurableSpace Z]
variable {X : Type uX} {A : Type uA}
variable [Fintype X] [Fintype A] [Nonempty A]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace A] [MeasurableSingletonClass A]
variable [MeasurableSpace (ConstitutiveState X A)]
variable [MeasurableSingletonClass (ConstitutiveState X A)]

variable {Csem : Type uC}
variable {Ssem : Type uS} [Fintype Ssem] [Nonempty Ssem]
noncomputable local instance rh8SemanticDecidableEq : DecidableEq Ssem :=
  Classical.decEq Ssem
noncomputable local instance rh8ConstitutiveDecidableEq :
    DecidableEq (ConstitutiveState X A) :=
  Classical.decEq (ConstitutiveState X A)

/-- RH8 homeostatic operational parent. This is a dependent extension of an
already selected semantically-stable self-repairing parent. RH adds only an
explicit recurrent fault model and its finite burden certificate; the parent,
persistence kernel, repair law, and semantic kernel remain those of base. -/
structure HomeostaticOperationalParent
    [Fintype Child]
    (readout : Finset V → H → Rout)
    (p : H → Probe → Measure Y)
    (regions : Child → Finset V)
    (response : Finset Child → E → Measure Z)
    (hprob : ∀ T e, IsProbabilityMeasure (response T e))
    (probes : Finset E)
    (dynamics : FormedCandidate readout p regions → X → A → PMF X)
    (persistenceDomain : FormedCandidate readout p regions → Set X)
    (pi : FormedCandidate readout p regions → Csem)
    (semanticKernel : FormedCandidate readout p regions → Matrix Ssem Ssem ℝ)
    (hSemanticKernel : ∀ q, semanticKernel q ∈ Matrix.rowStochastic ℝ Ssem) where
  base : SemanticallyStableSelfRepairingOperationalParent
    readout p regions response hprob probes dynamics persistenceDomain
    pi semanticKernel hSemanticKernel
  faultKernel : ConstitutiveState X A → PMF (ConstitutiveState X A)
  faultHazard : NNReal
  faultHazard_le_one : faultHazard ≤ 1
  fault_stays_carrier :
    ∀ ⦃z : ConstitutiveState X A⦄,
      z ∈ gcrHomeostaticCarrier
        (dynamics base.repairing.operational.parent)
        base.repairing.operational.persistence.K →
      StaysIn (faultKernel z)
        (gcrHomeostaticCarrier
          (dynamics base.repairing.operational.parent)
          base.repairing.operational.persistence.K)
  burden : FaultBurdenCertificate
    (objecthoodRecurrentHomeostasisSystem
      (dynamics base.repairing.operational.parent)
      base.repairing.operational.persistence.K
      base.repairing.operational.persistence.source_fixed
      faultKernel faultHazard faultHazard_le_one fault_stays_carrier)

namespace HomeostaticOperationalParent

noncomputable def system
    [Fintype Child]
    {readout : Finset V → H → Rout}
    {p : H → Probe → Measure Y}
    {regions : Child → Finset V}
    {response : Finset Child → E → Measure Z}
    {hprob : ∀ T e, IsProbabilityMeasure (response T e)}
    {probes : Finset E}
    {dynamics : FormedCandidate readout p regions → X → A → PMF X}
    {persistenceDomain : FormedCandidate readout p regions → Set X}
    {pi : FormedCandidate readout p regions → Csem}
    {semanticKernel : FormedCandidate readout p regions → Matrix Ssem Ssem ℝ}
    {hSemanticKernel : ∀ q, semanticKernel q ∈ Matrix.rowStochastic ℝ Ssem}
    (C : HomeostaticOperationalParent
      readout p regions response hprob probes dynamics persistenceDomain
      pi semanticKernel hSemanticKernel) :
    RecurrentHomeostasisSystem (ConstitutiveState X A) :=
  objecthoodRecurrentHomeostasisSystem
    (dynamics C.base.repairing.operational.parent)
    C.base.repairing.operational.persistence.K
    C.base.repairing.operational.persistence.source_fixed
    C.faultKernel C.faultHazard C.faultHazard_le_one C.fault_stays_carrier

theorem selected_parent_in_semantic_fiber
    [Fintype Child]
    {readout : Finset V → H → Rout}
    {p : H → Probe → Measure Y}
    {regions : Child → Finset V}
    {response : Finset Child → E → Measure Z}
    {hprob : ∀ T e, IsProbabilityMeasure (response T e)}
    {probes : Finset E}
    {dynamics : FormedCandidate readout p regions → X → A → PMF X}
    {persistenceDomain : FormedCandidate readout p regions → Set X}
    {pi : FormedCandidate readout p regions → Csem}
    {semanticKernel : FormedCandidate readout p regions → Matrix Ssem Ssem ℝ}
    {hSemanticKernel : ∀ q, semanticKernel q ∈ Matrix.rowStochastic ℝ Ssem}
    (C : HomeostaticOperationalParent
      readout p regions response hprob probes dynamics persistenceDomain
      pi semanticKernel hSemanticKernel) :
    pi C.base.repairing.operational.parent = C.base.semantic.child :=
  C.base.selected_parent_in_fiber

theorem selected_parent_pairwise_semantic_bound
    [Fintype Child]
    {readout : Finset V → H → Rout}
    {p : H → Probe → Measure Y}
    {regions : Child → Finset V}
    {response : Finset Child → E → Measure Z}
    {hprob : ∀ T e, IsProbabilityMeasure (response T e)}
    {probes : Finset E}
    {dynamics : FormedCandidate readout p regions → X → A → PMF X}
    {persistenceDomain : FormedCandidate readout p regions → Set X}
    {pi : FormedCandidate readout p regions → Csem}
    {semanticKernel : FormedCandidate readout p regions → Matrix Ssem Ssem ℝ}
    {hSemanticKernel : ∀ q, semanticKernel q ∈ Matrix.rowStochastic ℝ Ssem}
    (C : HomeostaticOperationalParent
      readout p regions response hprob probes dynamics persistenceDomain
      pi semanticKernel hSemanticKernel)
    (hcard : 1 < Fintype.card Ssem)
    {q : FormedCandidate readout p regions}
    (hq : pi q = C.base.semantic.child) :
    lawTV
      (C.base.semantic.invariantLaw C.base.repairing.operational.parent)
      (C.base.semantic.invariantLaw q) ≤
      C.base.semantic.epsilon / C.base.semantic.kappaMin :=
  C.base.selected_parent_pairwise_semantic_bound hcard hq

end HomeostaticOperationalParent

theorem nonempty_homeostaticOperationalParent
    [Fintype Child]
    {readout : Finset V → H → Rout}
    {p : H → Probe → Measure Y}
    {regions : Child → Finset V}
    {response : Finset Child → E → Measure Z}
    {hprob : ∀ T e, IsProbabilityMeasure (response T e)}
    {probes : Finset E}
    {dynamics : FormedCandidate readout p regions → X → A → PMF X}
    {persistenceDomain : FormedCandidate readout p regions → Set X}
    {pi : FormedCandidate readout p regions → Csem}
    {semanticKernel : FormedCandidate readout p regions → Matrix Ssem Ssem ℝ}
    {hSemanticKernel : ∀ q, semanticKernel q ∈ Matrix.rowStochastic ℝ Ssem}
    (base : SemanticallyStableSelfRepairingOperationalParent
      readout p regions response hprob probes dynamics persistenceDomain
      pi semanticKernel hSemanticKernel)
    (F : ConstitutiveState X A → PMF (ConstitutiveState X A))
    (epsilon : NNReal) (hepsilon : epsilon ≤ 1)
    (hF : ∀ ⦃z : ConstitutiveState X A⦄,
      z ∈ gcrHomeostaticCarrier
        (dynamics base.repairing.operational.parent)
        base.repairing.operational.persistence.K →
      StaysIn (F z)
        (gcrHomeostaticCarrier
          (dynamics base.repairing.operational.parent)
          base.repairing.operational.persistence.K)) :
    Nonempty (HomeostaticOperationalParent
      readout p regions response hprob probes dynamics persistenceDomain
      pi semanticKernel hSemanticKernel) := by
  obtain ⟨Cburden⟩ :=
    nonempty_objecthoodFaultBurdenCertificate
      (dynamics base.repairing.operational.parent)
      base.repairing.operational.persistence.K
      base.repairing.operational.persistence.source_fixed
      F epsilon hepsilon hF
  exact ⟨{
    base := base
    faultKernel := F
    faultHazard := epsilon
    faultHazard_le_one := hepsilon
    fault_stays_carrier := hF
    burden := Cburden
  }⟩


namespace HomeostaticOperationalParent

/-- **RH8 end-to-end synthesis.**  The same selected operational parent that
already carries persistence, autonomous repair, and the Track-X semantic
certificate also carries the recurrent-fault RH system.  Under the explicit RH7
statewise semantic coupling and a nondegenerate fault hazard, it admits an
invariant Cesaro cluster law with the certified semantic-defect bound. -/
theorem exists_invariant_semanticHomeostasis
    [Fintype Child]
    {readout : Finset V → H → Rout}
    {p : H → Probe → Measure Y}
    {regions : Child → Finset V}
    {response : Finset Child → E → Measure Z}
    {hprob : ∀ T e, IsProbabilityMeasure (response T e)}
    {probes : Finset E}
    {dynamics : FormedCandidate readout p regions → X → A → PMF X}
    {persistenceDomain : FormedCandidate readout p regions → Set X}
    {pi : FormedCandidate readout p regions → Csem}
    {semanticKernel : FormedCandidate readout p regions → Matrix Ssem Ssem ℝ}
    {hSemanticKernel : ∀ q, semanticKernel q ∈ Matrix.rowStochastic ℝ Ssem}
    (C : HomeostaticOperationalParent
      readout p regions response hprob probes dynamics persistenceDomain
      pi semanticKernel hSemanticKernel)
    (mu0 : PMF (ConstitutiveState X A))
    (hmu0 : StaysIn mu0
      (gcrHomeostaticCarrier
        (dynamics C.base.repairing.operational.parent)
        C.base.repairing.operational.persistence.K))
    (hhazard : C.faultHazard < 1)
    (defect : ConstitutiveState X A → ℝ) (good extra : ℝ)
    (hextra : 0 ≤ extra)
    (hpoint : ∀ z,
      defect z ≤ good + extra *
        damageIndicatorReal
          (legitimateConstitutiveDomain
            (dynamics C.base.repairing.operational.parent)
            C.base.repairing.operational.persistence.K) z) :
    let S := C.system
    let rho :=
      ((S.faultHazard : ENNReal) * C.burden.burden).toReal /
        (((1 - S.faultHazard : NNReal) : ENNReal) * S.repairDrift).toReal
    ∃ nu : stdSimplex ℝ (ConstitutiveState X A), ∃ phi : ℕ → ℕ,
      StrictMono phi ∧
      Filter.Tendsto
        (UEOT.V3.FiniteCesaroInvariant.cesaroRow
          (pmfKernelMatrix S.mixedKernel)
          (pmfKernelMatrix_rowStochastic S.mixedKernel)
          (pmfSimplex mu0) ∘ phi)
        Filter.atTop (nhds nu) ∧
      Matrix.vecMul nu.1 (pmfKernelMatrix S.mixedKernel) = nu.1 ∧
      semanticExpectation nu defect ≤ good + extra * rho := by
  let P := dynamics C.base.repairing.operational.parent
  let K := C.base.repairing.operational.persistence.K
  let hfix := C.base.repairing.operational.persistence.source_fixed
  let S := C.system
  dsimp
  apply S.exists_invariant_semanticHomeostasis
    (C := C.burden) (mu0 := mu0)
    (defect := defect) (good := good) (extra := extra)
  · simpa [S, HomeostaticOperationalParent.system,
      objecthoodRecurrentHomeostasisSystem, P, K] using hmu0
  · intro z hz
    have hpen :
        S.damagePenalty z = autonomousRepairDamagePenalty P K z := by
      classical
      simp [S, HomeostaticOperationalParent.system,
        RecurrentHomeostasisSystem.damagePenalty,
        objecthoodRecurrentHomeostasisSystem, P, K,
        autonomousRepairDamagePenalty]
    rw [hpen]
    change
      homeostaticENNExpectation
          (autonomousRepairLift P K hfix
            (maximalStationaryRepairCertificate P K) z ())
          (autonomousRepairPotential P K
            (maximalStationaryRepairCertificate P K)) +
        autonomousRepairDamagePenalty P K z ≤
      autonomousRepairPotential P K
        (maximalStationaryRepairCertificate P K) z
    simpa [homeostaticENNExpectation] using
      autonomousRepair_global_drift_budget P K hfix z
  · intro z hz
    exact autonomousRepairPotential_ne_top_on_gcrHomeostaticCarrier
      P K hfix (by
        simpa [S, HomeostaticOperationalParent.system,
          objecthoodRecurrentHomeostasisSystem, P, K] using hz)
  · simpa [S, HomeostaticOperationalParent.system,
      objecthoodRecurrentHomeostasisSystem] using hhazard
  · exact hextra
  · intro z
    simpa [S, HomeostaticOperationalParent.system,
      objecthoodRecurrentHomeostasisSystem, P, K] using hpoint z

end HomeostaticOperationalParent

end
end UEOT.V3.Compression.Objecthood
