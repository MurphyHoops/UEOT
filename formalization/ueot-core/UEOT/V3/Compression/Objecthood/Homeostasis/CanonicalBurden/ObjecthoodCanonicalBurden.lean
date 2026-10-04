import UEOT.V3.Compression.Objecthood.Homeostasis.CanonicalBurden.DownstreamTightening
import UEOT.V3.Compression.Objecthood.Homeostasis.HomeostaticOperationalParent

namespace UEOT.V3.Compression.Objecthood

open Set MeasureTheory ProbabilityTheory
open UEOT.V3.ViabilityKernel
open UEOT.V3.Compression.CrossTrack
open UEOT.V3.FiniteDobrushin
open scoped ENNReal BigOperators ProbabilityTheory

universe uX uA

noncomputable section

/-! ## QT3 Objecthood and same-parent canonical specializations -/

section Objecthood

variable {X : Type uX} {A : Type uA}
variable [Fintype X] [Fintype A] [Nonempty A]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace A] [MeasurableSingletonClass A]
variable [MeasurableSpace (ConstitutiveState X A)]
variable [MeasurableSingletonClass (ConstitutiveState X A)]
noncomputable local instance canonicalObjecthoodConstitutiveDecidableEq :
    DecidableEq (ConstitutiveState X A) :=
  Classical.decEq (ConstitutiveState X A)

noncomputable def canonicalObjecthoodFaultBurdenCertificate
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (F : ConstitutiveState X A → PMF (ConstitutiveState X A))
    (epsilon : NNReal) (hepsilon : epsilon ≤ 1)
    (hF : ∀ ⦃z : ConstitutiveState X A⦄,
      z ∈ gcrHomeostaticCarrier P K →
        StaysIn (F z) (gcrHomeostaticCarrier P K)) :
    FaultBurdenCertificate
      (objecthoodRecurrentHomeostasisSystem
        P K hfix F epsilon hepsilon hF) := by
  let S := objecthoodRecurrentHomeostasisSystem
    P K hfix F epsilon hepsilon hF
  apply canonicalFaultBurdenCertificate S
  intro z hz
  exact autonomousRepairPotential_ne_top_on_gcrHomeostaticCarrier
    P K hfix (by
      simpa [S, objecthoodRecurrentHomeostasisSystem] using hz)

theorem objecthood_eventually_realDamageAverage_le_canonical
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (F : ConstitutiveState X A → PMF (ConstitutiveState X A))
    (epsilon : NNReal) (hepsilon : epsilon ≤ 1) (hepsilon_lt : epsilon < 1)
    (hF : ∀ ⦃z : ConstitutiveState X A⦄,
      z ∈ gcrHomeostaticCarrier P K →
        StaysIn (F z) (gcrHomeostaticCarrier P K))
    (mu0 : PMF (ConstitutiveState X A))
    (hmu0 : StaysIn mu0 (gcrHomeostaticCarrier P K)) :
    let S := objecthoodRecurrentHomeostasisSystem
      P K hfix F epsilon hepsilon hF
    let Cstar := canonicalObjecthoodFaultBurdenCertificate
      P K hfix F epsilon hepsilon hF
    let D : ℕ → ENNReal := fun n =>
      (homeostaticMarginal S.mixedKernel mu0 n).toMeasure S.legitimateᶜ
    let kappa : ENNReal := ((1 - epsilon : NNReal) : ENNReal) * S.repairDrift
    let lambda : ENNReal := (epsilon : ENNReal) * Cstar.burden
    ∀ eta > 0, ∀ᶠ n in Filter.atTop,
      realDamageAverage D n ≤ lambda.toReal / kappa.toReal + eta := by
  dsimp
  exact objecthood_eventually_realDamageAverage_le
    P K hfix F epsilon hepsilon hepsilon_lt hF
    (canonicalObjecthoodFaultBurdenCertificate
      P K hfix F epsilon hepsilon hF)
    mu0 hmu0

theorem objecthood_exists_invariant_cesaro_canonical
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (F : ConstitutiveState X A → PMF (ConstitutiveState X A))
    (epsilon : NNReal) (hepsilon : epsilon ≤ 1) (hepsilon_lt : epsilon < 1)
    (hF : ∀ ⦃z : ConstitutiveState X A⦄,
      z ∈ gcrHomeostaticCarrier P K →
        StaysIn (F z) (gcrHomeostaticCarrier P K))
    (mu0 : PMF (ConstitutiveState X A))
    (hmu0 : StaysIn mu0 (gcrHomeostaticCarrier P K)) :
    let S := objecthoodRecurrentHomeostasisSystem
      P K hfix F epsilon hepsilon hF
    let Cstar := canonicalObjecthoodFaultBurdenCertificate
      P K hfix F epsilon hepsilon hF
    ∃ nu : stdSimplex ℝ (ConstitutiveState X A), ∃ phi : ℕ → ℕ,
      StrictMono phi ∧
      Filter.Tendsto
        (UEOT.V3.FiniteCesaroInvariant.cesaroRow
          (pmfKernelMatrix S.mixedKernel)
          (pmfKernelMatrix_rowStochastic S.mixedKernel)
          (pmfSimplex mu0) ∘ phi)
        Filter.atTop (nhds nu) ∧
      Matrix.vecMul nu.1 (pmfKernelMatrix S.mixedKernel) = nu.1 ∧
      simplexDamagedMass S.legitimate nu ≤
        ((epsilon : ENNReal) * Cstar.burden).toReal /
          (((1 - epsilon : NNReal) : ENNReal) * S.repairDrift).toReal := by
  dsimp
  let S := objecthoodRecurrentHomeostasisSystem
    P K hfix F epsilon hepsilon hF
  let Cstar := canonicalObjecthoodFaultBurdenCertificate
    P K hfix F epsilon hepsilon hF
  obtain ⟨nu, phi, hphi, hlim, hinv, hdamage, hlegit⟩ :=
    S.exists_invariant_cesaro_limit_with_damage_bound
      Cstar mu0 hmu0
      (by
        intro z hz
        have hpen :
            S.damagePenalty z = autonomousRepairDamagePenalty P K z := by
          classical
          simp [S, RecurrentHomeostasisSystem.damagePenalty,
            objecthoodRecurrentHomeostasisSystem,
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
          autonomousRepair_global_drift_budget P K hfix z)
      (by
        intro z hz
        exact autonomousRepairPotential_ne_top_on_gcrHomeostaticCarrier
          P K hfix (by
            simpa [S, objecthoodRecurrentHomeostasisSystem] using hz))
      (by simpa [S, objecthoodRecurrentHomeostasisSystem] using hepsilon_lt)
  exact ⟨nu, phi, hphi, hlim, hinv, by
    simpa [S, Cstar, objecthoodRecurrentHomeostasisSystem] using hdamage⟩

end Objecthood


universe uVQT uChildQT uHQT uProbeQT uRQT uYQT uEQT uZQT uXQT uAQT uCQT uSQT

variable {VQT : Type uVQT} {ChildQT : Type uChildQT}
variable {HQT : Type uHQT} {ProbeQT : Type uProbeQT}
variable {RoutQT : Type uRQT} {YQT : Type uYQT} [MeasurableSpace YQT]
variable {EQT : Type uEQT} {ZoutQT : Type uZQT} [MeasurableSpace ZoutQT]
variable {XQT : Type uXQT} {AQT : Type uAQT}
variable [Fintype XQT] [Fintype AQT] [Nonempty AQT]
variable [MeasurableSpace XQT] [MeasurableSingletonClass XQT]
variable [MeasurableSpace AQT] [MeasurableSingletonClass AQT]
variable [MeasurableSpace (ConstitutiveState XQT AQT)]
variable [MeasurableSingletonClass (ConstitutiveState XQT AQT)]
variable {CsemQT : Type uCQT}
variable {SsemQT : Type uSQT} [Fintype SsemQT] [Nonempty SsemQT]
noncomputable local instance canonicalParentSemanticDecidableEq :
    DecidableEq SsemQT := Classical.decEq SsemQT
noncomputable local instance canonicalParentConstitutiveDecidableEq :
    DecidableEq (ConstitutiveState XQT AQT) :=
  Classical.decEq (ConstitutiveState XQT AQT)

noncomputable def canonicalHomeostaticOperationalParent
    [Fintype ChildQT]
    {readout : Finset VQT → HQT → RoutQT}
    {p : HQT → ProbeQT → Measure YQT}
    {regions : ChildQT → Finset VQT}
    {response : Finset ChildQT → EQT → Measure ZoutQT}
    {hprob : ∀ T e, IsProbabilityMeasure (response T e)}
    {probes : Finset EQT}
    {dynamics : FormedCandidate readout p regions → XQT → AQT → PMF XQT}
    {persistenceDomain : FormedCandidate readout p regions → Set XQT}
    {pi : FormedCandidate readout p regions → CsemQT}
    {semanticKernel : FormedCandidate readout p regions → Matrix SsemQT SsemQT ℝ}
    {hSemanticKernel : ∀ q, semanticKernel q ∈ Matrix.rowStochastic ℝ SsemQT}
    (base : SemanticallyStableSelfRepairingOperationalParent
      readout p regions response hprob probes dynamics persistenceDomain
      pi semanticKernel hSemanticKernel)
    (F : ConstitutiveState XQT AQT → PMF (ConstitutiveState XQT AQT))
    (epsilon : NNReal) (hepsilon : epsilon ≤ 1)
    (hF : ∀ ⦃z : ConstitutiveState XQT AQT⦄,
      z ∈ gcrHomeostaticCarrier
        (dynamics base.repairing.operational.parent)
        base.repairing.operational.persistence.K →
      StaysIn (F z)
        (gcrHomeostaticCarrier
          (dynamics base.repairing.operational.parent)
          base.repairing.operational.persistence.K)) :
    HomeostaticOperationalParent
      readout p regions response hprob probes dynamics persistenceDomain
      pi semanticKernel hSemanticKernel where
  base := base
  faultKernel := F
  faultHazard := epsilon
  faultHazard_le_one := hepsilon
  fault_stays_carrier := hF
  burden := canonicalObjecthoodFaultBurdenCertificate
    (dynamics base.repairing.operational.parent)
    base.repairing.operational.persistence.K
    base.repairing.operational.persistence.source_fixed
    F epsilon hepsilon hF

omit [Nonempty SsemQT] in
theorem canonicalHomeostaticOperationalParent_system
    [Fintype ChildQT]
    {readout : Finset VQT → HQT → RoutQT}
    {p : HQT → ProbeQT → Measure YQT}
    {regions : ChildQT → Finset VQT}
    {response : Finset ChildQT → EQT → Measure ZoutQT}
    {hprob : ∀ T e, IsProbabilityMeasure (response T e)}
    {probes : Finset EQT}
    {dynamics : FormedCandidate readout p regions → XQT → AQT → PMF XQT}
    {persistenceDomain : FormedCandidate readout p regions → Set XQT}
    {pi : FormedCandidate readout p regions → CsemQT}
    {semanticKernel : FormedCandidate readout p regions → Matrix SsemQT SsemQT ℝ}
    {hSemanticKernel : ∀ q, semanticKernel q ∈ Matrix.rowStochastic ℝ SsemQT}
    (base : SemanticallyStableSelfRepairingOperationalParent
      readout p regions response hprob probes dynamics persistenceDomain
      pi semanticKernel hSemanticKernel)
    (F : ConstitutiveState XQT AQT → PMF (ConstitutiveState XQT AQT))
    (epsilon : NNReal) (hepsilon : epsilon ≤ 1)
    (hF : ∀ ⦃z : ConstitutiveState XQT AQT⦄,
      z ∈ gcrHomeostaticCarrier
        (dynamics base.repairing.operational.parent)
        base.repairing.operational.persistence.K →
      StaysIn (F z)
        (gcrHomeostaticCarrier
          (dynamics base.repairing.operational.parent)
          base.repairing.operational.persistence.K)) :
    (canonicalHomeostaticOperationalParent
      base F epsilon hepsilon hF).system =
      objecthoodRecurrentHomeostasisSystem
        (dynamics base.repairing.operational.parent)
        base.repairing.operational.persistence.K
        base.repairing.operational.persistence.source_fixed
        F epsilon hepsilon hF := by
  rfl


end
end UEOT.V3.Compression.Objecthood
