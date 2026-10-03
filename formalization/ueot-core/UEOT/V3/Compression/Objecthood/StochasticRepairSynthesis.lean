import UEOT.V3.Compression.Objecthood.GeneralCausalRepairBoundary
import UEOT.V3.Compression.Objecthood.FailureRepairabilityBoundary
import UEOT.V3.Compression.Objecthood.EventualAlwaysLegitimacy
import UEOT.V3.Compression.Objecthood.FormedParentSelfRepairSynthesis

/-!
# Track O / AR7 — stochastic Objecthood repair synthesis

This final AR stage composes AR0--AR6 with the existing Objecthood deletion and
autonomous-repair architecture.  The result is intentionally uncounted: it
selects no new generator and does not cross the AR6 general-causal G3 boundary.
-/

namespace UEOT.V3.Compression.Objecthood

open Set MeasureTheory ProbabilityTheory
open UEOT.V3.ViabilityKernel
open UEOT.V3.ViabilityTrajectory
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.OmegaMinimalFailure
open UEOT.V3.Compression.CrossTrack
open scoped ENNReal ProbabilityTheory

universe uV uChild uH uProbe uR uY uE uZ uX uA uDel uC uS

noncomputable section

/-- **AR7 stationary stochastic-repair synthesis.**  The AR3 maximal policy has
all structural properties established across AR0--AR5: the target is included,
the basin is one-step support closed outside the target, it is exactly the union
of every deterministic-stationary finite-expected-hitting basin, every strong
repair state lies inside it, and the optimal stationary hitting value is bounded
by the constructive strong-repair rank wherever that rank exists. -/
theorem stochasticObjecthood_stationaryRepair_synthesis
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X) :
    let piMax := maximalStationaryRepairPolicy P K
    let BMax := StationaryRepairBasin P K piMax
    K ⊆ BMax ∧
      (∀ ⦃x y : X⦄, x ∈ BMax → x ∉ K →
        y ∈ (P x (piMax x)).support → y ∈ BMax) ∧
      BMax = {x | ∃ pi : X → A, x ∈ StationaryRepairBasin P K pi} ∧
      {x | StrongRepairable P K x} ⊆ BMax ∧
      (∀ (x : X) (hx : StrongRepairable P K x),
        stationaryRepairValue P K x ≤ (repairRank P K x hx : ℝ≥0∞)) := by
  dsimp only
  refine ⟨target_subset_stationaryRepairBasin P K
      (maximalStationaryRepairPolicy P K), ?_,
    maximalStationaryRepairBasin_eq_exists_policy P K, ?_, ?_⟩
  · intro x y hx hxK hy
    exact stationaryRepairBasin_support_closed
      P K (maximalStationaryRepairPolicy P K) hx hxK hy
  · intro x hx
    exact strongRepairable_mem_maximalStationaryRepairBasin P K x hx
  · intro x hx
    exact stationaryRepairValue_le_rank_of_strongRepairable P K x hx

/-- The maximal deterministic-stationary certificate has exactly the AR3 union
basin.  This is the canonical certificate used by the AR7 deletion bridge. -/
theorem maximalStationaryRepairCertificate_basin_eq
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X) :
    (maximalStationaryRepairCertificate P K).basin =
      {x | DeterministicStationaryFiniteExpectedRepairable P K x} := by
  ext x
  change x ∈ (maximalStationaryRepairCertificate P K).basin ↔
    DeterministicStationaryFiniteExpectedRepairable P K x
  exact mem_maximalCertificate_basin_iff_exists_policy P K x

/-- **AR7 deletion-to-repair synthesis.**  If a failing deletion realizes a
physical state that is repairable by *some* deterministic stationary policy in
finite expected hitting time, then the single AR3 maximal certificate is enough
to feed the pre-existing O5/O6 autonomous repair architecture.  The conclusion
simultaneously supplies the minimal destructive deletion witness and almost-sure
return to the legitimate constitutive domain.

No new deletion primitive or repair architecture is introduced. -/
theorem stationaryRepairable_failure_restores_legitimate
    {X : Type uX} {A : Type uA} {V : Type uV}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (Failure : Finset V → Prop)
    (hmono : FailureMonotone Failure)
    (damage : Finset V → ConstitutiveState X A)
    (D : Finset V)
    (hfail : Failure D)
    (hrepair : DeterministicStationaryFiniteExpectedRepairable
      P K (damage D).1) :
    ∃ C, C ∈ minimalFailures Failure ∧ C ⊆ D ∧
      (∀ᵐ omega ∂stationaryTrajMeasure
          (autonomousRepairLift P K hfix
            (maximalStationaryRepairCertificate P K))
          noExternalControl (PMF.pure (damage D)),
        ∃ n : ℕ, omega n ∈ legitimateConstitutiveDomain P K) := by
  let R := maximalStationaryRepairCertificate P K
  have hbasin : (damage D).1 ∈ R.basin := by
    change (damage D).1 ∈ (maximalStationaryRepairCertificate P K).basin
    exact (mem_maximalCertificate_basin_iff_exists_policy P K (damage D).1).2 hrepair
  have hrepairDeletion : RepairableDeletion R damage D := hbasin
  simpa [R] using
    failure_witness_and_autonomous_repair
      P K hfix R Failure hmono damage D hfail hrepairDeletion

/-- The strict AR4 geometric-retry witness survives the end-to-end synthesis:
the new stochastic basin is a genuine enlargement of strong finite-rank repair,
not only a repackaging. -/
theorem stochasticObjecthood_strictly_extends_strongRepair :
    ¬ StrongRepairable
        GeometricRetryWitness.kernel GeometricRetryWitness.target false ∧
      false ∈ StationaryRepairBasin
        GeometricRetryWitness.kernel GeometricRetryWitness.target
        GeometricRetryWitness.policy :=
  GeometricRetryWitness.strict_separation

/-- **AR7 / ER0 closure.**  Any state repaired in finite expected time by some
deterministic stationary policy is eventually permanently legitimate under the
single AR3 maximal stationary certificate and the existing autonomous repair
lift. -/
theorem stationaryRepairable_eventually_always_legitimate
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    {z : ConstitutiveState X A}
    (hz : DeterministicStationaryFiniteExpectedRepairable P K z.1) :
    ∀ᵐ omega ∂stationaryTrajMeasure
        (autonomousRepairLift P K hfix (maximalStationaryRepairCertificate P K))
        noExternalControl (PMF.pure z),
      ∃ N : ℕ, ∀ m ≥ N, omega m ∈ legitimateConstitutiveDomain P K := by
  have hbasin : z.1 ∈ (maximalStationaryRepairCertificate P K).basin :=
    (mem_maximalCertificate_basin_iff_exists_policy P K z.1).2 hz
  exact autonomousRepair_eventually_always_legitimate_ae
    P K hfix (maximalStationaryRepairCertificate P K) hbasin

/-- Canonical O7 package.  Once AR3 is available, an already formed operational
parent no longer needs an externally supplied physical repair Lyapunov
certificate: its own stored dynamics and persistence kernel generate the
maximal stationary certificate. -/
noncomputable def canonicalSelfRepairingOperationalParent
    {V : Type uV} {Child : Type uChild}
    {H : Type uH} {Probe : Type uProbe}
    {Rout : Type uR} {Y : Type uY} [MeasurableSpace Y]
    {E : Type uE} {Z : Type uZ} [MeasurableSpace Z]
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    [Fintype Child]
    {readout : Finset V → H → Rout}
    {p : H → Probe → Measure Y}
    {regions : Child → Finset V}
    {response : Finset Child → E → Measure Z}
    {hprob : ∀ S e, IsProbabilityMeasure (response S e)}
    {probes : Finset E}
    {dynamics : FormedCandidate readout p regions → X → A → PMF X}
    {persistenceDomain : FormedCandidate readout p regions → Set X}
    (C : OperationalFormedPersistentParent
      readout p regions response hprob probes dynamics persistenceDomain) :
    SelfRepairingOperationalParent
      readout p regions response hprob probes dynamics persistenceDomain where
  operational := C
  physicalRepair := maximalStationaryRepairCertificate
    (dynamics C.parent) C.persistence.K

/-- **AR7 deletion + ER0 closure on the same formed parent.**  A failing
deletion whose damaged state belongs to the deterministic-stationary stochastic
repair class has a P-OMG minimal witness and, under the canonical maximal repair
certificate for that exact parent, eventually remains forever in that parent's
legitimate constitutive domain. -/
theorem stationaryRepairable_failingDeletion_eventually_always_same_parent
    {V : Type uV} {Child : Type uChild}
    {H : Type uH} {Probe : Type uProbe}
    {Rout : Type uR} {Y : Type uY} [MeasurableSpace Y]
    {E : Type uE} {Z : Type uZ} [MeasurableSpace Z]
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    [Fintype Child]
    {readout : Finset V → H → Rout}
    {p : H → Probe → Measure Y}
    {regions : Child → Finset V}
    {response : Finset Child → E → Measure Z}
    {hprob : ∀ S e, IsProbabilityMeasure (response S e)}
    {probes : Finset E}
    {dynamics : FormedCandidate readout p regions → X → A → PMF X}
    {persistenceDomain : FormedCandidate readout p regions → Set X}
    (C : OperationalFormedPersistentParent
      readout p regions response hprob probes dynamics persistenceDomain)
    {Del : Type uDel}
    (Failure : Finset Del → Prop)
    (hmono : FailureMonotone Failure)
    (damage : Finset Del → ConstitutiveState X A)
    (D : Finset Del)
    (hfail : Failure D)
    (hrepair : DeterministicStationaryFiniteExpectedRepairable
      (dynamics C.parent) C.persistence.K (damage D).1) :
    ∃ Dmin, Dmin ∈ minimalFailures Failure ∧ Dmin ⊆ D ∧
      (∀ᵐ omega ∂stationaryTrajMeasure
          (autonomousRepairLift
            (dynamics C.parent) C.persistence.K C.persistence.source_fixed
            (maximalStationaryRepairCertificate
              (dynamics C.parent) C.persistence.K))
          noExternalControl (PMF.pure (damage D)),
        ∃ N : ℕ, ∀ m ≥ N,
          omega m ∈ legitimateConstitutiveDomain
            (dynamics C.parent) C.persistence.K) := by
  obtain ⟨Dmin, hmin, hsub⟩ := (p_omg_01 Failure hmono D).1 hfail
  refine ⟨Dmin, hmin, hsub, ?_⟩
  exact stationaryRepairable_eventually_always_legitimate
    (dynamics C.parent) C.persistence.K C.persistence.source_fixed hrepair

variable {Csem : Type uC}
variable {Ssem : Type uS} [Fintype Ssem] [Nonempty Ssem]
noncomputable local instance ar7SemanticDecidableEq : DecidableEq Ssem :=
  Classical.decEq Ssem

/-- **AR7 / O7 / ER0 joint closure.**  The exact selected formed parent keeps
its Track-X long-run semantic bound while any physical state repairable by some
deterministic stationary finite-expected policy is driven by the AR3 maximal
certificate to that same parent's legitimate constitutive domain and remains
there eventually forever. -/
theorem canonical_semantic_bound_and_eventually_always_same_parent_repair
    {V : Type uV} {Child : Type uChild}
    {H : Type uH} {Probe : Type uProbe}
    {Rout : Type uR} {Y : Type uY} [MeasurableSpace Y]
    {E : Type uE} {Z : Type uZ} [MeasurableSpace Z]
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    [Fintype Child]
    {readout : Finset V → H → Rout}
    {p : H → Probe → Measure Y}
    {regions : Child → Finset V}
    {response : Finset Child → E → Measure Z}
    {hprob : ∀ S e, IsProbabilityMeasure (response S e)}
    {probes : Finset E}
    {dynamics : FormedCandidate readout p regions → X → A → PMF X}
    {persistenceDomain : FormedCandidate readout p regions → Set X}
    (C : OperationalFormedPersistentParent
      readout p regions response hprob probes dynamics persistenceDomain)
    {pi : FormedCandidate readout p regions → Csem}
    {semanticKernel : FormedCandidate readout p regions → Matrix Ssem Ssem ℝ}
    {hSemanticKernel : ∀ q, semanticKernel q ∈ Matrix.rowStochastic ℝ Ssem}
    (semantic : RobustParentSemanticCertificate pi semanticKernel hSemanticKernel)
    (hselected : pi C.parent = semantic.child)
    (hcard : 1 < Fintype.card Ssem)
    {q : FormedCandidate readout p regions}
    (hq : pi q = semantic.child)
    {z : ConstitutiveState X A}
    (hz : DeterministicStationaryFiniteExpectedRepairable
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
  constructor
  · exact semantic.pairwise_bound
      pi semanticKernel hSemanticKernel hcard hselected hq
  · exact stationaryRepairable_eventually_always_legitimate
      (dynamics C.parent) C.persistence.K C.persistence.source_fixed hz

end

end UEOT.V3.Compression.Objecthood
