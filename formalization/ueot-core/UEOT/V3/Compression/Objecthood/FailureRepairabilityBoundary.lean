import UEOT.V3.Compression.Objecthood.AutonomousSelfStabilization
import UEOT.V3.OmegaMinimalFailure
import UEOT.V3.OmegaIntegrityMargin

/-!
# Track O / O6 — P-OMG failure envelope versus repairability

P-OMG-01 characterizes monotone failure families by inclusion-minimal
destructive deletion sets. P-OMG-02 gives a 1-Lipschitz metric distance to a
failure set. Neither theorem supplies a repair policy or proves that a damaged
state lies in the O5 repair basin.

This module makes that separation explicit and then states the strongest
positive bridge justified by additional repairability data:

* deletion failure is classified by P-OMG-01 while basin membership is a
  separate predicate on the realized damaged constitutive state;
* a metric repair margin is the distance to the complement of the
  O5-repairable representation set;
* perturbations smaller than the minimum of integrity margin and repair margin
  remain both nonfailed and repairable;
* repairability then feeds the already-proved O5 autonomous almost-sure repair
  theorem.

No counted-core change is introduced.
-/

namespace UEOT.V3.Compression.Objecthood

open Set MeasureTheory ProbabilityTheory
open UEOT.V3.ViabilityKernel
open UEOT.V3.ViabilityTrajectory
open UEOT.V3.Compression.CrossTrack
open UEOT.V3.OmegaMinimalFailure
open UEOT.V3.OmegaIntegrityMargin
open scoped ENNReal ProbabilityTheory

universe uX uA uV uY

noncomputable section

/-- A deletion pattern is repairable when its realized damaged physical state
lies in the O4/O5 finite-potential repair basin. Failure and repairability are
therefore deliberately typed as separate predicates. -/
def RepairableDeletion
    {X : Type uX} {A : Type uA} {V : Type uV}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    {P : X → A → PMF X} {K : Set X}
    (R : PhysicalRepairCertificate P K)
    (damage : Finset V → ConstitutiveState X A)
    (D : Finset V) : Prop :=
  (damage D).1 ∈ R.basin

/-- **Positive O6 deletion bridge.** A failing deletion that is explicitly
known to realize inside the repair basin has both a P-OMG-01 minimal failure
witness and O5 almost-sure autonomous repair to legitimate organization. -/
theorem failure_witness_and_autonomous_repair
    {X : Type uX} {A : Type uA} {V : Type uV}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (R : PhysicalRepairCertificate P K)
    (Failure : Finset V → Prop)
    (hmono : FailureMonotone Failure)
    (damage : Finset V → ConstitutiveState X A)
    (D : Finset V)
    (hfail : Failure D)
    (hrepair : RepairableDeletion R damage D) :
    ∃ C, C ∈ minimalFailures Failure ∧ C ⊆ D ∧
      (∀ᵐ omega ∂stationaryTrajMeasure
          (autonomousRepairLift P K hfix R) noExternalControl
          (PMF.pure (damage D)),
        ∃ n : ℕ, omega n ∈ legitimateConstitutiveDomain P K) := by
  obtain ⟨C, hC, hCD⟩ := (p_omg_01 Failure hmono D).1 hfail
  exact ⟨C, hC, hCD,
    autonomousRepair_eventually_legitimate_ae P K hfix R hrepair⟩

/-- **Required O6 negative boundary.** P-OMG-01 still supplies its complete
minimal-failure witness even when the realized damage is explicitly outside the
repair basin. Thus failure characterization does not itself imply
repairability. -/
theorem p_omg_01_does_not_supply_repairability
    {X : Type uX} {A : Type uA} {V : Type uV}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    {P : X → A → PMF X} {K : Set X}
    (R : PhysicalRepairCertificate P K)
    (Failure : Finset V → Prop)
    (hmono : FailureMonotone Failure)
    (damage : Finset V → ConstitutiveState X A)
    (D : Finset V)
    (hfail : Failure D)
    (hnorepair : ¬ RepairableDeletion R damage D) :
    (∃ C, C ∈ minimalFailures Failure ∧ C ⊆ D) ∧
      ¬ RepairableDeletion R damage D := by
  exact ⟨(p_omg_01 Failure hmono D).1 hfail, hnorepair⟩

/-- Metric representations whose realized damaged constitutive states remain
inside the O5 repair basin. -/
def repairableRepresentationSet
    {X : Type uX} {A : Type uA} {Y : Type uY}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    {P : X → A → PMF X} {K : Set X}
    (R : PhysicalRepairCertificate P K)
    (damage : Y → ConstitutiveState X A) : Set Y :=
  {y | (damage y).1 ∈ R.basin}

/-- Repair margin: metric distance to representations whose damage falls
outside the certified repair basin. This deliberately mirrors P-OMG-02 but uses
the complement of the independently supplied repairable set. -/
def repairMargin
    {X : Type uX} {A : Type uA} {Y : Type uY}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [PseudoMetricSpace Y]
    {P : X → A → PMF X} {K : Set X}
    (R : PhysicalRepairCertificate P K)
    (damage : Y → ConstitutiveState X A) (T : Y) : ℝ :=
  integrityMargin (repairableRepresentationSet R damage)ᶜ T

/-- Perturbations strictly smaller than the repair margin stay in the
repairable representation set. The nonempty-complement hypothesis records the
source domain required by the P-OMG-02 interface. -/
theorem mem_repairableRepresentation_of_dist_lt_repairMargin
    {X : Type uX} {A : Type uA} {Y : Type uY}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [PseudoMetricSpace Y]
    {P : X → A → PMF X} {K : Set X}
    (R : PhysicalRepairCertificate P K)
    (damage : Y → ConstitutiveState X A)
    (T S : Y)
    (hcomp : (repairableRepresentationSet R damage)ᶜ.Nonempty)
    (hmargin : dist T S < repairMargin R damage T) :
    S ∈ repairableRepresentationSet R damage := by
  by_contra hS
  have hSc : S ∈ (repairableRepresentationSet R damage)ᶜ := hS
  have hlip := p_omg_02
    (repairableRepresentationSet R damage)ᶜ hcomp T S
  have hzero :
      integrityMargin (repairableRepresentationSet R damage)ᶜ S = 0 := by
    unfold integrityMargin
    exact Metric.infDist_zero_of_mem hSc
  rw [hzero, sub_zero] at hlip
  change
    |Metric.infDist T (repairableRepresentationSet R damage)ᶜ| ≤ dist T S
    at hlip
  rw [abs_of_nonneg (Metric.infDist_nonneg :
      0 ≤ Metric.infDist T (repairableRepresentationSet R damage)ᶜ)] at hlip
  have hle : repairMargin R damage T ≤ dist T S := by
    simpa [repairMargin, integrityMargin] using hlip
  exact not_lt_of_ge hle hmargin

/-- Combined robustness margin: the smaller of distance to failure and
distance to loss of O5 repairability. -/
def integrityRepairMargin
    {X : Type uX} {A : Type uA} {Y : Type uY}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [PseudoMetricSpace Y]
    {P : X → A → PMF X} {K : Set X}
    (R : PhysicalRepairCertificate P K)
    (damage : Y → ConstitutiveState X A)
    (failure : Set Y) (T : Y) : ℝ :=
  min (integrityMargin failure T) (repairMargin R damage T)

/-- A perturbation below the combined margin is simultaneously outside the
P-OMG failure set and inside the independently certified repairable region. -/
theorem safe_and_repairable_of_dist_lt_integrityRepairMargin
    {X : Type uX} {A : Type uA} {Y : Type uY}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [PseudoMetricSpace Y]
    {P : X → A → PMF X} {K : Set X}
    (R : PhysicalRepairCertificate P K)
    (damage : Y → ConstitutiveState X A)
    (failure : Set Y) (hfailure : failure.Nonempty)
    (hcomp : (repairableRepresentationSet R damage)ᶜ.Nonempty)
    (T S : Y)
    (hmargin : dist T S < integrityRepairMargin R damage failure T) :
    S ∉ failure ∧ S ∈ repairableRepresentationSet R damage := by
  have hboth : dist T S < integrityMargin failure T ∧
      dist T S < repairMargin R damage T := by
    simpa [integrityRepairMargin, lt_min_iff] using hmargin
  constructor
  · intro hSf
    have hlip := p_omg_02 failure hfailure T S
    have hzero : integrityMargin failure S = 0 := by
      unfold integrityMargin
      exact Metric.infDist_zero_of_mem hSf
    rw [hzero, sub_zero] at hlip
    change |Metric.infDist T failure| ≤ dist T S at hlip
    rw [abs_of_nonneg
      (Metric.infDist_nonneg : 0 ≤ Metric.infDist T failure)] at hlip
    have hle : integrityMargin failure T ≤ dist T S := by
      simpa [integrityMargin] using hlip
    exact not_lt_of_ge hle hboth.1
  · exact mem_repairableRepresentation_of_dist_lt_repairMargin
      R damage T S hcomp hboth.2

/-- **Positive O6 metric bridge.** Below the explicit combined margin, the
perturbed representation is nonfailed and its realized damaged object reaches
the legitimate constitutive domain almost surely under the O5 autonomous
hybrid dynamics. -/
theorem safe_repairable_and_eventually_legitimate
    {X : Type uX} {A : Type uA} {Y : Type uY}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    [PseudoMetricSpace Y]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (R : PhysicalRepairCertificate P K)
    (damage : Y → ConstitutiveState X A)
    (failure : Set Y) (hfailure : failure.Nonempty)
    (hcomp : (repairableRepresentationSet R damage)ᶜ.Nonempty)
    (T S : Y)
    (hmargin : dist T S < integrityRepairMargin R damage failure T) :
    S ∉ failure ∧
    (∀ᵐ omega ∂stationaryTrajMeasure
        (autonomousRepairLift P K hfix R) noExternalControl
        (PMF.pure (damage S)),
      ∃ n : ℕ, omega n ∈ legitimateConstitutiveDomain P K) := by
  have hs := safe_and_repairable_of_dist_lt_integrityRepairMargin
    R damage failure hfailure hcomp T S hmargin
  exact ⟨hs.1,
    autonomousRepair_eventually_legitimate_ae P K hfix R hs.2⟩

/-! ## Concrete separation witness

The following tiny finite model proves consistency of the negative boundary:
complete P-OMG-01 failure structure and a positive P-OMG-02 integrity margin can
coexist with a specified damaged state outside a valid physical repair basin.
-/

namespace FailureRepairBoundaryToy

def transition : Bool → Unit → PMF Bool := fun x _ => PMF.pure x

def kernel : Set Bool := {true}

theorem kernel_fixed : viabilityStep transition kernel = kernel := by
  ext x
  simp [viabilityStep, transition, kernel, StaysIn]

def repairCertificate : PhysicalRepairCertificate transition kernel where
  repairPolicy := fun _ => ()
  potential := fun x => if x then 0 else ∞
  drift := 1
  target_measurable := by simp [kernel]
  potential_measurable := measurable_of_finite _
  drift_ne_zero := by simp
  drift_ne_top := by simp
  drift_condition := by
    intro z hz
    have hzfalse : z = false := by
      cases z <;> simp_all [kernel]
    subst z
    simp [transition, stationaryKernel_apply]

def failure (D : Finset Unit) : Prop := () ∈ D

theorem failure_monotone : FailureMonotone failure := by
  intro D D' hsub hD
  exact hsub hD

def damage (_D : Finset Unit) : ConstitutiveState Bool Unit :=
  (false, fun _ => ())

theorem failedDeletion_not_repairable :
    failure {()} ∧
      ¬ RepairableDeletion repairCertificate damage {()} := by
  constructor
  · simp [failure]
  · change false ∉ repairCertificate.basin
    simp [PhysicalRepairCertificate.basin, repairCertificate]

/-- P-OMG-01 supplies a genuine minimal destructive witness while the same
deletion realizes outside the certified repair basin. -/
theorem minimal_failure_and_no_repair :
    (∃ C, C ∈ minimalFailures failure ∧ C ⊆ ({()} : Finset Unit)) ∧
      ¬ RepairableDeletion repairCertificate damage {()} :=
  p_omg_01_does_not_supply_repairability
    repairCertificate failure failure_monotone damage {()}
    (by simp [failure]) failedDeletion_not_repairable.2

/-- A strictly positive P-OMG-02 margin can coexist with that same
nonrepairable damaged state. Hence a positive integrity margin is a robustness
statement about distance to failure, not a repairability theorem. -/
theorem positive_integrity_margin_and_no_repair :
    0 < integrityMargin ({(1 : ℝ)} : Set ℝ) 0 ∧
      ¬ RepairableDeletion repairCertificate damage {()} := by
  constructor
  · simp [integrityMargin]
  · exact failedDeletion_not_repairable.2

end FailureRepairBoundaryToy

end

end UEOT.V3.Compression.Objecthood
