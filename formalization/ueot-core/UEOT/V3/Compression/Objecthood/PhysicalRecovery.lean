import UEOT.V3.Compression.Objecthood.ControllerSelfStabilization
import UEOT.V3.RecoveryHittingBound
import UEOT.V3.RecoveryHittingFirstStep

/-!
# Track O / O4 — physical repair basin through P-REC

O1--O3 solve controller corruption only while the physical coordinate remains
inside the P-PER winning kernel.  O4 addresses the orthogonal problem: physical
recovery from states outside a target set.

The construction deliberately reuses the frozen P-REC-04 hitting-time theorem.
A deterministic repair policy induces the repository's ordinary homogeneous
Markov kernel.  A measurable nonnegative Lyapunov potential with positive,
finite drift then yields the exact expected hitting-time bound.  Finite
expected hitting time is additionally converted to almost-sure eventual
hitting by a pointwise theorem showing that a never-hitting path has infinite
`hittingValue`.

No implication from viability, persistence, or an Omega integrity margin to
repairability is asserted here.
-/

namespace UEOT.V3.Compression.Objecthood

open Set Finset MeasureTheory ProbabilityTheory
open UEOT.V3.DynamicsKernel
open UEOT.V3.ViabilityTrajectory
open UEOT.V3.RecoveryHittingNonnegative
open UEOT.V3.RecoveryHittingFirstStep
open UEOT.V3.RecoveryHittingBound
open scoped ENNReal ProbabilityTheory

universe uX uA

noncomputable section

/-- Paths that never hit the target have every survival indicator equal to one,
so the truncation at `N` is exactly `N`. -/
theorem truncatedHittingValue_eq_natCast_of_never_hits
    {X : Type uX} [MeasurableSpace X]
    (A : Set X) (omega : ℕ → X)
    (hnever : ∀ n, omega n ∉ A) (N : ℕ) :
    truncatedHittingValue A N omega = (N : ℝ≥0∞) := by
  unfold truncatedHittingValue
  have hs : ∀ n, omega ∈ survivalSet A n := by
    intro n
    exact (mem_survivalSet_iff A n omega).2 fun k _ => hnever k
  simp [hs]

/-- A path that never reaches `A` has infinite extended hitting time. -/
theorem hittingValue_eq_top_of_never_hits
    {X : Type uX} [MeasurableSpace X]
    (A : Set X) (omega : ℕ → X)
    (hnever : ∀ n, omega n ∉ A) :
    hittingValue A omega = ∞ := by
  unfold hittingValue
  simp_rw [truncatedHittingValue_eq_natCast_of_never_hits A omega hnever]
  exact ENNReal.iSup_natCast

/-- Finite expected hitting time implies almost-sure eventual target hitting
under the genuine homogeneous Markov trajectory law. -/
theorem eventually_hits_ae_of_expectedHittingTime_ne_top
    {X : Type uX} [MeasurableSpace X]
    (Q : Kernel X X) [IsMarkovKernel Q]
    (x : X) (A : Set X) (hA : MeasurableSet A)
    (hfinite : expectedHittingTime Q x A ≠ ∞) :
    ∀ᵐ omega ∂homTrajMeasure (Measure.dirac x) Q,
      ∃ n : ℕ, omega n ∈ A := by
  have hae : ∀ᵐ omega ∂homTrajMeasure (Measure.dirac x) Q,
      hittingValue A omega < ∞ :=
    ae_lt_top (measurable_hittingValue hA) hfinite
  filter_upwards [hae] with omega homega
  by_contra hno
  have hnever : ∀ n : ℕ, omega n ∉ A := by
    intro n hn
    exact hno ⟨n, hn⟩
  have htop := hittingValue_eq_top_of_never_hits A omega hnever
  rw [htop] at homega
  exact (lt_irrefl (∞ : ℝ≥0∞)) homega

/-- A physical repair certificate is a policy plus a source-faithful P-REC
Lyapunov certificate for reaching `target`. -/
structure PhysicalRepairCertificate
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (target : Set X) where
  repairPolicy : X → A
  potential : X → ℝ≥0∞
  drift : ℝ≥0∞
  target_measurable : MeasurableSet target
  potential_measurable : Measurable potential
  drift_ne_zero : drift ≠ 0
  drift_ne_top : drift ≠ ∞
  drift_condition :
    ∀ z, z ∉ target →
      (∫⁻ y, potential y ∂stationaryKernel P repairPolicy z) + drift ≤
        potential z

namespace PhysicalRepairCertificate

/-- The repair basin is exactly the finite-potential part of state space.  This
is the maximal basin justified by the supplied P-REC Lyapunov certificate
without inventing a separate reachability assumption. -/
def basin
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    {P : X → A → PMF X} {target : Set X}
    (C : PhysicalRepairCertificate P target) : Set X :=
  {x | C.potential x ≠ ∞}

/-- Direct controlled-system wrapper around frozen P-REC-04. -/
theorem expectedHittingTime_le
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    {P : X → A → PMF X} {target : Set X}
    (C : PhysicalRepairCertificate P target) (x : X) :
    expectedHittingTime (stationaryKernel P C.repairPolicy) x target ≤
      C.potential x / C.drift := by
  exact p_rec_04_hitting_time_bound
    (stationaryKernel P C.repairPolicy) x target C.potential C.drift
    C.target_measurable C.potential_measurable
    C.drift_ne_zero C.drift_ne_top C.drift_condition

/-- Every state in the certified basin has finite expected recovery time. -/
theorem expectedHittingTime_ne_top_of_mem_basin
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    {P : X → A → PMF X} {target : Set X}
    (C : PhysicalRepairCertificate P target) {x : X}
    (hx : x ∈ C.basin) :
    expectedHittingTime (stationaryKernel P C.repairPolicy) x target ≠ ∞ := by
  have hquot : C.potential x / C.drift ≠ ∞ :=
    ENNReal.div_ne_top hx C.drift_ne_zero
  exact ne_top_of_le_ne_top hquot (C.expectedHittingTime_le x)

/-- **O4 physical recovery.** Every physical state in the P-REC repair basin
hits the target almost surely under the certified repair policy. -/
theorem eventually_hits_ae_of_mem_basin
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    {P : X → A → PMF X} {target : Set X}
    (C : PhysicalRepairCertificate P target) {x : X}
    (hx : x ∈ C.basin) :
    ∀ᵐ omega ∂homTrajMeasure
        (Measure.dirac x) (stationaryKernel P C.repairPolicy),
      ∃ n : ℕ, omega n ∈ target :=
  eventually_hits_ae_of_expectedHittingTime_ne_top
    (stationaryKernel P C.repairPolicy) x target C.target_measurable
    (C.expectedHittingTime_ne_top_of_mem_basin hx)

/-- Same almost-sure recovery statement using the repository's controlled PMF
trajectory wrapper. -/
theorem stationaryTrajMeasure_eventually_hits_ae_of_mem_basin
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    {P : X → A → PMF X} {target : Set X}
    (C : PhysicalRepairCertificate P target) {x : X}
    (hx : x ∈ C.basin) :
    ∀ᵐ omega ∂stationaryTrajMeasure P C.repairPolicy (PMF.pure x),
      ∃ n : ℕ, omega n ∈ target := by
  rw [stationaryTrajMeasure, PMF.toMeasure_pure]
  exact C.eventually_hits_ae_of_mem_basin hx

end PhysicalRepairCertificate

end

end UEOT.V3.Compression.Objecthood
