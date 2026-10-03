import UEOT.V3.Compression.Objecthood.MaximalStationaryRepair
import UEOT.V3.Compression.Objecthood.EndogenousRepairCertificate
import Mathlib.Probability.Distributions.Uniform
namespace UEOT.V3.Compression.Objecthood
open Set MeasureTheory
open UEOT.V3.ViabilityKernel
open UEOT.V3.ViabilityTrajectory
open UEOT.V3.RecoveryHittingNonnegative
open scoped ENNReal
universe uX uA
noncomputable section

theorem strongRepairable_subset_stationaryRepairable
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X) :
    {x | StrongRepairable P K x} ⊆
      {x | ∃ pi : X → A, x ∈ StationaryRepairBasin P K pi} := by
  intro x hx
  refine ⟨descendingRepairAction P K, ?_⟩
  change expectedHittingTime
    (stationaryKernel P (descendingRepairAction P K)) x K ≠ ∞
  exact ne_top_of_le_ne_top (ENNReal.natCast_ne_top _)
    (endogenous_expectedHittingTime_le_rank P K x hx)

namespace GeometricRetryWitness

def target : Set Bool := {true}

def kernel (x : Bool) (_ : Unit) : PMF Bool :=
  if x then PMF.pure true else PMF.uniformOfFintype Bool

def policy : Bool → Unit := fun _ => ()

def potential (x : Bool) : ℝ≥0∞ := if x then 0 else 2

noncomputable def certificate : PhysicalRepairCertificate kernel target where
  repairPolicy := policy
  potential := potential
  drift := 1
  target_measurable := (Set.toFinite target).measurableSet
  potential_measurable := measurable_of_finite _
  drift_ne_zero := by simp
  drift_ne_top := by simp
  drift_condition := by
    intro z hz
    cases z with
    | false =>
        rw [stationaryKernel_apply, lintegral_fintype]
        simp [kernel, potential, PMF.uniformOfFintype_apply]
        rw [ENNReal.mul_inv_cancel] <;> norm_num
    | true =>
        exfalso
        exact hz (by simp [target])

theorem false_mem_stationaryRepairBasin :
    false ∈ StationaryRepairBasin kernel target policy := by
  have hxC : false ∈ certificate.basin := by
    simp [certificate, PhysicalRepairCertificate.basin, potential]
  have hfin := certificate.expectedHittingTime_ne_top_of_mem_basin hxC
  change expectedHittingTime (stationaryKernel kernel policy) false target ≠ ∞
  exact hfin

theorem retry_false_mem_support :
    false ∈ (kernel false ()).support := by
  simp [kernel, PMF.support_uniformOfFintype]

theorem repairIter_eq_target (n : ℕ) : repairIter kernel target n = target := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [repairIter_succ, ih]
      have hnot : ¬ StaysIn (kernel false ()) target := by
        intro hs
        have hf := hs retry_false_mem_support
        simp [target] at hf
      ext x
      cases x
      · constructor
        · intro hx
          rcases hx with hx | ⟨a, ha⟩
          · exact hx
          · cases a
            exact (hnot ha).elim
        · intro hx
          exact Or.inl hx
      · simp [repairStep, target]

theorem false_not_strongRepairable :
    ¬ StrongRepairable kernel target false := by
  rintro ⟨n, hn⟩
  rw [repairIter_eq_target n] at hn
  simpa [target] using hn

theorem strict_separation :
    ¬ StrongRepairable kernel target false ∧
      false ∈ StationaryRepairBasin kernel target policy :=
  ⟨false_not_strongRepairable, false_mem_stationaryRepairBasin⟩

end GeometricRetryWitness
end
end UEOT.V3.Compression.Objecthood
