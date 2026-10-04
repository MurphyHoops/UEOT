import UEOT.V3.Compression.Objecthood.Homeostasis.CesaroHomeostasis

namespace UEOT.V3.Compression.Objecthood

open Set MeasureTheory ProbabilityTheory
open UEOT.V3.ViabilityKernel
open scoped ENNReal

noncomputable section

/-- Real certified repair capacity carried by the recurrent-fault drift. -/
def repairCapacityReal (epsilon : NNReal) (c : ENNReal) : ℝ :=
  (((1 - epsilon : NNReal) : ℝ)) * c.toReal

/-- Real certified fault load. -/
def faultLoadReal (epsilon : NNReal) (b : ENNReal) : ℝ :=
  (epsilon : ℝ) * b.toReal

/-- Positive margin is a sufficient homeostatic load condition, not a phase
transition statement. -/
def homeostaticMarginReal (epsilon : NNReal) (c b : ENNReal) : ℝ :=
  repairCapacityReal epsilon c - faultLoadReal epsilon b

def homeostaticLoadRatioReal (epsilon : NNReal) (c b : ENNReal) : ℝ :=
  faultLoadReal epsilon b / repairCapacityReal epsilon c

theorem repairCapacityReal_pos
    (epsilon : NNReal) (c : ENNReal)
    (hepsilon : epsilon < 1) (hc0 : c ≠ 0) (hctop : c ≠ ∞) :
    0 < repairCapacityReal epsilon c := by
  unfold repairCapacityReal
  apply mul_pos
  · exact_mod_cast (tsub_pos_iff_lt.mpr hepsilon : 0 < (1 - epsilon : NNReal))
  · exact ENNReal.toReal_pos hc0 hctop

theorem faultLoadReal_nonneg (epsilon : NNReal) (b : ENNReal) :
    0 ≤ faultLoadReal epsilon b := by
  exact mul_nonneg (by positivity) ENNReal.toReal_nonneg

theorem margin_pos_iff_load_lt_capacity
    (epsilon : NNReal) (c b : ENNReal) :
    0 < homeostaticMarginReal epsilon c b ↔
      faultLoadReal epsilon b < repairCapacityReal epsilon c := by
  simp [homeostaticMarginReal]

theorem loadRatioReal_lt_one_of_margin_pos
    (epsilon : NNReal) (c b : ENNReal)
    (hepsilon : epsilon < 1) (hc0 : c ≠ 0) (hctop : c ≠ ∞)
    (hmargin : 0 < homeostaticMarginReal epsilon c b) :
    homeostaticLoadRatioReal epsilon c b < 1 := by
  unfold homeostaticLoadRatioReal
  rw [div_lt_one (repairCapacityReal_pos epsilon c hepsilon hc0 hctop)]
  exact (margin_pos_iff_load_lt_capacity epsilon c b).1 hmargin

theorem repairCapacityReal_eq_zero_of_hazard_one (c : ENNReal) :
    repairCapacityReal 1 c = 0 := by
  simp [repairCapacityReal]

theorem repairCapacityReal_eq_zero_of_zero_drift (epsilon : NNReal) :
    repairCapacityReal epsilon 0 = 0 := by
  simp [repairCapacityReal]

theorem no_positive_margin_of_hazard_one (c b : ENNReal) :
    ¬ 0 < homeostaticMarginReal 1 c b := by
  rw [margin_pos_iff_load_lt_capacity, repairCapacityReal_eq_zero_of_hazard_one]
  exact not_lt_of_ge (faultLoadReal_nonneg 1 b)

theorem no_positive_margin_of_zero_drift (epsilon : NNReal) (b : ENNReal) :
    ¬ 0 < homeostaticMarginReal epsilon 0 b := by
  rw [margin_pos_iff_load_lt_capacity, repairCapacityReal_eq_zero_of_zero_drift]
  exact not_lt_of_ge (faultLoadReal_nonneg epsilon b)

/-- A one-step catastrophic fault that deterministically exits a designated
safe carrier. Positive RH theorems must therefore retain explicit carrier
support closure. -/
def catastrophicFaultBool : Bool → PMF Bool := fun _ => PMF.pure false

theorem catastrophicFaultBool_exits_safeCarrier :
    ¬ StaysIn (catastrophicFaultBool true) ({true} : Set Bool) := by
  intro h
  have hf : false ∈ (catastrophicFaultBool true).support := by
    simp [catastrophicFaultBool]
  have := h hf
  simp at this

/-- A finite recurrent system whose fault row stays in the declared carrier but
jumps from finite potential to infinite potential. -/
noncomputable def infiniteFaultBurdenSystem :
    RecurrentHomeostasisSystem Bool where
  legitimate := {true}
  carrier := Set.univ
  repairKernel := fun _ => PMF.pure true
  faultKernel := fun _ => PMF.pure false
  faultHazard := 1 / 2
  faultHazard_le_one := by norm_num
  potential := fun z => if z then 0 else ∞
  repairDrift := 1
  repairDrift_ne_zero := by norm_num
  repairDrift_ne_top := by simp
  legitimate_subset_carrier := Set.subset_univ _
  repair_stays_carrier := by
    intro z hz y hy
    trivial
  fault_stays_carrier := by
    intro z hz y hy
    trivial

private theorem infiniteFaultBurdenSystem_fault_expectation :
    (∫⁻ w, infiniteFaultBurdenSystem.potential w
      ∂(infiniteFaultBurdenSystem.faultKernel true).toMeasure) = ∞ := by
  rw [lintegral_fintype]
  simp [infiniteFaultBurdenSystem, PMF.pure_apply]

/-- Finite burden is a genuine certificate requirement: carrier closure alone
does not imply it when the declared potential may be infinite. -/
theorem no_finiteFaultBurdenCertificate_infinitePotential :
    IsEmpty (FaultBurdenCertificate infiniteFaultBurdenSystem) := by
  refine ⟨?_⟩
  intro C
  have h := C.fault_expectation_bound (z := true) (by
    simp [infiniteFaultBurdenSystem])
  rw [infiniteFaultBurdenSystem_fault_expectation] at h
  have htop :
      infiniteFaultBurdenSystem.potential true + C.burden ≠ ∞ := by
    simp [infiniteFaultBurdenSystem, C.burden_ne_top]
  exact htop (top_unique h)

end
end UEOT.V3.Compression.Objecthood
