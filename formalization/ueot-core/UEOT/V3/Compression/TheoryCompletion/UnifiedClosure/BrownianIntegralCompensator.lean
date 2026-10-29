import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralPastLocalization

/-!
Original commitment: actual continuous stochastic-integral square minus its SAME actual time-energy must be a martingale.
Existing result: actual original-source future-window localization/isometry and genuinely Fs-adapted actual timeEnergy.
Premise reduced: derive eventwise conditional second energy and the actual integrable compensated-square process.
Model/witness: SAME full predictable L2 input, fixed inputLaw T/sourceLaw/original naturalFiltration, including T=0.
Consumer: actual bracket/second-order Ito source; no L4, supplied compensator or general Ito/Girsanov is assumed.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralCompensator
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianTimeIntegrand BrownianPredictableInputs
open BrownianPredictableDensity BrownianIntegralTimeTruncation BrownianIntegralMartingale
open BrownianIntegralContinuousVersion BrownianIntegralTimeEnergy BrownianIntegralPastLocalization
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

def energyRectangle (T s : ℝ≥0) (A : Set (ℝ≥0 → ℝ)) : Set (ℝ × (ℝ≥0 → ℝ)) :=
  Ioc (0 : ℝ) ((min s T : ℝ≥0) : ℝ) ×ˢ A

private theorem timeEnergy_eq_setIntegral (T s : ℝ≥0) (f : fullPredictableL2 T) (ω : ℝ≥0 → ℝ) :
    timeEnergy T f s ω = ∫ t in Ioc (0 : ℝ) ((min s T : ℝ≥0) : ℝ), representative T f (t,ω)^2 ∂timeLaw T := by
  have he : (fun t => energyIntegrand T s f (t,ω)) =
      (Ioc (0 : ℝ) ((min s T : ℝ≥0) : ℝ)).indicator (fun t => representative T f (t,ω)^2) := by
    ext t
    by_cases h : t ∈ Ioc (0 : ℝ) ((min s T : ℝ≥0) : ℝ)
    · have hp : (t,ω) ∈ timeSet T s := ⟨h,mem_univ _⟩
      rw [energyIntegrand,Set.indicator_of_mem hp,Set.indicator_of_mem h]
    · have hp : (t,ω) ∉ timeSet T s := fun hp => h hp.1
      rw [energyIntegrand,Set.indicator_of_notMem hp,Set.indicator_of_notMem h]
  rw [timeEnergy,he,integral_indicator measurableSet_Ioc]

/-- Actual SAME-source energy on any ambient measurable event, via native
restricted-product Fubini; no conditional-energy identity is an input. -/
theorem timeEnergy_setIntegral (T s : ℝ≥0) (f : fullPredictableL2 T) (A : Set (ℝ≥0 → ℝ)) :
    (∫ ω in A, timeEnergy T f s ω ∂sourceLaw) =
      ∫ p in energyRectangle T s A, representative T f p^2 ∂inputLaw T := by
  have hi : Integrable (fun p => representative T f p^2)
      (((timeLaw T).restrict (Ioc (0 : ℝ) ((min s T : ℝ≥0) : ℝ))).prod (sourceLaw.restrict A)) := by
    rw [Measure.prod_restrict]
    exact (representative_memLp_two T f).integrable_sq.integrableOn
  have h := integral_prod_symm (fun p => representative T f p^2) hi
  simp only [Measure.prod_restrict] at h
  simp_rw [timeEnergy_eq_setIntegral]
  exact h.symm

private theorem rectangle_difference (T s t : ℝ≥0) (hst : s ≤ t) (A : Set (ℝ≥0 → ℝ)) :
    energyRectangle T t A \ energyRectangle T s A = eventWindow T s t A := by
  ext p
  by_cases hsT : s ≤ T
  · have hs : min s T = s := min_eq_left hsT
    simp only [energyRectangle,eventWindow,Set.mem_sdiff,mem_prod,mem_Ioc,hs]
    constructor
    · rintro ⟨⟨⟨hpos,hup⟩,hA⟩,hn⟩
      have hsp : (s : ℝ) < p.1 := lt_of_not_ge (fun h => hn ⟨⟨hpos,h⟩,hA⟩)
      exact ⟨⟨hsp,hup⟩,hA⟩
    · rintro ⟨⟨hsp,hup⟩,hA⟩
      refine ⟨⟨⟨lt_of_le_of_lt s.coe_nonneg hsp,hup⟩,hA⟩,?_⟩
      exact fun h => (not_le_of_gt hsp) h.1.2
  · have hTs : T ≤ s := (lt_of_not_ge hsT).le
    have hcs : min s T = T := min_eq_right hTs
    have hct : min t T = T := min_eq_right (hTs.trans hst)
    have hw : eventWindow T s t A = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact (not_lt_of_ge (hp.1.2.trans (by exact_mod_cast (min_le_right t T).trans hTs))) hp.1.1
    simp only [energyRectangle,hcs,hct,Set.sdiff_self,hw,mem_empty_iff_false]

/-- Actual time-energy FUTURE increment on the actual permitted past event
is the SAME localized product energy used by the actual integral isometry. -/
theorem timeEnergy_increment_setIntegral (T s t : ℝ≥0) (hst : s ≤ t)
    (A : Set (ℝ≥0 → ℝ)) (hA : MeasurableSet[naturalFiltration s] A) (f : fullPredictableL2 T) :
    (∫ ω in A, (timeEnergy T f t ω-timeEnergy T f s ω) ∂sourceLaw) =
      ∫ p in eventWindow T s t A, (f : Lp ℝ 2 (inputLaw T)) p^2 ∂inputLaw T := by
  have hA₀ := naturalFiltration.le s A hA
  have hsub : energyRectangle T s A ⊆ energyRectangle T t A := by
    intro p hp
    exact ⟨⟨hp.1.1,hp.1.2.trans (by exact_mod_cast min_le_min_right T hst)⟩,hp.2⟩
  rw [integral_sub (timeEnergy_integrable T t f).integrableOn (timeEnergy_integrable T s f).integrableOn,
    timeEnergy_setIntegral,timeEnergy_setIntegral]
  have hrect : MeasurableSet (energyRectangle T s A) := measurableSet_Ioc.prod hA₀
  have hd := setIntegral_sdiff (μ := inputLaw T) (f := fun p => representative T f p^2)
    (s := energyRectangle T t A) (t := energyRectangle T s A) hrect
    (representative_memLp_two T f).integrable_sq.integrableOn hsub
  rw [← hd,rectangle_difference T s t hst A]
  apply setIntegral_congr_ae (measurableSet_Ioc.prod hA₀)
  filter_upwards [representative_ae T f] with p hp _
  exact congrArg (fun x : ℝ => x^2) hp.symm

private theorem integral_increment_condExp_zero (T s t : ℝ≥0) (hst : s ≤ t) (f : fullPredictableL2 T) :
    sourceLaw[continuousIntegralProcess T f t-continuousIntegralProcess T f s | naturalFiltration s] =ᵐ[sourceLaw]
      fun _ => 0 := by
  have hm := continuousIntegralProcess_martingale T f
  have hs := condExp_sub (hm.integrable t) (hm.integrable s) (naturalFiltration s)
  apply hs.trans
  filter_upwards [hm.condExp_ae_eq hst,hm.condExp_ae_eq (le_refl s)] with ω ht hs
  simp only [Pi.sub_apply,ht,hs,sub_self]

private theorem cross_integrable (T s t : ℝ≥0) (f : fullPredictableL2 T) :
    Integrable (continuousIntegralProcess T f s *
      (continuousIntegralProcess T f t-continuousIntegralProcess T f s)) sourceLaw :=
  (continuousIntegralProcess_memLp_two T s f).integrable_mul
    ((continuousIntegralProcess_memLp_two T t f).sub (continuousIntegralProcess_memLp_two T s f))

private theorem integral_cross_condExp_zero (T s t : ℝ≥0) (hst : s ≤ t) (f : fullPredictableL2 T) :
    sourceLaw[continuousIntegralProcess T f s *
      (continuousIntegralProcess T f t-continuousIntegralProcess T f s) | naturalFiltration s] =ᵐ[sourceLaw]
      fun _ => 0 := by
  apply (condExp_mul_of_stronglyMeasurable_left (continuousIntegralProcess_stronglyAdapted T f s)
    (cross_integrable T s t f)
    (((continuousIntegralProcess_martingale T f).integrable t).sub
      ((continuousIntegralProcess_martingale T f).integrable s))).trans
  filter_upwards [integral_increment_condExp_zero T s t hst f] with ω hω
  simp only [Pi.mul_apply,hω,mul_zero]

private theorem integral_cross_setIntegral_zero (T s t : ℝ≥0) (hst : s ≤ t)
    (A : Set (ℝ≥0 → ℝ)) (hA : MeasurableSet[naturalFiltration s] A) (f : fullPredictableL2 T) :
    (∫ ω in A, continuousIntegralProcess T f s ω *
      (continuousIntegralProcess T f t ω-continuousIntegralProcess T f s ω) ∂sourceLaw) = 0 := by
  have hc := integral_cross_condExp_zero T s t hst f
  change (∫ ω in A, (continuousIntegralProcess T f s *
    (continuousIntegralProcess T f t-continuousIntegralProcess T f s)) ω ∂sourceLaw) = 0
  rw [← setIntegral_condExp (naturalFiltration.le s) (cross_integrable T s t f) hA,
    integral_congr_ae (ae_restrict_of_ae hc),integral_zero]

/-- The actual square increment on EACH permitted past event is its SAME
actual time-energy increment. Integrability is at L1; no fourth moments of f
or an externally supplied conditional variance are required. -/
theorem integral_square_increment_energy (T s t : ℝ≥0) (hst : s ≤ t)
    (A : Set (ℝ≥0 → ℝ)) (hA : MeasurableSet[naturalFiltration s] A) (f : fullPredictableL2 T) :
    (∫ ω in A, (continuousIntegralProcess T f t ω^2-continuousIntegralProcess T f s ω^2) ∂sourceLaw) =
      ∫ ω in A, (timeEnergy T f t ω-timeEnergy T f s ω) ∂sourceLaw := by
  have he : (fun ω => continuousIntegralProcess T f t ω^2-continuousIntegralProcess T f s ω^2) =
      (fun ω => (continuousIntegralProcess T f t ω-continuousIntegralProcess T f s ω)^2)+
        (fun ω => 2*(continuousIntegralProcess T f s ω *
          (continuousIntegralProcess T f t ω-continuousIntegralProcess T f s ω))) := by
    ext ω
    simp only [Pi.add_apply]
    ring
  have hd : Integrable (fun ω => (continuousIntegralProcess T f t ω-continuousIntegralProcess T f s ω)^2) sourceLaw :=
    ((continuousIntegralProcess_memLp_two T t f).sub (continuousIntegralProcess_memLp_two T s f)).integrable_sq
  rw [he]
  change (∫ ω in A, (continuousIntegralProcess T f t ω-continuousIntegralProcess T f s ω)^2+
    2*(continuousIntegralProcess T f s ω*(continuousIntegralProcess T f t ω-continuousIntegralProcess T f s ω)) ∂sourceLaw) = _
  rw [integral_add (f := fun ω => (continuousIntegralProcess T f t ω-continuousIntegralProcess T f s ω)^2)
    (g := fun ω => 2*(continuousIntegralProcess T f s ω*(continuousIntegralProcess T f t ω-continuousIntegralProcess T f s ω)))
    hd.integrableOn ((cross_integrable T s t f).const_mul 2).integrableOn,integral_const_mul,
    integral_cross_setIntegral_zero T s t hst A hA f,mul_zero,add_zero,
    localized_second_energy T s t hst A hA f,timeEnergy_increment_setIntegral T s t hst A hA f]

/-- ACTUAL compensated square: the SAME continuous integral process minus
its SAME literal time integral of the original input squared. -/
def compensatedIntegral (T : ℝ≥0) (f : fullPredictableL2 T) (s : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  continuousIntegralProcess T f s ω^2-timeEnergy T f s ω

theorem compensatedIntegral_stronglyAdapted (T : ℝ≥0) (f : fullPredictableL2 T) :
    StronglyAdapted naturalFiltration (compensatedIntegral T f) :=
  fun s => (continuousIntegralProcess_stronglyAdapted T f s).pow 2 |>.sub (timeEnergy_stronglyAdapted T f s)

theorem compensatedIntegral_integrable (T s : ℝ≥0) (f : fullPredictableL2 T) :
    Integrable (compensatedIntegral T f s) sourceLaw :=
  ((continuousIntegralProcess_memLp_two T s f).integrable_sq).sub (timeEnergy_integrable T s f)

theorem compensatedIntegral_setIntegral (T s t : ℝ≥0) (hst : s ≤ t)
    (A : Set (ℝ≥0 → ℝ)) (hA : MeasurableSet[naturalFiltration s] A) (f : fullPredictableL2 T) :
    (∫ ω in A, compensatedIntegral T f s ω ∂sourceLaw) =
      ∫ ω in A, compensatedIntegral T f t ω ∂sourceLaw := by
  have hs := (continuousIntegralProcess_memLp_two T s f).integrable_sq.integrableOn (s := A)
  have ht := (continuousIntegralProcess_memLp_two T t f).integrable_sq.integrableOn (s := A)
  have hEs := (timeEnergy_integrable T s f).integrableOn (s := A)
  have hEt := (timeEnergy_integrable T t f).integrableOn (s := A)
  have he := integral_square_increment_energy T s t hst A hA f
  rw [integral_sub ht hs,integral_sub hEt hEs] at he
  unfold compensatedIntegral
  rw [integral_sub hs hEs,integral_sub ht hEt]
  linarith

/-- Genuine same-source natural-filtration compensated-square MARTINGALE,
from proved conditional second energy and native condExp uniqueness. The
compensator/time-energy/martingale is never an input field. -/
theorem compensatedIntegral_martingale (T : ℝ≥0) (f : fullPredictableL2 T) :
    Martingale (compensatedIntegral T f) naturalFiltration sourceLaw := by
  refine ⟨compensatedIntegral_stronglyAdapted T f,?_⟩
  intro s t hst
  exact (ae_eq_condExp_of_forall_setIntegral_eq (naturalFiltration.le s)
    (compensatedIntegral_integrable T t f)
    (fun _ _ _ => (compensatedIntegral_integrable T s f).integrableOn)
    (fun A hA _ => compensatedIntegral_setIntegral T s t hst A hA f)
    (compensatedIntegral_stronglyAdapted T f s).aestronglyMeasurable).symm

/-- Actual zero-start consumer, retaining original continuous-integral version. -/
theorem compensatedIntegral_zero (T : ℝ≥0) (f : fullPredictableL2 T) :
    compensatedIntegral T f 0 =ᵐ[sourceLaw] fun _ => 0 := by
  filter_upwards [continuousIntegralProcess_zero T f] with ω hω
  simp only [compensatedIntegral,hω,zero_pow (by decide : (2 : ℕ) ≠ 0),timeEnergy_zero,Pi.zero_apply,sub_zero]

theorem compensatedIntegral_mean_zero (T s : ℝ≥0) (f : fullPredictableL2 T) :
    (∫ ω, compensatedIntegral T f s ω ∂sourceLaw) = 0 := by
  have h := (compensatedIntegral_martingale T f).setIntegral_eq (show (0 : ℝ≥0) ≤ s from bot_le) MeasurableSet.univ
  simp only [Measure.restrict_univ] at h
  rw [integral_congr_ae (compensatedIntegral_zero T f),integral_zero] at h
  exact h.symm

/-- ONE actual full-section Fubini event yields the time-energy's monotonicity
at EVERY pair of times. No uncountable AE intersection is taken. -/
theorem timeEnergy_monotone_ae (T : ℝ≥0) (f : fullPredictableL2 T) :
    ∀ᵐ ω ∂sourceLaw, Monotone (fun s => timeEnergy T f s ω) := by
  filter_upwards [(representative_memLp_two T f).integrable_sq.prod_left_ae] with ω hω
  intro s t hst
  simp_rw [timeEnergy_eq_setIntegral]
  apply setIntegral_mono_set hω.integrableOn (Eventually.of_forall (fun _ => sq_nonneg _))
  exact Eventually.of_forall (fun x hx => ⟨hx.1,hx.2.trans (by exact_mod_cast min_le_min_right T hst)⟩)

/-- Actual time-energy paths are continuous on ONE full-measure section event,
using native absolute-continuity/primitive analysis of the SAME time integral. -/
theorem timeEnergy_continuous_ae (T : ℝ≥0) (f : fullPredictableL2 T) :
    ∀ᵐ ω ∂sourceLaw, Continuous (fun s => timeEnergy T f s ω) := by
  filter_upwards [(representative_memLp_two T f).integrable_sq.prod_left_ae] with ω hω
  let : NullSingletonClass (timeLaw T) := by
    unfold timeLaw
    infer_instance
  have hc := hω.continuous_primitive (0 : ℝ)
  have ht : Continuous (fun s : ℝ≥0 => ((min s T : ℝ≥0) : ℝ)) :=
    continuous_subtype_val.comp (continuous_id.min continuous_const)
  convert hc.comp ht using 1
  ext s
  rw [Function.comp_apply,timeEnergy_eq_setIntegral,intervalIntegral.integral_of_le (min s T).coe_nonneg]

/-- The SAME actual compensated martingale has continuous source-a.e paths;
only two already derived full-measure events are intersected. -/
theorem compensatedIntegral_continuous_ae (T : ℝ≥0) (f : fullPredictableL2 T) :
    ∀ᵐ ω ∂sourceLaw, Continuous (fun s => compensatedIntegral T f s ω) := by
  filter_upwards [continuousIntegralProcess_continuous T f,timeEnergy_continuous_ae T f] with ω hM hA
  exact (hM.pow 2).sub hA

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralCompensator
