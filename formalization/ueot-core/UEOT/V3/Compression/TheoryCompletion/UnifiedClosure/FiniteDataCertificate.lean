import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataControl
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataCalibration
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataConditioned
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataObstacles
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataSource
open MeasureTheory UEOT.V3.PathError UEOT.V3.TotalVariation
open UEOT.V3.FiniteDiscountedControl UEOT.V3.CoreOperationalAssembly
open FiniteActionRealizabilityCheck ConditionedActionTransportCheck FiniteDataPathBounds
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2000000

def budget (estimate : Param) (T : ℕ) : ℝ :=
  min 1 (FiniteDataNumericalBounds.prepBudget T (max estimate.e0 estimate.e1)
    (estimate.r0+estimate.r1))

theorem target_stability (p : Param) (hp : Admissible p) (estimate : Param)
    (he : Admissible estimate) (T : ℕ) (hT : 0 < T) (d : ℝ) (hg : Good p estimate d) :
    tvDist (target p hp T).toMeasure (target estimate he T).toMeasure ≤
      min 1 ((T : ℝ)*d/(estimate.r0+estimate.r1)) := by
  have hs := add_pos hp.1 hp.2.2.1
  have hsh := add_pos he.1 he.2.2.1
  have h0 : |estimate.r0-p.r0| ≤ d := by
    simpa [Good,probeParameter,abs_sub_comm] using hg 0
  have h1 : |estimate.r1-p.r1| ≤ d := by
    simpa [Good,probeParameter,abs_sub_comm] using hg 1
  have hnu : tvDist (nu p hp).toMeasure (nu estimate he).toMeasure ≤
      d/(estimate.r0+estimate.r1) := by
    rw [nu,nu,FiniteDataCalibration.safePMF_tv]
    exact FiniteDataNumericalBounds.normalized_tilt_error hp.1.le hp.2.2.1.le hs hsh h0 h1
  apply le_min (tvDist_le_one _ _)
  have h := rank_one_path_tv_le (nu p hp) (nu estimate he) fair T hT
  have heq (q : Param) (hq : Admissible q) :
      target q hq T = rankOnePath (nu q hq) fair T := by
    simp only [target,if_neg (Nat.ne_of_gt hT),rankOnePath]
    rfl
  rw [heq p hp,heq estimate he]
  exact (h.trans (min_le_right _ _)).trans (by
    simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left hnu (Nat.cast_nonneg T))

/-- Data do not expose Good or true parameters: this universal theorem proves
what the computed budget entails whenever the shared scalar calibration holds.
The noisy preparation contributes its own entire failure mass. -/
theorem statistical_approximation (p : Param) (hp : Admissible p) (estimate : Param)
    (he : Admissible estimate) (T : ℕ) (hT : 0 < T)
    (hg : Good p estimate (1/250)) :
    tvDist (deployed p hp estimate he T).toMeasure (target p hp T).toMeasure ≤
      budget estimate T := by
  have he0 : p.e0 ≤ estimate.e0+1/250 := by
    have h := (abs_le.mp (hg 2)).2
    linarith [show p.e0-estimate.e0 ≤ 1/250 from by simpa [probeParameter] using h]
  have he1 : p.e1 ≤ estimate.e1+1/250 := by
    have h := (abs_le.mp (hg 3)).2
    linarith [show p.e1-estimate.e1 ≤ 1/250 from by simpa [probeParameter] using h]
  have hemax : max p.e0 p.e1 ≤ max estimate.e0 estimate.e1+1/250 := by
    apply max_le
    · linarith [le_max_left estimate.e0 estimate.e1]
    · linarith [le_max_right estimate.e0 estimate.e1]
  apply le_min (tvDist_le_one _ _)
  have hc := (deployed_reference_bound p hp estimate he T hT).trans (min_le_right _ _)
  have ht := (target_stability p hp estimate he T hT (1/250) hg).trans (min_le_right _ _)
  have hsym : tvDist (target estimate he T).toMeasure (target p hp T).toMeasure =
      tvDist (target p hp T).toMeasure (target estimate he T).toMeasure :=
    by rw [tvDist_eq_one_sub_pmfCommonMass,tvDist_eq_one_sub_pmfCommonMass]
       simp [pmfCommonMass,min_comm]
  have htri := UEOT.V3.TransportDefect.tvDist_triangle
    (deployed p hp estimate he T).toMeasure (target estimate he T).toMeasure (target p hp T).toMeasure
  rw [hsym] at htri
  have h := htri.trans (add_le_add hc ht)
  change _ ≤ FiniteDataNumericalBounds.prepBudget T (max estimate.e0 estimate.e1) _
  dsimp [FiniteDataNumericalBounds.prepBudget]
  have hm := mul_le_mul_of_nonneg_left hemax (by positivity : 0 ≤ (T : ℝ)+1)
  calc
    _ ≤ ((T : ℝ)+1)*max p.e0 p.e1 + (T : ℝ)*(1/250)/(estimate.r0+estimate.r1) := h
    _ ≤ ((T : ℝ)+1)*(max estimate.e0 estimate.e1+1/250) +
        (T : ℝ)*(1/250)/(estimate.r0+estimate.r1) := add_le_add hm le_rfl
    _ = _ := by push_cast; ring

/-- The target in the statistical certificate is the original source's own
conditioned baseline experiment, not a separately stipulated reference law. -/
theorem statistical_actual_conditioned_path (p : Param) (hp : Admissible p)
    (estimate : Param) (he : Admissible estimate) (T : ℕ) (hT : 0 < T)
    (hg : Good p estimate (1/250)) :
    tvDist (deployed p hp estimate he T).toMeasure
      (SameSourceFiniteWindowCheck.actualConditionedPrefix (model p hp) observe baseline initial
        FiniteDataConditioned.safe T 0 (FiniteDataConditioned.source_positive p hp T)).toMeasure ≤
      budget estimate T := by
  rw [← FiniteDataConditioned.target_eq_actual p hp T]
  exact statistical_approximation p hp estimate he T hT hg

/-- Exact zero-noise recovery is a zero path-error theorem, while the noisy
main consumer keeps an APPROX budget and never asserts path equality. -/
theorem zero_noise_path_error (p : Param) (hp : Admissible p) (T : ℕ) (hT : 0 < T)
    (h0 : p.e0=0) (h1 : p.e1=0) :
    tvDist (deployed p hp p hp T).toMeasure (target p hp T).toMeasure = 0 := by
  apply le_antisymm
  · have h := deployed_reference_bound p hp p hp T hT
    simpa only [h0,h1,max_self,mul_zero,min_eq_right (by norm_num : (0:ℝ)≤1)] using h
  · exact tvDist_nonneg _ _

/-- Exact recovery retains equality of the same returned zero-noise process. -/
theorem zero_noise_path_eq (p : Param) (hp : Admissible p) (T : ℕ) (hT : 0<T)
    (h0 : p.e0=0) (h1 : p.e1=0) : deployed p hp p hp T = target p hp T := by
  have h := zero_noise_path_error p hp T hT h0 h1
  rw [UEOT.V3.FiniteRecurrentDecompositionStability.pmf_tv_eq_half_sum_abs] at h
  apply PMF.ext
  intro x
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  apply sub_eq_zero.mp
  apply abs_eq_zero.mp
  have hi : |(deployed p hp p hp T x).toReal - (target p hp T x).toReal| ≤
      ∑ z, |(deployed p hp p hp T z).toReal - (target p hp T z).toReal| :=
    Finset.single_le_sum (f := fun z : CausalHistory State State T =>
      |(deployed p hp p hp T z).toReal - (target p hp T z).toReal|)
      (fun z _ => abs_nonneg _) (Finset.mem_univ x)
  exact le_antisymm (by linarith) (abs_nonneg _)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataSource
