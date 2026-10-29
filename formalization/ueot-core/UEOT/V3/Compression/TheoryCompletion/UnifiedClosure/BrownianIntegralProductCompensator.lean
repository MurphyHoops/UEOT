import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralCrossVariation
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralCompensator

/-!
Original commitment: actual product integral processes need SAME-source cross-energy compensators, derived rather than supplied.
Existing result: actual dt product crossEnergy, scalar square compensator and actual full-input linear integration.
Premise reduced: derive true natural-past adaptedness and integrable martingale of SAME Mf*Mg minus SAME actual dt integral f*g.
Model/witness: SAME original fullPredictableL2 T pair/sourceLaw/naturalFiltration/continuous versions, natural L1 only.
Consumer: actual integration-by-parts/C2 cross source; not a general Ito/Girsanov or arbitrary filtered/vector construction.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralProductCompensator
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianTimeIntegrand BrownianPredictableInputs
open BrownianIntegralTimeTruncation BrownianIntegralMartingale BrownianIntegralContinuousVersion
open BrownianIntegralTimeEnergy BrownianIntegralEnergyL1 BrownianIntegralCompensator BrownianIntegralCrossVariation
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Actual fixed-time linearity of the SAME continuous versions, derived from
original continuous linear integral classes; no common uncountable AE intersection. -/
theorem continuousIntegralProcess_add_ae (T u : ℝ≥0) (f g : fullPredictableL2 T) :
    continuousIntegralProcess T (f+g) u =ᵐ[sourceLaw]
      fun ω => continuousIntegralProcess T f u ω+continuousIntegralProcess T g u ω := by
  have ha := Lp.coeFn_add (integralAt T u f) (integralAt T u g)
  have hs : integralAt T u (f+g) = integralAt T u f+integralAt T u g := map_add _ _ _
  have hf (h : fullPredictableL2 T) : continuousIntegralProcess T h u =ᵐ[sourceLaw]
      (integralAt T u h : (ℝ≥0 → ℝ) → ℝ) :=
    (continuousIntegralProcess_eq_actual T u h).trans (integralProcess_eq_truncated T u h)
  rw [← hs] at ha
  filter_upwards [hf (f+g),hf f,hf g,ha] with ω hh hf hg ha
  exact hh.trans (ha.trans (congrArg₂ (fun x y : ℝ => x+y) hf.symm hg.symm))

theorem continuousIntegralProcess_sub_ae (T u : ℝ≥0) (f g : fullPredictableL2 T) :
    continuousIntegralProcess T (f-g) u =ᵐ[sourceLaw]
      fun ω => continuousIntegralProcess T f u ω-continuousIntegralProcess T g u ω := by
  have ha := Lp.coeFn_sub (integralAt T u f) (integralAt T u g)
  have hs : integralAt T u (f-g) = integralAt T u f-integralAt T u g := map_sub _ _ _
  have hf (h : fullPredictableL2 T) : continuousIntegralProcess T h u =ᵐ[sourceLaw]
      (integralAt T u h : (ℝ≥0 → ℝ) → ℝ) :=
    (continuousIntegralProcess_eq_actual T u h).trans (integralProcess_eq_truncated T u h)
  rw [← hs] at ha
  filter_upwards [hf (f-g),hf f,hf g,ha] with ω hh hf hg ha
  exact hh.trans (ha.trans (congrArg₂ (fun x y : ℝ => x-y) hf.symm hg.symm))

/-- Original predictable inclusion gives genuine Fs permission for the real
cross integrand; proof-only clipping never changes its active support. -/
theorem crossEnergyIntegrand_stronglyMeasurable_past (T s : ℝ≥0) (f g : fullPredictableL2 T) :
    StronglyMeasurable[MeasurableSpace.prod inferInstance (naturalFiltration s)] (crossEnergyIntegrand T s f g) := by
  let : MeasurableSpace (ℝ≥0 → ℝ) := naturalFiltration s
  let clip (t : ℝ) : Iic s := ⟨min (Real.toNNReal t) (min s T),by
    exact (min_le_right (Real.toNNReal t) (min s T)).trans (min_le_left s T)⟩
  have hc : Measurable clip := (measurable_id.real_toNNReal.min measurable_const).subtype_mk
  have hm (h : fullPredictableL2 T) : StronglyMeasurable (fun p : ℝ × (ℝ≥0 → ℝ) =>
      representative T h (((clip p.1 : ℝ≥0) : ℝ),p.2)) :=
    ((representative_native_predictable T h).isStronglyProgressive s).comp_measurable
      ((hc.comp measurable_fst).prodMk measurable_snd)
  have ht : MeasurableSet (timeSet T s) := measurableSet_Ioc.prod MeasurableSet.univ
  have he : crossEnergyIntegrand T s f g = (timeSet T s).indicator
      (fun p : ℝ × (ℝ≥0 → ℝ) => representative T f (((clip p.1 : ℝ≥0) : ℝ),p.2)*
        representative T g (((clip p.1 : ℝ≥0) : ℝ),p.2)) := by
    ext p
    by_cases hp : p ∈ timeSet T s
    · rw [crossEnergyIntegrand,Set.indicator_of_mem hp,Set.indicator_of_mem hp]
      have hn : Real.toNNReal p.1 ≤ min s T := (Real.toNNReal_le_iff_le_coe).mpr hp.1.2
      have heq : ((clip p.1 : ℝ≥0) : ℝ) = p.1 := by
        change ((min (Real.toNNReal p.1) (min s T) : ℝ≥0) : ℝ) = p.1
        rw [min_eq_left hn,Real.coe_toNNReal _ hp.1.1.le]
      rw [heq]
    · simp only [crossEnergyIntegrand,Set.indicator_of_notMem hp]
  rw [he]
  exact ((hm f).mul (hm g)).indicator ht

theorem crossTimeEnergy_stronglyAdapted (T : ℝ≥0) (f g : fullPredictableL2 T) :
    StronglyAdapted naturalFiltration (crossTimeEnergy T f g) := by
  intro s
  let : MeasurableSpace (ℝ≥0 → ℝ) := naturalFiltration s
  exact (crossEnergyIntegrand_stronglyMeasurable_past T s f g).integral_prod_left'

theorem crossTimeEnergy_polarization (T s : ℝ≥0) (f g : fullPredictableL2 T) :
    crossTimeEnergy T f g s =ᵐ[sourceLaw]
      fun ω => (1/4 : ℝ)*(timeEnergy T (f+g) s ω-timeEnergy T (f-g) s ω) := by
  have he := crossEnergyClass_polarization T s f g
  have hc := Lp.coeFn_smul (1/4 : ℝ) (energyClass T s (f+g)-energyClass T s (f-g))
  rw [← he] at hc
  filter_upwards [hc,crossEnergyClass_coe T s f g,
    Lp.coeFn_sub (energyClass T s (f+g)) (energyClass T s (f-g)),
    energyClass_coe T s (f+g),energyClass_coe T s (f-g)] with ω hc hx hs ha hb
  simp only [Pi.smul_apply,smul_eq_mul,Pi.sub_apply] at hc hs
  rw [hx,hs,ha,hb] at hc
  exact hc

/-- The actual SAME two integral outputs minus actual SAME dt product energy. -/
def compensatedProduct (T : ℝ≥0) (f g : fullPredictableL2 T) (s : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  continuousIntegralProcess T f s ω*continuousIntegralProcess T g s ω-crossTimeEnergy T f g s ω

theorem compensatedProduct_stronglyAdapted (T : ℝ≥0) (f g : fullPredictableL2 T) :
    StronglyAdapted naturalFiltration (compensatedProduct T f g) :=
  fun s => ((continuousIntegralProcess_stronglyAdapted T f s).mul
    (continuousIntegralProcess_stronglyAdapted T g s)).sub (crossTimeEnergy_stronglyAdapted T f g s)

theorem compensatedProduct_polarization (T s : ℝ≥0) (f g : fullPredictableL2 T) :
    compensatedProduct T f g s =ᵐ[sourceLaw]
      fun ω => (1/4 : ℝ)*(compensatedIntegral T (f+g) s ω-compensatedIntegral T (f-g) s ω) := by
  filter_upwards [continuousIntegralProcess_add_ae T s f g,continuousIntegralProcess_sub_ae T s f g,
    crossTimeEnergy_polarization T s f g] with ω ha hs hc
  simp only [compensatedProduct,compensatedIntegral,ha,hs,hc]
  ring

/-- Actual product compensation is an original natural-filtration integrable
martingale, with no L4 assumption and no external product/bracket certificate. -/
theorem compensatedProduct_martingale (T : ℝ≥0) (f g : fullPredictableL2 T) :
    Martingale (compensatedProduct T f g) naturalFiltration sourceLaw := by
  have hm := ((compensatedIntegral_martingale T (f+g)).sub
    (compensatedIntegral_martingale T (f-g))).smul (1/4 : ℝ)
  apply hm.congr (compensatedProduct_stronglyAdapted T f g)
  intro s
  exact (compensatedProduct_polarization T s f g).symm

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralProductCompensator
