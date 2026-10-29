import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralContinuousVersion
import Mathlib.MeasureTheory.Function.Holder

/-!
Original commitment: actual L2 integral approximation must justify its squared outputs at the correct L1 scale.
Existing result: actual full predictable integration is continuous in native L2; native Holder multiplication is available.
Premise reduced: derive SAME-measure square-class continuity and the explicit L2-to-square-L1 error estimate.
Model/witness: one original measure throughout; instantiated by timeLaw T times sourceLaw and actual sourceLaw.
Consumer: actual time-energy and compensated-square martingale limits; no L2 bracket or fourth-moment assumption is inserted.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralSquareL1
open MeasureTheory ProbabilityTheory Filter
open BrownianProjectiveSource BrownianPredictableInputs BrownianIntegralTimeTruncation
open BrownianIntegralMartingale BrownianIntegralL2TimeContinuity BrownianIntegralContinuousVersion
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- Native Holder multiplication of the actual same L2 class by itself. -/
def squareClass (μ : Measure α) (f : Lp ℝ 2 μ) : Lp ℝ 1 μ :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL μ 2 2 1 f f

theorem squareClass_coe (μ : Measure α) (f : Lp ℝ 2 μ) :
    squareClass μ f =ᵐ[μ] fun a => f a ^ 2 := by
  simp only [squareClass,ContinuousLinearMap.holderL_apply_apply]
  simpa only [ContinuousLinearMap.mul_apply',← pow_two] using
    (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 1) f f

theorem continuous_squareClass (μ : Measure α) : Continuous (squareClass μ) :=
  ((ContinuousLinearMap.mul ℝ ℝ).holderL μ 2 2 1).continuous₂.comp (continuous_id.prodMk continuous_id)

/-- The actual square difference is the actual Holder product of difference
and sum, retaining the ORIGINAL same-measure representatives. -/
theorem squareClass_sub (μ : Measure α) (f g : Lp ℝ 2 μ) :
    squareClass μ f-squareClass μ g = (ContinuousLinearMap.mul ℝ ℝ).holderL μ 2 2 1 (f-g) (f+g) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (squareClass μ f) (squareClass μ g),squareClass_coe μ f,squareClass_coe μ g,
    (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 1) (f-g) (f+g),Lp.coeFn_sub f g,Lp.coeFn_add f g]
    with a hs hf hg hh hd ha
  simp only [Pi.sub_apply,Pi.add_apply,ContinuousLinearMap.mul_apply'] at *
  rw [hs,hf,hg]
  simp only [ContinuousLinearMap.holderL_apply_apply]
  rw [hh,hd,ha]
  ring

/-- Explicit natural-scale estimate; no L4 condition is needed. -/
theorem squareClass_sub_norm_le (μ : Measure α) (f g : Lp ℝ 2 μ) :
    ‖squareClass μ f-squareClass μ g‖ ≤ ‖f-g‖*(‖f‖+‖g‖) := by
  rw [squareClass_sub]
  have hh := (ContinuousLinearMap.mul ℝ ℝ).norm_holder_apply_apply_le (r := 1) (f-g) (f+g)
  calc
    _ ≤ ‖ContinuousLinearMap.mul ℝ ℝ‖*‖f-g‖*‖f+g‖ := hh
    _ ≤ 1*‖f-g‖*(‖f‖+‖g‖) := by
      gcongr
      · exact ContinuousLinearMap.opNorm_mul_le ℝ ℝ
      · exact norm_add_le f g
    _ = _ := by ring

theorem squareClass_tendsto (μ : Measure α) {l : Filter ℕ} {f : ℕ → Lp ℝ 2 μ} {g : Lp ℝ 2 μ}
    (h : Tendsto f l (𝓝 g)) : Tendsto (fun n => squareClass μ (f n)) l (𝓝 (squareClass μ g)) :=
  ((continuous_squareClass μ).tendsto g).comp h

/-- ACTUAL continuous integral square class, using its already proved actual
L2 membership; not an independently chosen stochastic output. -/
def actualSquareClass (T s : ℝ≥0) (f : fullPredictableL2 T) : Lp ℝ 1 sourceLaw :=
  ((continuousIntegralProcess_memLp_two T s f).integrable_sq).toL1
    (fun ω => continuousIntegralProcess T f s ω ^ 2)

theorem actualSquareClass_eq (T s : ℝ≥0) (f : fullPredictableL2 T) :
    actualSquareClass T s f = squareClass sourceLaw (integralClassProcess T f s) := by
  apply Lp.ext
  apply ((continuousIntegralProcess_memLp_two T s f).integrable_sq).coeFn_toL1.trans
  apply EventuallyEq.trans ?_ (squareClass_coe sourceLaw (integralClassProcess T f s)).symm
  exact ((continuousIntegralProcess_eq_actual T s f).trans
    (integralProcess_eq_truncated T s f)).mono (fun _ h => congrArg (fun x : ℝ => x^2) h)

/-- The actual continuous version's squared outputs converge in native L1
for EVERY original input L2 approximation, at each observation time. -/
theorem actualSquareClass_tendsto (T s : ℝ≥0) {f : ℕ → fullPredictableL2 T} {g : fullPredictableL2 T}
    (h : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun n => actualSquareClass T s (f n)) atTop (𝓝 (actualSquareClass T s g)) := by
  simp_rw [actualSquareClass_eq]
  exact squareClass_tendsto sourceLaw (((integralAt T s).continuous.tendsto g).comp h)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralSquareL1
