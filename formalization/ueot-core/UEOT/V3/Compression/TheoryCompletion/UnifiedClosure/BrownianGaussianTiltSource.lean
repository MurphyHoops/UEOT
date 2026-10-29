import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianMartingaleSource

/-!
Original commitment: normalized density alone does not prove a shifted Brownian/change-of-integrator source.
Existing result: SAME actual Brownian process, explicit exponentialProcess and normalized tiltedLaw on original path space.
Premise reduced: derive actual Gaussian exponential tilt and SAME terminal Brownian/shifted-noise law under that actual measure.
Model/witness: every real u, every nonnegative T including zero; actual nonzero u and original sourceLaw, no alternative measure chosen.
Consumer: constant-control finite-increment Girsanov source; whole shifted-process independence and general predictable control remain separate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianGaussianTiltSource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- The literal exponential weighting used by the SAME terminal source. -/
def gaussianTiltWeight (u : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (u*x-u^2*(v : ℝ)/2))

/-- Completing the square identifies the actual tilted Gaussian law,
including the zero-variance Dirac boundary. -/
theorem gaussian_exponential_tilt (u : ℝ) (v : ℝ≥0) :
    (gaussianReal 0 v).withDensity (gaussianTiltWeight u v) = gaussianReal (u*(v : ℝ)) v := by
  by_cases hv : v=0
  · subst v
    rw [gaussianReal_zero_var,dirac_withDensity]
    simp [gaussianTiltWeight]
  · rw [gaussianReal_of_var_ne_zero _ hv,gaussianReal_of_var_ne_zero _ hv,
      ← withDensity_mul volume (measurable_gaussianPDF 0 v) (by unfold gaussianTiltWeight; fun_prop)]
    congr 1
    funext x
    change ENNReal.ofReal (gaussianPDFReal 0 v x)*ENNReal.ofReal (Real.exp (u*x-u^2*(v : ℝ)/2)) =
      ENNReal.ofReal (gaussianPDFReal (u*(v : ℝ)) v x)
    rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 v x)]
    congr 1
    unfold gaussianPDFReal
    rw [mul_assoc,← Real.exp_add]
    congr 2
    have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    field_simp [hvR]
    ring

/-- Pushforward of a density that is a literal function of the SAME readout.
This is a measure identity, with no solver or output-law hypothesis. -/
theorem map_readout_density {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] (P : Measure Ω)
    (X : Ω → E) (hX : Measurable X) (w : E → ℝ≥0∞) (hw : Measurable w) :
    (P.withDensity (fun ω => w (X ω))).map X = (P.map X).withDensity w := by
  ext A hA
  rw [Measure.map_apply hX hA,withDensity_apply _ (hX hA),withDensity_apply _ hA]
  rw [← lintegral_indicator (hX hA),← lintegral_indicator hA,
    lintegral_map (hw.indicator hA) hX]
  apply lintegral_congr
  intro ω
  rfl

/-- SAME actual terminal readout under the SAME earlier constructed
normalized exponential change of measure, with its actual shifted mean. -/
theorem terminal_hasLaw_tilted (u : ℝ) (T : ℝ≥0) :
    HasLaw (process T) (gaussianReal (u*(T : ℝ)) T) (tiltedLaw u T) := by
  refine ⟨(measurable_process T).aemeasurable,?_⟩
  change (sourceLaw.withDensity (fun ω => gaussianTiltWeight u T (process T ω))).map (process T) = _
  rw [map_readout_density sourceLaw (process T) (measurable_process T) (gaussianTiltWeight u T)
    (by unfold gaussianTiltWeight; fun_prop),(process_isPreBrownian.hasLaw_eval T).map_eq]
  exact gaussian_exponential_tilt u T

/-- The actual centered terminal noise has the original variance, under
that actual changed measure. This is a terminal source result only. -/
theorem shifted_terminal_hasLaw (u : ℝ) (T : ℝ≥0) :
    HasLaw (fun ω => process T ω-u*(T : ℝ)) (gaussianReal 0 T) (tiltedLaw u T) := by
  simpa only [sub_self] using gaussianReal_sub_const (terminal_hasLaw_tilted u T) (u*(T : ℝ))

/-- Actual tilted terminal mean is shifted by the supplied control. -/
theorem tilted_terminal_mean (u : ℝ) (T : ℝ≥0) :
    (∫ ω, process T ω ∂tiltedLaw u T) = u*(T : ℝ) := by
  have h := (terminal_hasLaw_tilted u T).integral_comp (f := id) (by fun_prop)
  simpa only [Function.id_comp,id_eq,integral_id_gaussianReal] using h

/-- Genuine centered terminal noise retains Brownian variance. -/
theorem shifted_terminal_mean (u : ℝ) (T : ℝ≥0) :
    (∫ ω, (process T ω-u*(T : ℝ)) ∂tiltedLaw u T) = 0 := by
  have h := (shifted_terminal_hasLaw u T).integral_comp (f := id) (by fun_prop)
  simpa only [Function.id_comp,id_eq,integral_id_gaussianReal] using h

theorem shifted_terminal_second_moment (u : ℝ) (T : ℝ≥0) :
    (∫ ω, (process T ω-u*(T : ℝ))^2 ∂tiltedLaw u T) = (T : ℝ) := by
  have h := variance_id_gaussianReal (μ := 0) (v := T)
  rw [variance_eq_integral measurable_id.aemeasurable] at h
  have hs := (shifted_terminal_hasLaw u T).integral_comp (f := fun x => x^2) (by fun_prop)
  exact hs.trans (by simpa only [id_eq,integral_id_gaussianReal,sub_zero] using h)

/-- Literal constant-control change-of-integrator identity at the actual
terminal time. This does not supply a whole shifted-Brownian hypothesis. -/
theorem constant_terminal_integral_shift (u : ℝ) (T : ℝ≥0) (ω : ℝ≥0 → ℝ) :
    u*process T ω = u*(process T ω-u*(T : ℝ))+u^2*(T : ℝ) := by ring

/-- Zero-horizon density is the original actual measure, by the actual
zero-time readout on its source full-measure event. -/
theorem tiltedLaw_zero (u : ℝ) : tiltedLaw u 0 = sourceLaw := by
  have he : (fun ω => ENNReal.ofReal (exponentialProcess u 0 ω)) =ᵐ[sourceLaw] (1 : (ℝ≥0 → ℝ) → ℝ≥0∞) := by
    filter_upwards [process_zero] with ω hω
    change ENNReal.ofReal (Real.exp (u*process 0 ω-u^2*(0 : ℝ)/2))=1
    simp [hω]
  rw [tiltedLaw,withDensity_congr_ae he,withDensity_one]

theorem tiltedLaw_zero_control (T : ℝ≥0) : tiltedLaw 0 T = sourceLaw := by
  have he : (fun ω => ENNReal.ofReal (exponentialProcess 0 T ω)) = (1 : (ℝ≥0 → ℝ) → ℝ≥0∞) := by
    funext ω
    change ENNReal.ofReal (Real.exp (0*process T ω-0^2*(T : ℝ)/2))=1
    simp
  rw [tiltedLaw,he,withDensity_one]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianGaussianTiltSource
