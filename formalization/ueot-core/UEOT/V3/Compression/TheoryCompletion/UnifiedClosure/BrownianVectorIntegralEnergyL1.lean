import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorIntegralTimeEnergy

/-!
Original commitment: actual vector full-input QV must compare SAME pathwise dt energies at natural L1, without a hidden fourth-moment premise.
Existing result: genuine Euclidean timeEnergy/Fubini and original joint-source full-input L2/grid stability.
Premise reduced: native real inner-product Holder and original time marginal derive uniform L2-to-energy-L1 stability.
Model: SAME timeLaw T times productLaw d, same full joint-predictable Euclidean inputs and cutoff, including d0/T0.
Consumer: full-input QV extension from actual finite inputs; this stability result is not a QV/Itô certificate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorIntegralEnergyL1
open MeasureTheory ProbabilityTheory Set Filter
open BrownianFiniteProductSource BrownianVectorTimeInput BrownianVectorIntegralClosure
open BrownianVectorPredictableInputs BrownianVectorPredictableDensity BrownianVectorIntegralTimeSource
open BrownianVectorIntegralTimeEnergy
open BrownianTimeIntegrand (timeLaw)
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

section NativeNormSquare
variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Native same-measure Holder inner product, including the zero-dimensional
Hilbert space. No custom tensor/norm quotient is introduced. -/
def normSquareClass (μ : Measure α) (f : Lp E 2 μ) : Lp ℝ 1 μ :=
  (innerSL ℝ (E := E)).holderL μ 2 2 1 f f

theorem normSquareClass_coe (μ : Measure α) (f : Lp E 2 μ) :
    normSquareClass μ f =ᵐ[μ] fun a => ‖f a‖^2 := by
  simp only [normSquareClass,ContinuousLinearMap.holderL_apply_apply]
  apply ((innerSL ℝ (E := E)).coeFn_holder (r := 1) f f).trans
  exact ae_of_all μ (fun a => real_inner_self_eq_norm_sq (f a))

theorem normSquareClass_sub (μ : Measure α) (f g : Lp E 2 μ) :
    normSquareClass μ f-normSquareClass μ g =
      (innerSL ℝ (E := E)).holderL μ 2 2 1 (f-g) (f+g) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (normSquareClass μ f) (normSquareClass μ g),
    normSquareClass_coe μ f,normSquareClass_coe μ g,
    (innerSL ℝ (E := E)).coeFn_holder (r := 1) (f-g) (f+g),Lp.coeFn_sub f g,Lp.coeFn_add f g]
      with a hs hf hg hh hd ha
  simp only [Pi.sub_apply,Pi.add_apply] at *
  rw [hs,hf,hg]
  simp only [ContinuousLinearMap.holderL_apply_apply]
  rw [hh,hd,ha]
  change ‖f a‖^2-‖g a‖^2=inner ℝ (f a-g a) (f a+g a)
  rw [inner_sub_left,inner_add_right,inner_add_right,
    real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,real_inner_comm (g a) (f a)]
  ring

/-- Natural L2-to-norm-square-L1 estimate uses no L4 input restriction. -/
theorem normSquareClass_sub_norm_le (μ : Measure α) (f g : Lp E 2 μ) :
    ‖normSquareClass μ f-normSquareClass μ g‖≤‖f-g‖*(‖f‖+‖g‖) := by
  rw [normSquareClass_sub]
  have hh := (innerSL ℝ (E := E)).norm_holder_apply_apply_le (r := 1) (f-g) (f+g)
  calc
    _ ≤ ‖innerSL ℝ (E := E)‖*‖f-g‖*‖f+g‖ := hh
    _ ≤ 1*‖f-g‖*(‖f‖+‖g‖) := by
      gcongr
      · exact norm_innerSL_le ℝ
      · exact norm_add_le f g
    _ = _ := by ring
end NativeNormSquare

variable (d : ℕ)

private theorem lp1_norm_integral {α : Type*} [MeasurableSpace α] (μ : Measure α) (g : Lp ℝ 1 μ) :
    ‖g‖ = ∫ a, ‖g a‖ ∂μ := by
  rw [L1.norm_def,integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable g)]

/-- Actual scalar time marginal, before deriving its native linear bound. -/
private def marginalValue (T : ℝ≥0) (g : Lp ℝ 1 (inputLaw d T)) : Lp ℝ 1 (productLaw d) :=
  ((L1.integrable_coeFn g).integral_prod_right).toL1 (fun ω => ∫ t, g (t,ω) ∂timeLaw T)

private theorem marginalValue_coe (T : ℝ≥0) (g : Lp ℝ 1 (inputLaw d T)) :
    marginalValue d T g =ᵐ[(productLaw d)] (fun ω => ∫ t, g (t,ω) ∂timeLaw T) :=
  ((L1.integrable_coeFn g).integral_prod_right).coeFn_toL1

private theorem section_eq {g h : ℝ × (Sample d) → ℝ} (he : g =ᵐ[inputLaw d T] h) :
    ∀ᵐ ω ∂(productLaw d), (fun t => g (t,ω)) =ᵐ[timeLaw T] fun t => h (t,ω) :=
  Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := (productLaw d)) (ν := timeLaw T)).quasiMeasurePreserving.ae he)

private def marginalLinear (T : ℝ≥0) : Lp ℝ 1 (inputLaw d T) →ₗ[ℝ] Lp ℝ 1 (productLaw d) where
  toFun := marginalValue d T
  map_add' g h := by
    apply Lp.ext
    have he := section_eq d (Lp.coeFn_add g h)
    filter_upwards [marginalValue_coe d T (g+h),Lp.coeFn_add (marginalValue d T g) (marginalValue d T h),
      marginalValue_coe d T g,marginalValue_coe d T h,he,
      (L1.integrable_coeFn g).prod_left_ae,(L1.integrable_coeFn h).prod_left_ae]
      with ω hm hs hg hh he ig ih
    simp only [Pi.add_apply] at hs he
    rw [hm,hs,hg,hh]
    exact (integral_congr_ae he).trans (integral_add ig ih)
  map_smul' c g := by
    apply Lp.ext
    have he := section_eq d (Lp.coeFn_smul c g)
    filter_upwards [marginalValue_coe d T (c • g),Lp.coeFn_smul c (marginalValue d T g),
      marginalValue_coe d T g,he] with ω hm hs hg he
    simp only [Pi.smul_apply,smul_eq_mul] at hs he
    simp only [RingHom.id_apply]
    rw [hm,hs,hg,integral_congr_ae he,integral_const_mul]

private theorem marginalValue_bound (T : ℝ≥0) (g : Lp ℝ 1 (inputLaw d T)) : ‖marginalValue d T g‖ ≤ ‖g‖ := by
  calc
    _ = ∫ ω, ‖∫ t, g (t,ω) ∂timeLaw T‖ ∂(productLaw d) := by
      rw [lp1_norm_integral]
      exact integral_congr_ae ((marginalValue_coe d T g).mono (fun _ h => congrArg norm h))
    _ ≤ ∫ ω, ∫ t, ‖g (t,ω)‖ ∂timeLaw T ∂(productLaw d) :=
      integral_mono (L1.integrable_coeFn g).integral_prod_right.norm
        (L1.integrable_coeFn g).integral_norm_prod_right (fun _ => norm_integral_le_integral_norm _)
    _ = ∫ p, ‖g p‖ ∂inputLaw d T :=
      (integral_prod_symm (fun p => ‖g p‖) (L1.integrable_coeFn g).norm).symm
    _ = _ := (lp1_norm_integral _ _).symm

/-- Native CLM constructed from the actual original-time integral and proved
contraction; no desired marginal/transport certificate is supplied. -/
def timeMarginal (T : ℝ≥0) : Lp ℝ 1 (inputLaw d T) →L[ℝ] Lp ℝ 1 (productLaw d) :=
  (marginalLinear d T).mkContinuous 1 (fun g => by
    change ‖marginalValue d T g‖ ≤ 1*‖g‖
    simpa only [one_mul] using marginalValue_bound d T g)

theorem timeMarginal_coe (T : ℝ≥0) (g : Lp ℝ 1 (inputLaw d T)) :
    timeMarginal d T g =ᵐ[(productLaw d)] (fun ω => ∫ t, g (t,ω) ∂timeLaw T) := marginalValue_coe d T g

theorem timeMarginal_norm_le (T : ℝ≥0) (g : Lp ℝ 1 (inputLaw d T)) : ‖timeMarginal d T g‖ ≤ ‖g‖ :=
  marginalValue_bound d T g


/-- Native source L1 class of SAME actual Euclidean dt energy. -/
def energyClass (T s : ℝ≥0) (f : fullPredictableL2 d T) : Lp ℝ 1 (productLaw d) :=
  (timeEnergy_integrable d T s f).toL1 (timeEnergy d T f s)

theorem energyClass_coe (T s : ℝ≥0) (f : fullPredictableL2 d T) :
    energyClass d T s f =ᵐ[productLaw d] timeEnergy d T f s :=
  (timeEnergy_integrable d T s f).coeFn_toL1

/-- SAME cutoff norm-square and literal time marginal derive energy identity;
no desired energy-transport field is supplied. -/
theorem energyClass_eq_marginal_normSquare (T s : ℝ≥0) (f : fullPredictableL2 d T) :
    energyClass d T s f = timeMarginal d T (normSquareClass (inputLaw d T)
      (truncate d T s f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T))) := by
  have he : normSquareClass (inputLaw d T)
      (truncate d T s f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) =ᵐ[inputLaw d T]
        energyIntegrand d T s f := by
    filter_upwards [normSquareClass_coe (inputLaw d T)
      (truncate d T s f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)),
      truncate_coe d T s f,representative_ae d T f] with p hsq htr hf
    rw [hsq,htr]
    by_cases h : p∈timeSet d T s <;> simp [energyIntegrand,h,hf]
  have hi : (fun ω => ∫ t, normSquareClass (inputLaw d T)
      (truncate d T s f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) (t,ω) ∂timeLaw T)
        =ᵐ[productLaw d] timeEnergy d T f s := (section_eq d he).mono (fun _ h => integral_congr_ae h)
  apply Lp.ext
  exact (energyClass_coe d T s f).trans
    ((timeMarginal_coe d T (normSquareClass (inputLaw d T)
      (truncate d T s f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)))).trans hi).symm

/-- Grid-independent/time-uniform natural-L1 energy stability at original L2
scale. No fourth moment nor a source-provided bracket is assumed. -/
theorem energyClass_sub_norm_le (T s : ℝ≥0) (f g : fullPredictableL2 d T) :
    ‖energyClass d T s f-energyClass d T s g‖ ≤ ‖f-g‖*(‖f‖+‖g‖) := by
  rw [energyClass_eq_marginal_normSquare,energyClass_eq_marginal_normSquare,← map_sub]
  apply (timeMarginal_norm_le d T _).trans
  apply (normSquareClass_sub_norm_le (inputLaw d T)
    (truncate d T s f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T))
    (truncate d T s g : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T))).trans
  have hd : ‖(truncate d T s f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T))-
      (truncate d T s g : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T))‖ ≤ ‖f-g‖ := by
    change ‖truncate d T s f-truncate d T s g‖ ≤ ‖f-g‖
    rw [← map_sub]
    exact truncate_norm_le d T s (f-g)
  exact mul_le_mul hd (add_le_add (truncate_norm_le d T s f) (truncate_norm_le d T s g))
    (by positivity) (norm_nonneg _)

/-- Every original full-input L2 approximation converges in the actual SAME
dt-energy source L1 class at each observation time. -/
theorem energyClass_tendsto (T s : ℝ≥0) {f : ℕ → fullPredictableL2 d T} {g : fullPredictableL2 d T}
    (h : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun n=>energyClass d T s (f n)) atTop (𝓝 (energyClass d T s g)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hd : Tendsto (fun n=>‖f n-g‖) atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero] using (h.sub (tendsto_const_nhds (x := g))).norm
  have hb : Tendsto (fun n=>‖f n-g‖*(‖f n‖+‖g‖)) atTop (𝓝 0) := by
    simpa only [zero_mul] using hd.mul (h.norm.add tendsto_const_nhds)
  exact squeeze_zero (fun _=>norm_nonneg _) (fun n=>energyClass_sub_norm_le d T s (f n) g) hb

/-- The same energy convergence concerns the ACTUAL pathwise time integral,
not only a separately selected L1 class representative. -/
theorem timeEnergy_tendstoInMeasure (T s : ℝ≥0) {f : ℕ → fullPredictableL2 d T} {g : fullPredictableL2 d T}
    (h : Tendsto f atTop (𝓝 g)) :
    TendstoInMeasure (productLaw d) (fun n=>timeEnergy d T (f n) s) atTop (timeEnergy d T g s) :=
  TendstoInMeasure.congr (fun n=>energyClass_coe d T s (f n)) (energyClass_coe d T s g)
    (tendstoInMeasure_of_tendsto_Lp (energyClass_tendsto d T s h))

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorIntegralEnergyL1
