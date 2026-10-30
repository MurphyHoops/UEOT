import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorFiniteStateCrossQV

/-!
Original commitment: state Itô needs actual state-dependent coefficients multiplying the SAME Euclidean noise input.
Existing result: native joint-predictable L2 integration, actual continuous finite state, and pure deterministic-clock left approximation.
Premise reduced: derive predictable permission of real continuous joint-past readouts and construct their actual native scalar-times-vector input.
Model/witness: SAME productLaw d, jointNaturalFiltration d and inputLaw d T; finite d/T including zero, original L2 input only.
Consumer: original I(H times f), with H a bounded continuous function of the actual state; START-sum binding and state Itô are separate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorPredictableMultiplier
open MeasureTheory ProbabilityTheory Set Filter
open BrownianFiniteProductSource BrownianVectorTimeInput BrownianVectorPredictableInputs
open BrownianVectorPredictableDensity BrownianVectorIntegralContinuousVersion BrownianVectorFiniteStateCrossQV
open BrownianVectorIntegralTimeEnergy FiniteClockLeftApproximation BrownianQuadraticVariation
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
variable (d : ℕ)

/-- Real coefficient block on the original joint-past predictable sigma. -/
def scalarBlock (s t : ℝ≥0) (H : Sample d → ℝ) (p : ℝ × Sample d) : ℝ :=
  (Ioc (s : ℝ) (t : ℝ)).indicator (fun _ => H p.2) p.1

theorem scalarBlock_predictable (s t : ℝ≥0) (H : Sample d → ℝ)
    (hH : StronglyMeasurable[jointNaturalFiltration d s] H) :
    StronglyMeasurable[predictableSigma d] (scalarBlock d s t H) := by
  apply Measurable.stronglyMeasurable
  intro B hB
  have hr := predictable_interval_rectangle d s t (hH.measurable hB)
  have hw := predictable_interval_rectangle d s t
    (MeasurableSet.univ : MeasurableSet[jointNaturalFiltration d s] (univ : Set (Sample d)))
  by_cases h0 : (0 : ℝ) ∈ B
  · have he : scalarBlock d s t H ⁻¹' B =
        (Ioc (s : ℝ) (t : ℝ) ×ˢ (H ⁻¹' B)) ∪ (Ioc (s : ℝ) (t : ℝ) ×ˢ (univ : Set (Sample d)))ᶜ := by
      ext p
      by_cases hp : p.1 ∈ Ioc (s : ℝ) (t : ℝ) <;> simp [scalarBlock,hp,h0]
    rw [he]
    exact hr.union hw.compl
  · have he : scalarBlock d s t H ⁻¹' B = Ioc (s : ℝ) (t : ℝ) ×ˢ (H ⁻¹' B) := by
      ext p
      by_cases hp : p.1 ∈ Ioc (s : ℝ) (t : ℝ) <;> simp [scalarBlock,hp,h0]
    rw [he]
    exact hr

def leftCoefficient {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (H : ℝ≥0 → Sample d → ℝ)
    (p : ℝ × Sample d) : ℝ := ∑ i : Fin n, scalarBlock d (τ i.castSucc) (τ i.succ) (H (τ i.castSucc)) p

theorem leftCoefficient_predictable {n : ℕ} (τ : Fin (n+1) → ℝ≥0)
    (H : ℝ≥0 → Sample d → ℝ) (hp : StronglyAdapted (jointNaturalFiltration d) H) :
    StronglyMeasurable[predictableSigma d] (leftCoefficient d τ H) := by
  convert Finset.stronglyMeasurable_sum Finset.univ (fun (i : Fin n) _ =>
    scalarBlock_predictable d (τ i.castSucc) (τ i.succ) _ (hp _)) using 1
  ext p
  simp only [leftCoefficient,Finset.sum_apply]

theorem leftCoefficient_eq_leftSample {n : ℕ} (τ : Fin (n+1) → ℝ≥0)
    (H : ℝ≥0 → Sample d → ℝ) (p : ℝ × Sample d) :
    leftCoefficient d τ H p = leftSample τ (fun u => H u p.2) p.1 := rfl

/-- Native AE limit of actual causal left readouts derives original
predictable permission. No new source, completion, or future-Good branch. -/
theorem continuousReadout_predictable (T : ℝ≥0) (H : ℝ≥0 → Sample d → ℝ)
    (hp : StronglyAdapted (jointNaturalFiltration d) H)
    (hc : ∀ᵐ ω ∂productLaw d, Continuous (fun u => H u ω)) :
    AEStronglyMeasurable[predictableSigma d] (fun p : ℝ × Sample d => H (Real.toNNReal p.1) p.2) (inputLaw d T) := by
  let G (p : ℝ × Sample d) := limUnder atTop (fun n => leftCoefficient d (uniformClock T n) H p)
  have hG : StronglyMeasurable[predictableSigma d] G := by
    let : MeasurableSpace (ℝ × Sample d) := predictableSigma d
    change StronglyMeasurable (fun p => limUnder atTop (fun n => leftCoefficient d (uniformClock T n) H p))
    apply StronglyMeasurable.limUnder
    intro n
    exact leftCoefficient_predictable d (uniformClock T n) H hp
  refine ⟨G,hG,?_⟩
  have hcp : ∀ᵐ p ∂inputLaw d T, Continuous (fun u => H u p.2) := Measure.quasiMeasurePreserving_snd.ae hc
  filter_upwards [time_support_ae d T,hcp] with p ht hc
  have hl := leftSample_tendsto T (fun n => n+1) (uniformClock T) (uniformClock_mono T)
    (uniformClock_zero T) (uniformClock_end T) (uniformClock_mesh_tendsto T)
    (fun u => H u p.2) p.1 ht.1 ht.2 hc.continuousWithinAt
  exact hl.limUnder_eq.symm

/-- Actual native Holder scalar multiplication of the original Euclidean
input. It does not transport any scalar-source filtration theorem. -/
def ambientMultiplier (T : ℝ≥0) (H : ℝ × Sample d → ℝ) (hH : MemLp H ∞ (inputLaw d T)) :
    fullPredictableL2 d T →L[ℝ] Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T) :=
  ((ContinuousLinearMap.lsmul ℝ ℝ (E := EuclideanSpace ℝ (Fin d))).holderL
    (inputLaw d T) ∞ 2 2 (hH.toLp H)).comp (fullPredictableL2 d T).subtypeL

theorem ambientMultiplier_coe (T : ℝ≥0) (H : ℝ × Sample d → ℝ) (hH : MemLp H ∞ (inputLaw d T))
    (f : fullPredictableL2 d T) : ambientMultiplier d T H hH f =ᵐ[inputLaw d T]
      fun p => H p • (f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) p := by
  have hh := (ContinuousLinearMap.lsmul ℝ ℝ (E := EuclideanSpace ℝ (Fin d))).coeFn_holder
    (r := 2) (hH.toLp H) (f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T))
  filter_upwards [hh,hH.coeFn_toLp] with p hh hp
  exact hh.trans (congrArg (fun c : ℝ => c • (f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) p) hp)

theorem ambientMultiplier_predictable (T : ℝ≥0) (H : ℝ × Sample d → ℝ)
    (hH : MemLp H ∞ (inputLaw d T)) (hp : AEStronglyMeasurable[predictableSigma d] H (inputLaw d T))
    (f : fullPredictableL2 d T) : ambientMultiplier d T H hH f ∈ fullPredictableL2 d T := by
  apply mem_lpMeas_iff_aestronglyMeasurable.mpr
  exact (hp.smul (mem_lpMeas_iff_aestronglyMeasurable.mp f.property)).congr
    (ambientMultiplier_coe d T H hH f).symm

def inputMultiplier (T : ℝ≥0) (H : ℝ × Sample d → ℝ) (hH : MemLp H ∞ (inputLaw d T))
    (hp : AEStronglyMeasurable[predictableSigma d] H (inputLaw d T)) :
    fullPredictableL2 d T →L[ℝ] fullPredictableL2 d T :=
  (ambientMultiplier d T H hH).codRestrict (fullPredictableL2 d T) (ambientMultiplier_predictable d T H hH hp)

theorem inputMultiplier_coe (T : ℝ≥0) (H : ℝ × Sample d → ℝ) (hH : MemLp H ∞ (inputLaw d T))
    (hp : AEStronglyMeasurable[predictableSigma d] H (inputLaw d T)) (f : fullPredictableL2 d T) :
    (inputMultiplier d T H hH hp f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) =ᵐ[inputLaw d T]
      fun p => H p • (f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) p := ambientMultiplier_coe d T H hH f

theorem inputMultiplier_norm_le (T : ℝ≥0) (H : ℝ × Sample d → ℝ) (hH : MemLp H ∞ (inputLaw d T))
    (hp : AEStronglyMeasurable[predictableSigma d] H (inputLaw d T)) (f : fullPredictableL2 d T) :
    ‖inputMultiplier d T H hH hp f‖ ≤ ‖hH.toLp H‖*‖f‖ := by
  have hh := (ContinuousLinearMap.lsmul ℝ ℝ (E := EuclideanSpace ℝ (Fin d))).norm_holder_apply_apply_le
    (r := 2) (hH.toLp H) (f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T))
  change ‖(ContinuousLinearMap.lsmul ℝ ℝ (E := EuclideanSpace ℝ (Fin d))).holderL
    (inputLaw d T) ∞ 2 2 (hH.toLp H) (f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T))‖ ≤ _
  exact hh.trans (calc
    _ ≤ 1*‖hH.toLp H‖*‖(f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T))‖ := by
      gcongr
      exact ContinuousLinearMap.opNorm_lsmul_le
    _ = _ := by simp only [one_mul]; rfl)

theorem boundedCoefficient_memLp (T : ℝ≥0) (H : ℝ × Sample d → ℝ)
    (hp : AEStronglyMeasurable[predictableSigma d] H (inputLaw d T))
    (K : ℝ) (hb : ∀ᵐ p ∂inputLaw d T, ‖H p‖ ≤ K) : MemLp H ∞ (inputLaw d T) :=
  memLp_top_of_bound (AEStronglyMeasurable.mono (predictableSigma_le d) hp) K hb

def boundedMultiplier (T : ℝ≥0) (H : ℝ × Sample d → ℝ)
    (hp : AEStronglyMeasurable[predictableSigma d] H (inputLaw d T))
    (K : ℝ) (hb : ∀ᵐ p ∂inputLaw d T, ‖H p‖ ≤ K) :
    fullPredictableL2 d T →L[ℝ] fullPredictableL2 d T :=
  inputMultiplier d T H (boundedCoefficient_memLp d T H hp K hb) hp

theorem boundedMultiplier_coe (T : ℝ≥0) (H : ℝ × Sample d → ℝ)
    (hp : AEStronglyMeasurable[predictableSigma d] H (inputLaw d T))
    (K : ℝ) (hb : ∀ᵐ p ∂inputLaw d T, ‖H p‖ ≤ K) (f : fullPredictableL2 d T) :
    (boundedMultiplier d T H hp K hb f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) =ᵐ[inputLaw d T]
      fun p => H p • (f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) p :=
  inputMultiplier_coe d T H _ hp f

/-- Original source-AE bounded coefficient limits multiply the SAME supplied
Euclidean L2 input in native L2. No fourth moment or pointwise input bound. -/
theorem boundedMultiplier_tendsto (T : ℝ≥0)
    (H : ℕ → ℝ × Sample d → ℝ) (G : ℝ × Sample d → ℝ)
    (hHp : ∀ n, AEStronglyMeasurable[predictableSigma d] (H n) (inputLaw d T))
    (hGp : AEStronglyMeasurable[predictableSigma d] G (inputLaw d T))
    (K : ℝ) (hK : 0 ≤ K)
    (hHb : ∀ n, ∀ᵐ p ∂inputLaw d T, ‖H n p‖ ≤ K) (hGb : ∀ᵐ p ∂inputLaw d T, ‖G p‖ ≤ K)
    (hlim : ∀ᵐ p ∂inputLaw d T, Tendsto (fun n => H n p) atTop (𝓝 (G p)))
    (f : fullPredictableL2 d T) :
    Tendsto (fun n => boundedMultiplier d T (H n) (hHp n) K (hHb n) f) atTop
      (𝓝 (boundedMultiplier d T G hGp K hGb f)) := by
  let F (n : ℕ) : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T) := boundedMultiplier d T (H n) (hHp n) K (hHb n) f
  let g : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T) := boundedMultiplier d T G hGp K hGb f
  let R (n : ℕ) (p : ℝ × Sample d) := (H n p-G p) • (f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) p
  have hid (n : ℕ) : ‖F n-g‖^2 = ∫ p, ‖R n p‖^2 ∂inputLaw d T := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (F n) g,boundedMultiplier_coe d T (H n) (hHp n) K (hHb n) f,
      boundedMultiplier_coe d T G hGp K hGb f] with p hd hf hg
    simp only [Pi.sub_apply] at hd
    rw [hd]
    change ‖(boundedMultiplier d T (H n) (hHp n) K (hHb n) f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) p-
      (boundedMultiplier d T G hGp K hGb f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) p‖^2 = _
    rw [hf,hg,← sub_smul]
  have hm (n : ℕ) : AEStronglyMeasurable (fun p => ‖R n p‖^2) (inputLaw d T) :=
    ((((boundedCoefficient_memLp d T (H n) (hHp n) K (hHb n)).aestronglyMeasurable.sub
      (boundedCoefficient_memLp d T G hGp K hGb).aestronglyMeasurable).smul
      (Lp.aestronglyMeasurable (f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)))).norm.pow 2)
  have hb (n : ℕ) : ∀ᵐ p ∂inputLaw d T,
      ‖‖R n p‖^2‖ ≤ (2*K)^2*‖(f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) p‖^2 := by
    filter_upwards [hHb n,hGb] with p hH hG
    have hd : ‖H n p-G p‖ ≤ 2*K := (norm_sub_le _ _).trans (by linarith)
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖R n p‖)]
    simp only [R,norm_smul,mul_pow]
    simpa only [mul_pow] using mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2*K)).mpr hd)
      (sq_nonneg ‖(f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) p‖)
  have hl : ∀ᵐ p ∂inputLaw d T, Tendsto (fun n => ‖R n p‖^2) atTop (𝓝 0) := by
    filter_upwards [hlim] with p hp
    have h := (((hp.sub_const (G p)).smul_const ((f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) p)).norm).pow 2
    simpa only [sub_self,zero_smul,norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0)] using h
  have hi := ((Lp.memLp (f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T))).norm.integrable_sq).const_mul ((2*K)^2)
  have hmean : Tendsto (fun n => ‖F n-g‖^2) atTop (𝓝 0) :=
    (tendsto_congr' (Eventually.of_forall hid)).mpr (by
      simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
        (fun p => (2*K)^2*‖(f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) p‖^2) hm hi hb hl)
  apply tendsto_subtype_rng.mpr
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hs := Real.continuous_sqrt.tendsto (0 : ℝ) |>.comp hmean
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),Real.sqrt_zero] using hs

/-- The SAME original integral consumes the converging multiplied inputs.
This is an integral-class limit, not an assumed stochastic Riemann sum. -/
theorem boundedMultipliedIntegral_tendsto (T : ℝ≥0)
    (H : ℕ → ℝ × Sample d → ℝ) (G : ℝ × Sample d → ℝ)
    (hHp : ∀ n, AEStronglyMeasurable[predictableSigma d] (H n) (inputLaw d T))
    (hGp : AEStronglyMeasurable[predictableSigma d] G (inputLaw d T))
    (K : ℝ) (hK : 0 ≤ K)
    (hHb : ∀ n, ∀ᵐ p ∂inputLaw d T, ‖H n p‖ ≤ K) (hGb : ∀ᵐ p ∂inputLaw d T, ‖G p‖ ≤ K)
    (hlim : ∀ᵐ p ∂inputLaw d T, Tendsto (fun n => H n p) atTop (𝓝 (G p)))
    (f : fullPredictableL2 d T) :
    Tendsto (fun n => predictableIntegral d T (boundedMultiplier d T (H n) (hHp n) K (hHb n) f)) atTop
      (𝓝 (predictableIntegral d T (boundedMultiplier d T G hGp K hGb f))) :=
  ((predictableIntegral d T).continuous.tendsto _).comp
    (boundedMultiplier_tendsto d T H G hHp hGp K hK hHb hGb hlim f)

/-- Actual bounded continuous joint-past readout multiplying SAME f. The
coefficient's predictable permission is derived above, not a caller field. -/
def continuousMultiplier (T : ℝ≥0) (H : ℝ≥0 → Sample d → ℝ)
    (hm : Measurable (Function.uncurry H)) (hp : StronglyAdapted (jointNaturalFiltration d) H)
    (hc : ∀ᵐ ω ∂productLaw d, Continuous (fun u => H u ω))
    (K : ℝ) (hb : ∀ u ω, ‖H u ω‖ ≤ K) : fullPredictableL2 d T →L[ℝ] fullPredictableL2 d T :=
  inputMultiplier d T (fun p => H (Real.toNNReal p.1) p.2)
    (memLp_top_of_bound
      (hm.comp ((measurable_fst.real_toNNReal).prodMk measurable_snd)).aestronglyMeasurable K
      (ae_of_all _ (fun _ => hb _ _))) (continuousReadout_predictable d T H hp hc)

theorem continuousMultiplier_coe (T : ℝ≥0) (H : ℝ≥0 → Sample d → ℝ)
    (hm : Measurable (Function.uncurry H)) (hp : StronglyAdapted (jointNaturalFiltration d) H)
    (hc : ∀ᵐ ω ∂productLaw d, Continuous (fun u => H u ω))
    (K : ℝ) (hb : ∀ u ω, ‖H u ω‖ ≤ K) (f : fullPredictableL2 d T) :
    (continuousMultiplier d T H hm hp hc K hb f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) =ᵐ[inputLaw d T]
      fun p => H (Real.toNNReal p.1) p.2 • (f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) p :=
  inputMultiplier_coe d T _ _ _ f

/-- Finite-state readout F is computed from SAME actual state, and
multiplies any original input on the SAME noise and whole joint filtration. -/
def functionOfStateInput (T : ℝ≥0) {m : ℕ} (family : Fin m → fullPredictableL2 d T)
    (F : EuclideanSpace ℝ (Fin m) → ℝ) (hF : Continuous F)
    (K : ℝ) (hbound : ∀ x, ‖F x‖ ≤ K) (f : fullPredictableL2 d T) : fullPredictableL2 d T :=
  continuousMultiplier d T (fun u ω => F (stateProcess d T family u ω))
    (hF.measurable.comp (stateProcess_measurable d T family))
    (fun u => hF.comp_stronglyMeasurable (stateProcess_stronglyAdapted d T family u))
    ((stateProcess_continuous d T family).mono (fun _ h => hF.comp h)) K (fun _ _ => hbound _) f

theorem functionOfStateInput_coe (T : ℝ≥0) {m : ℕ} (family : Fin m → fullPredictableL2 d T)
    (F : EuclideanSpace ℝ (Fin m) → ℝ) (hF : Continuous F)
    (K : ℝ) (hbound : ∀ x, ‖F x‖ ≤ K) (f : fullPredictableL2 d T) :
    (functionOfStateInput d T family F hF K hbound f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) =ᵐ[inputLaw d T]
      fun p => F (stateProcess d T family (Real.toNNReal p.1) p.2) •
        (f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) p :=
  continuousMultiplier_coe d T _ _ _ _ K _ f

theorem functionOfStateInput_martingale (T : ℝ≥0) {m : ℕ} (family : Fin m → fullPredictableL2 d T)
    (F : EuclideanSpace ℝ (Fin m) → ℝ) (hF : Continuous F)
    (K : ℝ) (hbound : ∀ x, ‖F x‖ ≤ K) (f : fullPredictableL2 d T) :
    Martingale (continuousIntegralProcess d T (functionOfStateInput d T family F hF K hbound f))
      (jointNaturalFiltration d) (productLaw d) := continuousIntegralProcess_martingale d T _

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorPredictableMultiplier
