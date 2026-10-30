import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUExponentialRiemann
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUExponentialGaussianIntegral
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUPhysicalVolterraSource

/-!
Original commitment: the constructed restoring physical OU must consume the SAME returned native exponential Brownian integral.
Existing result: exact physical Volterra equation, pure path integration-by-parts limit and native left-table L2 limit/Gaussian law are derived.
Premise reduced: identify native integral with the physical path functional by actual shared sums and AE subsequence uniqueness.
Model/witness: SAME canonical P/B; k≥0, every finite T; centered source guarantees literal initial state and k0/T0 boundaries.
Consumer/boundary: physical state Gaussian marginal and original-Fs conditional innovation next; no samplewise identification with old timechanged OU.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUPhysicalIntegralBinding
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource BrownianTimeIntegrand BrownianIntegralClosure
open BrownianPredictableInputs BrownianPredictableDensity BrownianContinuousAdaptedInputs BrownianDeterministicGaussianIntegral
open BrownianSimplePredictableIntegral BrownianOneStepIntegral BrownianQuadraticVariation
open OUPhysicalVolterraSource OUExponentialGaussianIntegral OUExponentialRiemann
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

private theorem left_literal_identity (T : ℝ≥0) (k : ℝ) (hk : 0≤k) (n : ℕ) (ω : ℝ≥0→ℝ) :
    simpleIntegral (leftRecord T (lifted (weight T k)) (lifted_adapted (weight T k))
      (Real.exp (k*T)) (fun u _=>weight_bound T k hk u) n).clock
      (leftRecord T (lifted (weight T k)) (lifted_adapted (weight T k))
      (Real.exp (k*T)) (fun u _=>weight_bound T k hk u) n).coefficient ω=
    ∑ i : Fin (n+1),Real.exp (k*uniformClock T n i.castSucc)*
      (brownianReadout (uniformClock T n i.succ) ω-brownianReadout (uniformClock T n i.castSucc) ω) := by
  change (∑ i : Fin (n+1),weight T k (uniformClock T n i.castSucc)*
    (process (uniformClock T n i.succ) ω-process (uniformClock T n i.castSucc) ω))=_
  apply Finset.sum_congr rfl
  intro i _
  have hi : uniformClock T n i.castSucc ≤ T := (uniformClock_mono T n (Fin.le_last _)).trans_eq (uniformClock_end T n)
  rw [weight,min_eq_left hi]
  simp only [brownianReadout,Real.toNNReal_coe]
  ring

/-- The returned native integral equals this SAME physical Volterra functional; no replacement Gaussian variable is chosen. -/
theorem native_integral_binding (T : ℝ≥0) (k : ℝ) (hk : 0≤k) :
    (value T k hk : (ℝ≥0→ℝ)→ℝ)=ᵐ[sourceLaw]
      fun ω=>Real.exp (k*T)*brownianReadout T ω-k*primitive k T ω := by
  let r (n : ℕ) := leftRecord T (lifted (weight T k)) (lifted_adapted (weight T k))
    (Real.exp (k*T)) (fun u _=>weight_bound T k hk u) n
  have hlp : Tendsto (fun n=>outputValue (r n)) atTop (𝓝 (value T k hk)) :=
    left_outputs_tendsto T (lifted (weight T k)) (lifted_joint _ (weight_continuous T k))
      (lifted_adapted _) (lifted_continuous _ (weight_continuous T k))
      (Real.exp (k*T)) (Real.exp_pos _).le (fun u _=>weight_bound T k hk u)
  obtain ⟨ns,hns,hAE⟩ := (tendstoInMeasure_of_tendsto_Lp hlp).exists_seq_tendsto_ae
  have hc : ∀ᵐ ω ∂sourceLaw,∀ n,outputValue (r n) ω=simpleIntegral (r n).clock (r n).coefficient ω :=
    ae_all_iff.mpr (fun n=>(simpleIntegral_memLp_two (r n).clock (r n).coefficient (r n).coefficient_bounded).coeFn_toLp)
  filter_upwards [hAE,hc] with ω hω hcoe
  have hp := left_sums_tendsto T (fun n=>n+1) (uniformClock T) (uniformClock_mono T)
    (uniformClock_zero T) (uniformClock_end T) (uniformClock_mesh_tendsto T) k hk
    (fun s=>brownianReadout s ω) (brownianReadout_continuous ω)
  have hb0 : brownianReadout 0 ω=0 := by simp[brownianReadout]
  simp only [hb0,sub_zero] at hp
  have he (n : ℕ) : outputValue (r (ns n)) ω=
      ∑ i : Fin (ns n+1),Real.exp (k*uniformClock T (ns n) i.castSucc)*
        (brownianReadout (uniformClock T (ns n) i.succ) ω-brownianReadout (uniformClock T (ns n) i.castSucc) ω) :=
    (hcoe (ns n)).trans (left_literal_identity T k hk (ns n) ω)
  exact tendsto_nhds_unique hω ((tendsto_congr' (Eventually.of_forall he)).mpr (hp.comp hns.tendsto_atTop))

/-- Physical restoring state and the ACTUAL returned native Gaussian integral are bound on SAME source samples. -/
theorem state_native_binding (T : ℝ≥0) (k σ x₀ : ℝ) (hk : 0≤k) :
    state k σ x₀ T=ᵐ[sourceLaw]
      fun ω=>Real.exp (-k*T)*x₀+(Real.exp (-k*T)*σ)*value T k hk ω := by
  filter_upwards [native_integral_binding T k hk] with ω hω
  rw [hω]
  unfold state regularPart
  have he : Real.exp (-k*T)*Real.exp (k*T)=1 := by
    rw [←Real.exp_add,show -k*(T : ℝ)+k*T=0 by ring,Real.exp_zero]
  have hh:=congrArg (fun z : ℝ=>σ*brownianReadout T ω*z) he
  nlinarith

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUPhysicalIntegralBinding
