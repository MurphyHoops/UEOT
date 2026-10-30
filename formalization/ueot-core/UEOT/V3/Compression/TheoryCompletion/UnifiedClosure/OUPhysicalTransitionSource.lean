import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUPhysicalFutureNoise

/-!
Original commitment: physical restoring OU must derive its true conditional transition from the SAME original Brownian future.
Existing result: physical Volterra/native Gaussian integral binding and measurable finite-coordinate future noise independent of whole Fs.
Premise reduced: derive pathwise elapsed-time transition identity and identify its noise law with the ORIGINAL OU transitionVariance/kernel.
Model/witness: SAME physical state/P/B/originalFs, k>0, arbitrary sigma/x0, all s≤t including equal clocks and sigma0.
Consumer/boundary: whole-past conditional kernel and original recovery consumers; old timechangedOU and physicalX are never equated samplewise.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUPhysicalTransitionSource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource
open OUPhysicalVolterraSource OUPhysicalFutureNoise OUConditionalInnovationSource OUQuadraticDynkinSource
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

private theorem exp_cancel (k s : ℝ) : Real.exp (-k*s)*Real.exp (k*s)=1 := by
  rw [←Real.exp_add,show -k*s+k*s=0 by ring,Real.exp_zero]

private theorem shifted_primitive (k s d : ℝ) (ω : ℝ≥0→ℝ) :
    k*(∫u in (0 : ℝ)..d,Real.exp (k*u)*(brownianReadout (s+u) ω-brownianReadout s ω))=
      Real.exp (-k*s)*k*(primitive k (s+d) ω-primitive k s ω)-brownianReadout s ω*(Real.exp (k*d)-1) := by
  let b : ℝ→ℝ := fun u=>brownianReadout u ω
  have hb : Continuous b := brownianReadout_continuous ω
  have hc : Continuous (fun u : ℝ=>Real.exp (k*u)) := by fun_prop
  have hcb : Continuous (fun u : ℝ=>Real.exp (k*u)*b (s+u)) := by fun_prop
  have hd (u : ℝ) : Real.exp (k*u)=Real.exp (-k*s)*Real.exp (k*(s+u)) := by
    rw[←Real.exp_add]
    congr 1
    ring
  have hshift : (∫u in (0 : ℝ)..d,Real.exp (k*u)*b (s+u))=
      Real.exp (-k*s)*(primitive k (s+d) ω-primitive k s ω) := by
    rw[show (fun u=>Real.exp (k*u)*b (s+u))=
      (fun u=>Real.exp (-k*s)*(Real.exp (k*(s+u))*b (s+u))) from by
        funext u
        rw[hd u]
        ring,intervalIntegral.integral_const_mul]
    have hi:=intervalIntegral.integral_comp_add_left (a:=0) (b:=d)
      (fun u=>Real.exp (k*u)*b u) s
    simp only[add_zero] at hi
    rw[hi]
    congr 1
    exact (intervalIntegral.integral_interval_sub_left
      ((weighted_path_continuous k ω).intervalIntegrable 0 (s+d))
      ((weighted_path_continuous k ω).intervalIntegrable 0 s)).symm
  have hexp : k*(∫u in (0 : ℝ)..d,Real.exp (k*u))=Real.exp (k*d)-1 := by
    rw[←intervalIntegral.integral_const_mul]
    have hder (u : ℝ) : HasDerivAt (fun v : ℝ=>Real.exp (k*v)) (k*Real.exp (k*u)) u := by
      simpa only[id_eq,mul_one,one_mul,mul_comm] using (((hasDerivAt_id u).const_mul k).exp)
    simpa only[mul_zero,Real.exp_zero] using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u (_hu : u∈uIcc (0 : ℝ) d)=>hder u) ((continuous_const.mul hc).intervalIntegrable 0 d)
  change k*(∫u in (0 : ℝ)..d,Real.exp (k*u)*(b (s+u)-b s))=_
  have hconst : Continuous (fun u : ℝ=>Real.exp (k*u)*b s) := by fun_prop
  rw[show (fun u=>Real.exp (k*u)*(b (s+u)-b s))=(fun u=>Real.exp (k*u)*b (s+u)-Real.exp (k*u)*b s) from by funext u;ring,
    intervalIntegral.integral_sub (hcb.intervalIntegrable 0 d) (hconst.intervalIntegrable 0 d),
    intervalIntegral.integral_mul_const,hshift]
  have hexp' := congrArg (fun z : ℝ => b s*z) hexp
  dsimp only [b] at hexp' ⊢
  nlinarith

/-- Genuine pathwise physical transition. Its noise reads only future increments after s. -/
theorem physical_elapsed_transition (k σ x₀ : ℝ) (hk : 0≤k) (s d : ℝ≥0) (ω : ℝ≥0→ℝ) :
    state k σ x₀ (s+d) ω=Real.exp (-k*d)*state k σ x₀ s ω+
      (Real.exp (-k*d)*σ)*futureNoise k s d ω := by
  have hcont : Continuous (fun u : ℝ=>brownianReadout ((s : ℝ)+u) ω-brownianReadout s ω) :=
    ((brownianReadout_continuous ω).comp (continuous_const.add continuous_id)).sub continuous_const
  have hfun : futurePath s ω=(fun u : ℝ≥0=>brownianReadout ((s : ℝ)+u) ω-brownianReadout s ω) := by
    funext u
    simp only[futurePath,brownianReadout,←NNReal.coe_add,Real.toNNReal_coe]
    ring
  have hn := pathNoise_on_continuous d k hk _ hcont
  rw[←hfun] at hn
  have hz : brownianReadout ((s : ℝ)+0) ω-brownianReadout s ω=0 := by simp
  rw[hz,sub_zero] at hn
  change state k σ x₀ (s+d) ω=Real.exp (-k*d)*state k σ x₀ s ω+(Real.exp (-k*d)*σ)*pathNoise d k (futurePath s ω)
  rw[hn]
  have hp := shifted_primitive k s d ω
  have he : Real.exp (-k*((s : ℝ)+d))=Real.exp (-k*d)*Real.exp (-k*s) := by
    rw[←Real.exp_add]
    congr 1
    ring
  unfold state regularPart
  rw[he]
  have hc:=exp_cancel k d
  have hh:=congrArg (fun z : ℝ=>σ*brownianReadout ((s : ℝ)+d) ω*z) hc
  have hp' := congrArg (fun z : ℝ=>Real.exp (-k*d)*σ*z) hp
  linear_combination hp' - hh

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUPhysicalTransitionSource
