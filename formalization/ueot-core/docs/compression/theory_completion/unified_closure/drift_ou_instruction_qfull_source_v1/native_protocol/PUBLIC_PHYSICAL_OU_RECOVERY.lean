import UEOT
namespace UEOTIndependentPhysicalOU
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource
open BrownianQuadraticVariation BrownianDeterministicGaussianIntegral
open OUPhysicalVolterraSource OUPhysicalIntegralBinding OUPhysicalFutureNoise
open OUPhysicalTransitionSource OUPhysicalConditionalKernelSource OUPhysicalRecoverySource
open OUExponentialGaussianIntegral OUExponentialRiemann OUQuadraticDynkinSource
open OUConditionalInnovationSource OUTransitionKernelSource
open scoped NNReal ENNReal Topology
noncomputable section

-- New non-author parameters: rate3/2, noise−4, initial5; different clocks2→5/T7.
example : (∀ᵐ ω ∂sourceLaw,∀t : ℝ≥0,
    state (3/2) (-4) 5 t ω=5+(-4)*process t ω-(3/2)*(∫u in (0 : ℝ)..(t : ℝ),state (3/2) (-4) 5 u ω)) ∧
    HasLaw (state (3/2) (-4) 5 (5 : ℝ≥0)) (transitionKernel (3/2) (-4) 0 5 5) sourceLaw ∧
    (∀t∈Icc (0 : ℝ) 7,(∫x,x^2 ∂physicalLaw (3/2) (-4) 5 t)≤
      Real.exp (-3*t)*25+(16/3 : ℝ)*(1-Real.exp (-3*t))) := by
  refine ⟨actual_original_source_equation _ _ _,physical_hasLaw _ _ _ (by norm_num) _,?_⟩
  convert physical_source_p_rec_02 (3/2) (-4) 5 7 (by norm_num) (by norm_num) using 1; norm_num

example : (state (3/2) (-4) 5 (5 : ℝ≥0))=ᵐ[sourceLaw]
    fun ω=>Real.exp (-(3/2)*(5 : ℝ≥0))*5+
      (Real.exp (-(3/2)*(5 : ℝ≥0))*(-4))*value 5 (3/2) (by norm_num) ω :=
  state_native_binding 5 (3/2) (-4) 5 (by norm_num)

example : Measurable (Function.uncurry (state (3/2) (-4) 5)) := state_joint _ _ _
example : StronglyAdapted naturalFiltration (fun t : ℝ≥0=>state (3/2) (-4) 5 t) := state_stronglyAdapted _ _ _
example : IsProbabilityMeasure (physicalLaw (3/2) (-4) 5 5) := physicalLaw_probability _ _ _ _
example : physicalLaw (3/2) (-4) 5 0=Measure.dirac 5 := physicalLaw_initial _ _ _
example : physicalLaw (3/2) (-4) 5 5=ouLaw sourceLaw process (3/2) (-4) 5 5 :=
  physicalLaw_eq_existing_ouLaw _ _ _ (by norm_num) _

example : UEOT.V3.RecoveryDynkin.DynkinExpectationCertificate
    (fun t=>∫x,x^2 ∂physicalLaw (3/2) (-4) 5 t)
    (fun t=>∫x,(-3*x^2+16) ∂physicalLaw (3/2) (-4) 5 t) 7 := by
  convert physical_quadratic_dynkin (3/2) (-4) 5 7 (by norm_num) (by norm_num) using 1;
    norm_num [quadraticGenerator]

example : 0<(transitionVariance (3/2) (-4) 2 5 : ℝ) :=
  physical_positive_transition_noise _ _ (by norm_num) (by norm_num) _ _ (by norm_num)

-- Bounded nonlinear query of the SAME physical process conditioned on entire original Fs2.
def query (x : ℝ) : ℝ:=Real.cos (2*x+1)
theorem query_measurable : Measurable query := by unfold query; fun_prop
theorem query_bound (x : ℝ) : ‖query x‖≤1 := by simpa [query,Real.norm_eq_abs] using Real.abs_cos_le_one (2*x+1)
example : sourceLaw[fun ω=>query (state (3/2) (-4) 5 5 ω)|naturalFiltration 2]=ᵐ[sourceLaw]
    fun ω=>∫y,query y ∂transitionKernel (3/2) (-4) 2 5 (state (3/2) (-4) 5 2 ω) :=
  physical_condExp_kernel (3/2) (-4) 5 (by norm_num) 2 5 (by norm_num) query query_measurable 1 query_bound

-- Whole-past nonlinear discontinuous test uses three distinct source times,
-- not only X2 or a single Brownian endpoint.
def early : Iic (2 : ℝ≥0):=⟨1/2,by exact_mod_cast (by norm_num : (1/2 : ℝ)≤2)⟩
def middle : Iic (2 : ℝ≥0):=⟨7/4,by exact_mod_cast (by norm_num : (7/4 : ℝ)≤2)⟩
def terminal : Iic (2 : ℝ≥0):=⟨2,by simp⟩
def pastTest (v : Iic (2 : ℝ≥0)→ℝ) : ℝ :=
  if v early*v middle>v terminal then Real.cos (v early+v terminal) else Real.sin (v middle)

theorem pastTest_measurable : Measurable pastTest := by
  exact Measurable.ite
    (measurableSet_lt (measurable_pi_apply terminal) ((measurable_pi_apply early).mul (measurable_pi_apply middle)))
    (Real.measurable_cos.comp ((measurable_pi_apply early).add (measurable_pi_apply terminal)))
    (Real.measurable_sin.comp (measurable_pi_apply middle))

example : IndepFun (physicalInnovation (3/2) (-4) 2 5)
    (fun ω=>pastTest (fun r=>process r ω)) sourceLaw :=
  (physicalInnovation_indep_whole_past (3/2) (-4) 2 5).comp measurable_id pastTest_measurable

example : HasLaw (futureNoise (3/2) 2 3) (gaussianReal 0 (ouClock (3/2) 3)) sourceLaw :=
  futureNoise_hasLaw _ (by norm_num) _ _

-- Repeated actual finite clocks retain Gaussianity; no spurious independence assumption.
example : HasGaussianLaw (fun ω=>∑i : Fin 2,(if i=0 then (3 : ℝ) else -2)*
    increment (![0,0,2] i.castSucc) (![0,0,2] i.succ) ω) sourceLaw :=
  weighted_increments_gaussian (![0,0,2]) _

-- Pure path IBP also admits nonsmooth continuous paths and actual uniform grids.
example : Tendsto (fun n=>∑i : Fin (n+1),Real.exp ((3/2)*uniformClock 3 n i.castSucc)*
    (|((uniformClock 3 n i.succ : ℝ≥0) : ℝ)-1|-|((uniformClock 3 n i.castSucc : ℝ≥0) : ℝ)-1|)) atTop
    (nhds (Real.exp ((3/2)*(3 : ℝ≥0))*|(3 : ℝ)-1|-|(0 : ℝ)-1|-
      (3/2)*(∫s in (0 : ℝ)..3,Real.exp ((3/2)*s)*|s-1|))) :=
  left_sums_tendsto 3 (fun n=>n+1) (uniformClock 3) (uniformClock_mono 3)
    (uniformClock_zero 3) (uniformClock_end 3) (uniformClock_mesh_tendsto 3)
    (3/2) (by norm_num) (fun s=>|s-1|) (by fun_prop)

-- k0 physical source retains genuine Brownian noise; old k0 clock is zero.
example : (∫ω,value 2 0 le_rfl ω^2 ∂sourceLaw)=(2 : ℝ) ∧ ouClock 0 2=0 := by
  exact ⟨zero_rate_second_moment 2,by simp [ouClock]⟩
example (ω : ℝ≥0→ℝ) : state 0 (-4) 5 2 ω=5+(-4)*brownianReadout 2 ω := zero_restoring_rate _ _ _ _
example (ω : ℝ≥0→ℝ) : state (3/2) 0 5 2 ω=Real.exp (-(3/2)*2)*5 := zero_noise _ _ _ _
example (ω : ℝ≥0→ℝ) : state (3/2) (-4) 5 0 ω=5 := state_initial _ _ _ _
example : UEOT.V3.RecoveryDynkin.DynkinExpectationCertificate
    (fun t=>∫x,x^2 ∂physicalLaw (3/2) (-4) 5 t)
    (fun t=>∫x,quadraticGenerator (3/2) (-4) x ∂physicalLaw (3/2) (-4) 5 t) 0 :=
  physical_quadratic_dynkin _ _ _ _ (by norm_num) le_rfl

end
end UEOTIndependentPhysicalOU
