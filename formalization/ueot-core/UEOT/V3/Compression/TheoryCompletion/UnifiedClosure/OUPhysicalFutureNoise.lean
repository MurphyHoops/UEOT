import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUPhysicalIntegralBinding

/-!
Original commitment: physical OU conditional noise must derive from the SAME future Brownian increments independent of the ENTIRE original past.
Existing result: actual native exponential integral and physical Volterra are sample-bound; deterministic path limits retain finite coordinates.
Premise reduced: construct a measurable raw-path noise via finite-coordinate limUnder, prove its actual Gaussian law and entire original-Fs independence after shifting.
Model/witness: SAME P/B and original naturalFiltration, k>0 for original OU variance clock; k≥0 path identities, finite horizon including zero.
Consumer/boundary: physical-state transition decomposition/kernel and original recovery next; no uncountable raw-evaluation integral measurability or natural-filtration inversion is assumed.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUPhysicalFutureNoise
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource BrownianQuadraticVariation
open OUPhysicalVolterraSource OUPhysicalIntegralBinding OUExponentialGaussianIntegral OUExponentialRiemann OUQuadraticDynkinSource
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Only finite coordinate readouts are used on arbitrary raw paths. -/
def pathNoise (T : ℝ≥0) (k : ℝ) (v : ℝ≥0→ℝ) : ℝ :=
  limUnder atTop (fun n=>∑ i : Fin (n+1),Real.exp (k*uniformClock T n i.castSucc)*
    (v (uniformClock T n i.succ)-v (uniformClock T n i.castSucc)))

theorem pathNoise_measurable (T : ℝ≥0) (k : ℝ) : Measurable (pathNoise T k) := by
  have hm (n : ℕ) : Measurable (fun v : ℝ≥0→ℝ => ∑ i : Fin (n+1),
      Real.exp (k*uniformClock T n i.castSucc)*(v (uniformClock T n i.succ)-v (uniformClock T n i.castSucc))) := by
    exact Finset.measurable_fun_sum Finset.univ (fun i _=>measurable_const.mul
      ((measurable_pi_apply (uniformClock T n i.succ)).sub (measurable_pi_apply (uniformClock T n i.castSucc))))
  exact (StronglyMeasurable.limUnder (l:=atTop) (fun n=>(hm n).stronglyMeasurable)).measurable

theorem pathNoise_sub_const (T : ℝ≥0) (k c : ℝ) (v : ℝ≥0→ℝ) :
    pathNoise T k (fun u=>v u-c)=pathNoise T k v := by
  unfold pathNoise
  congr 1
  funext n
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The raw measurable functional equals the ordinary integral only AFTER it
is evaluated on the given continuous path. No assertion for arbitrary raw paths. -/
theorem pathNoise_on_continuous (T : ℝ≥0) (k : ℝ) (hk : 0≤k) (b : ℝ→ℝ) (hb : Continuous b) :
    pathNoise T k (fun u=>b u)=Real.exp (k*T)*b T-b 0-k*(∫ s in 0..(T : ℝ),Real.exp (k*s)*b s) :=
  (left_sums_tendsto T (fun n=>n+1) (uniformClock T) (uniformClock_mono T)
    (uniformClock_zero T) (uniformClock_end T) (uniformClock_mesh_tendsto T) k hk b hb).limUnder_eq

/-- Finite Brownian laws determine its whole product-coordinate law by the
EXISTING native projective uniqueness; no new extension construction. -/
theorem preBrownian_path_law (X : ℝ≥0→(ℝ≥0→ℝ)→ℝ)
    (hX : IsPreBrownianReal X sourceLaw) (hm : ∀t,Measurable (X t)) :
    HasLaw (fun ω t=>X t ω) sourceLaw sourceLaw := by
  have hp : Measurable (fun ω t=>X t ω) := measurable_pi_lambda _ hm
  refine ⟨hp.aemeasurable,IsProjectiveLimit.unique ?_ sourceLaw_finite⟩
  intro I
  rw [Measure.map_map (Finset.measurable_restrict I) hp]
  exact (hX.hasLaw I).map_eq

theorem pathNoise_process_binding (T : ℝ≥0) (k : ℝ) (hk : 0≤k) :
    (fun ω=>pathNoise T k (fun u=>process u ω))=ᵐ[sourceLaw] value T k hk := by
  filter_upwards [native_integral_binding T k hk] with ω hω
  rw [←pathNoise_sub_const T k (process 0 ω) (fun u=>process u ω)]
  have he := pathNoise_on_continuous T k hk (fun s=>brownianReadout s ω) (brownianReadout_continuous ω)
  have hfun : (fun u : ℝ≥0=>brownianReadout u ω)=(fun u=>process u ω-process 0 ω) := by
    funext u
    simp only[brownianReadout,Real.toNNReal_coe]
  rw[hfun] at he
  rw[he,hω]
  simp[brownianReadout,primitive]

theorem pathNoise_hasLaw (T : ℝ≥0) (k : ℝ) (hk : 0<k) :
    HasLaw (pathNoise T k) (gaussianReal 0 (ouClock k T)) sourceLaw := by
  have hp := preBrownian_path_law process process_isPreBrownian measurable_process
  have h := (value_hasLaw T k hk).congr (pathNoise_process_binding T k hk.le)
  refine ⟨(pathNoise_measurable T k).aemeasurable,?_⟩
  have he:=h.map_eq
  rw [show (fun ω=>pathNoise T k (fun u=>process u ω))=pathNoise T k ∘ (fun ω u=>process u ω) from rfl,
    ←Measure.map_map (pathNoise_measurable T k) (show Measurable (fun ω u=>process u ω) from measurable_pi_lambda _ measurable_process),hp.map_eq] at he
  exact he

def futurePath (s : ℝ≥0) (ω : ℝ≥0→ℝ) (u : ℝ≥0) : ℝ := process (s+u) ω-process s ω

theorem futurePath_measurable (s : ℝ≥0) : Measurable (futurePath s) :=
  measurable_pi_lambda _ (fun u=>(measurable_process (s+u)).sub (measurable_process s))

theorem futurePath_hasLaw (s : ℝ≥0) : HasLaw (futurePath s) sourceLaw sourceLaw :=
  preBrownian_path_law _ (process_isPreBrownian.shift s) (fun u=>(measurable_process (s+u)).sub (measurable_process s))

def futureNoise (k : ℝ) (s T : ℝ≥0) (ω : ℝ≥0→ℝ) : ℝ := pathNoise T k (futurePath s ω)

theorem futureNoise_measurable (k : ℝ) (s T : ℝ≥0) : Measurable (futureNoise k s T) :=
  (pathNoise_measurable T k).comp (futurePath_measurable s)

theorem futureNoise_hasLaw (k : ℝ) (hk : 0<k) (s T : ℝ≥0) :
    HasLaw (futureNoise k s T) (gaussianReal 0 (ouClock k T)) sourceLaw :=
  (pathNoise_hasLaw T k hk).comp (futurePath_hasLaw s)

/-- Independence from the WHOLE original natural past, not only current state. -/
theorem futureNoise_indep_whole_past (k : ℝ) (s T : ℝ≥0) :
    IndepFun (futureNoise k s T) (fun ω (r : Iic s)=>process r ω) sourceLaw :=
  (process_isPreBrownian.indepFun_shift s).comp (pathNoise_measurable T k) measurable_id

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUPhysicalFutureNoise
