import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorIntegralFinitePaths
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorIntegralMaximalControl
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.DenseEmbedding

/-!
Original commitment: SAME full Euclidean joint-predictable vector-noise integral needs an actual sample-continuous version.
Existing result: actual dense finite continuous paths and native whole-time maximum control on the original productLaw/joint past.
Premise reduced: derive one common-AE continuous limit and bind each ORIGINAL Fs-measurable limUnder to the SAME supplied input.
Model/witness: fixed d/T/inputLaw d T/productLaw d/jointNaturalFiltration, including d0/T0 and actual cross-coordinate START coefficients.
Consumer: actual sample-continuous adapted martingale with original Euclidean energy and ALL-time literal returns; no vector Ito/SDE/Girsanov claimed.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorIntegralContinuousVersion
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open BrownianFiniteProductSource BrownianVectorTimeInput BrownianVectorIntegralClosure
open BrownianVectorPredictableInputs BrownianVectorPredictableDensity BrownianVectorIntegralTimeSource
open BrownianVectorIntegralConditionalSource BrownianVectorIntegralL2TimeContinuity
open BrownianVectorIntegralFinitePaths BrownianVectorIntegralMaximalControl
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
variable (d : ℕ)

/-- Strict all-time maximum is an actual COUNTABLE union for the already
proved continuous finite path; no uncountable measurability axiom is used. -/
def spanMaximumEvent {T : ℝ≥0} (a : (ElementaryInput d) T →₀ ℝ) (ε : ℝ) : Set (Sample d) :=
  {ω | ∃ u, ε < |(spanPath d) a u ω|}

theorem spanMaximumEvent_dense {T : ℝ≥0} (a : (ElementaryInput d) T →₀ ℝ) (ε : ℝ) :
    (spanMaximumEvent d) a ε = ⋃ n, {ω | ε < |(spanPath d) a (denseSeq ℝ≥0 n) ω|} := by
  ext ω
  simp only [spanMaximumEvent,mem_ofPred_eq,mem_iUnion]
  constructor
  · rintro ⟨u,hu⟩
    by_contra hn
    have hn' : ∀ n, |(spanPath d) a (denseSeq ℝ≥0 n) ω| ≤ ε := by simpa only [not_exists,not_lt] using hn
    have hall := isClosed_property (denseRange_denseSeq ℝ≥0)
      (isClosed_le ((spanPath_continuous d) a ω).abs continuous_const) hn'
    exact (not_le.mpr hu) (hall u)
  · rintro ⟨n,hn⟩
    exact ⟨denseSeq ℝ≥0 n,hn⟩

theorem spanMaximumEvent_measurable {T : ℝ≥0} (a : (ElementaryInput d) T →₀ ℝ) (ε : ℝ) :
    MeasurableSet ((spanMaximumEvent d) a ε) := by
  rw [(spanMaximumEvent_dense d)]
  exact MeasurableSet.iUnion (fun n => measurableSet_lt measurable_const
    ((((spanPath_stronglyAdapted d) a (denseSeq ℝ≥0 n)).mono ((jointNaturalFiltration d).le _)).measurable.abs))

/-- Weak bound for the actual ENTIRE continuous finite path, obtained through
one countable dense readout and its proved original-integral binding. -/
theorem spanMaximumEvent_bound (T : ℝ≥0) (a : (ElementaryInput d) T →₀ ℝ) (ε : ℝ≥0) :
    (ε : ℝ≥0∞)^2 * (productLaw d) ((spanMaximumEvent d) a ε) ≤ ENNReal.ofReal (‖(spanInput d) T a‖ ^ 2) := by
  have hi : ∀ᵐ ω ∂(productLaw d), ∀ n,
      (integralProcess d) T ((spanInput d) T a) (denseSeq ℝ≥0 n) ω = (spanPath d) a (denseSeq ℝ≥0 n) ω :=
    ae_all_iff.mpr (fun n => (integralProcess_eq_spanPath d) T _ a)
  have hs : (spanMaximumEvent d) a ε ≤ᵐ[(productLaw d)]
      {ω | ∃ n, (ε : ℝ) ≤ |(integralProcess d) T ((spanInput d) T a) (denseSeq ℝ≥0 n) ω|} := by
    filter_upwards [hi] with ω hi hω
    rw [(spanMaximumEvent_dense d)] at hω
    obtain ⟨n,hn⟩ := mem_iUnion.mp hω
    exact ⟨n,by rw [hi n]; exact le_of_lt hn⟩
  apply le_trans ?_ ((integralProcess_countable_maximum d) T ((spanInput d) T a) (denseSeq ℝ≥0) ε)
  exact mul_le_mul_of_nonneg_left (measure_mono_ae hs) (show (0 : ℝ≥0∞) ≤ (ε : ℝ≥0∞)^2 from bot_le)

/-- Every (approximation d) is an ACTUAL finite native combination chosen from
proved density at the frozen deterministic geometric error budget. -/
def approximation (T : ℝ≥0) (f : (fullPredictableL2 d) T) (n : ℕ) : (ElementaryInput d) T →₀ ℝ :=
  Classical.choose ((exists_spanInput_dist_lt d) T f ((1/4 : ℝ)^(n+1)) (by positivity))

theorem approximation_error (T : ℝ≥0) (f : (fullPredictableL2 d) T) (n : ℕ) :
    dist ((spanInput d) T ((approximation d) T f n)) f < (1/4 : ℝ)^(n+1) :=
  Classical.choose_spec ((exists_spanInput_dist_lt d) T f ((1/4 : ℝ)^(n+1)) (by positivity))

private theorem spanPath_sub {T : ℝ≥0} (a b : (ElementaryInput d) T →₀ ℝ) (u : ℝ≥0) (ω : Sample d) :
    (spanPath d) (a-b) u ω = (spanPath d) a u ω-(spanPath d) b u ω :=
  Finsupp.sum_sub_index (fun _ _ _ => sub_mul _ _ _)

private theorem approximation_difference_norm (T : ℝ≥0) (f : (fullPredictableL2 d) T) (n : ℕ) :
    ‖(spanInput d) T ((approximation d) T f (n+1)-(approximation d) T f n)‖ ≤ (1/4 : ℝ)^n := by
  rw [map_sub,← dist_eq_norm]
  apply le_trans (dist_triangle _ f _)
  rw [dist_comm f]
  have h₁ := ((approximation_error d) T f (n+1)).le
  have h₂ := ((approximation_error d) T f n).le
  apply (add_le_add h₁ h₂).trans
  simp only [Nat.add_assoc,pow_succ]
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/4) n]

private def bad (T : ℝ≥0) (f : (fullPredictableL2 d) T) (n : ℕ) : Set (Sample d) :=
  (spanMaximumEvent d) ((approximation d) T f (n+1)-(approximation d) T f n) ((1/2 : ℝ)^n)

private theorem bad_bound (T : ℝ≥0) (f : (fullPredictableL2 d) T) (n : ℕ) :
    (productLaw d) ((bad d) T f n) ≤ (1/4 : ℝ≥0∞)^n := by
  let ε : ℝ≥0 := (1/2)^n
  have hε0 : (ε : ℝ≥0∞)^2 ≠ 0 := by simp [ε]
  have hεtop : (ε : ℝ≥0∞)^2 ≠ ∞ := by finiteness
  have hm := (spanMaximumEvent_bound d) T ((approximation d) T f (n+1)-(approximation d) T f n) ε
  have hn := (sq_le_sq₀ (norm_nonneg _) (by positivity : (0 : ℝ) ≤ (1/4)^n)).mpr
    ((approximation_difference_norm d) T f n)
  have he : ((bad d) T f n) = (spanMaximumEvent d) ((approximation d) T f (n+1)-(approximation d) T f n) ε := by
    norm_num only [bad,ε,NNReal.coe_pow,NNReal.coe_div,NNReal.coe_ofNat,NNReal.coe_one]
  rw [← he] at hm
  have hr : ENNReal.ofReal (((1/4 : ℝ)^n)^2) = (ε : ℝ≥0∞)^2 * (1/4 : ℝ≥0∞)^n := by
    have hh : ((2⁻¹ : ℝ≥0∞)^n)^2 = (4⁻¹ : ℝ≥0∞)^n := by
      rw [← pow_mul,Nat.mul_comm n 2,pow_mul,← ENNReal.inv_pow]
      norm_num
    rw [ENNReal.ofReal_pow (by positivity),ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1/4)]
    simp only [ε,ENNReal.coe_pow]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
    norm_num only [ENNReal.ofReal_one,ENNReal.ofReal_ofNat,ENNReal.coe_div,ENNReal.coe_one,ENNReal.coe_ofNat,one_div]
    rw [hh,pow_two]
  apply (ENNReal.mul_le_mul_iff_left hε0 hεtop).mp
  rw [mul_comm ((productLaw d) _),mul_comm ((1/4 : ℝ≥0∞)^n)]
  exact hm.trans ((ENNReal.ofReal_le_ofReal hn).trans_eq hr)

/-- ONE common full-measure event controls all real observation times of all
sufficiently late (approximation d) differences. It is only a PROOF event, never
used to decide the adapted output's value. -/
theorem approximation_eventually_uniform (T : ℝ≥0) (f : (fullPredictableL2 d) T) :
    ∀ᵐ ω ∂(productLaw d), ∀ᶠ n in atTop, ∀ u,
      |(spanPath d) ((approximation d) T f (n+1)) u ω-(spanPath d) ((approximation d) T f n) u ω| ≤ (1/2 : ℝ)^n := by
  have hs : (∑' n, (productLaw d) ((bad d) T f n)) ≠ ∞ := by
    apply ne_top_of_le_ne_top (tsum_geometric_lt_top.mpr (by norm_num : (1/4 : ℝ≥0∞) < 1)).ne
    exact ENNReal.tsum_le_tsum ((bad_bound d) T f)
  filter_upwards [ae_eventually_notMem hs] with ω hω
  apply hω.mono
  intro n hn u
  have h := not_exists.mp hn u
  simpa only [bad,spanMaximumEvent,mem_ofPred_eq,(spanPath_sub d),not_lt] using h

/-- Pointwise limUnder uses ONLY the original natural-past measurable finite
values at u. A future-dependent global Good event is never an output branch. -/
def continuousIntegralProcess (T : ℝ≥0) (f : (fullPredictableL2 d) T) (u : ℝ≥0) (ω : Sample d) : ℝ :=
  limUnder atTop (fun n => (spanPath d) ((approximation d) T f n) u ω)

theorem continuousIntegralProcess_stronglyAdapted (T : ℝ≥0) (f : (fullPredictableL2 d) T) :
    StronglyAdapted (jointNaturalFiltration d) ((continuousIntegralProcess d) T f) := by
  intro u
  unfold continuousIntegralProcess
  let : MeasurableSpace (Sample d) := (jointNaturalFiltration d) u
  apply StronglyMeasurable.limUnder
  intro n
  exact (spanPath_stronglyAdapted d) ((approximation d) T f n) u

private theorem continuous_limit_of_eventual_uniform_increments
    (F : ℕ → ℝ≥0 → ℝ) (hF : ∀ n, Continuous (F n))
    (h : ∀ᶠ n in atTop, ∀ u, |F (n+1) u-F n u| ≤ (1/2 : ℝ)^n) :
    Continuous (fun u => limUnder atTop (fun n => F n u)) ∧
      ∀ u, Tendsto (fun n => F n u) atTop (𝓝 (limUnder atTop (fun n => F n u))) := by
  let D (n : ℕ) (u : ℝ≥0) := F (n+1) u-F n u
  have hs : Summable (fun n : ℕ => (1/2 : ℝ)^n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hd : ∀ᶠ n in atTop, ∀ u ∈ (univ : Set ℝ≥0), ‖D n u‖ ≤ (1/2 : ℝ)^n :=
    h.mono (fun _ hn u _ => by simpa only [D,Real.norm_eq_abs] using hn u)
  have hu := tendstoUniformlyOn_tsum_nat_eventually hs hd
  have hc : Continuous (fun u => ∑' n, D n u) :=
    continuousOn_univ.mp (hu.continuousOn (Frequently.of_forall
      (fun n => (continuous_finsetSum _ (fun i _ => (hF (i+1)).sub (hF i))).continuousOn)))
  have ht (u : ℝ≥0) : Tendsto (fun n => F n u) atTop (𝓝 (F 0 u+∑' n, D n u)) := by
    have hp := (tendsto_const_nhds (x := F 0 u)).add (hu.tendsto_at (mem_univ u))
    convert hp using 1
    · ext n
      change F n u = F 0 u+∑ i ∈ Finset.range n, (F (i+1) u-F i u)
      rw [Finset.sum_range_sub (fun i => F i u) n]
      ring
  have he : (fun u => limUnder atTop (fun n => F n u)) = (fun u => F 0 u+∑' n, D n u) :=
    funext (fun u => (ht u).limUnder_eq)
  refine ⟨?_,?_⟩
  · rw [he]
    exact (hF 0).add hc
  · intro u
    rw [congrFun he u]
    exact ht u

/-- The actual pointwise naturally adapted output has continuous paths on
ONE common full-measure event. The event never controls its fallback value. -/
theorem continuousIntegralProcess_continuous (T : ℝ≥0) (f : (fullPredictableL2 d) T) :
    ∀ᵐ ω ∂(productLaw d), Continuous (fun u => (continuousIntegralProcess d) T f u ω) := by
  filter_upwards [(approximation_eventually_uniform d) T f] with ω hω
  exact (continuous_limit_of_eventual_uniform_increments
    (fun n u => (spanPath d) ((approximation d) T f n) u ω)
    (fun n => (spanPath_continuous d) ((approximation d) T f n) ω) hω).1

/-- One common full-measure event gives pointwise convergence at EVERY time;
this is derived from uniform increments, not an uncountable AE intersection. -/
theorem approximation_tendsto_every_time (T : ℝ≥0) (f : (fullPredictableL2 d) T) :
    ∀ᵐ ω ∂(productLaw d), ∀ u, Tendsto (fun n => (spanPath d) ((approximation d) T f n) u ω)
      atTop (𝓝 ((continuousIntegralProcess d) T f u ω)) := by
  filter_upwards [(approximation_eventually_uniform d) T f] with ω hω
  exact (continuous_limit_of_eventual_uniform_increments
    (fun n u => (spanPath d) ((approximation d) T f n) u ω)
    (fun n => (spanPath_continuous d) ((approximation d) T f n) ω) hω).2

/-- Same original full predictable input is approximated in its native
product-measure L2 norm, at the declared deterministic rate. -/
theorem approximation_tendsto_input (T : ℝ≥0) (f : (fullPredictableL2 d) T) :
    Tendsto (fun n => (spanInput d) T ((approximation d) T f n)) atTop (𝓝 f) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg)
    (fun n => ((approximation_error d) T f n).le)
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/4) (by norm_num : (1/4 : ℝ) < 1)
  simpa only [pow_succ,zero_mul] using h.mul_const (1/4 : ℝ)

/-- The constructed continuous version is EACH fixedtime the actual original
integral, by actual L2 convergence and uniqueness of convergence in measure. -/
theorem continuousIntegralProcess_eq_actual (T u : ℝ≥0) (f : (fullPredictableL2 d) T) :
    (continuousIntegralProcess d) T f u =ᵐ[(productLaw d)] (integralProcess d) T f u := by
  have hL : Tendsto (fun n => (integralClassProcess d) T ((spanInput d) T ((approximation d) T f n)) u)
      atTop (𝓝 ((integralClassProcess d) T f u)) :=
    (((integralAt d) T u).continuous.tendsto f).comp ((approximation_tendsto_input d) T f)
  have he (n : ℕ) : ((integralClassProcess d) T ((spanInput d) T ((approximation d) T f n)) u : (Sample d) → ℝ) =ᵐ[(productLaw d)]
      (spanPath d) ((approximation d) T f n) u :=
    ((integralProcess_eq_truncated d) T u ((spanInput d) T ((approximation d) T f n))).symm.trans
      ((integralProcess_eq_spanPath d) T u ((approximation d) T f n))
  have hm₁ : TendstoInMeasure (productLaw d) (fun n => (spanPath d) ((approximation d) T f n) u) atTop
      ((integralProcess d) T f u) :=
    TendstoInMeasure.congr he ((integralProcess_eq_truncated d) T u f).symm
      (tendstoInMeasure_of_tendsto_Lp hL)
  have hm₂ : TendstoInMeasure (productLaw d) (fun n => (spanPath d) ((approximation d) T f n) u) atTop
      ((continuousIntegralProcess d) T f u) :=
    tendstoInMeasure_of_tendsto_ae
      (fun n => ((spanPath_memLp_two d) ((approximation d) T f n) u).aestronglyMeasurable)
      (((approximation_tendsto_every_time d) T f).mono (fun _ h => h u))
  exact tendstoInMeasure_ae_unique hm₂ hm₁

/-- Actual continuous version retains the ORIGINAL natural-filtration
martingale; no completed-filtration transport or future Good branch appears. -/
theorem continuousIntegralProcess_martingale (T : ℝ≥0) (f : (fullPredictableL2 d) T) :
    Martingale ((continuousIntegralProcess d) T f) (jointNaturalFiltration d) (productLaw d) :=
  ((integralProcess_martingale d) T f).congr ((continuousIntegralProcess_stronglyAdapted d) T f)
    (fun u => ((continuousIntegralProcess_eq_actual d) T u f).symm)

/-- Actual L2 output and literal energy are preserved by the SAME version. -/
theorem continuousIntegralProcess_memLp_two (T u : ℝ≥0) (f : (fullPredictableL2 d) T) :
    MemLp ((continuousIntegralProcess d) T f u) 2 (productLaw d) :=
  (memLp_congr_ae ((continuousIntegralProcess_eq_actual d) T u f)).mpr ((integralProcess_memLp_two d) T u f)

theorem continuousIntegralProcess_energy (T u : ℝ≥0) (f : (fullPredictableL2 d) T) :
    (∫ ω, (continuousIntegralProcess d) T f u ω ^ 2 ∂(productLaw d)) =
      ∫ p in timeSet d T u, ‖(f : Lp (EuclideanSpace ℝ (Fin d)) 2 ((inputLaw d) T)) p‖ ^ 2 ∂(inputLaw d) T := by
  rw [integral_congr_ae (((continuousIntegralProcess_eq_actual d) T u f).mono
    (fun _ h => congrArg (fun x : ℝ => x^2) h))]
  exact (integralProcess_energy d) T u f

/-- The actual continuous version begins at the original zero output. -/
theorem continuousIntegralProcess_zero (T : ℝ≥0) (f : (fullPredictableL2 d) T) :
    (continuousIntegralProcess d) T f 0 =ᵐ[(productLaw d)] fun _ => 0 :=
  ((continuousIntegralProcess_eq_actual d) T 0 f).trans ((integralProcess_zero d) T f)

/-- Its actual horizon output is the SAME original native integral class. -/
theorem continuousIntegralProcess_horizon (T : ℝ≥0) (f : (fullPredictableL2 d) T) :
    (continuousIntegralProcess d) T f T =ᵐ[(productLaw d)] (predictableIntegral d T f : (Sample d) → ℝ) :=
  ((continuousIntegralProcess_eq_actual d) T T f).trans (integralProcess_horizon d T f)

/-- The continuous version returns the SAME entire literal finite path on a
common full-measure event. Only countably many fixed-time identities are
intersected; continuity then supplies ALL observation times. -/
theorem continuousIntegralProcess_returns_literal {T : ℝ≥0} (r : (ElementaryInput d) T) :
    ∀ᵐ ω ∂(productLaw d), ∀ u,
      (continuousIntegralProcess d) T ((literalPredictableInput d) r) u ω = (literalPath d) r u ω := by
  have hd : ∀ᵐ ω ∂(productLaw d), ∀ n,
      (continuousIntegralProcess d) T ((literalPredictableInput d) r) (denseSeq ℝ≥0 n) ω =
        (literalPath d) r (denseSeq ℝ≥0 n) ω :=
    ae_all_iff.mpr (fun n => ((continuousIntegralProcess_eq_actual d) T _ ((literalPredictableInput d) r)).trans
      ((integralProcess_eq_literalPath d) r _))
  filter_upwards [(continuousIntegralProcess_continuous d) T ((literalPredictableInput d) r),hd] with ω hc hd
  have he := (denseRange_denseSeq ℝ≥0).equalizer hc ((literalPath_continuous d) r ω) (funext hd)
  exact congrFun he

/-- The SAME entire-path consumer also holds for original native finite
linear combinations used in the (approximation d), without changing coefficients. -/
theorem continuousIntegralProcess_returns_span (T : ℝ≥0) (a : (ElementaryInput d) T →₀ ℝ) :
    ∀ᵐ ω ∂(productLaw d), ∀ u,
      (continuousIntegralProcess d) T ((spanInput d) T a) u ω = (spanPath d) a u ω := by
  have hd : ∀ᵐ ω ∂(productLaw d), ∀ n,
      (continuousIntegralProcess d) T ((spanInput d) T a) (denseSeq ℝ≥0 n) ω = (spanPath d) a (denseSeq ℝ≥0 n) ω :=
    ae_all_iff.mpr (fun n => ((continuousIntegralProcess_eq_actual d) T _ ((spanInput d) T a)).trans
      ((integralProcess_eq_spanPath d) T _ a))
  filter_upwards [(continuousIntegralProcess_continuous d) T ((spanInput d) T a),hd] with ω hc hd
  have he := (denseRange_denseSeq ℝ≥0).equalizer hc ((spanPath_continuous d) a ω) (funext hd)
  exact congrFun he

/-- Native progressive measurability also survives the ACTUAL pointwise
limUnder construction, on each Iic s times the ORIGINAL Fs. This does not
require modifying the process using a future-dependent Good event. -/
theorem continuousIntegralProcess_isStronglyProgressive (T : ℝ≥0) (f : (fullPredictableL2 d) T) :
    IsStronglyProgressive (jointNaturalFiltration d) ((continuousIntegralProcess d) T f) := by
  intro s
  unfold continuousIntegralProcess
  let : MeasurableSpace (Iic s × (Sample d)) := Subtype.instMeasurableSpace.prod ((jointNaturalFiltration d) s)
  apply StronglyMeasurable.limUnder
  intro n
  exact (((spanPath_stronglyAdapted d) ((approximation d) T f n)).isStronglyProgressive_of_continuous
    (fun ω => (spanPath_continuous d) ((approximation d) T f n) ω)) s

/-- Joint measurability of the actual version follows from the same finite
jointly measurable approximants; it does not assert continuity on (bad d) samples. -/
theorem continuousIntegralProcess_measurable (T : ℝ≥0) (f : (fullPredictableL2 d) T) :
    Measurable (Function.uncurry ((continuousIntegralProcess d) T f)) := by
  apply StronglyMeasurable.measurable
  unfold continuousIntegralProcess Function.uncurry
  apply StronglyMeasurable.limUnder
  intro n
  exact stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    (fun ω => (spanPath_continuous d) ((approximation d) T f n) ω)
    (fun u => ((spanPath_stronglyAdapted d) ((approximation d) T f n) u).mono ((jointNaturalFiltration d).le u))

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorIntegralContinuousVersion
