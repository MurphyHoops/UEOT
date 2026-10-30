import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorCrossPartitionQV

/-!
Original commitment: finite-dimensional state Itô needs a real state family and covariance matrix driven by the SAME noise.
Existing result: actual joint-source continuous scalar integral outputs and source-derived cross-QV for every full Euclidean input pair.
Premise reduced: construct the actual Euclidean state and derive its entire finite matrix and fixed-matrix weighted partition limits.
Model/witness: arbitrary finite state/noise dimensions including zero, original whole joint past, arbitrary deterministic vanishing-mesh clocks.
Consumer: actual finite-state matrix/fixed-matrix quadratic terms; state-dependent time weights and general state Itô remain separate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorFiniteStateCrossQV
open MeasureTheory ProbabilityTheory Set Filter
open BrownianFiniteProductSource BrownianVectorTimeInput BrownianVectorPredictableInputs
open BrownianVectorIntegralContinuousVersion BrownianVectorIntegralTimeEnergy
open BrownianVectorCrossPartitionQV BrownianQuadraticVariation
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
variable (d : ℕ) (T : ℝ≥0) {m : ℕ}

/-- Original scalar outputs, assembled by the native Euclidean equivalence.
No new state dynamics, source, or bracket is supplied. -/
def stateProcess (f : Fin m → fullPredictableL2 d T) (u : ℝ≥0) (ω : Sample d) :
    EuclideanSpace ℝ (Fin m) :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => continuousIntegralProcess d T (f j) u ω)

theorem stateProcess_apply (f : Fin m → fullPredictableL2 d T) (u : ℝ≥0) (ω : Sample d) (j : Fin m) :
    stateProcess d T f u ω j = continuousIntegralProcess d T (f j) u ω := rfl

theorem stateProcess_stronglyAdapted (f : Fin m → fullPredictableL2 d T) :
    StronglyAdapted (jointNaturalFiltration d) (stateProcess d T f) := by
  intro u
  let : MeasurableSpace (Sample d) := jointNaturalFiltration d u
  exact (EuclideanSpace.equiv (Fin m) ℝ).symm.continuous.comp_stronglyMeasurable
    (measurable_pi_lambda _ (fun j => (continuousIntegralProcess_stronglyAdapted d T (f j) u).measurable)).stronglyMeasurable

theorem stateProcess_continuous (f : Fin m → fullPredictableL2 d T) :
    ∀ᵐ ω ∂productLaw d, Continuous (fun u => stateProcess d T f u ω) := by
  have hc : ∀ᵐ ω ∂productLaw d, ∀ j, Continuous (fun u => continuousIntegralProcess d T (f j) u ω) :=
    ae_all_iff.mpr (fun j => continuousIntegralProcess_continuous d T (f j))
  filter_upwards [hc] with ω hc
  exact (EuclideanSpace.equiv (Fin m) ℝ).symm.continuous.comp (continuous_pi hc)

theorem stateProcess_measurable (f : Fin m → fullPredictableL2 d T) :
    Measurable (Function.uncurry (stateProcess d T f)) := by
  exact (EuclideanSpace.equiv (Fin m) ℝ).symm.continuous.measurable.comp
    (measurable_pi_lambda _ (fun j => continuousIntegralProcess_measurable d T (f j)))

def matrixGrid (f : Fin m → fullPredictableL2 d T) {n : ℕ} (τ : Fin (n+1) → ℝ≥0) :
    Matrix (Fin m) (Fin m) (Lp ℝ 1 (productLaw d)) := fun j k => gridCross d T τ (f j) (f k)

def matrixEnergy (f : Fin m → fullPredictableL2 d T) (s : ℝ≥0) :
    Matrix (Fin m) (Fin m) (Lp ℝ 1 (productLaw d)) := fun j k => crossEnergyClass d T s (f j) (f k)

/-- Every entry is the actual SAME-input dt inner energy, with original Fs
permission and common-AE continuity, rather than a matrix certificate field. -/
theorem matrixEnergy_coe (f : Fin m → fullPredictableL2 d T) (s : ℝ≥0) :
    ∀ᵐ ω ∂productLaw d, ∀ j k,
      matrixEnergy d T f s j k ω = crossTimeEnergy d T (f j) (f k) s ω :=
  ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun k => crossEnergyClass_coe d T s (f j) (f k)))

theorem matrixGrid_coe (f : Fin m → fullPredictableL2 d T) {n : ℕ} (τ : Fin (n+1) → ℝ≥0) :
    ∀ᵐ ω ∂productLaw d, ∀ j k, matrixGrid d T f τ j k ω = ∑ i : Fin n,
      (stateProcess d T f (τ i.succ) ω j-stateProcess d T f (τ i.castSucc) ω j)*
      (stateProcess d T f (τ i.succ) ω k-stateProcess d T f (τ i.castSucc) ω k) :=
  ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun k => gridCross_coe d T τ (f j) (f k)))

/-- Finite product topology: simultaneous convergence of the actual matrix
of native source-L1 entries. Its norm is not identified with an Euclidean norm. -/
theorem matrix_partition_QV (f : Fin m → fullPredictableL2 d T) (N : ℕ → ℕ)
    (τ : (n : ℕ) → Fin (N n+1) → ℝ≥0) (hmono : ∀ n, Monotone (τ n))
    (hzero : ∀ n, τ n 0=0) (hend : ∀ n, τ n (Fin.last (N n))=T)
    (hmesh : Tendsto (fun n => (mesh (τ n) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => matrixGrid d T f (τ n)) atTop (𝓝 (matrixEnergy d T f T)) := by
  apply tendsto_pi_nhds.mpr
  intro j
  apply tendsto_pi_nhds.mpr
  intro k
  exact fullInput_partition_crossVariation d T N τ hmono hzero hend hmesh (f j) (f k)

/-- Literal original state-coordinate increment table. -/
def stateCrossSum (f : Fin m → fullPredictableL2 d T) {n : ℕ} (τ : Fin (n+1) → ℝ≥0)
    (j k : Fin m) (ω : Sample d) : ℝ := ∑ i : Fin n,
  (stateProcess d T f (τ i.succ) ω j-stateProcess d T f (τ i.castSucc) ω j)*
  (stateProcess d T f (τ i.succ) ω k-stateProcess d T f (τ i.castSucc) ω k)

theorem state_partition_crossVariation_inMeasure (f : Fin m → fullPredictableL2 d T) (N : ℕ → ℕ)
    (τ : (n : ℕ) → Fin (N n+1) → ℝ≥0) (hmono : ∀ n, Monotone (τ n))
    (hzero : ∀ n, τ n 0=0) (hend : ∀ n, τ n (Fin.last (N n))=T)
    (hmesh : Tendsto (fun n => (mesh (τ n) : ℝ)) atTop (𝓝 0)) (j k : Fin m) :
    TendstoInMeasure (productLaw d) (fun n => stateCrossSum d T f (τ n) j k)
      atTop (crossTimeEnergy d T (f j) (f k) T) :=
  fullInput_partition_crossVariation_inMeasure d T N τ hmono hzero hend hmesh (f j) (f k)

def weightedGrid (A : Matrix (Fin m) (Fin m) ℝ) (f : Fin m → fullPredictableL2 d T)
    {n : ℕ} (τ : Fin (n+1) → ℝ≥0) : Lp ℝ 1 (productLaw d) :=
  ∑ j, ∑ k, A j k • matrixGrid d T f τ j k

def weightedEnergy (A : Matrix (Fin m) (Fin m) ℝ) (f : Fin m → fullPredictableL2 d T) :
    Lp ℝ 1 (productLaw d) := ∑ j, ∑ k, A j k • matrixEnergy d T f T j k

/-- Fixed matrix weights need no additional moments, rank, or symmetry.
Time-varying weights require a separate actual multiplier approximation. -/
theorem weighted_partition_QV (A : Matrix (Fin m) (Fin m) ℝ) (f : Fin m → fullPredictableL2 d T)
    (N : ℕ → ℕ) (τ : (n : ℕ) → Fin (N n+1) → ℝ≥0) (hmono : ∀ n, Monotone (τ n))
    (hzero : ∀ n, τ n 0=0) (hend : ∀ n, τ n (Fin.last (N n))=T)
    (hmesh : Tendsto (fun n => (mesh (τ n) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => weightedGrid d T A f (τ n)) atTop (𝓝 (weightedEnergy d T A f)) := by
  apply tendsto_finsetSum
  intro j _
  apply tendsto_finsetSum
  intro k _
  exact (fullInput_partition_crossVariation d T N τ hmono hzero hend hmesh (f j) (f k)).const_smul (A j k)

/-- Native coefficient readout for an arbitrary finite real weighted matrix.
Only finite AE intersections and native Lp coercion identities are used. -/
private theorem weighted_coe (A : Matrix (Fin m) (Fin m) ℝ)
    (F : Matrix (Fin m) (Fin m) (Lp ℝ 1 (productLaw d))) :
    (∑ j, ∑ k, A j k • F j k : Lp ℝ 1 (productLaw d)) =ᵐ[productLaw d]
      fun ω => ∑ j, ∑ k, A j k * F j k ω := by
  have hi : ∀ᵐ ω ∂productLaw d, ∀ j,
      (∑ k, A j k • F j k : Lp ℝ 1 (productLaw d)) ω = ∑ k, A j k * F j k ω := by
    apply ae_all_iff.mpr
    intro j
    have hc : ∀ᵐ ω ∂productLaw d, ∀ k, (A j k • F j k : Lp ℝ 1 (productLaw d)) ω = A j k * F j k ω :=
      ae_all_iff.mpr (fun k => by
        filter_upwards [Lp.coeFn_smul (A j k) (F j k)] with ω h
        exact h)
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun k => A j k • F j k),hc] with ω hs hc
    simp only [Finset.sum_apply] at hs
    exact hs.trans (Finset.sum_congr rfl (fun k _ => hc k))
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun j => ∑ k, A j k • F j k),hi] with ω hs hi
  simp only [Finset.sum_apply] at hs
  exact hs.trans (Finset.sum_congr rfl (fun j _ => hi j))

def weightedStateSum (A : Matrix (Fin m) (Fin m) ℝ) (f : Fin m → fullPredictableL2 d T)
    {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (ω : Sample d) : ℝ :=
  ∑ j, ∑ k, A j k * stateCrossSum d T f τ j k ω

/-- SAME-source actual dt integral; all entries are original input inner
products, with original timeLaw and no inferred covariance field. -/
def weightedTimeEnergy (A : Matrix (Fin m) (Fin m) ℝ) (f : Fin m → fullPredictableL2 d T)
    (ω : Sample d) : ℝ := ∫ t, ∑ j, ∑ k, A j k * crossEnergyIntegrand d T T (f j) (f k) (t,ω)
      ∂BrownianTimeIntegrand.timeLaw T

theorem weightedGrid_coe (A : Matrix (Fin m) (Fin m) ℝ) (f : Fin m → fullPredictableL2 d T)
    {n : ℕ} (τ : Fin (n+1) → ℝ≥0) :
    weightedGrid d T A f τ =ᵐ[productLaw d] weightedStateSum d T A f τ := by
  filter_upwards [weighted_coe d A (matrixGrid d T f τ),matrixGrid_coe d T f τ] with ω hw hm
  exact hw.trans (Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => congrArg (A j k * ·) (hm j k))))

theorem weightedEnergy_coe (A : Matrix (Fin m) (Fin m) ℝ) (f : Fin m → fullPredictableL2 d T) :
    weightedEnergy d T A f =ᵐ[productLaw d] weightedTimeEnergy d T A f := by
  have hi : ∀ᵐ ω ∂productLaw d, ∀ j k,
      Integrable (fun t => A j k * crossEnergyIntegrand d T T (f j) (f k) (t,ω))
        (BrownianTimeIntegrand.timeLaw T) :=
    ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun k =>
      ((crossEnergyIntegrand_integrable d T T (f j) (f k)).const_mul (A j k)).prod_left_ae))
  filter_upwards [weighted_coe d A (matrixEnergy d T f T),matrixEnergy_coe d T f T,hi] with ω hw hm hi
  rw [weightedTimeEnergy,integral_finsetSum Finset.univ (fun j _ => integrable_finsetSum _ (fun k _ => hi j k))]
  simp_rw [integral_finsetSum Finset.univ (fun k _ => hi _ k),integral_const_mul]
  exact hw.trans (Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => congrArg (A j k * ·) (hm j k))))

/-- Literal fixed-matrix weighted quadratic increments of the actual
Euclidean state tend in measure to the actual original dt bilinear integral. -/
theorem weighted_state_partition_QV_inMeasure (A : Matrix (Fin m) (Fin m) ℝ)
    (f : Fin m → fullPredictableL2 d T) (N : ℕ → ℕ)
    (τ : (n : ℕ) → Fin (N n+1) → ℝ≥0) (hmono : ∀ n, Monotone (τ n))
    (hzero : ∀ n, τ n 0=0) (hend : ∀ n, τ n (Fin.last (N n))=T)
    (hmesh : Tendsto (fun n => (mesh (τ n) : ℝ)) atTop (𝓝 0)) :
    TendstoInMeasure (productLaw d) (fun n => weightedStateSum d T A f (τ n)) atTop
      (weightedTimeEnergy d T A f) :=
  TendstoInMeasure.congr (fun n => weightedGrid_coe d T A f (τ n)) (weightedEnergy_coe d T A f)
    (tendstoInMeasure_of_tendsto_Lp (weighted_partition_QV d T A f N τ hmono hzero hend hmesh))

/-- The actual covariance energy is positive on every rank-one test:
this is a derived Gram integral, including singular and zero state families. -/
theorem weightedTimeEnergy_rankOne (v : Fin m → ℝ) (f : Fin m → fullPredictableL2 d T) (ω : Sample d) :
    weightedTimeEnergy d T (fun j k => v j*v k) f ω =
      ∫ t, (BrownianVectorIntegralTimeSource.timeSet d T T).indicator
        (fun p => ‖∑ j, v j • BrownianVectorIntegralTimeEnergy.representative d T (f j) p‖^2) (t,ω)
          ∂BrownianTimeIntegrand.timeLaw T := by
  apply integral_congr_ae
  apply ae_of_all
  intro t
  by_cases ht : (t,ω) ∈ BrownianVectorIntegralTimeSource.timeSet d T T
  · simp only [crossEnergyIntegrand,Set.indicator_of_mem ht]
    rw [← real_inner_self_eq_norm_sq]
    simp_rw [sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  · simp only [crossEnergyIntegrand,Set.indicator_of_notMem ht,mul_zero,Finset.sum_const_zero]

theorem weightedTimeEnergy_rankOne_nonneg (v : Fin m → ℝ)
    (f : Fin m → fullPredictableL2 d T) (ω : Sample d) :
    0 ≤ weightedTimeEnergy d T (fun j k => v j*v k) f ω := by
  rw [weightedTimeEnergy_rankOne]
  apply integral_nonneg
  intro t
  apply Set.indicator_nonneg
  intro _ _
  exact sq_nonneg _

/-- Zero-dimensional state is the actual unique Euclidean zero path. -/
theorem stateProcess_zero_dimension (f : Fin 0 → fullPredictableL2 d T) (u : ℝ≥0) (ω : Sample d) :
    stateProcess d T f u ω = 0 := by ext j; exact Fin.elim0 j

theorem weighted_zero_dimension (A : Matrix (Fin 0) (Fin 0) ℝ) (f : Fin 0 → fullPredictableL2 d T)
    {n : ℕ} (τ : Fin (n+1) → ℝ≥0) : weightedGrid d T A f τ = 0 := by simp [weightedGrid]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorFiniteStateCrossQV
