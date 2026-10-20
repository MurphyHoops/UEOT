import UEOTQM.Stability
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Sequences

/-!
# Actual finite-channel Cesàro averages

The iteration and averages below are built from the declared complete Kraus
channel on density matrices. The telescope identity and its all-effect bound
are proved for that channel, not supplied as a certificate field.

The topology is the ordinary finite complex-matrix topology. We use Mathlib's
scoped Euclidean operator norm, whose topology agrees with the entrywise matrix
topology. Stationarity of average cluster points does not assert uniqueness,
pointwise mixing of the orbit, or empirical convergence of random trajectories.
-/

namespace UEOTQM.Cesaro

open Matrix Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

noncomputable section

variable {ι O κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype O] [Fintype κ]

/-- Iteration of one fixed, complete, outcome-forgetting Kraus channel. -/
def iterateState (I : Instrument ι O κ) (ρ : Density ι) : ℕ → Density ι :=
  channelTrajectory (fun _ => I) ρ

@[simp] theorem iterateState_zero (I : Instrument ι O κ) (ρ : Density ι) :
    iterateState I ρ 0 = ρ := rfl

@[simp] theorem iterateState_succ (I : Instrument ι O κ) (ρ : Density ι) (n : ℕ) :
    iterateState I ρ (n + 1) = I.channelState (iterateState I ρ n) := rfl

/-- The actual complete channel as a real-linear map on all operators. -/
def channelLinear (I : Instrument ι O κ) : Operator ι →ₗ[ℝ] Operator ι where
  toFun := I.channel
  map_add' X Y := by
    simp only [Instrument.channel, Instrument.branch, krausMap,
      Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' r X := by
    simp only [Instrument.channel, Instrument.branch_smul, Finset.smul_sum,
      RingHom.id_apply]

@[simp] theorem channelLinear_apply (I : Instrument ι O κ) (X : Operator ι) :
    channelLinear I X = I.channel X := rfl

/-- The first N chronological density matrices, including the initial state. -/
def orbitSum (I : Instrument ι O κ) (ρ : Density ι) (N : ℕ) : Operator ι :=
  ∑ n ∈ Finset.range N, (iterateState I ρ n).matrix

theorem orbitSum_positive (I : Instrument ι O κ) (ρ : Density ι) (N : ℕ) :
    (orbitSum I ρ N).PosSemidef :=
  Matrix.posSemidef_sum _ (fun n _ => (iterateState I ρ n).positive)

theorem orbitSum_trace (I : Instrument ι O κ) (ρ : Density ι) (N : ℕ) :
    (orbitSum I ρ N).trace = (N : ℂ) := by
  simp [orbitSum, Matrix.trace_sum, Density.trace_one]

/-- An average is a density matrix only for a strictly positive sample count. -/
def averageState (I : Instrument ι O κ) (ρ : Density ι) (N : ℕ)
    (hN : 0 < N) : Density ι where
  matrix := (N : ℝ)⁻¹ • orbitSum I ρ N
  positive := (orbitSum_positive I ρ N).smul (by positivity)
  trace_one := by
    rw [Matrix.trace_smul, orbitSum_trace]
    apply Complex.ext
    · simp only [Complex.smul_re, Complex.natCast_re, smul_eq_mul, Complex.one_re]
      exact inv_mul_cancel₀ (by exact_mod_cast hN.ne')
    · simp

@[simp] theorem averageState_matrix (I : Instrument ι O κ) (ρ : Density ι)
    (N : ℕ) (hN : 0 < N) :
    (averageState I ρ N hN).matrix = (N : ℝ)⁻¹ • orbitSum I ρ N := rfl

theorem orbitSum_telescope (I : Instrument ι O κ) (ρ : Density ι) (N : ℕ) :
    I.channel (orbitSum I ρ N) - orbitSum I ρ N =
      (iterateState I ρ N).matrix - ρ.matrix := by
  change channelLinear I (orbitSum I ρ N) - orbitSum I ρ N = _
  rw [orbitSum, map_sum, ← Finset.sum_sub_distrib]
  have h (n : ℕ) :
      channelLinear I (iterateState I ρ n).matrix = (iterateState I ρ (n + 1)).matrix := rfl
  simp_rw [h]
  simpa only [iterateState_zero] using
    Finset.sum_range_sub (fun n => (iterateState I ρ n).matrix) N

/-- Exact matrix residual, before taking any norm or probability bound. -/
theorem matrix_residual (I : Instrument ι O κ) (ρ : Density ι)
    (N : ℕ) (hN : 0 < N) :
    (I.channelState (averageState I ρ N hN)).matrix -
        (averageState I ρ N hN).matrix =
      (N : ℝ)⁻¹ • ((iterateState I ρ N).matrix - ρ.matrix) := by
  change channelLinear I ((N : ℝ)⁻¹ • orbitSum I ρ N) -
    (N : ℝ)⁻¹ • orbitSum I ρ N = _
  rw [map_smul, ← smul_sub, channelLinear_apply, orbitSum_telescope]

omit [DecidableEq ι] in
theorem pairing_sub_right (E X Y : Operator ι) :
    pairing E (X - Y) = pairing E X - pairing E Y := by
  simp [pairing, mass, Matrix.mul_sub]

theorem probability_residual (I : Instrument ι O κ) (ρ : Density ι)
    (N : ℕ) (hN : 0 < N) (E : Effect ι) :
    E.probability (I.channelState (averageState I ρ N hN)) -
        E.probability (averageState I ρ N hN) =
      (N : ℝ)⁻¹ * (E.probability (iterateState I ρ N) - E.probability ρ) := by
  simp only [Effect.probability, ← pairing_sub_right, matrix_residual,
    pairing_smul_right]

/-- Every effect sees a residual at most 1/N, without a finite test restriction. -/
theorem probability_residual_le (I : Instrument ι O κ) (ρ : Density ι)
    (N : ℕ) (hN : 0 < N) (E : Effect ι) :
    |E.probability (I.channelState (averageState I ρ N hN)) -
      E.probability (averageState I ρ N hN)| ≤ 1 / (N : ℝ) := by
  rw [probability_residual, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (N : ℝ)⁻¹)]
  simpa only [mul_one, one_div] using
    mul_le_mul_of_nonneg_left (E.probability_abs_sub_le_one (iterateState I ρ N) ρ)
      (by positivity : 0 ≤ (N : ℝ)⁻¹)

theorem effectDistance_residual_le (I : Instrument ι O κ) (ρ : Density ι)
    (N : ℕ) (hN : 0 < N) :
    effectDistance (I.channelState (averageState I ρ N hN))
      (averageState I ρ N hN) ≤ 1 / (N : ℝ) := by
  exact (effectDistance_le_iff _ _ _).mpr (probability_residual_le I ρ N hN)

/-- PSD trace one gives a Euclidean operator norm bound; no bound is assumed. -/
theorem density_operatorNorm_le_one (ρ : Density ι) : ‖ρ.matrix‖ ≤ 1 := by
  have hsum : ∑ i, ρ.positive.isHermitian.eigenvalues i = 1 := by
    apply RCLike.ofReal_injective (K := ℂ)
    rw [RCLike.ofReal_sum, RCLike.ofReal_one,
      ← ρ.positive.isHermitian.trace_eq_sum_eigenvalues, ρ.trace_one]
  have heig (i : ι) : ρ.positive.isHermitian.eigenvalues i ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => ρ.positive.eigenvalues_nonneg j)
      (Finset.mem_univ i)
  calc
    ‖ρ.matrix‖ = ‖(RCLike.ofReal ∘ ρ.positive.isHermitian.eigenvalues : ι → ℂ)‖ := by
      conv_lhs => rw [ρ.positive.isHermitian.spectral_theorem]
      simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
        CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
        Matrix.l2_opNorm_diagonal]
    _ ≤ 1 := by
      apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
      intro i
      simpa only [Function.comp_apply, RCLike.norm_ofReal,
        abs_of_nonneg (ρ.positive.eigenvalues_nonneg i)] using heig i

/-- The concrete density-matrix subset of the finite complex matrix space. -/
def densityMatrices (ι : Type*) [Fintype ι] : Set (Operator ι) :=
  {X | X.PosSemidef ∧ X.trace = 1}

theorem densityMatrices_closed : IsClosed (densityMatrices ι) := by
  have hpositive : IsClosed {X : Operator ι | X.PosSemidef} := by
    simpa only [Matrix.nonneg_iff_posSemidef] using
      (CStarAlgebra.isClosed_nonneg (A := Operator ι))
  exact hpositive.inter (isClosed_eq continuous_id.matrix_trace continuous_const)

/-- Compactness follows from closedness and the proved norm bound in finite dimension. -/
theorem densityMatrices_compact : IsCompact (densityMatrices ι) := by
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨densityMatrices_closed, isBounded_iff_forall_norm_le.mpr ⟨1, ?_⟩⟩
  intro X hX
  exact density_operatorNorm_le_one ⟨X, hX.1, hX.2⟩

theorem continuous_channel (I : Instrument ι O κ) : Continuous I.channel := by
  exact (channelLinear I).continuous_of_finiteDimensional

/-- This is the Euclidean operator norm, not a claim of a formalized trace norm. -/
theorem matrix_residual_norm_le (I : Instrument ι O κ) (ρ : Density ι)
    (N : ℕ) (hN : 0 < N) :
    ‖(I.channelState (averageState I ρ N hN)).matrix -
        (averageState I ρ N hN).matrix‖ ≤ 2 / (N : ℝ) := by
  rw [matrix_residual, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (N : ℝ)⁻¹)]
  have hnorm : ‖(iterateState I ρ N).matrix - ρ.matrix‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by
      have h1 := density_operatorNorm_le_one (iterateState I ρ N)
      have h2 := density_operatorNorm_le_one ρ
      linarith)
  simpa only [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_left hnorm (by positivity : 0 ≤ (N : ℝ)⁻¹)

/-- A total sequence with the positive sample count n+1. -/
def averageSequence (I : Instrument ι O κ) (ρ : Density ι) (n : ℕ) : Density ι :=
  averageState I ρ (n + 1) (Nat.succ_pos n)

theorem matrix_residual_tendsto_zero (I : Instrument ι O κ) (ρ : Density ι) :
    Tendsto (fun n => I.channel (averageSequence I ρ n).matrix -
      (averageSequence I ρ n).matrix) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n => matrix_residual_norm_le I ρ (n + 1) (Nat.succ_pos n))
  exact (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).comp
    (tendsto_add_atTop_nat 1)

/-- Any convergent subsequence of actual Cesàro matrices has a stationary limit. -/
theorem subsequence_limit_invariant (I : Instrument ι O κ) (ρ : Density ι)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {X : Operator ι}
    (hX : Tendsto (fun n => (averageSequence I ρ (φ n)).matrix) atTop (𝓝 X)) :
    I.channel X = X := by
  have hres := (matrix_residual_tendsto_zero I ρ).comp hφ.tendsto_atTop
  have hlim := ((continuous_channel I).tendsto X |>.comp hX).sub hX
  have hz : I.channel X - X = 0 := tendsto_nhds_unique hlim hres
  exact sub_eq_zero.mp hz

/-- The limit is itself a density matrix; positivity and normalization are closed conditions. -/
theorem subsequence_limit_density (I : Instrument ι O κ) (ρ : Density ι)
    {φ : ℕ → ℕ} {X : Operator ι}
    (hX : Tendsto (fun n => (averageSequence I ρ (φ n)).matrix) atTop (𝓝 X)) :
    X.PosSemidef ∧ X.trace = 1 := by
  apply densityMatrices_closed.mem_of_tendsto hX
  exact Filter.Eventually.of_forall (fun n =>
    ⟨(averageSequence I ρ (φ n)).positive, (averageSequence I ρ (φ n)).trace_one⟩)

/-- A stationary density and a convergent average subsequence are constructed together. -/
theorem exists_stationary_subsequence (I : Instrument ι O κ) (ρ : Density ι) :
    ∃ σ : Density ι, I.channelState σ = σ ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n => (averageSequence I ρ (φ n)).matrix) atTop (𝓝 σ.matrix) := by
  obtain ⟨X, hX, φ, hφ, hlim⟩ :=
    densityMatrices_compact.tendsto_subseq
      (fun n => show (averageSequence I ρ n).matrix ∈ densityMatrices ι from
        ⟨(averageSequence I ρ n).positive, (averageSequence I ρ n).trace_one⟩)
  let σ : Density ι := ⟨X, hX.1, hX.2⟩
  refine ⟨σ, ?_, φ, hφ, hlim⟩
  apply Density.ext
  exact subsequence_limit_invariant I ρ hφ hlim

theorem exists_stationary_of_density (I : Instrument ι O κ) (ρ : Density ι) :
    ∃ σ : Density ι, I.channelState σ = σ := by
  obtain ⟨σ, hσ, _⟩ := exists_stationary_subsequence I ρ
  exact ⟨σ, hσ⟩

/-- A nonzero finite Hilbert space supplies a density without assuming a stationary seed. -/
def normalizedIdentity [Nonempty ι] : Density ι :=
  normalize (1 : Operator ι) Matrix.PosSemidef.one (by
    have hcard : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
    simpa [mass, Matrix.trace_one] using hcard)

/-- Every declared complete finite Kraus channel on a nonzero Hilbert space
has a stationary density. Uniqueness and pointwise mixing are not conclusions. -/
theorem exists_stationary [Nonempty ι] (I : Instrument ι O κ) :
    ∃ σ : Density ι, I.channelState σ = σ :=
  exists_stationary_of_density I normalizedIdentity

end

end UEOTQM.Cesaro
