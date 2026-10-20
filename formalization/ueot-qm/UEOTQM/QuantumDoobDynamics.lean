import UEOTQM.QuantumDoobModel
import UEOTQM.Cesaro

/-!
# Exact dynamics of the fixed noncommutative quantum survival model

The operators and states in this file are the actual source and Doob instruments
of QuantumDoobModel. Every iteration is connected to successOperator or the
existing complete-channel iterateState. The normalized filter is not assumed
linear or trace preserving. General Perron existence and infinite path
conditioning are not asserted by this explicitly solvable finite model.
-/

namespace UEOTQM.QuantumDoobDynamics

open Matrix Filter
open UEOTQM.QuantumDoob UEOTQM.QuantumDoobModel
open scoped BigOperators ComplexOrder Topology

noncomputable section

/-- Exact decay coefficient of this particular Doob channel. -/
def decay (n : ℕ) : ℝ := (1 / 3) ^ n

@[simp] theorem decay_zero : decay 0 = 1 := by simp [decay]

theorem decay_pos (n : ℕ) : 0 < decay n := pow_pos (by norm_num) n

theorem decay_le_one (n : ℕ) : decay n ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

theorem decay_succ (n : ℕ) : decay (n + 1) = decay n * (1 / 3) := by
  simp [decay, pow_succ]

theorem decay_tendsto : Tendsto decay atTop (𝓝 (0 : ℝ)) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- Scaling actual matrix differences scales the supremum over all effects.
The zero case needs no unproved tomography or distance-separation principle. -/
theorem effectDistance_eq_of_matrix_sub_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ σ τ υ : Density ι) (a : ℝ) (ha : 0 ≤ a)
    (h : ρ.matrix - σ.matrix = a • (τ.matrix - υ.matrix)) :
    effectDistance ρ σ = a * effectDistance τ υ := by
  have hg (E : Effect ι) :
      |E.probability ρ - E.probability σ| =
        a * |E.probability τ - E.probability υ| := by
    simp only [Effect.probability, ← Cesaro.pairing_sub_right, h,
      pairing_smul_right, abs_mul, abs_of_nonneg ha]
  apply le_antisymm
  · apply (effectDistance_le_iff _ _ _).mpr
    intro E
    rw [hg]
    exact mul_le_mul_of_nonneg_left (E.probability_sub_le_effectDistance τ υ) ha
  · rcases ha.eq_or_lt with rfl | hpos
    · simp [effectDistance_nonneg]
    · have hdiv : effectDistance τ υ ≤ effectDistance ρ σ / a := by
        apply (effectDistance_le_iff _ _ _).mpr
        intro E
        apply (le_div_iff₀ hpos).mpr
        have he := E.probability_sub_le_effectDistance ρ σ
        rw [hg] at he
        simpa only [mul_comm] using he
      have hl := (le_div_iff₀ hpos).mp hdiv
      simpa only [mul_comm] using hl

/-- The complex trace is retained for arbitrary, possibly non-Hermitian input. -/
theorem doob_branch_formula (X : Operator (Fin 2)) :
    transformedInstrument.branch () X =
      (1/3 : ℝ) • X + (2/3 : ℝ) • (X.trace • plus.matrix) := by
  rw [transformed_branch_formula, plus_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [plusMatrix, Complex.real_smul] <;> ring

theorem doob_branch_trace (X : Operator (Fin 2)) :
    (transformedInstrument.branch () X).trace = X.trace := by
  simpa only [Instrument.channel, Fintype.sum_unique] using
    transformedInstrument.trace_channel X

/-- All finite iterations of the actual one-outcome Doob instrument. -/
theorem doob_successOperator_formula (n : ℕ) (X : Operator (Fin 2)) :
    successOperator transformedInstrument () n X =
      decay n • X + (1 - decay n) • (X.trace • plus.matrix) := by
  induction n generalizing X with
  | zero => simp
  | succ n ih =>
    rw [successOperator_succ, ih, doob_branch_trace, doob_branch_formula, decay_succ]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
    push_cast
    ring

/-- The actual complete-channel density trajectory has the same exact formula. -/
theorem doob_iterateState_matrix (τ : Density (Fin 2)) (n : ℕ) :
    (Cesaro.iterateState transformedInstrument τ n).matrix =
      decay n • τ.matrix + (1 - decay n) • plus.matrix := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Cesaro.iterateState_succ, Instrument.channelState_matrix,
      Instrument.channel, Fintype.sum_unique, doob_branch_formula,
      (Cesaro.iterateState transformedInstrument τ n).trace_one, one_smul, ih,
      decay_succ]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
    push_cast
    ring

theorem doob_stationary_plus : transformedInstrument.channelState plus = plus :=
  doob_channelState filter sourceInstrument true (3/16) (by norm_num)
    source_left_eigen rho source_right_eigen

/-- Uniqueness follows from the exact matrix equation, not metric separation. -/
theorem doob_stationary_unique (τ : Density (Fin 2))
    (hτ : transformedInstrument.channelState τ = τ) : τ = plus := by
  apply Density.ext
  have h := congrArg Density.matrix hτ
  rw [Instrument.channelState_matrix, Instrument.channel, Fintype.sum_unique,
    doob_branch_formula, τ.trace_one, one_smul] at h
  ext i j
  have hij := congrArg (fun X : Operator (Fin 2) => X i j) h
  simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul] at hij
  norm_num at hij
  rw [plus_matrix]
  linear_combination -(3/2 : ℂ) * hij

theorem doob_effectDistance_exact (τ υ : Density (Fin 2)) (n : ℕ) :
    effectDistance (Cesaro.iterateState transformedInstrument τ n)
      (Cesaro.iterateState transformedInstrument υ n) =
      decay n * effectDistance τ υ := by
  apply effectDistance_eq_of_matrix_sub_smul _ _ _ _ _ (decay_pos n).le
  rw [doob_iterateState_matrix, doob_iterateState_matrix]
  module

/-- Convergence of the entire orbit in the usual finite matrix topology. -/
theorem doob_matrix_tendsto (τ : Density (Fin 2)) :
    Tendsto (fun n => (Cesaro.iterateState transformedInstrument τ n).matrix)
      atTop (𝓝 plus.matrix) := by
  simp_rw [doob_iterateState_matrix]
  have hτ : Tendsto (fun _ : ℕ => τ.matrix) atTop (𝓝 τ.matrix) := tendsto_const_nhds
  have hσ : Tendsto (fun _ : ℕ => plus.matrix) atTop (𝓝 plus.matrix) := tendsto_const_nhds
  have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  simpa using (decay_tendsto.smul hτ).add ((h1.sub decay_tendsto).smul hσ)

/-- A normalization factor; it is not the physical success probability. -/
def filterMass (τ : Density (Fin 2)) : ℝ := mass (filter.apply τ.matrix)

def pullbackWeight (τ : Density (Fin 2)) : ℝ := (5/8) * filterMass τ

def normalizer (τ : Density (Fin 2)) (n : ℕ) : ℝ :=
  decay n + (1 - decay n) * pullbackWeight τ

theorem filterMass_diag (τ : Density (Fin 2)) :
    filterMass τ = 4 * (τ.matrix 0 0).re + (τ.matrix 1 1).re := by
  norm_num [filterMass, InvertibleFilter.apply, filter, S, mass,
    Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply,
    Matrix.trace, Fin.sum_univ_succ, Complex.mul_re] <;> ring

theorem filterMass_trace (τ : Density (Fin 2)) :
    (filterMass τ : ℂ) = (filter.apply τ.matrix).trace := by
  apply Complex.ext
  · simp [filterMass, mass]
  · simpa using (trace_im_eq_zero (filter.apply_posSemidef τ.positive)).symm

theorem filterMass_metric_trace (τ : Density (Fin 2)) :
    (filterMass τ : ℂ) = (filter.metric * τ.matrix).trace := by
  rw [filterMass_trace]
  exact Matrix.trace_mul_cycle filter.matrix τ.matrix filter.matrixᴴ

theorem filterMass_bounds (τ : Density (Fin 2)) :
    1 ≤ filterMass τ ∧ filterMass τ ≤ 4 := by
  have h0 : 0 ≤ (τ.matrix 0 0).re :=
    (Complex.nonneg_iff.mp (τ.positive.diag_nonneg (i := 0))).1
  have h1 : 0 ≤ (τ.matrix 1 1).re :=
    (Complex.nonneg_iff.mp (τ.positive.diag_nonneg (i := 1))).1
  have ht : (τ.matrix 0 0).re + (τ.matrix 1 1).re = 1 := by
    have h := congrArg Complex.re τ.trace_one
    simpa [Matrix.trace, Fin.sum_univ_succ] using h
  rw [filterMass_diag]
  constructor <;> linarith

theorem pullbackWeight_bounds (τ : Density (Fin 2)) :
    5/8 ≤ pullbackWeight τ ∧ pullbackWeight τ ≤ 5/2 := by
  have h := filterMass_bounds τ
  unfold pullbackWeight
  constructor <;> linarith

theorem normalizer_bounds (τ : Density (Fin 2)) (n : ℕ) :
    5/8 ≤ normalizer τ n ∧ normalizer τ n ≤ 5/2 := by
  have ha := (decay_pos n).le
  have ha1 := decay_le_one n
  have hb := pullbackWeight_bounds τ
  have hlo := mul_le_mul_of_nonneg_left hb.1 (sub_nonneg.mpr ha1)
  have hhi := mul_le_mul_of_nonneg_left hb.2 (sub_nonneg.mpr ha1)
  unfold normalizer
  constructor <;> nlinarith

theorem normalizer_pos (τ : Density (Fin 2)) (n : ℕ) :
    0 < normalizer τ n := lt_of_lt_of_le (by norm_num) (normalizer_bounds τ n).1

theorem unapply_plus : filter.unapply plus.matrix = (5/8 : ℝ) • rho.matrix := by
  rw [plus_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [InvertibleFilter.unapply, filter, T, plusMatrix, rho, rhoMatrix,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Complex.real_smul, map_ofNat]

/-- Pulling back the actual Doob iteration yields the source iteration on every
complex matrix; no Hermitian, trace-one, or commutativity restriction is imposed. -/
theorem source_successOperator_formula (n : ℕ) (X : Operator (Fin 2)) :
    successOperator sourceInstrument true n X =
      (3/16 : ℝ)^n • (decay n • X +
        (1 - decay n) • ((filter.apply X).trace • ((5/8 : ℝ) • rho.matrix))) := by
  have h := doob_successOperator_apply filter sourceInstrument true (3/16)
    (by norm_num) source_left_eigen n X
  change successOperator transformedInstrument () n (filter.apply X) = _ at h
  rw [doob_successOperator_formula] at h
  have hu := congrArg filter.unapply h
  have hadd (A B : Operator (Fin 2)) : filter.unapply (A + B) =
      filter.unapply A + filter.unapply B := by
    simp only [InvertibleFilter.unapply, Matrix.mul_add, Matrix.add_mul]
  have hreal (s : ℝ) (A : Operator (Fin 2)) : filter.unapply (s • A) =
      s • filter.unapply A := by
    simp only [InvertibleFilter.unapply, Matrix.mul_smul, Matrix.smul_mul]
  have hcomplex (s : ℂ) (A : Operator (Fin 2)) : filter.unapply (s • A) =
      s • filter.unapply A := by
    simp only [InvertibleFilter.unapply, Matrix.mul_smul, Matrix.smul_mul]
  simp only [hadd, hreal, hcomplex, filter.unapply_apply, unapply_plus] at hu
  calc
    successOperator sourceInstrument true n X =
        (3/16 : ℝ)^n • (((3/16 : ℝ)⁻¹)^n •
          successOperator sourceInstrument true n X) := by
      rw [smul_smul, ← mul_pow, mul_inv_cancel₀ (by norm_num : (3/16 : ℝ) ≠ 0)]
      simp
    _ = _ := by rw [← hu]

theorem source_successOperator_density (τ : Density (Fin 2)) (n : ℕ) :
    successOperator sourceInstrument true n τ.matrix =
      (3/16 : ℝ)^n • (decay n • τ.matrix +
        ((1 - decay n) * pullbackWeight τ) • rho.matrix) := by
  rw [source_successOperator_formula, ← filterMass_trace]
  congr 1
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, pullbackWeight]
  push_cast
  ring

/-- This is the actual physical finite-record mass, not filtered mass. -/
theorem source_successMass_formula (τ : Density (Fin 2)) (n : ℕ) :
    successMass sourceInstrument true τ n = (3/16 : ℝ)^n * normalizer τ n := by
  simp only [successMass, source_successOperator_density, mass_smul]
  congr 1
  simp [mass, Matrix.trace_add, Matrix.trace_smul, τ.trace_one, rho.trace_one,
    Complex.real_smul, normalizer]

theorem source_response_formula (τ : Density (Fin 2)) (n : ℕ) :
    response (fun _ : Unit => sourceInstrument) τ (List.replicate n ((), true)) =
      (3/16 : ℝ)^n * normalizer τ n :=
  source_successMass_formula τ n

theorem source_successMass_pos (τ : Density (Fin 2)) (n : ℕ) :
    0 < successMass sourceInstrument true τ n := by
  rw [source_successMass_formula]
  exact mul_pos (pow_pos (by norm_num) n) (normalizer_pos τ n)

theorem source_successMass_bounds (τ : Density (Fin 2)) (n : ℕ) :
    (5/8 : ℝ) * (3/16 : ℝ)^n ≤ successMass sourceInstrument true τ n ∧
    successMass sourceInstrument true τ n ≤ (5/2 : ℝ) * (3/16 : ℝ)^n := by
  rw [source_successMass_formula]
  have hr : 0 ≤ (3/16 : ℝ)^n := (pow_pos (by norm_num) n).le
  constructor
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_left (normalizer_bounds τ n).1 hr
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_left (normalizer_bounds τ n).2 hr

theorem source_conditionalState_matrix (τ : Density (Fin 2)) (n : ℕ)
    (hp : 0 < successMass sourceInstrument true τ n) :
    (conditionalState sourceInstrument true τ n hp).matrix =
      (decay n / normalizer τ n) • τ.matrix +
      (((1 - decay n) * pullbackWeight τ) / normalizer τ n) • rho.matrix := by
  change (successMass sourceInstrument true τ n)⁻¹ •
    successOperator sourceInstrument true n τ.matrix = _
  rw [source_successMass_formula, source_successOperator_density, smul_smul]
  have hn := (normalizer_pos τ n).ne'
  have hr : (3/16 : ℝ)^n ≠ 0 := pow_ne_zero n (by norm_num)
  have hs : ((3/16 : ℝ)^n * normalizer τ n)⁻¹ * (3/16 : ℝ)^n =
      (normalizer τ n)⁻¹ := by field_simp
  rw [hs, smul_add, smul_smul, smul_smul]
  simp only [div_eq_mul_inv, mul_comm]

/-- The actual finite conditional state, with positivity proved for every input. -/
def conditioned (τ : Density (Fin 2)) (n : ℕ) : Density (Fin 2) :=
  conditionalState sourceInstrument true τ n (source_successMass_pos τ n)

theorem conditioned_matrix (τ : Density (Fin 2)) (n : ℕ) :
    (conditioned τ n).matrix =
      (decay n / normalizer τ n) • τ.matrix +
      (((1 - decay n) * pullbackWeight τ) / normalizer τ n) • rho.matrix :=
  source_conditionalState_matrix τ n _

theorem conditioned_matrix_affine (τ : Density (Fin 2)) (n : ℕ) :
    (conditioned τ n).matrix =
      (decay n / normalizer τ n) • τ.matrix +
      (1 - decay n / normalizer τ n) • rho.matrix := by
  rw [conditioned_matrix]
  have hnum : (1 - decay n) * pullbackWeight τ = normalizer τ n - decay n := by
    unfold normalizer
    ring
  rw [hnum, sub_div, div_self (normalizer_pos τ n).ne']

theorem conditioned_matrix_sub (τ : Density (Fin 2)) (n : ℕ) :
    (conditioned τ n).matrix - rho.matrix =
      (decay n / normalizer τ n) • (τ.matrix - rho.matrix) := by
  rw [conditioned_matrix_affine]
  module

/-- Exact contraction is with respect to every finite-dimensional quantum effect. -/
theorem conditioned_effectDistance_exact (τ : Density (Fin 2)) (n : ℕ) :
    effectDistance (conditioned τ n) rho =
      (decay n / normalizer τ n) * effectDistance τ rho :=
  effectDistance_eq_of_matrix_sub_smul _ _ _ _ _
    (div_nonneg (decay_pos n).le (normalizer_pos τ n).le) (conditioned_matrix_sub τ n)

theorem conditioned_effectDistance_le (τ : Density (Fin 2)) (n : ℕ) :
    effectDistance (conditioned τ n) rho ≤
      (8/5 : ℝ) * decay n * effectDistance τ rho := by
  rw [conditioned_effectDistance_exact]
  apply mul_le_mul_of_nonneg_right _ (effectDistance_nonneg τ rho)
  have h := div_le_div_of_nonneg_left (decay_pos n).le
    (by norm_num : (0 : ℝ) < 5/8) (normalizer_bounds τ n).1
  calc
    decay n / normalizer τ n ≤ decay n / (5/8) := h
    _ = (8/5 : ℝ) * decay n := by ring

theorem normalizer_tendsto (τ : Density (Fin 2)) :
    Tendsto (normalizer τ) atTop (𝓝 (pullbackWeight τ)) := by
  unfold normalizer
  have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hb : Tendsto (fun _ : ℕ => pullbackWeight τ) atTop
      (𝓝 (pullbackWeight τ)) := tendsto_const_nhds
  simpa only [sub_zero, one_mul, zero_add] using
    decay_tendsto.add ((h1.sub decay_tendsto).mul hb)

theorem conditionalWeight_tendsto (τ : Density (Fin 2)) :
    Tendsto (fun n => decay n / normalizer τ n) atTop (𝓝 (0 : ℝ)) := by
  have hb : 0 < pullbackWeight τ := lt_of_lt_of_le (by norm_num) (pullbackWeight_bounds τ).1
  convert decay_tendsto.div (normalizer_tendsto τ) hb.ne' using 1 <;>
    first | rfl | simp only [zero_div]

theorem conditioned_matrix_tendsto (τ : Density (Fin 2)) :
    Tendsto (fun n => (conditioned τ n).matrix) atTop (𝓝 rho.matrix) := by
  simp_rw [conditioned_matrix_affine]
  have hτ : Tendsto (fun _ : ℕ => τ.matrix) atTop (𝓝 τ.matrix) := tendsto_const_nhds
  have hρ : Tendsto (fun _ : ℕ => rho.matrix) atTop (𝓝 rho.matrix) := tendsto_const_nhds
  have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  simpa using ((conditionalWeight_tendsto τ).smul hτ).add
    ((h1.sub (conditionalWeight_tendsto τ)).smul hρ)

theorem conditioned_effectDistance_tendsto (τ : Density (Fin 2)) :
    Tendsto (fun n => effectDistance (conditioned τ n) rho) atTop (𝓝 (0 : ℝ)) := by
  simp_rw [conditioned_effectDistance_exact]
  simpa using (conditionalWeight_tendsto τ).mul_const (effectDistance τ rho)

/-- Actual finite success probabilities vanish although every finite one is
positive and the corresponding conditional states converge. No infinite path
measure or event is assumed in this assertion. -/
theorem source_successMass_tendsto_zero (τ : Density (Fin 2)) :
    Tendsto (successMass sourceInstrument true τ) atTop (𝓝 (0 : ℝ)) := by
  change Tendsto (fun n => successMass sourceInstrument true τ n) atTop (𝓝 (0 : ℝ))
  simp_rw [source_successMass_formula]
  have hr : Tendsto (fun n : ℕ => (3/16 : ℝ)^n) atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa only [zero_mul] using hr.mul (normalizer_tendsto τ)

@[simp] theorem filterMass_rho : filterMass rho = 8/5 := filtered_mass_exact

@[simp] theorem pullbackWeight_rho : pullbackWeight rho = 1 := by
  norm_num [pullbackWeight]

@[simp] theorem normalizer_rho (n : ℕ) : normalizer rho n = 1 := by
  simp [normalizer]

theorem source_successMass_rho (n : ℕ) :
    successMass sourceInstrument true rho n = (3/16 : ℝ)^n := by
  simp [source_successMass_formula]

end
end UEOTQM.QuantumDoobDynamics
