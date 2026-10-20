import UEOTQM.QuantumDoobDynamics

/-!
# Exact finite survival dynamics and the identity-Doob negative control

The positive checks use the same rational, noncommuting source model as v31.6.
The separate negative control supplies an actual complete instrument, a positive
left eigenmetric and a positive survival rate, yet its Doob channel is identity.
Thus those spectral/filter assumptions alone do not imply unique attraction.
-/

namespace UEOTQM.QuantumDoobDynamicsExamples

open Matrix Filter
open UEOTQM.QuantumDoob UEOTQM.QuantumDoobModel UEOTQM.QuantumDoobDynamics
open scoped BigOperators ComplexOrder Topology

noncomputable section

def uniformDensity : Density (Fin 2) where
  matrix := (1/2 : ℝ) • (1 : Operator (Fin 2))
  positive := Matrix.PosSemidef.one.smul (by norm_num)
  trace_one := by norm_num [Matrix.trace, Fin.sum_univ_succ, Complex.real_smul]

theorem uniform_filterMass : filterMass uniformDensity = 5/2 := by
  rw [filterMass_diag]
  norm_num [uniformDensity, Complex.real_smul]

theorem uniform_pullbackWeight : pullbackWeight uniformDensity = 25/16 := by
  norm_num [pullbackWeight, uniform_filterMass]

theorem uniform_successMass_one :
    successMass sourceInstrument true uniformDensity 1 = 33/128 := by
  rw [source_successMass_formula]
  norm_num [normalizer, uniform_pullbackWeight, decay]

theorem uniform_successMass_one_ne_rate :
    successMass sourceInstrument true uniformDensity 1 ≠ (3/16 : ℝ) := by
  rw [uniform_successMass_one]
  norm_num

theorem uniform_conditioned_one :
    (conditioned uniformDensity 1).matrix =
      (!![3/11, 10/33; 10/33, 8/11] : Operator (Fin 2)) := by
  rw [conditioned_matrix]
  simp only [normalizer, uniform_pullbackWeight]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [decay, uniformDensity, rho, rhoMatrix, Complex.real_smul]

theorem uniform_conditional_limit :
    Tendsto (fun n => (conditioned uniformDensity n).matrix) atTop (𝓝 rho.matrix) :=
  conditioned_matrix_tendsto uniformDensity

theorem uniform_successMass_limit :
    Tendsto (successMass sourceInstrument true uniformDensity) atTop (𝓝 (0 : ℝ)) :=
  source_successMass_tendsto_zero uniformDensity

/-- The off-diagonal complex input is not replaced by a diagonal surrogate. -/
theorem coherent_input_two_steps :
    successOperator transformedInstrument () 2
      (!![0, Complex.I; 0, 0] : Operator (Fin 2)) =
      (!![0, Complex.I/9; 0, 0] : Operator (Fin 2)) := by
  rw [doob_successOperator_formula]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [decay, Matrix.trace, Fin.sum_univ_succ, Complex.real_smul] <;> ring

/-- One success Kraus I/2 and three failure Kraus I/2 form a complete source. -/
def identitySourceK (o : Bool) (k : Fin 3) : Operator (Fin 2) :=
  if o then (if k = 0 then !![1/2, 0; 0, 1/2] else 0)
  else !![1/2, 0; 0, 1/2]

theorem identitySource_complete :
    (∑ o, ∑ k, (identitySourceK o k)ᴴ * identitySourceK o k) =
      (1 : Operator (Fin 2)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Fintype.sum_bool, identitySourceK, Matrix.ofNat_apply, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, map_ofNat, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ]

def identitySource : Instrument (Fin 2) Bool (Fin 3) where
  kraus := identitySourceK
  complete := identitySource_complete

theorem identitySource_branch (X : Operator (Fin 2)) :
    identitySource.branch true X = (1/4 : ℝ) • X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Instrument.branch, krausMap, identitySource, identitySourceK,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, map_ofNat,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ, Complex.real_smul] <;> ring

def identityFilter : InvertibleFilter (Fin 2) where
  matrix := 1
  inverse := 1
  inverse_mul := by simp
  mul_inverse := by simp

theorem identityFilter_metric : identityFilter.metric = 1 := by
  simp [InvertibleFilter.metric, identityFilter]

theorem identitySource_left_eigen :
    heisenberg (identitySource.kraus true) identityFilter.metric =
      (1/4 : ℝ) • identityFilter.metric := by
  rw [identityFilter_metric]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [heisenberg, identitySource, identitySourceK, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, map_ofNat, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Complex.real_smul]

def identityDoob : Instrument (Fin 2) Unit (Fin 3) :=
  doobInstrument identityFilter identitySource true (1/4) (by norm_num)
    identitySource_left_eigen

theorem identityDoob_branch (X : Operator (Fin 2)) : identityDoob.branch () X = X := by
  rw [identityDoob, doob_branch, identitySource_branch]
  norm_num [InvertibleFilter.apply, InvertibleFilter.unapply, identityFilter,
    smul_smul]

theorem identityDoob_channelState (τ : Density (Fin 2)) :
    identityDoob.channelState τ = τ := by
  apply Density.ext
  simpa only [Instrument.channelState_matrix, Instrument.channel, Fintype.sum_unique]
    using identityDoob_branch τ.matrix

theorem identityDoob_iterateState (τ : Density (Fin 2)) (n : ℕ) :
    Cesaro.iterateState identityDoob τ n = τ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Cesaro.iterateState_succ, identityDoob_channelState, ih]

theorem rho_ne_plus : rho ≠ plus := by
  intro h
  have h01 := congrArg (fun τ : Density (Fin 2) => τ.matrix 0 1) h
  rw [plus_matrix] at h01
  norm_num [rho, rhoMatrix, plusMatrix] at h01

/-- Actual positive left eigenmetric data do not imply a unique stationary state. -/
theorem identityDoob_not_unique_stationary :
    ¬ ∃ σ : Density (Fin 2), ∀ τ : Density (Fin 2),
      identityDoob.channelState τ = τ → τ = σ := by
  rintro ⟨σ, hσ⟩
  exact rho_ne_plus ((hσ rho (identityDoob_channelState rho)).trans
    (hσ plus (identityDoob_channelState plus)).symm)

/-- No density attracts every actual Doob trajectory in the matrix topology. -/
theorem identityDoob_not_common_limit :
    ¬ ∃ σ : Density (Fin 2), ∀ τ : Density (Fin 2),
      Tendsto (fun n => (Cesaro.iterateState identityDoob τ n).matrix)
        atTop (𝓝 σ.matrix) := by
  rintro ⟨σ, hσ⟩
  have hr : rho.matrix = σ.matrix := tendsto_nhds_unique tendsto_const_nhds
    (by simpa only [identityDoob_iterateState] using hσ rho)
  have hp : plus.matrix = σ.matrix := tendsto_nhds_unique tendsto_const_nhds
    (by simpa only [identityDoob_iterateState] using hσ plus)
  exact rho_ne_plus (Density.ext (hr.trans hp.symm))

theorem identitySource_successMass (τ : Density (Fin 2)) (n : ℕ) :
    successMass identitySource true τ n = (1/4 : ℝ)^n :=
  eigen_successMass identitySource true τ (1/4) (identitySource_branch τ.matrix) n

theorem identitySource_conditional_fixed (τ : Density (Fin 2)) (n : ℕ)
    (hp : 0 < successMass identitySource true τ n) :
    conditionalState identitySource true τ n hp = τ :=
  eigen_conditionalState identitySource true τ (1/4) (by norm_num)
    (identitySource_branch τ.matrix) n hp

end
end UEOTQM.QuantumDoobDynamicsExamples

/-! Every explicitly named witness definition and theorem is axiom-audited. -/
#print axioms UEOTQM.QuantumDoobDynamicsExamples.uniformDensity
#print axioms UEOTQM.QuantumDoobDynamicsExamples.uniform_filterMass
#print axioms UEOTQM.QuantumDoobDynamicsExamples.uniform_pullbackWeight
#print axioms UEOTQM.QuantumDoobDynamicsExamples.uniform_successMass_one
#print axioms UEOTQM.QuantumDoobDynamicsExamples.uniform_successMass_one_ne_rate
#print axioms UEOTQM.QuantumDoobDynamicsExamples.uniform_conditioned_one
#print axioms UEOTQM.QuantumDoobDynamicsExamples.uniform_conditional_limit
#print axioms UEOTQM.QuantumDoobDynamicsExamples.uniform_successMass_limit
#print axioms UEOTQM.QuantumDoobDynamicsExamples.coherent_input_two_steps
#print axioms UEOTQM.QuantumDoobDynamicsExamples.identitySourceK
#print axioms UEOTQM.QuantumDoobDynamicsExamples.identitySource_complete
#print axioms UEOTQM.QuantumDoobDynamicsExamples.identitySource
#print axioms UEOTQM.QuantumDoobDynamicsExamples.identitySource_branch
#print axioms UEOTQM.QuantumDoobDynamicsExamples.identityFilter
#print axioms UEOTQM.QuantumDoobDynamicsExamples.identityFilter_metric
#print axioms UEOTQM.QuantumDoobDynamicsExamples.identitySource_left_eigen
#print axioms UEOTQM.QuantumDoobDynamicsExamples.identityDoob
#print axioms UEOTQM.QuantumDoobDynamicsExamples.identityDoob_branch
#print axioms UEOTQM.QuantumDoobDynamicsExamples.identityDoob_channelState
#print axioms UEOTQM.QuantumDoobDynamicsExamples.identityDoob_iterateState
#print axioms UEOTQM.QuantumDoobDynamicsExamples.rho_ne_plus
#print axioms UEOTQM.QuantumDoobDynamicsExamples.identityDoob_not_unique_stationary
#print axioms UEOTQM.QuantumDoobDynamicsExamples.identityDoob_not_common_limit
#print axioms UEOTQM.QuantumDoobDynamicsExamples.identitySource_successMass
#print axioms UEOTQM.QuantumDoobDynamicsExamples.identitySource_conditional_fixed
