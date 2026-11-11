import UEOTQM.Mixture
import UEOTQM.QuantumFiniteWindow
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# An actual scaled filter and the source-record retry cost

The accepted filter Kraus operator is sqrt(1/c) B, with H = B†B.  A PSD
residual constructs the other Kraus operator.  Its probability p/c and its
normalized output are derived from that complete instrument.

The retry-cost recursion is an explicit finite tree of independent draws from
one finite source RECORD law.  A record cost may depend on success/failure;
it is the actual early-stop cost, not a fixed padded horizon cost.
-/

namespace UEOTQM.QuantumInitializationCost

open Matrix Filter
open scoped BigOperators ComplexOrder MatrixOrder Topology

noncomputable section

section Filter

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Obtain an actual Gram factor from PSD; no square-root algorithm is claimed. -/
def gramFactor (X : Operator ι) (hX : X.PosSemidef) : Operator ι :=
  Classical.choose (CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX.nonneg)

theorem gramFactor_gram (X : Operator ι) (hX : X.PosSemidef) :
    (gramFactor X hX)ᴴ * gramFactor X hX = X := by
  exact (Classical.choose_spec
    (CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX.nonneg)).symm

/-- `true` is filter success.  The residual condition is precisely admissible
Kraus contraction; c >= ||H|| and c > 0 suffice for canonical B = sqrt(H). -/
def filterInstrument (B : Operator ι) (c : ℝ) (hc : 0 < c)
    (hresidual : (1 - c⁻¹ • (Bᴴ * B)).PosSemidef) : Instrument ι Bool Unit where
  kraus o _ := if o = true then Real.sqrt (c⁻¹) • B
    else gramFactor (1 - c⁻¹ • (Bᴴ * B)) hresidual
  complete := by
    simp only [Fintype.sum_bool, Fintype.sum_unique]
    change (Real.sqrt (c⁻¹) • B)ᴴ * (Real.sqrt (c⁻¹) • B) +
      (gramFactor (1 - c⁻¹ • (Bᴴ * B)) hresidual)ᴴ *
        gramFactor (1 - c⁻¹ • (Bᴴ * B)) hresidual = 1
    rw [sqrt_smul_gram c⁻¹ B (inv_nonneg.mpr hc.le), gramFactor_gram]
    abel

theorem filter_success_branch (B : Operator ι) (c : ℝ) (hc : 0 < c)
    (hresidual : (1 - c⁻¹ • (Bᴴ * B)).PosSemidef) (X : Operator ι) :
    (filterInstrument B c hc hresidual).branch true X = c⁻¹ • (B * X * Bᴴ) := by
  simp only [Instrument.branch, krausMap, filterInstrument, if_pos rfl,
    Fintype.sum_unique]
  exact sqrt_smul_krausTerm c⁻¹ B X (inv_nonneg.mpr hc.le)

theorem gram_filter_mass (B X : Operator ι) :
    mass (B * X * Bᴴ) = pairing (Bᴴ * B) X := by
  exact congrArg Complex.re (Matrix.trace_mul_cycle B X Bᴴ)

/-- Actual physical acceptance probability is p/c, not p for arbitrary c. -/
theorem filter_success_probability (B : Operator ι) (c : ℝ) (hc : 0 < c)
    (hresidual : (1 - c⁻¹ • (Bᴴ * B)).PosSemidef) (ρ : Density ι) :
    (filterInstrument B c hc hresidual).probability ρ true =
      pairing (Bᴴ * B) ρ.matrix / c := by
  rw [Instrument.probability, filter_success_branch, mass_smul, gram_filter_mass]
  ring

theorem filter_success_probability_pos (B : Operator ι) (c : ℝ) (hc : 0 < c)
    (hresidual : (1 - c⁻¹ • (Bᴴ * B)).PosSemidef) (ρ : Density ι)
    (hp : 0 < pairing (Bᴴ * B) ρ.matrix) :
    0 < (filterInstrument B c hc hresidual).probability ρ true := by
  rw [filter_success_probability]
  exact div_pos hp hc

/-- Changing the physical scale changes the rate, not the accepted state. -/
theorem filter_posterior_matrix (B : Operator ι) (c : ℝ) (hc : 0 < c)
    (hresidual : (1 - c⁻¹ • (Bᴴ * B)).PosSemidef) (ρ : Density ι)
    (hp : 0 < pairing (Bᴴ * B) ρ.matrix) :
    ((filterInstrument B c hc hresidual).posterior ρ true
      (filter_success_probability_pos B c hc hresidual ρ hp)).matrix =
      (pairing (Bᴴ * B) ρ.matrix)⁻¹ • (B * ρ.matrix * Bᴴ) := by
  rw [Instrument.posterior_matrix, filter_success_probability,
    filter_success_branch, smul_smul]
  congr 1
  field_simp [hc.ne', hp.ne']

theorem scaled_filter_mean_attempts (p c : ℝ) (hp : 0 < p) (hc : 0 < c) :
    (p / c)⁻¹ = c / p := by
  field_simp [hp.ne', hc.ne']

end Filter

section Retry

variable {R : Type*} [Fintype R]

def successProbability (w : Mixture.Weights R) (accepted : R → Bool) : ℝ :=
  ∑ r, if accepted r then w.weight r else 0

def meanTrialCost (w : Mixture.Weights R) (cost : R → ℝ) : ℝ :=
  ∑ r, w.weight r * cost r

/-- The finite repeated-source tree, truncated after n independent trials. -/
def retryTreeCost (w : Mixture.Weights R) (accepted : R → Bool) (cost : R → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => ∑ r, w.weight r *
      (cost r + if accepted r then 0 else retryTreeCost w accepted cost n)

theorem successProbability_nonneg (w : Mixture.Weights R) (accepted : R → Bool) :
    0 ≤ successProbability w accepted := by
  apply Finset.sum_nonneg
  intro r _
  cases h : accepted r <;> simp [h, w.nonneg r]

theorem failureWeight_eq (w : Mixture.Weights R) (accepted : R → Bool) :
    (∑ r, if accepted r then 0 else w.weight r) = 1 - successProbability w accepted := by
  have hs : successProbability w accepted +
      (∑ r, if accepted r then 0 else w.weight r) = 1 := by
    rw [successProbability, ← Finset.sum_add_distrib]
    convert w.sum_one using 1
    apply Finset.sum_congr rfl
    intro r _
    cases h : accepted r <;> simp [h]
  linarith

theorem successProbability_le_one (w : Mixture.Weights R) (accepted : R → Bool) :
    successProbability w accepted ≤ 1 := by
  have hn : 0 ≤ ∑ r, if accepted r then 0 else w.weight r := by
    apply Finset.sum_nonneg
    intro r _
    cases h : accepted r <;> simp [h, w.nonneg r]
  rw [failureWeight_eq] at hn
  linarith

/-- The mean cost separates from the fresh continuation despite correlation
between this trial's early-stop cost and this trial's success event. -/
theorem retryTreeCost_succ (w : Mixture.Weights R) (accepted : R → Bool)
    (cost : R → ℝ) (n : ℕ) :
    retryTreeCost w accepted cost (n + 1) = meanTrialCost w cost +
      (1 - successProbability w accepted) * retryTreeCost w accepted cost n := by
  rw [retryTreeCost]
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  rw [← failureWeight_eq, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  cases h : accepted r <;> simp [h]

theorem retryTreeCost_closed (w : Mixture.Weights R) (accepted : R → Bool)
    (cost : R → ℝ) (hp : 0 < successProbability w accepted) (n : ℕ) :
    retryTreeCost w accepted cost n =
      (meanTrialCost w cost / successProbability w accepted) *
        (1 - (1 - successProbability w accepted) ^ n) := by
  induction n with
  | zero => simp [retryTreeCost]
  | succ n ih =>
    rw [retryTreeCost_succ, ih, pow_succ]
    field_simp [hp.ne']
    ring

/-- Exact finite-source cost limit.  For nonnegative source-record costs,
monotone convergence identifies this with the expected cost until success. -/
theorem retryTreeCost_tendsto (w : Mixture.Weights R) (accepted : R → Bool)
    (cost : R → ℝ) (hp : 0 < successProbability w accepted) :
    Tendsto (retryTreeCost w accepted cost) atTop
      (nhds (meanTrialCost w cost / successProbability w accepted)) := by
  have h0 : 0 ≤ 1 - successProbability w accepted :=
    sub_nonneg.mpr (successProbability_le_one w accepted)
  have h1 : 1 - successProbability w accepted < 1 := by linarith
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1
  have hconst : Tendsto
      (fun _ : ℕ => meanTrialCost w cost / successProbability w accepted) atTop
      (nhds (meanTrialCost w cost / successProbability w accepted)) := tendsto_const_nhds
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have h := hconst.mul (hone.sub hpow)
  have hfun : retryTreeCost w accepted cost = fun n =>
      (meanTrialCost w cost / successProbability w accepted) *
        (1 - (1 - successProbability w accepted) ^ n) :=
    funext (retryTreeCost_closed w accepted cost hp)
  rw [hfun]
  simpa only [sub_zero, mul_one] using h

end Retry

section SourceTreeBridge

open QuantumFiniteWindow

variable {ι O κ ξ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype O] [Fintype κ] [Fintype ξ]

/-- The source tree itself proves the admissibility of the unscaled initial
filter: the residual PSD premise is no longer independently supplied. -/
def sourceInitialFilter (P : FilterTree ι O κ) (h : P.Valid) : Instrument ι Bool Unit :=
  filterInstrument P.rootFilter.matrix 1 (by norm_num) (by
    simpa only [inv_one, one_smul, SupportFilter.metric] using
      P.metric_complement_posSemidef h)

theorem sourceInitialFilter_probability (J : Instrument ι O ξ)
    (P : FilterTree ι O κ) (h : P.Valid) (ρ : Density ι) :
    (sourceInitialFilter P h).probability ρ true = P.successMass ρ.matrix := by
  rw [sourceInitialFilter, filter_success_probability, div_one, ← gram_filter_mass]
  exact (FilterTree.successMass_eq_filtered_mass J P h ρ.matrix).symm

/-- Resource probabilities are the same actual original leaf probabilities
used by the finite conditioning theorem. -/
theorem source_successProbability (P : FilterTree ι O κ) (ρ : Density ι) :
    successProbability (P.sourceWeights ρ) P.accepts = P.successMass ρ.matrix :=
  P.sourceWeights_accepted_sum ρ

theorem source_retryTreeCost_tendsto (P : FilterTree ι O κ) (ρ : Density ι)
    (cost : P.Leaf → ℝ) (hp : 0 < P.successMass ρ.matrix) :
    Tendsto (retryTreeCost (P.sourceWeights ρ) P.accepts cost) atTop
      (nhds (meanTrialCost (P.sourceWeights ρ) cost / P.successMass ρ.matrix)) := by
  have hp' : 0 < successProbability (P.sourceWeights ρ) P.accepts := by
    rw [source_successProbability]
    exact hp
  simpa only [source_successProbability] using
    retryTreeCost_tendsto (P.sourceWeights ρ) P.accepts cost hp'

end SourceTreeBridge

end

end UEOTQM.QuantumInitializationCost
