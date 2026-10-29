import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteProductSource

/-!
Original commitment: finite-dimensional controlled stochastic consumers need actual causal noise actions.
Existing result: the actual product Brownian source has whole-joint-past zero means and covariance matrix.
Premise reduced: derive a literal one-step vector-noise projection and its energy, instead of assuming isometry.
Model/witness: arbitrary finite d, bounded coefficients measurable at the SAME interval start's joint natural past.
Consumer: later vector simple predictable integration; full vector integration, Ito and Girsanov are not asserted.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorOneStepIntegral
open MeasureTheory ProbabilityTheory
open BrownianFiniteProductSource
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory BigOperators
noncomputable section

/-- Actual finite coordinate weights, read as a Euclidean vector (PiLp 2). -/
def coefficient (d : ℕ) (H : Fin d → Sample d → ℝ) (ω : Sample d) : EuclideanSpace ℝ (Fin d) :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => H i ω)

@[simp] theorem coefficient_apply (d : ℕ) (H : Fin d → Sample d → ℝ) (ω : Sample d) (i : Fin d) :
    coefficient d H ω i = H i ω := rfl

/-- Literal allowed coefficient times SAME actual source coordinate increment. -/
def component (d : ℕ) (H : Fin d → Sample d → ℝ) (i : Fin d) (s t : ℝ≥0) : Sample d → ℝ :=
  H i * coordinateIncrement d i s t

/-- The actual scalar projection of the actual vector increment. -/
def oneStep (d : ℕ) (H : Fin d → Sample d → ℝ) (s t : ℝ≥0) (ω : Sample d) : ℝ :=
  ∑ i : Fin d, component d H i s t ω

theorem oneStep_eq_inner (d : ℕ) (H : Fin d → Sample d → ℝ) (s t : ℝ≥0) (ω : Sample d) :
    oneStep d H s t ω = inner ℝ (coefficient d H ω) (vectorIncrement d s t ω) := by
  simp only [oneStep,PiLp.inner_apply,Real.inner_apply,coefficient_apply,vectorIncrement_apply,
    component,Pi.mul_apply]

theorem component_memLp_two {d : ℕ} {H : Fin d → Sample d → ℝ} (i : Fin d)
    (hH : MemLp (H i) ∞ (productLaw d)) (s t : ℝ≥0) :
    MemLp (component d H i s t) 2 (productLaw d) :=
  (coordinateIncrement_memLp_two d i s t).mul hH

theorem oneStep_memLp_two {d : ℕ} {H : Fin d → Sample d → ℝ}
    (hH : ∀ i, MemLp (H i) ∞ (productLaw d)) (s t : ℝ≥0) :
    MemLp (oneStep d H s t) 2 (productLaw d) :=
  memLp_finsetSum Finset.univ (fun i _ => component_memLp_two i (hH i) s t)

theorem component_stronglyMeasurable_end {d : ℕ} {H : Fin d → Sample d → ℝ}
    (i : Fin d) (s t : ℝ≥0) (hst : s ≤ t)
    (hHpast : StronglyMeasurable[jointNaturalFiltration d s] (H i)) :
    StronglyMeasurable[jointNaturalFiltration d t] (component d H i s t) := by
  have hc (r : ℝ≥0) : StronglyMeasurable[jointNaturalFiltration d r] (coordinate d i r) :=
    (EuclideanSpace.proj (𝕜:=ℝ) i).continuous.comp_stronglyMeasurable (vectorProcess_stronglyAdapted d r)
  exact (hHpast.mono ((jointNaturalFiltration d).mono hst)).mul
    ((hc t).sub ((hc s).mono ((jointNaturalFiltration d).mono hst)))

/-- Original joint-past permissions, not separate own-coordinate permissions. -/
theorem component_condExp_zero {d : ℕ} {H : Fin d → Sample d → ℝ}
    (i : Fin d) (s t : ℝ≥0) (hst : s ≤ t)
    (hHpast : StronglyMeasurable[jointNaturalFiltration d s] (H i))
    (hH : MemLp (H i) ∞ (productLaw d)) :
    (productLaw d)[component d H i s t | jointNaturalFiltration d s] =ᵐ[productLaw d]
      fun _ => (0 : ℝ) := by
  apply (condExp_mul_of_stronglyMeasurable_left hHpast
    ((component_memLp_two i hH s t).integrable (by norm_num))
    (coordinateIncrement_integrable d i s t)).trans
  filter_upwards [coordinateIncrement_condExp d i s t hst] with ω hω
  simp only [Pi.mul_apply,hω,mul_zero]

/-- Causal bounded weights preserve the source-derived full covariance matrix. -/
theorem component_condExp_product {d : ℕ} {H : Fin d → Sample d → ℝ}
    (i j : Fin d) (s t : ℝ≥0) (hst : s ≤ t)
    (hHpast : ∀ k, StronglyMeasurable[jointNaturalFiltration d s] (H k))
    (hH : ∀ k, MemLp (H k) ∞ (productLaw d)) :
    (productLaw d)[fun ω => component d H i s t ω * component d H j s t ω |
      jointNaturalFiltration d s] =ᵐ[productLaw d]
      fun ω => (H i ω * H j ω) * (if i = j then (t : ℝ)-(s : ℝ) else 0) := by
  have he : (fun ω => component d H i s t ω * component d H j s t ω) =
      (H i * H j) * (fun ω => coordinateIncrement d i s t ω * coordinateIncrement d j s t ω) := by
    funext ω
    simp only [component,Pi.mul_apply]
    ring
  have hint : Integrable
      ((H i * H j) * (fun ω => coordinateIncrement d i s t ω * coordinateIncrement d j s t ω))
      (productLaw d) := by
    rw [← he]
    exact (component_memLp_two i (hH i) s t).integrable_mul (component_memLp_two j (hH j) s t)
  rw [he]
  apply (condExp_mul_of_stronglyMeasurable_left ((hHpast i).mul (hHpast j)) hint
    (coordinateIncrement_product_integrable d i j s t)).trans
  filter_upwards [coordinateIncrement_condExp_product d i j s t hst] with ω hω
  simp only [Pi.mul_apply,hω]

theorem component_product_mean {d : ℕ} {H : Fin d → Sample d → ℝ}
    (i j : Fin d) (s t : ℝ≥0) (hst : s ≤ t)
    (hHpast : ∀ k, StronglyMeasurable[jointNaturalFiltration d s] (H k))
    (hH : ∀ k, MemLp (H k) ∞ (productLaw d)) :
    (∫ ω, component d H i s t ω * component d H j s t ω ∂productLaw d) =
      if i = j then ((t : ℝ)-(s : ℝ)) * (∫ ω, H i ω ^ 2 ∂productLaw d) else 0 := by
  rw [← integral_condExp ((jointNaturalFiltration d).le s),
    integral_congr_ae (component_condExp_product i j s t hst hHpast hH)]
  by_cases hij : i = j
  · subst j
    simp only [ite_true,← pow_two]
    rw [integral_mul_const,mul_comm]
  · simp only [if_neg hij,mul_zero,integral_zero]

theorem oneStep_condExp_zero {d : ℕ} {H : Fin d → Sample d → ℝ}
    (s t : ℝ≥0) (hst : s ≤ t)
    (hHpast : ∀ k, StronglyMeasurable[jointNaturalFiltration d s] (H k))
    (hH : ∀ k, MemLp (H k) ∞ (productLaw d)) :
    (productLaw d)[oneStep d H s t | jointNaturalFiltration d s] =ᵐ[productLaw d]
      fun _ => (0 : ℝ) := by
  have hs := condExp_finsetSum (s := Finset.univ)
    (fun i _ => (component_memLp_two i (hH i) s t).integrable (by norm_num))
    (jointNaturalFiltration d s)
  have he : (∑ i : Fin d, component d H i s t) = oneStep d H s t := by
    funext ω
    simp only [Finset.sum_apply,oneStep]
  rw [he] at hs
  apply hs.trans
  have hz := ae_all_iff.mpr (fun i => component_condExp_zero i s t hst (hHpast i) (hH i))
  filter_upwards [hz] with ω hω
  simp only [Finset.sum_apply,hω,Finset.sum_const_zero]

/-- Actual one-step vector-noise isometry with the GENUINE Euclidean coefficient norm. -/
theorem oneStep_isometry {d : ℕ} {H : Fin d → Sample d → ℝ}
    (s t : ℝ≥0) (hst : s ≤ t)
    (hHpast : ∀ k, StronglyMeasurable[jointNaturalFiltration d s] (H k))
    (hH : ∀ k, MemLp (H k) ∞ (productLaw d)) :
    (∫ ω, oneStep d H s t ω ^ 2 ∂productLaw d) =
      ((t : ℝ)-(s : ℝ)) * (∫ ω, ‖coefficient d H ω‖ ^ 2 ∂productLaw d) := by
  have hprod (i j : Fin d) : Integrable
      (fun ω => component d H i s t ω * component d H j s t ω) (productLaw d) :=
    (component_memLp_two i (hH i) s t).integrable_mul (component_memLp_two j (hH j) s t)
  have he : (fun ω => oneStep d H s t ω ^ 2) =
      (fun ω => ∑ i : Fin d, ∑ j : Fin d, component d H i s t ω * component d H j s t ω) := by
    funext ω
    simp only [oneStep,pow_two,Fintype.sum_mul_sum]
  rw [he,integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hprod i j))]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => hprod _ j),
    component_product_mean _ _ s t hst hHpast hH]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
  simp_rw [EuclideanSpace.real_norm_sq_eq,coefficient_apply]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    ((hH i).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ ∞)).integrable_sq),Finset.mul_sum]


/-- The same literal returned sum has the end-time permission needed by a
later interval. Coefficients may read ALL coordinates' start-time past. -/
theorem oneStep_stronglyMeasurable_end {d : ℕ} {H : Fin d → Sample d → ℝ}
    (s t : ℝ≥0) (hst : s ≤ t)
    (hHpast : ∀ k, StronglyMeasurable[jointNaturalFiltration d s] (H k)) :
    StronglyMeasurable[jointNaturalFiltration d t] (oneStep d H s t) :=
  Finset.stronglyMeasurable_fun_sum Finset.univ
    (fun i _ => component_stronglyMeasurable_end i s t hst (hHpast i))

theorem oneStep_mean_zero {d : ℕ} {H : Fin d → Sample d → ℝ}
    (s t : ℝ≥0) (hst : s ≤ t)
    (hHpast : ∀ k, StronglyMeasurable[jointNaturalFiltration d s] (H k))
    (hH : ∀ k, MemLp (H k) ∞ (productLaw d)) :
    (∫ ω, oneStep d H s t ω ∂productLaw d) = 0 := by
  rw [← integral_condExp ((jointNaturalFiltration d).le s),
    integral_congr_ae (oneStep_condExp_zero s t hst hHpast hH),integral_zero]

/-- Dimension zero is retained: the literal projection of no coordinates is zero. -/
theorem oneStep_zero_dimension (H : Fin 0 → Sample 0 → ℝ) (s t : ℝ≥0) (ω : Sample 0) :
    oneStep 0 H s t ω = 0 := by simp [oneStep]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorOneStepIntegral
