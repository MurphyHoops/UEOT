import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorSimplePredictableIntegral
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianTimeIntegrand
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
Original commitment: finite vector-noise integration must bind the actual time-dependent Euclidean input.
Existing result: same product-source finite projection output has exact Euclidean coefficient energy.
Premise reduced: realize that energy as the native Euclidean-valued L2 input norm under original real time times SAME source.
Model/witness: arbitrary finite d and nondecreasing finite clock, including0 dimensions/empty/repeated intervals and horizon0.
Consumer: cross-partition representation and native Finsupp extension; full predictable density is not asserted here.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorTimeInput
open MeasureTheory ProbabilityTheory Set
open BrownianFiniteProductSource BrownianVectorOneStepIntegral BrownianVectorSimplePredictableIntegral
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Original scalar construction's REAL time measure, with actual product Brownian source. -/
def inputLaw (d : ℕ) (T : ℝ≥0) : Measure (ℝ × Sample d) :=
  (BrownianTimeIntegrand.timeLaw T).prod (productLaw d)

instance inputLaw_finite (d : ℕ) (T : ℝ≥0) : IsFiniteMeasure (inputLaw d T) := by
  unfold inputLaw
  infer_instance

/-- Literal Euclidean interval input; coefficients are unchanged original functions. -/
def intervalInput (d : ℕ) (H : Fin d → Sample d → ℝ) (s t : ℝ≥0) (p : ℝ × Sample d) :
    EuclideanSpace ℝ (Fin d) :=
  ((Ioc (s : ℝ) (t : ℝ)).indicator (fun _ => (1 : ℝ)) p.1) • coefficient d H p.2

@[simp] theorem intervalInput_apply (d : ℕ) (H : Fin d → Sample d → ℝ) (s t : ℝ≥0)
    (p : ℝ × Sample d) (k : Fin d) :
    intervalInput d H s t p k =
      (Ioc (s : ℝ) (t : ℝ)).indicator (fun _ => (1 : ℝ)) p.1 * H k p.2 := rfl

theorem intervalInput_memLp_two {d : ℕ} {H : Fin d → Sample d → ℝ}
    (hH : ∀ k, MemLp (H k) ∞ (productLaw d)) (T s t : ℝ≥0) :
    MemLp (intervalInput d H s t) 2 (inputLaw d T) := by
  apply MemLp.of_eval_piLp
  intro k
  have hi : MemLp ((Ioc (s : ℝ) (t : ℝ)).indicator (fun _ : ℝ => (1 : ℝ))) ∞
      (BrownianTimeIntegrand.timeLaw T) := (memLp_top_const 1).indicator measurableSet_Ioc
  exact (((hH k).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ ∞)).comp_snd
    (BrownianTimeIntegrand.timeLaw T)).mul (hi.comp_fst (productLaw d))

private theorem time_cell_mass (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) :
    (BrownianTimeIntegrand.timeLaw T).real (Ioc (s : ℝ) (t : ℝ)) = (t : ℝ)-(s : ℝ) := by
  have hsub : Ioc (s : ℝ) (t : ℝ) ⊆ Icc 0 (T : ℝ) := by
    intro x hx
    exact ⟨s.coe_nonneg.trans hx.1.le,hx.2.trans (by exact_mod_cast htT)⟩
  rw [measureReal_def,BrownianTimeIntegrand.timeLaw,Measure.restrict_apply measurableSet_Ioc,
    inter_eq_left.mpr hsub,Real.volume_Ioc,ENNReal.toReal_ofReal]
  exact sub_nonneg.mpr (by exact_mod_cast hst)

/-- Exact energy of the SAME vector block under original unnormalized real time. -/
theorem intervalInput_energy (d : ℕ) (H : Fin d → Sample d → ℝ) (T s t : ℝ≥0)
    (hst : s ≤ t) (htT : t ≤ T) :
    (∫ p, ‖intervalInput d H s t p‖^2 ∂inputLaw d T) =
      ((t : ℝ)-(s : ℝ)) * (∫ ω, ‖coefficient d H ω‖^2 ∂productLaw d) := by
  have he : (fun p => ‖intervalInput d H s t p‖^2) =
      (fun p : ℝ × Sample d => (Ioc (s : ℝ) (t : ℝ)).indicator (fun _ => (1 : ℝ)) p.1 *
        ‖coefficient d H p.2‖^2) := by
    funext p
    by_cases hp : p.1 ∈ Ioc (s : ℝ) (t : ℝ) <;> simp [intervalInput,hp]
  rw [he,inputLaw,integral_prod_mul ((Ioc (s : ℝ) (t : ℝ)).indicator (fun _ => (1 : ℝ)))
    (fun ω => ‖coefficient d H ω‖^2),integral_indicator measurableSet_Ioc,integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_one]
  have hc := time_cell_mass T s t hst htT
  change ((BrownianTimeIntegrand.timeLaw T) (Ioc (s : ℝ) (t : ℝ))).toReal = _ at hc
  rw [hc]

/-- The literal vector time input corresponding to the actual finite output. -/
def integrand (d : ℕ) {n : ℕ} (τ : Fin (n+1) → ℝ≥0)
    (H : Fin n → Fin d → Sample d → ℝ) (p : ℝ × Sample d) : EuclideanSpace ℝ (Fin d) :=
  ∑ i : Fin n, intervalInput d (H i) (τ i.castSucc) (τ i.succ) p

theorem integrand_memLp_two {d n : ℕ} (T : ℝ≥0) (τ : Fin (n+1) → ℝ≥0)
    (H : Fin n → Fin d → Sample d → ℝ) (hH : ∀ i k, MemLp (H i k) ∞ (productLaw d)) :
    MemLp (integrand d τ H) 2 (inputLaw d T) :=
  memLp_finsetSum Finset.univ (fun i _ => intervalInput_memLp_two (hH i) T _ _)

/-- Disjoint time cells have pointwise zero Euclidean inner product; this
uses no stochastic independence or coordinatewise sup norm. -/
theorem intervalInput_nonoverlap (d : ℕ) (H K : Fin d → Sample d → ℝ) (s t u v : ℝ≥0)
    (h : t ≤ u ∨ v ≤ s) (p : ℝ × Sample d) :
    inner ℝ (intervalInput d H s t p) (intervalInput d K u v p) = 0 := by
  have hd : ¬ (p.1 ∈ Ioc (s : ℝ) (t : ℝ) ∧ p.1 ∈ Ioc (u : ℝ) (v : ℝ)) := by
    rintro ⟨hs,hu⟩
    rcases h with h | h
    · exact (not_lt_of_ge (hs.2.trans (by exact_mod_cast h))) hu.1
    · exact (not_lt_of_ge (hu.2.trans (by exact_mod_cast h))) hs.1
  by_cases hs : p.1 ∈ Ioc (s : ℝ) (t : ℝ)
  · have hu : p.1 ∉ Ioc (u : ℝ) (v : ℝ) := fun hu => hd ⟨hs,hu⟩
    simp [intervalInput,hu]
  · simp [intervalInput,hs]

private theorem finite_norm_square {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Z : ι → EuclideanSpace ℝ (Fin d))
    (hcross : ∀ i j, i ≠ j → inner ℝ (Z i) (Z j) = 0) :
    ‖∑ i, Z i‖^2 = ∑ i, ‖Z i‖^2 := by
  simp only [← real_inner_self_eq_norm_sq,sum_inner,inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · intro j _ hji
    exact hcross j i hji
  · simp

/-- Native Euclidean energy for an actual finite DISJOINT interval family.
The time-order premises are supplied by real clocks, not stochastic fields. -/
theorem finiteIntervalInput_energy {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ℝ≥0) (A B : ι → ℝ≥0) (H : ι → Fin d → Sample d → ℝ)
    (hAB : ∀ i, A i ≤ B i) (hBT : ∀ i, B i ≤ T)
    (hdis : ∀ i j, i ≠ j → B i ≤ A j ∨ B j ≤ A i)
    (hH : ∀ i k, MemLp (H i k) ∞ (productLaw d)) :
    (∫ p, ‖∑ i, intervalInput d (H i) (A i) (B i) p‖^2 ∂inputLaw d T) =
      ∑ i, ((B i : ℝ)-(A i : ℝ))*(∫ ω, ‖coefficient d (H i) ω‖^2 ∂productLaw d) := by
  have he (p : ℝ × Sample d) : ‖∑ i, intervalInput d (H i) (A i) (B i) p‖^2 =
      ∑ i, ‖intervalInput d (H i) (A i) (B i) p‖^2 :=
    finite_norm_square _ (fun i j hij => intervalInput_nonoverlap d _ _ _ _ _ _ (hdis i j hij) p)
  simp_rw [he]
  rw [integral_finsetSum Finset.univ (fun i _ => (intervalInput_memLp_two (hH i) T _ _).norm.integrable_sq)]
  exact Finset.sum_congr rfl (fun i _ => intervalInput_energy d (H i) T _ _ (hAB i) (hBT i))

private theorem finite_scalar_square {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace α] (μ : Measure α) (Y : ι → α → ℝ)
    (hY : ∀ i, MemLp (Y i) 2 μ)
    (hcross : ∀ i j, i ≠ j → (∫ a, Y i a*Y j a ∂μ) = 0) :
    (∫ a, (∑ i, Y i a)^2 ∂μ) = ∑ i, ∫ a, Y i a^2 ∂μ := by
  simp_rw [pow_two,Fintype.sum_mul_sum]
  rw [integral_finsetSum Finset.univ (f := fun i a => ∑ j, Y i a*Y j a) (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => (hY i).integrable_mul (hY j)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (f := fun j a => Y i a*Y j a)
    (fun j _ => (hY i).integrable_mul (hY j)),Finset.sum_eq_single i]
  · intro j _ hji
    exact hcross i j hji.symm
  · simp

/-- Actual same-source finite-disjoint-family isometry. Cross terms are
proved from whole-joint-past permissions, not assumed as a Gram certificate. -/
theorem finiteInterval_isometry {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ℝ≥0) (A B : ι → ℝ≥0) (H : ι → Fin d → Sample d → ℝ)
    (hAB : ∀ i, A i ≤ B i) (hBT : ∀ i, B i ≤ T)
    (hdis : ∀ i j, i ≠ j → B i ≤ A j ∨ B j ≤ A i)
    (hHpast : ∀ i k, StronglyMeasurable[jointNaturalFiltration d (A i)] (H i k))
    (hH : ∀ i k, MemLp (H i k) ∞ (productLaw d)) :
    (∫ ω, (∑ i, oneStep d (H i) (A i) (B i) ω)^2 ∂productLaw d) =
      ∫ p, ‖∑ i, intervalInput d (H i) (A i) (B i) p‖^2 ∂inputLaw d T := by
  rw [finite_scalar_square (productLaw d) _ (fun i => oneStep_memLp_two (hH i) _ _) ?_,
    finiteIntervalInput_energy T A B H hAB hBT hdis hH]
  · exact Finset.sum_congr rfl (fun i _ => oneStep_isometry _ _ (hAB i) (hHpast i) (hH i))
  · intro i j hij
    rcases hdis i j hij with h | h
    · exact nonoverlap_orthogonal _ _ _ _ (hAB i) h (hAB j) (hHpast i) (hHpast j) (hH i) (hH j)
    · simpa only [mul_comm] using nonoverlap_orthogonal _ _ _ _ (hAB j) h (hAB i)
        (hHpast j) (hHpast i) (hH j) (hH i)

/-- Actual native vector-input energy, including repeated and empty time cells. -/
theorem integrand_energy {d n : ℕ} (T : ℝ≥0) (τ : Fin (n+1) → ℝ≥0)
    (H : Fin n → Fin d → Sample d → ℝ) (hτ : Monotone τ) (hτT : τ (Fin.last n) ≤ T)
    (hH : ∀ i k, MemLp (H i k) ∞ (productLaw d)) :
    (∫ p, ‖integrand d τ H p‖^2 ∂inputLaw d T) =
      ∑ i : Fin n, ((τ i.succ : ℝ)-(τ i.castSucc : ℝ)) * (∫ ω, ‖coefficient d (H i) ω‖^2 ∂productLaw d) := by
  have he (p : ℝ × Sample d) : ‖integrand d τ H p‖^2 =
      ∑ i : Fin n, ‖intervalInput d (H i) (τ i.castSucc) (τ i.succ) p‖^2 := by
    apply finite_norm_square
    intro i j hij
    apply intervalInput_nonoverlap
    rcases lt_or_gt_of_ne hij with h | h
    · exact Or.inl (hτ (by exact_mod_cast Nat.succ_le_of_lt h))
    · exact Or.inr (hτ (by exact_mod_cast Nat.succ_le_of_lt h))
  simp_rw [he]
  rw [integral_finsetSum Finset.univ (fun i _ => (intervalInput_memLp_two (hH i) T _ _).norm.integrable_sq)]
  exact Finset.sum_congr rfl (fun i _ => intervalInput_energy d (H i) T _ _
    (hτ (by exact_mod_cast Nat.le_succ (i : ℕ))) ((hτ (Fin.le_last i.succ)).trans hτT))

def inputClass {d n : ℕ} (T : ℝ≥0) (τ : Fin (n+1) → ℝ≥0)
    (H : Fin n → Fin d → Sample d → ℝ) (hH : ∀ i k, MemLp (H i k) ∞ (productLaw d)) :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T) :=
  (integrand_memLp_two T τ H hH).toLp (integrand d τ H)

def outputClass {d n : ℕ} (τ : Fin (n+1) → ℝ≥0)
    (H : Fin n → Fin d → Sample d → ℝ) (hH : ∀ i k, MemLp (H i k) ∞ (productLaw d)) :
    Lp ℝ 2 (productLaw d) := (simpleIntegral_memLp_two τ H hH).toLp (simpleIntegral d τ H)

private theorem toLp_norm_square {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (μ : Measure α) (f : α → E) (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖^2 = ∫ a, ‖f a‖^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  exact hf.coeFn_toLp.mono (fun a h => by
    change inner ℝ (hf.toLp f a) (hf.toLp f a) = ‖f a‖^2
    rw [h,real_inner_self_eq_norm_sq])

/-- The input and output in their ORIGINAL native L2 spaces have equal norms. -/
theorem input_output_norm {d n : ℕ} (T : ℝ≥0) (τ : Fin (n+1) → ℝ≥0)
    (H : Fin n → Fin d → Sample d → ℝ) (hτ : Monotone τ) (hτT : τ (Fin.last n) ≤ T)
    (hHpast : ∀ i k, StronglyMeasurable[jointNaturalFiltration d (τ i.castSucc)] (H i k))
    (hH : ∀ i k, MemLp (H i k) ∞ (productLaw d)) :
    ‖outputClass τ H hH‖ = ‖inputClass T τ H hH‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [outputClass,inputClass,toLp_norm_square,toLp_norm_square]
  simp only [Real.norm_eq_abs,sq_abs]
  rw [simpleIntegral_isometry τ H hτ hHpast hH,integrand_energy T τ H hτ hτT hH]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorTimeInput
