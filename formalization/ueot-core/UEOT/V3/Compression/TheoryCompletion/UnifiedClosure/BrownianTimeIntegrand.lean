import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianSimplePredictableIntegral
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
Original commitment: an actual predictable integral must bind its time-dependent input, not just a coefficient list.
Existing result: actual finite deterministic predictable outputs have exact elapsed-time energy isometry.
Premise reduced: realize that energy as the native L2 norm of an explicit time-times-source integrand on [0,T].
Model/witness: SAME source and finite deterministic nondecreasing clock; left-end natural-past bounded coefficients.
Consumer: representation-independent integration and L2-closure extension; density in all predictable inputs remains open.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianTimeIntegrand
open MeasureTheory ProbabilityTheory Set
open BrownianContinuousSource BrownianProjectiveSource BrownianMartingaleSource
open BrownianOneStepIntegral BrownianSimplePredictableIntegral
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Actual Lebesgue time restricted to the declared horizon. -/
def timeLaw (T : ℝ≥0) : Measure ℝ := volume.restrict (Icc 0 (T : ℝ))

instance timeLaw_finite (T : ℝ≥0) : IsFiniteMeasure (timeLaw T) := by
  unfold timeLaw
  infer_instance

/-- The same source in the native product space, with no extra noise coordinate. -/
def inputLaw (T : ℝ≥0) : Measure (ℝ × (ℝ≥0 → ℝ)) := (timeLaw T).prod sourceLaw

instance inputLaw_finite (T : ℝ≥0) : IsFiniteMeasure (inputLaw T) := by
  unfold inputLaw
  infer_instance

/-- Coefficient fixed at the interval's LEFT endpoint, active on (s,t]. -/
def intervalIntegrand (H : (ℝ≥0 → ℝ) → ℝ) (s t : ℝ≥0) (p : ℝ × (ℝ≥0 → ℝ)) : ℝ :=
  (Ioc (s : ℝ) (t : ℝ)).indicator (fun _ => 1) p.1 * H p.2

theorem intervalIntegrand_memLp_two {H : (ℝ≥0 → ℝ) → ℝ} (hH : MemLp H ∞ sourceLaw)
    (T s t : ℝ≥0) : MemLp (intervalIntegrand H s t) 2 (inputLaw T) := by
  have hi : MemLp ((Ioc (s : ℝ) (t : ℝ)).indicator (fun _ : ℝ => (1 : ℝ))) ∞ (timeLaw T) :=
    (memLp_top_const 1).indicator measurableSet_Ioc
  exact ((hH.mono_exponent (by simp : (2 : ℝ≥0∞) ≤ ∞)).comp_snd (timeLaw T)).mul
    (hi.comp_fst sourceLaw)

private theorem timeLaw_real_Ioc (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) :
    (timeLaw T).real (Ioc (s : ℝ) (t : ℝ)) = (t : ℝ)-(s : ℝ) := by
  have hsub : Ioc (s : ℝ) (t : ℝ) ⊆ Icc 0 (T : ℝ) := by
    intro x hx
    exact ⟨(s.coe_nonneg.trans hx.1.le),hx.2.trans (by exact_mod_cast htT)⟩
  rw [measureReal_def,timeLaw,Measure.restrict_apply measurableSet_Ioc,
    inter_eq_left.mpr hsub,Real.volume_Ioc,ENNReal.toReal_ofReal]
  exact sub_nonneg.mpr (by exact_mod_cast hst)

/-- Exact product-measure energy of one literal input block. -/
theorem intervalIntegrand_energy (H : (ℝ≥0 → ℝ) → ℝ) (T s t : ℝ≥0)
    (hst : s ≤ t) (htT : t ≤ T) :
    (∫ p, intervalIntegrand H s t p ^ 2 ∂inputLaw T) =
      ((t : ℝ)-(s : ℝ)) * (∫ ω, H ω ^ 2 ∂sourceLaw) := by
  have he : (fun p => intervalIntegrand H s t p ^ 2) =
      (fun p : ℝ × (ℝ≥0 → ℝ) =>
        (Ioc (s : ℝ) (t : ℝ)).indicator (fun _ => 1) p.1 * H p.2 ^ 2) := by
    funext p
    by_cases hp : p.1 ∈ Ioc (s : ℝ) (t : ℝ) <;> simp [intervalIntegrand,hp]
  rw [he,inputLaw,integral_prod_mul ((Ioc (s : ℝ) (t : ℝ)).indicator (fun _ => 1))
    (fun ω => H ω ^ 2),integral_indicator measurableSet_Ioc,integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_one]
  have hc := timeLaw_real_Ioc T s t hst htT
  change ((timeLaw T) (Ioc (s : ℝ) (t : ℝ))).toReal = _ at hc
  rw [hc]

/-- Literal finite time-dependent input, with zero value at time zero and
outside the specified deterministic partition cells. -/
def integrand {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (H : Fin n → (ℝ≥0 → ℝ) → ℝ)
    (p : ℝ × (ℝ≥0 → ℝ)) : ℝ :=
  ∑ i : Fin n, intervalIntegrand (H i) (τ i.castSucc) (τ i.succ) p

theorem integrand_memLp_two {n : ℕ} (T : ℝ≥0) (τ : Fin (n+1) → ℝ≥0)
    (H : Fin n → (ℝ≥0 → ℝ) → ℝ) (hH : ∀ i, MemLp (H i) ∞ sourceLaw) :
    MemLp (integrand τ H) 2 (inputLaw T) :=
  memLp_finsetSum Finset.univ (fun i _ => intervalIntegrand_memLp_two (hH i) T _ _)

private theorem cell_order {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ) (i : Fin n) :
    τ i.castSucc ≤ τ i.succ := hτ (by exact_mod_cast Nat.le_succ (i : ℕ))

private theorem intervalIntegrand_mul_zero {n : ℕ} (τ : Fin (n+1) → ℝ≥0)
    (H : Fin n → (ℝ≥0 → ℝ) → ℝ) (hτ : Monotone τ) (i j : Fin n) (hij : i ≠ j)
    (p : ℝ × (ℝ≥0 → ℝ)) :
    intervalIntegrand (H i) (τ i.castSucc) (τ i.succ) p *
      intervalIntegrand (H j) (τ j.castSucc) (τ j.succ) p = 0 := by
  have hdis : ¬ (p.1 ∈ Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ) ∧
      p.1 ∈ Ioc (τ j.castSucc : ℝ) (τ j.succ : ℝ)) := by
    intro hp
    rcases lt_or_gt_of_ne hij with hij | hji
    · have h := hτ (show i.succ ≤ j.castSucc by exact_mod_cast Nat.succ_le_of_lt hij)
      have hc : (τ i.succ : ℝ) ≤ (τ j.castSucc : ℝ) := by exact_mod_cast h
      exact (not_lt_of_ge (hp.1.2.trans hc)) hp.2.1
    · have h := hτ (show j.succ ≤ i.castSucc by exact_mod_cast Nat.succ_le_of_lt hji)
      have hc : (τ j.succ : ℝ) ≤ (τ i.castSucc : ℝ) := by exact_mod_cast h
      exact (not_lt_of_ge (hp.2.2.trans hc)) hp.1.1
  by_cases hi : p.1 ∈ Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ)
  · have hj : p.1 ∉ Ioc (τ j.castSucc : ℝ) (τ j.succ : ℝ) := fun hj => hdis ⟨hi,hj⟩
    simp [intervalIntegrand,hj]
  · simp [intervalIntegrand,hi]

private theorem integrand_square {n : ℕ} (τ : Fin (n+1) → ℝ≥0)
    (H : Fin n → (ℝ≥0 → ℝ) → ℝ) (hτ : Monotone τ) (p : ℝ × (ℝ≥0 → ℝ)) :
    integrand τ H p ^ 2 =
      ∑ i : Fin n, intervalIntegrand (H i) (τ i.castSucc) (τ i.succ) p ^ 2 := by
  simp only [integrand,pow_two,Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · intro j _ hji
    exact intervalIntegrand_mul_zero τ H hτ i j hji.symm p
  · simp

/-- The finite source energy is the actual product dt-times-P energy. -/
theorem integrand_energy {n : ℕ} (T : ℝ≥0) (τ : Fin (n+1) → ℝ≥0)
    (H : Fin n → (ℝ≥0 → ℝ) → ℝ) (hτ : Monotone τ) (hT : τ (Fin.last n) ≤ T)
    (hH : ∀ i, MemLp (H i) ∞ sourceLaw) :
    (∫ p, integrand τ H p ^ 2 ∂inputLaw T) =
      ∑ i : Fin n, ((τ i.succ : ℝ)-(τ i.castSucc : ℝ)) * (∫ ω, H i ω ^ 2 ∂sourceLaw) := by
  simp_rw [integrand_square τ H hτ]
  rw [integral_finsetSum Finset.univ
    (fun i _ => (intervalIntegrand_memLp_two (hH i) T _ _).integrable_sq)]
  exact Finset.sum_congr rfl (fun i _ => intervalIntegrand_energy (H i) T _ _ (cell_order τ hτ i)
    ((hτ (Fin.le_last i.succ)).trans hT))

/-- Native L2 equivalence class of the actual time-dependent input. -/
def inputClass {n : ℕ} (T : ℝ≥0) (τ : Fin (n+1) → ℝ≥0)
    (H : Fin n → (ℝ≥0 → ℝ) → ℝ) (hH : ∀ i, MemLp (H i) ∞ sourceLaw) : Lp ℝ 2 (inputLaw T) :=
  (integrand_memLp_two T τ H hH).toLp (integrand τ H)

/-- The energy is the NATIVE L2 norm, not a new abstract energy field. -/
theorem inputClass_norm_sq {n : ℕ} (T : ℝ≥0) (τ : Fin (n+1) → ℝ≥0)
    (H : Fin n → (ℝ≥0 → ℝ) → ℝ) (hH : ∀ i, MemLp (H i) ∞ sourceLaw) :
    ‖inputClass T τ H hH‖ ^ 2 = ∫ p, integrand τ H p ^ 2 ∂inputLaw T := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(integrand_memLp_two T τ H hH).coeFn_toLp] with p hp
  simp only [inputClass] at hp ⊢
  rw [hp]
  simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]

/-- The already constructed literal output obeys the actual input-class norm
identity, with every coefficient still restricted to the START's natural past. -/
theorem output_isometry {n : ℕ} (T : ℝ≥0) (τ : Fin (n+1) → ℝ≥0)
    (H : Fin n → (ℝ≥0 → ℝ) → ℝ) (hτ : Monotone τ) (hT : τ (Fin.last n) ≤ T)
    (hHpast : ∀ i, StronglyMeasurable[naturalFiltration (τ i.castSucc)] (H i))
    (hH : ∀ i, MemLp (H i) ∞ sourceLaw) :
    (∫ ω, simpleIntegral τ H ω ^ 2 ∂sourceLaw) = ‖inputClass T τ H hH‖ ^ 2 := by
  rw [inputClass_norm_sq,integrand_energy T τ H hτ hT hH]
  exact simpleIntegral_isometry τ H hτ hHpast hH

/-- Native L2 class of the already constructed literal source output. -/
def outputClass {n : ℕ} (τ : Fin (n+1) → ℝ≥0)
    (H : Fin n → (ℝ≥0 → ℝ) → ℝ) (hH : ∀ i, MemLp (H i) ∞ sourceLaw) : Lp ℝ 2 sourceLaw :=
  (simpleIntegral_memLp_two τ H hH).toLp (simpleIntegral τ H)

private theorem outputClass_norm_sq {n : ℕ} (τ : Fin (n+1) → ℝ≥0)
    (H : Fin n → (ℝ≥0 → ℝ) → ℝ) (hH : ∀ i, MemLp (H i) ∞ sourceLaw) :
    ‖outputClass τ H hH‖ ^ 2 = ∫ ω, simpleIntegral τ H ω ^ 2 ∂sourceLaw := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(simpleIntegral_memLp_two τ H hH).coeFn_toLp] with ω hω
  simp only [outputClass] at hω ⊢
  rw [hω]
  simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]

/-- Actual input/output identity in the existing native Hilbert spaces. -/
theorem outputClass_norm {n : ℕ} (T : ℝ≥0) (τ : Fin (n+1) → ℝ≥0)
    (H : Fin n → (ℝ≥0 → ℝ) → ℝ) (hτ : Monotone τ) (hT : τ (Fin.last n) ≤ T)
    (hHpast : ∀ i, StronglyMeasurable[naturalFiltration (τ i.castSucc)] (H i))
    (hH : ∀ i, MemLp (H i) ∞ sourceLaw) :
    ‖outputClass τ H hH‖ = ‖inputClass T τ H hH‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [outputClass_norm_sq,output_isometry T τ H hτ hT hHpast hH]

/-- Zero native input class forces zero ACTUAL output class. This is a
proved dependency of representation independence, not a certificate field. -/
theorem outputClass_zero_of_input_zero {n : ℕ} (T : ℝ≥0) (τ : Fin (n+1) → ℝ≥0)
    (H : Fin n → (ℝ≥0 → ℝ) → ℝ) (hτ : Monotone τ) (hT : τ (Fin.last n) ≤ T)
    (hHpast : ∀ i, StronglyMeasurable[naturalFiltration (τ i.castSucc)] (H i))
    (hH : ∀ i, MemLp (H i) ∞ sourceLaw) (hz : inputClass T τ H hH = 0) :
    outputClass τ H hH = 0 := by
  apply norm_eq_zero.mp
  rw [outputClass_norm T τ H hτ hT hHpast hH,hz,norm_zero]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianTimeIntegrand
