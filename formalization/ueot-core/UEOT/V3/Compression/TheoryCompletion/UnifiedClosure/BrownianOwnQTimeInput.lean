import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQSimpleIntegral

/-!
Original commitment: actual Q integration must depend on its actual time-input class, not an old source-P label.
Existing result: literal permitted finite Q tables have exact isometry and actual real-time energy.
Premise reduced: construct SAME timeLaw U × ownQ native L2 inputs/outputs and identify their exact energy/norm.
Model/witness: original Fs START elementary tables, actual shifted W_f and own Q_f, arbitrary horizon U including zero.
Consumer/boundary: prepares representation-independent Q extension; closure/full-predictable density and ItoRun are not assumed.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQTimeInput
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianTimeIntegrand BrownianPredictableInputs BrownianIntegralClosure
open BrownianBoundedExponentialLimitSource BrownianOwnQOneStepIntegral BrownianOwnQSimpleIntegral
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory InnerProductSpace RealInnerProductSpace
noncomputable section
variable (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K)

/-- Native product dt × OWN-Q, with no independent source coordinate. -/
def inputLawQ (U : ℝ≥0) : Measure (ℝ × (ℝ≥0 → ℝ)) := (timeLaw U).prod (fullLaw T f)

include hK hbound

theorem interval_memLp_two {H : (ℝ≥0 → ℝ) → ℝ} (hH : MemLp H ∞ (fullLaw T f)) (U s t : ℝ≥0) :
    MemLp (intervalIntegrand H s t) 2 (inputLawQ T f U) := by
  let _ := fullLaw_probability T f K hK hbound
  have hi : MemLp ((Ioc (s : ℝ) (t : ℝ)).indicator (fun _ : ℝ => (1 : ℝ))) ∞ (timeLaw U) :=
    (memLp_top_const 1).indicator measurableSet_Ioc
  exact ((hH.mono_exponent (by simp : (2 : ℝ≥0∞)≤∞)).comp_snd (timeLaw U)).mul
    (hi.comp_fst (fullLaw T f))

theorem integrand_memLp_two {U : ℝ≥0} (r : ElementaryInput U) :
    MemLp (integrand r.clock r.coefficient) 2 (inputLawQ T f U) :=
  memLp_finsetSum Finset.univ (fun i _ => interval_memLp_two T f K hK hbound
    (coefficient_bounded_Q T f K hK hbound (r.coefficient_bounded i)) U _ _)

/-- Direct product-law energy of one real-time block. -/
theorem interval_energy (H : (ℝ≥0 → ℝ) → ℝ) (U s t : ℝ≥0) (hst : s≤t) (htU : t≤U) :
    (∫ p, intervalIntegrand H s t p^2 ∂inputLawQ T f U)=((t : ℝ)-(s : ℝ))*(∫ ω, H ω^2 ∂fullLaw T f) := by
  let _ := fullLaw_probability T f K hK hbound
  have he : (fun p => intervalIntegrand H s t p^2)=
      (fun p : ℝ × (ℝ≥0 → ℝ) => (Ioc (s : ℝ) (t : ℝ)).indicator (fun _ => 1) p.1*H p.2^2) := by
    funext p
    by_cases hp : p.1∈Ioc (s : ℝ) (t : ℝ) <;> simp [intervalIntegrand,hp]
  rw [he,inputLawQ,integral_prod_mul ((Ioc (s : ℝ) (t : ℝ)).indicator (fun _ => 1))
    (fun ω => H ω^2),integral_indicator measurableSet_Ioc,integral_const]
  have hsub : Ioc (s : ℝ) (t : ℝ)⊆Icc 0 (U : ℝ) := by
    intro x hx
    exact ⟨s.coe_nonneg.trans hx.1.le,hx.2.trans (by exact_mod_cast htU)⟩
  simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_one]
  rw [timeLaw,Measure.restrict_apply measurableSet_Ioc,inter_eq_left.mpr hsub,Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (show (s : ℝ)≤(t : ℝ) by exact_mod_cast hst))]

omit hK hbound in
private theorem integrand_square {U : ℝ≥0} (r : ElementaryInput U) (p : ℝ × (ℝ≥0 → ℝ)) :
    integrand r.clock r.coefficient p^2=∑ i : Fin r.n, intervalIntegrand (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ) p^2 := by
  have hz (i j : Fin r.n) (hij : i≠j) :
      intervalIntegrand (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ) p*
        intervalIntegrand (r.coefficient j) (r.clock j.castSucc) (r.clock j.succ) p=0 := by
    have hdis : ¬(p.1∈Ioc (r.clock i.castSucc : ℝ) (r.clock i.succ : ℝ) ∧
        p.1∈Ioc (r.clock j.castSucc : ℝ) (r.clock j.succ : ℝ)) := by
      intro hp
      rcases lt_or_gt_of_ne hij with hij | hji
      · have h := r.clock_mono (show i.succ ≤ j.castSucc by exact_mod_cast Nat.succ_le_of_lt hij)
        exact (not_lt_of_ge (hp.1.2.trans (show (r.clock i.succ : ℝ)≤(r.clock j.castSucc : ℝ) by exact_mod_cast h))) hp.2.1
      · have h := r.clock_mono (show j.succ ≤ i.castSucc by exact_mod_cast Nat.succ_le_of_lt hji)
        exact (not_lt_of_ge (hp.2.2.trans (show (r.clock j.succ : ℝ)≤(r.clock i.castSucc : ℝ) by exact_mod_cast h))) hp.1.1
    by_cases hi : p.1∈Ioc (r.clock i.castSucc : ℝ) (r.clock i.succ : ℝ)
    · have hj : p.1∉Ioc (r.clock j.castSucc : ℝ) (r.clock j.succ : ℝ) := fun hj => hdis ⟨hi,hj⟩
      simp [intervalIntegrand,hj]
    · simp [intervalIntegrand,hi]
  simp only [integrand,pow_two,Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · intro j _ hji
    exact hz i j hji.symm
  · simp

/-- Exact dt × Q energy of the original real time-dependent input. -/
theorem integrand_energy {U : ℝ≥0} (r : ElementaryInput U) :
    (∫ p, integrand r.clock r.coefficient p^2 ∂inputLawQ T f U)=
      ∑ i : Fin r.n, ((r.clock i.succ : ℝ)-(r.clock i.castSucc : ℝ))*(∫ ω, r.coefficient i ω^2 ∂fullLaw T f) := by
  simp_rw [integrand_square r]
  rw [integral_finsetSum Finset.univ (fun i _ => (interval_memLp_two T f K hK hbound
    (coefficient_bounded_Q T f K hK hbound (r.coefficient_bounded i)) U _ _).integrable_sq)]
  apply Finset.sum_congr rfl
  intro i _
  apply interval_energy T f K hK hbound
  · exact r.clock_mono (by exact_mod_cast Nat.le_succ (i : ℕ))
  · simpa only [r.clock_end] using r.clock_mono (Fin.le_last i.succ)

def inputValueQ {U : ℝ≥0} (r : ElementaryInput U) : Lp ℝ 2 (inputLawQ T f U) :=
  (integrand_memLp_two T f K hK hbound r).toLp (integrand r.clock r.coefficient)
def outputValueQ {U : ℝ≥0} (r : ElementaryInput U) : Lp ℝ 2 (fullLaw T f) :=
  (simpleIntegral_memLp_two T f K hK hbound r).toLp (BrownianOwnQSimpleIntegral.simpleIntegral T f K r)

theorem family_norm {U : ℝ≥0} (r : ElementaryInput U) :
    ‖outputValueQ T f K hK hbound r‖=‖inputValueQ T f K hK hbound r‖ := by
  have hOut : ‖outputValueQ T f K hK hbound r‖^2=∫ ω, BrownianOwnQSimpleIntegral.simpleIntegral T f K r ω^2 ∂fullLaw T f := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
    exact integral_congr_ae ((simpleIntegral_memLp_two T f K hK hbound r).coeFn_toLp.mono
      (fun _ h => congrArg (fun x : ℝ => x^2) h))
  have hIn : ‖inputValueQ T f K hK hbound r‖^2=∫ p, integrand r.clock r.coefficient p^2 ∂inputLawQ T f U := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
    exact integral_congr_ae ((integrand_memLp_two T f K hK hbound r).coeFn_toLp.mono
      (fun _ h => congrArg (fun x : ℝ => x^2) h))
  rw [simpleIntegral_isometry T f K hK hbound,← integrand_energy T f K hK hbound r,← hIn] at hOut
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hOut

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQTimeInput
