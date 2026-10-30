import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQOneStepIntegral

/-!
Original commitment: actual controlled-source finite integration must return the literal permitted table under its OWN Q.
Existing result: actual W_f/Q_f has original Fs conditional moments and one-step isometry, with P-bounds transported by Q absolute continuity.
Premise reduced: derive actual finite-table orthogonality, isometry, original-clock prefix martingale and real dt energy identity.
Model/witness: original ElementaryInput U, arbitrary nondecreasing 0/U clock and START coefficients, same bounded f/ownQ, repeated/empty cells allowed.
Consumer/boundary: genuine Q finite predictable integration feeds Q extension and actual control sources; it is not the old P integral or a desired Ito field.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQSimpleIntegral
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianTimeIntegrand BrownianPredictableInputs BrownianIntegralClosure
open BrownianBoundedExponentialLimitSource BrownianOwnQOneStepIntegral
open BrownianFiniteStepExponentialSource BrownianFiniteStepTerminalKLSource
open UEOT.V3.GirsanovPathKL
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
variable (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K)

/-- Returned actual finite table integral against the actual Q-Brownian. -/
def simpleIntegral {U : ℝ≥0} (r : ElementaryInput U) (ω : ℝ≥0 → ℝ) : ℝ :=
  ∑ i : Fin r.n, oneStep T f K (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ) ω

/-- Literal actual original-clock prefix, no independently selected process. -/
def prefixIntegral {U : ℝ≥0} (r : ElementaryInput U) (k : Fin (r.n+1)) : (ℝ≥0 → ℝ) → ℝ :=
  Fin.partialSum (fun i => oneStep T f K (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ)) k

private theorem cell_mono {U : ℝ≥0} (r : ElementaryInput U) (i : Fin r.n) : r.clock i.castSucc≤r.clock i.succ :=
  r.clock_mono (by exact_mod_cast Nat.le_succ (i : ℕ))

include hK hbound
private theorem coefficient_Q {U : ℝ≥0} (r : ElementaryInput U) (i : Fin r.n) : MemLp (r.coefficient i) ∞ (fullLaw T f) :=
  coefficient_bounded_Q T f K hK hbound (r.coefficient_bounded i)

theorem simpleIntegral_memLp_two {U : ℝ≥0} (r : ElementaryInput U) :
    MemLp (simpleIntegral T f K r) 2 (fullLaw T f) :=
  memLp_finsetSum Finset.univ (fun i _ => oneStep_memLp_two T f K hK hbound (coefficient_Q T f K hK hbound r i) _ _)

/-- Actual nonoverlapping rows are orthogonal under final OWN-Q; both
coefficients see only their original START past. -/
theorem nonoverlap_orthogonal {H G : (ℝ≥0 → ℝ) → ℝ} (s t u v : ℝ≥0)
    (hst : s≤t) (htu : t≤u) (huv : u≤v)
    (hHpast : StronglyMeasurable[naturalFiltration s] H) (hGpast : StronglyMeasurable[naturalFiltration u] G)
    (hH : MemLp H ∞ (fullLaw T f)) (hG : MemLp G ∞ (fullLaw T f)) :
    (∫ ω, oneStep T f K H s t ω*oneStep T f K G u v ω ∂fullLaw T f)=0 := by
  let _ := fullLaw_probability T f K hK hbound
  have hi : Integrable (oneStep T f K H s t*oneStep T f K G u v) (fullLaw T f) :=
    (oneStep_memLp_two T f K hK hbound hH s t).integrable_mul (oneStep_memLp_two T f K hK hbound hG u v)
  have hm := (oneStep_past_end T f K s t hst hHpast).mono (naturalFiltration.mono htu)
  have hc := condExp_mul_of_stronglyMeasurable_left hm hi
    ((oneStep_memLp_two T f K hK hbound hG u v).integrable one_le_two)
  have hz : (fullLaw T f)[oneStep T f K H s t*oneStep T f K G u v | naturalFiltration u]=ᵐ[fullLaw T f] fun _ => 0 := by
    apply hc.trans
    filter_upwards [oneStep_condExp_zero T f K hK hbound u v huv hGpast hG] with ω h
    simp only [Pi.mul_apply,h,mul_zero]
  simp only [Pi.mul_def] at hz
  rw [← integral_condExp (naturalFiltration.le u),integral_congr_ae hz,integral_zero]

private theorem cross_zero {U : ℝ≥0} (r : ElementaryInput U) (i j : Fin r.n) (hij : i≠j) :
    (∫ ω, oneStep T f K (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ) ω*
      oneStep T f K (r.coefficient j) (r.clock j.castSucc) (r.clock j.succ) ω ∂fullLaw T f)=0 := by
  have ho (a b : Fin r.n) (hab : a<b) :
      (∫ ω, oneStep T f K (r.coefficient a) (r.clock a.castSucc) (r.clock a.succ) ω*
        oneStep T f K (r.coefficient b) (r.clock b.castSucc) (r.clock b.succ) ω ∂fullLaw T f)=0 := by
    apply nonoverlap_orthogonal T f K hK hbound _ _ _ _ (cell_mono r a) ?_ (cell_mono r b)
      (r.coefficient_past a) (r.coefficient_past b) (coefficient_Q T f K hK hbound r a) (coefficient_Q T f K hK hbound r b)
    exact r.clock_mono (by exact_mod_cast Nat.succ_le_of_lt hab)
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact ho i j hij
  · simpa only [mul_comm] using ho j i hji

/-- Genuine Q Ito isometry for the returned finite table. All elapsed
clocks and expected coefficients are from this same table and final Q. -/
theorem simpleIntegral_isometry {U : ℝ≥0} (r : ElementaryInput U) :
    (∫ ω, simpleIntegral T f K r ω^2 ∂fullLaw T f)=
      ∑ i : Fin r.n, ((r.clock i.succ : ℝ)-(r.clock i.castSucc : ℝ))*(∫ ω, r.coefficient i ω^2 ∂fullLaw T f) := by
  let _ := fullLaw_probability T f K hK hbound
  let Y (i : Fin r.n) := oneStep T f K (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ)
  have hi (i j : Fin r.n) : Integrable (fun ω => Y i ω*Y j ω) (fullLaw T f) :=
    (oneStep_memLp_two T f K hK hbound (coefficient_Q T f K hK hbound r i) _ _).integrable_mul
      (oneStep_memLp_two T f K hK hbound (coefficient_Q T f K hK hbound r j) _ _)
  have he : (fun ω => simpleIntegral T f K r ω^2)=(fun ω => ∑ i : Fin r.n, ∑ j : Fin r.n, Y i ω*Y j ω) := by
    funext ω
    simp only [simpleIntegral,pow_two,Fintype.sum_mul_sum,Y]
  rw [he,integral_finsetSum Finset.univ (f := fun i ω => ∑ j : Fin r.n, Y i ω*Y j ω)
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ => hi i j),Finset.sum_eq_single i]
  · simpa only [← pow_two] using oneStep_isometry T f K hK hbound (r.clock i.castSucc) (r.clock i.succ)
      (cell_mono r i) (r.coefficient_past i) (coefficient_Q T f K hK hbound r i)
  · intro j _ hji
    exact cross_zero T f K hK hbound r i j hji.symm
  · simp

/-- SAME real dt control energy, reusing its literal pathwise identity.
The actual Q expectation is retained rather than silently changed to P. -/
theorem simpleIntegral_real_energy {U : ℝ≥0} (r : ElementaryInput U) :
    (∫ ω, simpleIntegral T f K r ω^2 ∂fullLaw T f)=
      ∫ ω, controlEnergy U (tableControl r) ω ∂fullLaw T f := by
  let _ := fullLaw_probability T f K hK hbound
  rw [simpleIntegral_isometry T f K hK hbound]
  simp_rw [tableControl_energy,tableEnergy]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul]
  · intro i _
    exact (((coefficient_Q T f K hK hbound r i).mono_exponent (show (2 : ℝ≥0∞)≤∞ from le_top)).integrable_sq).const_mul _

omit hK hbound in
theorem prefix_zero {U : ℝ≥0} (r : ElementaryInput U) : prefixIntegral T f K r 0=0 := Fin.partialSum_zero _
omit hK hbound in
theorem prefix_succ {U : ℝ≥0} (r : ElementaryInput U) (i : Fin r.n) :
    prefixIntegral T f K r i.succ=prefixIntegral T f K r i.castSucc+
      oneStep T f K (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ) := Fin.partialSum_succ _ i

omit hK hbound in
theorem prefix_past {U : ℝ≥0} (r : ElementaryInput U) (k : Fin (r.n+1)) :
    StronglyMeasurable[naturalFiltration (r.clock k)] (prefixIntegral T f K r k) := by
  refine Fin.induction ?_ ?_ k
  · rw [prefix_zero]
    exact stronglyMeasurable_zero
  · intro i hi
    rw [prefix_succ]
    exact (hi.mono (naturalFiltration.mono (cell_mono r i))).add
      (oneStep_past_end T f K _ _ (cell_mono r i) (r.coefficient_past i))

theorem prefix_integrable {U : ℝ≥0} (r : ElementaryInput U) (k : Fin (r.n+1)) :
    Integrable (prefixIntegral T f K r k) (fullLaw T f) := by
  let _ := fullLaw_probability T f K hK hbound
  refine Fin.induction ?_ ?_ k
  · rw [prefix_zero]
    exact integrable_zero _ _ _
  · intro i hi
    rw [prefix_succ]
    exact hi.add ((oneStep_memLp_two T f K hK hbound (coefficient_Q T f K hK hbound r i) _ _).integrable one_le_two)

theorem prefix_step_conditional {U : ℝ≥0} (r : ElementaryInput U) (i : Fin r.n) :
    (fullLaw T f)[prefixIntegral T f K r i.succ | naturalFiltration (r.clock i.castSucc)]=ᵐ[fullLaw T f]
      prefixIntegral T f K r i.castSucc := by
  let _ := fullLaw_probability T f K hK hbound
  rw [prefix_succ]
  apply (condExp_add (prefix_integrable T f K hK hbound r i.castSucc)
    ((oneStep_memLp_two T f K hK hbound (coefficient_Q T f K hK hbound r i) _ _).integrable one_le_two)
      (naturalFiltration (r.clock i.castSucc))).trans
  rw [condExp_of_stronglyMeasurable (naturalFiltration.le _) (prefix_past T f K r _)
    (prefix_integrable T f K hK hbound r _)]
  filter_upwards [oneStep_condExp_zero T f K hK hbound _ _ (cell_mono r i) (r.coefficient_past i)
    (coefficient_Q T f K hK hbound r i)] with ω h
  simp only [Pi.add_apply,h,add_zero]

theorem prefix_conditional {U : ℝ≥0} (r : ElementaryInput U) (j : Fin (r.n+1)) :
    ∀ i, i≤j → (fullLaw T f)[prefixIntegral T f K r j | naturalFiltration (r.clock i)]=ᵐ[fullLaw T f] prefixIntegral T f K r i := by
  let _ := fullLaw_probability T f K hK hbound
  refine Fin.induction ?_ ?_ j
  · intro i hi
    have he : i=0 := le_antisymm hi bot_le
    subst i
    rw [condExp_of_stronglyMeasurable (naturalFiltration.le _) (prefix_past T f K r _)
      (prefix_integrable T f K hK hbound r _)]
  · intro j hj i hi
    by_cases he : i=j.succ
    · subst i
      rw [condExp_of_stronglyMeasurable (naturalFiltration.le _) (prefix_past T f K r _)
        (prefix_integrable T f K hK hbound r _)]
    · have hlt : i < j.succ := lt_of_le_of_ne hi he
      have hij : i≤j.castSucc := by
        change (i : ℕ)≤(j : ℕ)
        have hh : (i : ℕ)<(j : ℕ)+1 := hlt
        omega
      have ht := condExp_condExp_of_le (μ := fullLaw T f) (f := prefixIntegral T f K r j.succ)
        (naturalFiltration.mono (r.clock_mono hij)) (naturalFiltration.le (r.clock j.castSucc))
      exact ht.symm.trans ((condExp_congr_ae (m := naturalFiltration (r.clock i))
        (prefix_step_conditional T f K hK hbound r j)).trans (hj i hij))

/-- True martingale of actual literal Q integral prefixes in the ORIGINAL
finite-clock filtration, including collapsed cells. -/
theorem prefix_martingale {U : ℝ≥0} (r : ElementaryInput U) :
    Martingale (prefixIntegral T f K r) (prefixFiltration r) (fullLaw T f) :=
  ⟨prefix_past T f K r,fun i j hij => prefix_conditional T f K hK hbound r j i hij⟩

omit hK hbound in
/-- The actual final prefix is literally the returned finite integral. -/
theorem prefix_last {U : ℝ≥0} (r : ElementaryInput U) :
    prefixIntegral T f K r (Fin.last r.n)=simpleIntegral T f K r := by
  unfold prefixIntegral Fin.partialSum
  rw [List.take_of_length_le (by simp),List.sum_ofFn]
  funext ω
  simp only [simpleIntegral,Finset.sum_apply]

theorem simpleIntegral_mean_zero {U : ℝ≥0} (r : ElementaryInput U) :
    (∫ ω, simpleIntegral T f K r ω ∂fullLaw T f)=0 := by
  let _ := fullLaw_probability T f K hK hbound
  change (∫ ω, ∑ i : Fin r.n, oneStep T f K (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ) ω ∂fullLaw T f)=0
  rw [integral_finsetSum Finset.univ (fun i _ =>
    (oneStep_memLp_two T f K hK hbound (coefficient_Q T f K hK hbound r i) _ _).integrable one_le_two)]
  exact Finset.sum_eq_zero (fun i _ => oneStep_mean_zero T f K hK hbound _ _ (cell_mono r i)
    (r.coefficient_past i) (coefficient_Q T f K hK hbound r i))

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQSimpleIntegral
