import UEOT
open MeasureTheory ProbabilityTheory Set
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianFiniteProductSource BrownianVectorOneStepIntegral BrownianVectorSimplePredictableIntegral
open BrownianVectorTimeInput BrownianVectorRepresentation
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

-- Universal same-source permissions are joint-past and require no own-source factorization.
example {d n m : ℕ} (T : ℝ≥0) (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (hτ : Monotone τ) (hσ : Monotone σ) (hzτ : τ 0=0) (hzσ : σ 0=0)
    (heτ : τ (Fin.last n)=T) (heσ : σ (Fin.last m)=T)
    (H : Fin n → Fin d → Sample d → ℝ) (K : Fin m → Fin d → Sample d → ℝ)
    (hpH : ∀ i k, StronglyMeasurable[jointNaturalFiltration d (τ i.castSucc)] (H i k))
    (hpK : ∀ j k, StronglyMeasurable[jointNaturalFiltration d (σ j.castSucc)] (K j k))
    (hbH : ∀ i k, MemLp (H i k) ∞ (productLaw d)) (hbK : ∀ j k, MemLp (K j k) ∞ (productLaw d)) :
    dist (outputClass τ H hbH) (outputClass σ K hbK) = dist (inputClass T τ H hbH) (inputClass T σ K hbK) :=
  input_output_distance T τ σ hτ hσ hzτ hzσ heτ heσ H K hpH hpK hbH hbK

def coarse : Fin 2 → ℝ≥0 := ![0,1]
def split : Fin 3 → ℝ≥0 := ![0,0,1]
def H : Fin 1 → Fin 2 → Sample 2 → ℝ := fun _ _ _ => 1
def K : Fin 2 → Fin 2 → Sample 2 → ℝ := fun _ _ _ => 1

theorem coarse_mono : Monotone coarse := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [coarse]
theorem split_mono : Monotone split := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [split]

theorem raw_same (p : ℝ × Sample 2) : integrand 2 coarse H p = integrand 2 split K p := by
  simp only [integrand,Fin.sum_univ_one,Fin.sum_univ_two]
  change intervalInput 2 (fun _ _ => 1) 0 1 p =
    intervalInput 2 (fun _ _ => 1) 0 0 p + intervalInput 2 (fun _ _ => 1) 0 1 p
  simp [intervalInput]

theorem same_native_input :
    inputClass 1 coarse H (fun _ _ => memLp_top_const 1) =
      inputClass 1 split K (fun _ _ => memLp_top_const 1) := by
  apply Lp.ext
  filter_upwards [(integrand_memLp_two 1 coarse H (fun _ _ => memLp_top_const 1)).coeFn_toLp,
    (integrand_memLp_two 1 split K (fun _ _ => memLp_top_const 1)).coeFn_toLp] with p hc hs
  change (inputClass 1 coarse H (fun _ _ => memLp_top_const 1)) p = _ at hc
  change (inputClass 1 split K (fun _ _ => memLp_top_const 1)) p = _ at hs
  rw [hc,hs,raw_same]

-- Two genuinely different partitions/classes return the actual original sums.
example : simpleIntegral 2 coarse H =ᵐ[productLaw 2] simpleIntegral 2 split K :=
  output_ae_eq_of_inputClass_eq 1 coarse split coarse_mono split_mono rfl rfl rfl rfl H K
    (fun _ _ => stronglyMeasurable_const) (fun _ _ => stronglyMeasurable_const)
    (fun _ _ => memLp_top_const 1) (fun _ _ => memLp_top_const 1) same_native_input

-- In this empty common cell the right coefficient belongs to time2, while
-- the collapsed left cell is at1. It must become0, not be granted time1 access.
def earlier (i : Fin 3) : ℝ≥0 := if (i : ℕ)=0 then 0 else if (i : ℕ)=1 then 1 else 3
def later (i : Fin 3) : ℝ≥0 := if (i : ℕ)=0 then 0 else if (i : ℕ)=1 then 2 else 3

example (A B : Fin 2 → Fin 2 → Sample 2 → ℝ) (k : Fin 2) (ω : Sample 2) :
    commonDifference earlier later A B 0 1 k ω = 0 := by
  norm_num [commonDifference,BrownianCommonRefinement.commonStart,BrownianCommonRefinement.commonEnd,
    BrownianCommonRefinement.clamp,earlier,later]

-- Empty/zero-dimensional inputs stay literal, before any quotient extension.
example (p : ℝ × Sample 0) : integrand 0 (fun _ : Fin 1 => (0 : ℝ≥0))
    (fun i : Fin 0 => Fin.elim0 i) p = 0 := by simp [integrand]

-- d0 passes THROUGH representation independence, with vacuous legitimate
-- permissions and no nonempty noise-coordinate assumption.
example {n m : ℕ} (T : ℝ≥0) (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (hτ : Monotone τ) (hσ : Monotone σ) (hzτ : τ 0=0) (hzσ : σ 0=0)
    (heτ : τ (Fin.last n)=T) (heσ : σ (Fin.last m)=T)
    (A : Fin n → Fin 0 → Sample 0 → ℝ) (B : Fin m → Fin 0 → Sample 0 → ℝ) :
    simpleIntegral 0 τ A =ᵐ[productLaw 0] simpleIntegral 0 σ B := by
  apply output_ae_eq_of_inputClass_eq T τ σ hτ hσ hzτ hzσ heτ heσ A B
    (fun _ k => Fin.elim0 k) (fun _ k => Fin.elim0 k)
    (fun _ k => Fin.elim0 k) (fun _ k => Fin.elim0 k)
  apply Lp.ext
  exact ae_of_all _ (fun _ => Subsingleton.elim _ _)

example (d : ℕ) :
    simpleIntegral d (fun _ : Fin 1 => (0 : ℝ≥0)) (fun i : Fin 0 => Fin.elim0 i)
      =ᵐ[productLaw d]
    simpleIntegral d (fun _ : Fin 1 => (0 : ℝ≥0)) (fun i : Fin 0 => Fin.elim0 i) := by
  apply output_ae_eq_of_inputClass_eq 0 _ _ (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl)
    rfl rfl rfl rfl _ _ (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  rfl
