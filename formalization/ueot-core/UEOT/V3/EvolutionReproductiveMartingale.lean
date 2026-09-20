import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Probability.Martingale.Basic
import Mathlib.Tactic

/-!
# P-EVO-04 — reproductive-value martingale

The frozen Core 3 source considers a finite-type branching population with
count vector `Z_n`, mean offspring matrix `M`, and the natural filtration.  Its
mechanism-level first-moment statement is

`E[Z_{n+1} | F_n] = Z_n M`.

K-PF-01 supplies a positive Perron factor `R` and positive right eigenvector
`r`, `M r = R r`.  This module keeps the vector conditional-mean premise
literal, derives the scalar reproductive-value recursion through a finite
continuous-linear readout, and proves that

`W_n = R^{-n} Z_n r`

is a nonnegative integrable martingale with constant mean `Z_0 r`.

The explicit adaptedness/integrability/nonnegativity hypotheses are the process
semantic consequences of the source's natural-filtration, finite-first-moment
branching setup.  In particular, the scalar martingale recursion is not assumed.
Perron existence or power asymptotics are not reproved here; as elsewhere in
Core 3, K-PF-01 Perron data are standard theorem input.
-/

namespace UEOT.V3.EvolutionReproductiveMartingale

noncomputable section

open MeasureTheory
open scoped BigOperators

universe uI uΩ

variable {I : Type uI} [Fintype I] [DecidableEq I]
variable {Ω : Type uΩ} {m0 : MeasurableSpace Ω}
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration ℕ m0}

/-- Finite reproductive-value readout `z ↦ z r`. -/
def reproValueCLM (r : I → ℝ) : (I → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => ∑ i : I, z i * r i
      map_add' := by
        intro x y
        simp only [Pi.add_apply]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      map_smul' := by
        intro c x
        simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring }

@[simp] theorem reproValueCLM_apply (r z : I → ℝ) :
    reproValueCLM r z = ∑ i : I, z i * r i := rfl

/-- Perron right-eigenvector relation turns the reproductive-value readout of
one mean offspring step into multiplication by `R`. -/
theorem reproValue_vecMul
    (M : Matrix I I ℝ) (r z : I → ℝ) (R : ℝ)
    (hperron : ∀ i, ∑ j : I, M i j * r j = R * r i) :
    reproValueCLM r (Matrix.vecMul z M) = R * reproValueCLM r z := by
  simp only [reproValueCLM_apply, Matrix.vecMul, dotProduct]
  calc
    (∑ j : I, (∑ i : I, z i * M i j) * r j) =
        ∑ j : I, ∑ i : I, (z i * M i j) * r j := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.sum_mul]
    _ = ∑ i : I, ∑ j : I, (z i * M i j) * r j := by
          rw [Finset.sum_comm]
    _ = ∑ i : I, z i * (∑ j : I, M i j * r j) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = ∑ i : I, z i * (R * r i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hperron i]
    _ = R * ∑ i : I, z i * r i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring

/-- Source normalized reproductive value. -/
def W (R : ℝ) (r : I → ℝ) (Z : ℕ → Ω → (I → ℝ)) (n : ℕ) (ω : Ω) : ℝ :=
  (R ^ n)⁻¹ * reproValueCLM r (Z n ω)

/-- A vector-valued conditional mean identity implies the scalar reproductive
value conditional mean identity. -/
theorem condExp_reproValue
    (M : Matrix I I ℝ) (R : ℝ) (r : I → ℝ)
    (Z : ℕ → Ω → (I → ℝ))
    (hZint : ∀ n, Integrable (Z n) μ)
    (hmean : ∀ n,
      μ[Z (n + 1) | ℱ n] =ᵐ[μ]
        fun ω => Matrix.vecMul (Z n ω) M)
    (hperron : ∀ i, ∑ j : I, M i j * r j = R * r i)
    (n : ℕ) :
    μ[fun ω => reproValueCLM r (Z (n + 1) ω) | ℱ n] =ᵐ[μ]
      fun ω => R * reproValueCLM r (Z n ω) := by
  have hcomm :=
    ContinuousLinearMap.comp_condExp_comm
      (m := ℱ n) (hZint (n + 1)) (reproValueCLM r)
  calc
    μ[fun ω => reproValueCLM r (Z (n + 1) ω) | ℱ n]
        =ᵐ[μ] (reproValueCLM r) ∘ μ[Z (n + 1) | ℱ n] := hcomm.symm
    _ =ᵐ[μ] fun ω => reproValueCLM r (Matrix.vecMul (Z n ω) M) := by
      exact (hmean n).mono fun ω hω => congrArg (reproValueCLM r) hω
    _ =ᵐ[μ] fun ω => R * reproValueCLM r (Z n ω) := by
      exact Filter.Eventually.of_forall fun ω => reproValue_vecMul M r (Z n ω) R hperron

/-- The normalized reproductive value has the one-step martingale conditional
expectation relation. -/
theorem condExp_W_succ
    (M : Matrix I I ℝ) (R : ℝ) (r : I → ℝ)
    (Z : ℕ → Ω → (I → ℝ))
    (hR : 0 < R)
    (hZint : ∀ n, Integrable (Z n) μ)
    (hmean : ∀ n,
      μ[Z (n + 1) | ℱ n] =ᵐ[μ]
        fun ω => Matrix.vecMul (Z n ω) M)
    (hperron : ∀ i, ∑ j : I, M i j * r j = R * r i)
    (n : ℕ) :
    μ[W R r Z (n + 1) | ℱ n] =ᵐ[μ] W R r Z n := by
  have hscalar := condExp_reproValue M R r Z hZint hmean hperron n
  have hsmul := condExp_smul (μ := μ) ((R ^ (n + 1))⁻¹)
    (fun ω => reproValueCLM r (Z (n + 1) ω)) (ℱ n)
  have hR0 : R ≠ 0 := hR.ne'
  change
    μ[fun ω => (R ^ (n + 1))⁻¹ * reproValueCLM r (Z (n + 1) ω) | ℱ n]
      =ᵐ[μ] fun ω => (R ^ n)⁻¹ * reproValueCLM r (Z n ω)
  calc
    μ[fun ω => (R ^ (n + 1))⁻¹ * reproValueCLM r (Z (n + 1) ω) | ℱ n]
        =ᵐ[μ] fun ω => (R ^ (n + 1))⁻¹ *
          μ[fun ω => reproValueCLM r (Z (n + 1) ω) | ℱ n] ω := by
            change
              μ[((R ^ (n + 1))⁻¹) • (fun ω => reproValueCLM r (Z (n + 1) ω)) | ℱ n]
                =ᵐ[μ] ((R ^ (n + 1))⁻¹) •
                  μ[fun ω => reproValueCLM r (Z (n + 1) ω) | ℱ n]
            exact hsmul
    _ =ᵐ[μ] fun ω => (R ^ (n + 1))⁻¹ *
          (R * reproValueCLM r (Z n ω)) := by
            exact hscalar.mono fun ω hω => congrArg (fun x => (R ^ (n + 1))⁻¹ * x) hω
    _ =ᵐ[μ] fun ω => (R ^ n)⁻¹ * reproValueCLM r (Z n ω) := by
      exact Filter.Eventually.of_forall fun ω => by
        rw [pow_succ]
        field_simp [hR0]

/-- Strong adaptedness descends from the count-vector process to `W`. -/
theorem stronglyAdapted_W
    (R : ℝ) (r : I → ℝ) (Z : ℕ → Ω → (I → ℝ))
    (hZadapt : StronglyAdapted ℱ Z) :
    StronglyAdapted ℱ (W R r Z) := by
  intro n
  have hv : StronglyMeasurable[ℱ n] (fun ω => reproValueCLM r (Z n ω)) :=
    (reproValueCLM r).continuous.comp_stronglyMeasurable (hZadapt n)
  exact (continuous_const.mul continuous_id).comp_stronglyMeasurable hv

/-- Integrability descends from the count-vector process to `W`. -/
theorem integrable_W
    (R : ℝ) (r : I → ℝ) (Z : ℕ → Ω → (I → ℝ))
    (hZint : ∀ n, Integrable (Z n) μ) :
    ∀ n, Integrable (W R r Z n) μ := by
  intro n
  have hv : Integrable (fun ω => reproValueCLM r (Z n ω)) μ :=
    (reproValueCLM r).integrable_comp (hZint n)
  change Integrable (fun ω => (R ^ n)⁻¹ * reproValueCLM r (Z n ω)) μ
  exact hv.const_mul ((R ^ n)⁻¹)

/-- Nonnegative counts and nonnegative Perron weights make `W` nonnegative. -/
theorem W_nonneg
    (R : ℝ) (r : I → ℝ) (Z : ℕ → Ω → (I → ℝ))
    (hR : 0 < R)
    (hr : ∀ i, 0 ≤ r i)
    (hZ0 : ∀ n ω i, 0 ≤ Z n ω i) :
    ∀ n ω, 0 ≤ W R r Z n ω := by
  intro n ω
  have hscale : 0 ≤ (R ^ n)⁻¹ := inv_nonneg.mpr (pow_nonneg (le_of_lt hR) n)
  have hsum : 0 ≤ reproValueCLM r (Z n ω) := by
    simp only [reproValueCLM_apply]
    exact Finset.sum_nonneg fun i hi => mul_nonneg (hZ0 n ω i) (hr i)
  exact mul_nonneg hscale hsum

/-- The full normalized reproductive-value process is a martingale. -/
theorem reproductiveValue_martingale
    (M : Matrix I I ℝ) (R : ℝ) (r : I → ℝ)
    (Z : ℕ → Ω → (I → ℝ))
    (hR : 0 < R)
    (hZadapt : StronglyAdapted ℱ Z)
    (hZint : ∀ n, Integrable (Z n) μ)
    (hmean : ∀ n,
      μ[Z (n + 1) | ℱ n] =ᵐ[μ]
        fun ω => Matrix.vecMul (Z n ω) M)
    (hperron : ∀ i, ∑ j : I, M i j * r j = R * r i) :
    Martingale (W R r Z) ℱ μ := by
  apply martingale_nat (stronglyAdapted_W R r Z hZadapt)
    (integrable_W R r Z hZint)
  intro n
  exact (condExp_W_succ M R r Z hR hZint hmean hperron n).symm

/-- If generation zero is a deterministic finite count vector, every `W_n`
has expectation equal to its initial reproductive value. -/
theorem reproductiveValue_expectation
    (M : Matrix I I ℝ) (R : ℝ) (r : I → ℝ)
    (Z : ℕ → Ω → (I → ℝ))
    (z0 : I → ℕ)
    (hR : 0 < R)
    (hZadapt : StronglyAdapted ℱ Z)
    (hZint : ∀ n, Integrable (Z n) μ)
    (hmean : ∀ n,
      μ[Z (n + 1) | ℱ n] =ᵐ[μ]
        fun ω => Matrix.vecMul (Z n ω) M)
    (hperron : ∀ i, ∑ j : I, M i j * r j = R * r i)
    (hinit : ∀ ω i, Z 0 ω i = (z0 i : ℝ)) :
    ∀ n, ∫ ω, W R r Z n ω ∂μ = ∑ i : I, (z0 i : ℝ) * r i := by
  intro n
  have hmart := reproductiveValue_martingale M R r Z hR hZadapt hZint hmean hperron
  have hEq := hmart.setIntegral_eq (i := 0) (j := n) (Nat.zero_le n)
    (s := Set.univ) MeasurableSet.univ
  have h0 : (fun ω => W R r Z 0 ω) = fun _ => ∑ i : I, (z0 i : ℝ) * r i := by
    funext ω
    simp only [W, pow_zero, inv_one, one_mul, reproValueCLM_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hinit ω i]
  have hEq' : ∫ ω, W R r Z 0 ω ∂μ = ∫ ω, W R r Z n ω ∂μ := by
    simpa only [Measure.restrict_univ] using hEq
  have hW0 : ∫ ω, W R r Z 0 ω ∂μ = ∑ i : I, (z0 i : ℝ) * r i := by
    rw [h0]
    simp
  exact hEq'.symm.trans hW0

/-- **P-EVO-04.** The normalized reproductive value is a nonnegative
integrable martingale and its expectation is the deterministic initial
reproductive value. -/
theorem p_evo_04
    (M : Matrix I I ℝ) (R : ℝ) (r : I → ℝ)
    (Z : ℕ → Ω → (I → ℝ))
    (z0 : I → ℕ)
    (hR : 0 < R)
    (hr : ∀ i, 0 < r i)
    (hZnonneg : ∀ n ω i, 0 ≤ Z n ω i)
    (hZadapt : StronglyAdapted ℱ Z)
    (hZint : ∀ n, Integrable (Z n) μ)
    (hmean : ∀ n,
      μ[Z (n + 1) | ℱ n] =ᵐ[μ]
        fun ω => Matrix.vecMul (Z n ω) M)
    (hperron : ∀ i, ∑ j : I, M i j * r j = R * r i)
    (hinit : ∀ ω i, Z 0 ω i = (z0 i : ℝ)) :
    Martingale (W R r Z) ℱ μ ∧
      (∀ n ω, 0 ≤ W R r Z n ω) ∧
      (∀ n, Integrable (W R r Z n) μ) ∧
      (∀ n, ∫ ω, W R r Z n ω ∂μ = ∑ i : I, (z0 i : ℝ) * r i) := by
  have hmart := reproductiveValue_martingale M R r Z hR hZadapt hZint hmean hperron
  refine ⟨hmart, ?_, ?_, ?_⟩
  · exact W_nonneg R r Z hR (fun i => (hr i).le) hZnonneg
  · exact fun n => hmart.integrable n
  · exact reproductiveValue_expectation M R r Z z0 hR hZadapt hZint hmean hperron hinit

end

end UEOT.V3.EvolutionReproductiveMartingale
