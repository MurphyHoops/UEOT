import UEOT.V3.PersistenceOccupation
import UEOT.V3.FiniteCesaroInvariant

/-!
# Experimental M-OI-01 — occupation-limit invariance

This module tests whether the common core of P-PER-02 and P-GOA-01 can be
factored through one generic limit-residual principle without weakening either
source theorem.  It is deliberately experimental and does not alter the frozen
compression ledger.
-/

namespace UEOT.V3.Compression.OccupationLimitInvariance

open Filter Topology MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

/-- If two observable sequences converge to the two candidate limit values,
while their difference converges to zero, the candidate limit values are equal.

This is the abstract asymptotic-invariance core shared by the finite Cesaro and
Feller occupation arguments.  Compactness/tightness, continuity of the
domain-specific observable, and support inheritance remain adapters. -/
theorem equal_at_limit_of_residual
    {Y : Type*} [AddGroup Y] [TopologicalSpace Y] [T2Space Y]
    [ContinuousSub Y]
    (Fseq Gseq : ℕ → Y) (Fstar Gstar : Y)
    (hF : Tendsto Fseq atTop (𝓝 Fstar))
    (hG : Tendsto Gseq atTop (𝓝 Gstar))
    (hres : Tendsto (fun n => Fseq n - Gseq n) atTop (𝓝 0)) :
    Fstar = Gstar := by
  have hdiff :
      Tendsto (fun n => Fseq n - Gseq n) atTop (𝓝 (Fstar - Gstar)) :=
    hF.sub hG
  have hz : Fstar - Gstar = 0 :=
    tendsto_nhds_unique hdiff hres
  exact sub_eq_zero.mp hz

section FiniteCesaro

open UEOT.V3.FiniteCesaroInvariant

universe uS

variable {S : Type uS} [Fintype S] [DecidableEq S]

/-- The invariant-limit half of P-GOA-01 reconstructed through the generic
limit-residual theorem. -/
theorem finite_invariant_of_cesaro_tendsto
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (μ0 : stdSimplex ℝ S)
    (ν : stdSimplex ℝ S) (φ : ℕ → ℕ)
    (hφ : StrictMono φ)
    (hlim : Tendsto (cesaroRow P hP μ0 ∘ φ) atTop (𝓝 ν)) :
    Matrix.vecMul ν.1 P = ν.1 := by
  let F : stdSimplex ℝ S → (S → ℝ) :=
    fun μ => Matrix.vecMul μ.1 P
  let G : stdSimplex ℝ S → (S → ℝ) :=
    fun μ => μ.1
  have hFcontinuous : Continuous F := by
    exact Continuous.matrix_vecMul continuous_subtype_val continuous_const
  have hGcontinuous : Continuous G :=
    continuous_subtype_val
  have hF :
      Tendsto (fun n => F ((cesaroRow P hP μ0 ∘ φ) n))
        atTop (𝓝 (F ν)) :=
    (hFcontinuous.tendsto ν).comp hlim
  have hG :
      Tendsto (fun n => G ((cesaroRow P hP μ0 ∘ φ) n))
        atTop (𝓝 (G ν)) :=
    (hGcontinuous.tendsto ν).comp hlim
  have hresGlobal := cesaro_residual_tendsto_zero P hP μ0
  have hresSub :
      Tendsto
        (fun n =>
          Matrix.vecMul (cesaroRow P hP μ0 (φ n) : S → ℝ) P -
            (cesaroRow P hP μ0 (φ n) : S → ℝ))
        atTop (𝓝 0) :=
    hresGlobal.comp hφ.tendsto_atTop
  have hEq : F ν = G ν := by
    apply equal_at_limit_of_residual
      (fun n => F ((cesaroRow P hP μ0 ∘ φ) n))
      (fun n => G ((cesaroRow P hP μ0 ∘ φ) n))
      (F ν) (G ν) hF hG
    change
      Tendsto
        (fun n =>
          Matrix.vecMul (cesaroRow P hP μ0 (φ n) : S → ℝ) P -
            (cesaroRow P hP μ0 (φ n) : S → ℝ))
        atTop (𝓝 0)
    exact hresSub
  simpa [F, G] using hEq

/-- Full P-GOA-01 statement with only the invariant-limit step delegated to
M-OI-01.  Finite-simplex compactness remains the explicit extraction adapter. -/
theorem p_goa_01_via_occupationLimit
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (μ0 : stdSimplex ℝ S) :
    (∃ ν : stdSimplex ℝ S, ∃ φ : ℕ → ℕ,
        StrictMono φ ∧ Tendsto (cesaroRow P hP μ0 ∘ φ) atTop (𝓝 ν)) ∧
      (∀ (ν : stdSimplex ℝ S) (φ : ℕ → ℕ),
        StrictMono φ →
        Tendsto (cesaroRow P hP μ0 ∘ φ) atTop (𝓝 ν) →
        Matrix.vecMul ν.1 P = ν.1) := by
  constructor
  · rcases CompactSpace.tendsto_subseq (cesaroRow P hP μ0) with
      ⟨ν, φ, hφ, hlim⟩
    exact ⟨ν, φ, hφ, hlim⟩
  · intro ν φ hφ hlim
    exact finite_invariant_of_cesaro_tendsto P hP μ0 ν φ hφ hlim

end FiniteCesaro

section FellerOccupation

open UEOT.V3.PersistenceOccupation
open UEOT.V3.PersistenceOccupation.FellerOccupationSystem

universe uX

variable {X : Type uX}
variable [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompleteSpace X] [SecondCountableTopology X]

/-- The invariant-limit half of P-PER-02 reconstructed through the same
limit-residual theorem used by P-GOA-01. -/
theorem feller_invariant_of_occupation_tendsto
    (S : FellerOccupationSystem X)
    (Tseq : ℕ → NNReal) (hTseq : Tendsto Tseq atTop atTop)
    (ν : ProbabilityMeasure X)
    (hconv : Tendsto (fun n => S.occupation (Tseq n)) atTop (𝓝 ν)) :
    ∀ s : NNReal, S.P s ∘ₘ (ν : Measure X) = (ν : Measure X) := by
  intro s
  letI : IsMarkovKernel (S.P s) := S.markov s
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let Fseq : ℕ → ℝ := fun n =>
    ∫ x, f x ∂(S.P s ∘ₘ (S.occupation (Tseq n) : Measure X))
  let Gseq : ℕ → ℝ := fun n =>
    ∫ x, f x ∂(S.occupation (Tseq n) : Measure X)
  let Fstar : ℝ :=
    ∫ x, f x ∂(S.P s ∘ₘ (ν : Measure X))
  let Gstar : ℝ :=
    ∫ x, f x ∂(ν : Measure X)
  have hG : Tendsto Gseq atTop (𝓝 Gstar) := by
    simpa [Gseq, Gstar] using
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv) f
  have haction :
      Tendsto
        (fun n =>
          ∫ x, S.action s f x ∂(S.occupation (Tseq n) : Measure X))
        atTop (𝓝 (∫ x, S.action s f x ∂(ν : Measure X))) :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv) (S.action s f)
  have hF : Tendsto Fseq atTop (𝓝 Fstar) := by
    simpa [Fseq, Fstar, integral_push_eq_action] using haction
  have hcoe : Tendsto (fun n => (Tseq n : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.2 hTseq
  have hbound :
      Tendsto (fun n => 2 * (s : ℝ) * ‖f‖ / (Tseq n : ℝ))
        atTop (𝓝 0) := by
    have hinv : Tendsto (fun n => ((Tseq n : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hcoe
    simpa [div_eq_mul_inv] using hinv.const_mul (2 * (s : ℝ) * ‖f‖)
  have hlarge : ∀ᶠ n in atTop, (1 : NNReal) ≤ Tseq n :=
    (tendsto_atTop.1 hTseq) 1
  have hle : ∀ᶠ n in atTop, |Fseq n - Gseq n| ≤
      2 * (s : ℝ) * ‖f‖ / (Tseq n : ℝ) := by
    filter_upwards [hlarge] with n hn
    simpa [Fseq, Gseq] using
      S.occupation_shift_bound
        (Tseq n) s (ne_of_gt (zero_lt_one.trans_le hn)) f
  have hres : Tendsto (fun n => Fseq n - Gseq n) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hbound
      (Eventually.of_forall fun n => abs_nonneg (Fseq n - Gseq n)) hle
  exact equal_at_limit_of_residual
    Fseq Gseq Fstar Gstar hF hG hres

/-- Full P-PER-02 statement with extraction and closed-support inheritance kept
as explicit Feller/Prokhorov/Portmanteau adapters, while the invariant-limit
step is shared with the finite GOA theorem. -/
theorem p_per_02_via_occupationLimit
    (S : FellerOccupationSystem X)
    (hTight : IsTightMeasureSet
      {((ν : ProbabilityMeasure X) : Measure X) | ν ∈ occupationFamily S})
    (Tseq : ℕ → NNReal) (hTseq : Tendsto Tseq atTop atTop) :
    ∃ (ν : ProbabilityMeasure X) (φ : ℕ → ℕ),
      StrictMono φ ∧
      Tendsto (fun n => S.occupation (Tseq (φ n))) atTop (𝓝 ν) ∧
      Tendsto (fun n => Tseq (φ n)) atTop atTop ∧
      (∀ s : NNReal, S.P s ∘ₘ (ν : Measure X) = (ν : Measure X)) ∧
      (∀ K : Set X, IsClosed K →
        (∀ t : NNReal, (S.marginal t : Measure X) K = 1) →
        (ν : Measure X) K = 1) ∧
      (∀ (U : ℕ → NNReal) (ν' : ProbabilityMeasure X),
        Tendsto U atTop atTop →
        Tendsto (fun n => S.occupation (U n)) atTop (𝓝 ν') →
        (∀ s : NNReal, S.P s ∘ₘ (ν' : Measure X) = (ν' : Measure X)) ∧
        (∀ K : Set X, IsClosed K →
          (∀ t : NNReal, (S.marginal t : Measure X) K = 1) →
          (ν' : Measure X) K = 1)) := by
  obtain ⟨ν, φ, hφ, hconv, htime⟩ :=
    S.occupation_tendsto_subseq_of_tight hTight Tseq hTseq
  refine ⟨ν, φ, hφ, hconv, htime, ?_, ?_, ?_⟩
  · exact feller_invariant_of_occupation_tendsto
      S (fun n => Tseq (φ n)) htime ν hconv
  · intro K hK hstay
    exact S.closed_support_of_occupation_tendsto
      (fun n => Tseq (φ n)) htime ν hconv K hK hstay
  · intro U ν' hU hUconv
    refine ⟨feller_invariant_of_occupation_tendsto S U hU ν' hUconv, ?_⟩
    intro K hK hstay
    exact S.closed_support_of_occupation_tendsto U hU ν' hUconv K hK hstay

end FellerOccupation

end UEOT.V3.Compression.OccupationLimitInvariance
