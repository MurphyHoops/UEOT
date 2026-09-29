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

/-- Observable form of asymptotic invariance.

For every evolution label and every registered observable, if the base
trajectory and its evolved image both have observable limits and their
observable residual vanishes, then the two limiting observable values agree.

Unlike `equal_at_limit_of_residual`, this theorem owns the simultaneous
time/observable quantifiers used by long-run invariance arguments.  The
domain-specific construction of the observables, convergence, and residual
bounds remains explicit. -/
theorem observable_invariance_of_residual
    {State : Type*} {Time : Type*} {Obs : Type*}
    {Y : Type*} [AddGroup Y] [TopologicalSpace Y] [T2Space Y]
    [ContinuousSub Y]
    (observe : Obs → State → Y)
    (advance : Time → State → State)
    (seq : ℕ → State) (limit : State)
    (hbase : ∀ o, Tendsto (fun n => observe o (seq n))
      atTop (𝓝 (observe o limit)))
    (hpush : ∀ t o, Tendsto (fun n => observe o (advance t (seq n)))
      atTop (𝓝 (observe o (advance t limit))))
    (hres : ∀ t o, Tendsto
      (fun n => observe o (advance t (seq n)) - observe o (seq n))
      atTop (𝓝 0)) :
    ∀ t o, observe o (advance t limit) = observe o limit := by
  intro t o
  exact equal_at_limit_of_residual
    (fun n => observe o (advance t (seq n)))
    (fun n => observe o (seq n))
    (observe o (advance t limit))
    (observe o limit)
    (hpush t o) (hbase o) (hres t o)

/-- If the observable family separates states, observable asymptotic
invariance upgrades to actual invariance of the limiting state. -/
theorem invariant_of_observable_residual
    {State : Type*} {Time : Type*} {Obs : Type*}
    {Y : Type*} [AddGroup Y] [TopologicalSpace Y] [T2Space Y]
    [ContinuousSub Y]
    (observe : Obs → State → Y)
    (advance : Time → State → State)
    (seq : ℕ → State) (limit : State)
    (hseparates :
      ∀ x y : State, (∀ o, observe o x = observe o y) → x = y)
    (hbase : ∀ o, Tendsto (fun n => observe o (seq n))
      atTop (𝓝 (observe o limit)))
    (hpush : ∀ t o, Tendsto (fun n => observe o (advance t (seq n)))
      atTop (𝓝 (observe o (advance t limit))))
    (hres : ∀ t o, Tendsto
      (fun n => observe o (advance t (seq n)) - observe o (seq n))
      atTop (𝓝 0)) :
    ∀ t, advance t limit = limit := by
  intro t
  apply hseparates
  intro o
  exact observable_invariance_of_residual
    observe advance seq limit hbase hpush hres t o

/-- Continuous-observable form of asymptotic invariance.

This is the stronger reusable core used by the source-facing wrappers.  The
domain adapter supplies one convergent state sequence, a separating observable
family, continuity of the base/evolved observables, and a vanishing observable
evolution residual.  Passage of both observable faces to the limit and the
final state equality are handled here. -/
theorem invariant_of_continuous_observable_residual
    {State : Type*} [TopologicalSpace State]
    {Time : Type*} {Obs : Type*}
    {Y : Type*} [AddGroup Y] [TopologicalSpace Y] [T2Space Y]
    [ContinuousSub Y]
    (observe : Obs → State → Y)
    (advance : Time → State → State)
    (seq : ℕ → State) (limit : State)
    (hseq : Tendsto seq atTop (𝓝 limit))
    (hObserve : ∀ o, Continuous (observe o))
    (hAdvanceObserve : ∀ t o, Continuous (fun x => observe o (advance t x)))
    (hseparates :
      ∀ x y : State, (∀ o, observe o x = observe o y) → x = y)
    (hres : ∀ t o, Tendsto
      (fun n => observe o (advance t (seq n)) - observe o (seq n))
      atTop (𝓝 0)) :
    ∀ t, advance t limit = limit := by
  apply invariant_of_observable_residual
    observe advance seq limit hseparates
  · intro o
    exact ((hObserve o).tendsto limit).comp hseq
  · intro t o
    exact ((hAdvanceObserve t o).tendsto limit).comp hseq
  · exact hres

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
  let seq : ℕ → (S → ℝ) :=
    Subtype.val ∘ cesaroRow P hP μ0 ∘ φ
  let limit : S → ℝ := ν.1
  let advance : Unit → (S → ℝ) → (S → ℝ) := fun _ μ =>
    Matrix.vecMul μ P
  let observe : S → (S → ℝ) → ℝ := fun j μ => μ j
  have hseq : Tendsto seq atTop (𝓝 limit) := by
    exact (continuous_subtype_val.tendsto ν).comp hlim
  have hObserve : ∀ j, Continuous (observe j) := by
    intro j
    exact continuous_apply j
  have hAdvanceObserve : ∀ t j,
      Continuous (fun μ => observe j (advance t μ)) := by
    intro _ j
    have hcont : Continuous (fun μ : S → ℝ => Matrix.vecMul μ P) :=
      Continuous.matrix_vecMul continuous_id continuous_const
    exact (continuous_apply j).comp hcont
  have hresGlobal := cesaro_residual_tendsto_zero P hP μ0
  have hresSub :
      Tendsto
        (fun n =>
          Matrix.vecMul (cesaroRow P hP μ0 (φ n) : S → ℝ) P -
            (cesaroRow P hP μ0 (φ n) : S → ℝ))
        atTop (𝓝 0) :=
    hresGlobal.comp hφ.tendsto_atTop
  change Tendsto (fun n => Matrix.vecMul (seq n) P - seq n)
    atTop (𝓝 0) at hresSub
  have hres : ∀ t j, Tendsto
      (fun n => observe j (advance t (seq n)) - observe j (seq n))
        atTop (𝓝 0) := by
    intro _ j
    have hj := ((continuous_apply j).tendsto (0 : S → ℝ)).comp hresSub
    change Tendsto (fun n => (Matrix.vecMul (seq n) P - seq n) j)
      atTop (𝓝 0) at hj
    change Tendsto (fun n => (Matrix.vecMul (seq n) P - seq n) j)
      atTop (𝓝 0)
    exact hj
  have hinv : ∀ t, advance t limit = limit :=
    invariant_of_continuous_observable_residual
      observe advance seq limit hseq hObserve hAdvanceObserve
      (fun x y hxy => funext hxy)
      hres
  simpa [advance, limit] using hinv ()

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

/-- Markov evolution lifted from measures to probability measures. -/
noncomputable def fellerAdvancePM
    (S : FellerOccupationSystem X) (s : NNReal)
    (μ : ProbabilityMeasure X) : ProbabilityMeasure X := by
  letI : IsMarkovKernel (S.P s) := S.markov s
  exact ⟨S.P s ∘ₘ (μ : Measure X), by infer_instance⟩

@[simp] theorem fellerAdvancePM_toMeasure
    (S : FellerOccupationSystem X) (s : NNReal)
    (μ : ProbabilityMeasure X) :
    (fellerAdvancePM S s μ : Measure X) = S.P s ∘ₘ (μ : Measure X) := rfl

/-- The invariant-limit half of P-PER-02 reconstructed through the same
limit-residual theorem used by P-GOA-01. -/
theorem feller_invariant_of_occupation_tendsto
    (S : FellerOccupationSystem X)
    (Tseq : ℕ → NNReal) (hTseq : Tendsto Tseq atTop atTop)
    (ν : ProbabilityMeasure X)
    (hconv : Tendsto (fun n => S.occupation (Tseq n)) atTop (𝓝 ν)) :
    ∀ s : NNReal, S.P s ∘ₘ (ν : Measure X) = (ν : Measure X) := by
  let observe : BoundedContinuousFunction X ℝ → ProbabilityMeasure X → ℝ :=
    fun f μ => ∫ x, f x ∂(μ : Measure X)
  let advance : NNReal → ProbabilityMeasure X → ProbabilityMeasure X :=
    fellerAdvancePM S
  let seq : ℕ → ProbabilityMeasure X := fun n => S.occupation (Tseq n)
  have hseparates :
      ∀ μ η : ProbabilityMeasure X,
        (∀ f, observe f μ = observe f η) → μ = η := by
    intro μ η h
    letI : IsFiniteMeasure (μ : Measure X) := by infer_instance
    letI : IsFiniteMeasure (η : Measure X) := by infer_instance
    apply ProbabilityMeasure.toMeasure_injective
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro f
    exact h f
  have hObserve : ∀ f, Continuous (observe f) := by
    intro f
    simpa [observe] using
      (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f)
  have hAdvanceObserve : ∀ s f,
      Continuous (fun μ => observe f (advance s μ)) := by
    intro s f
    have haction :=
      ProbabilityMeasure.continuous_integral_boundedContinuousFunction
        (S.action s f)
    simpa [observe, advance, integral_push_eq_action] using haction
  have hres : ∀ s f, Tendsto
      (fun n => observe f (advance s (seq n)) - observe f (seq n))
        atTop (𝓝 0) := by
    intro s f
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
    have hle : ∀ᶠ n in atTop,
        |observe f (advance s (seq n)) - observe f (seq n)| ≤
          2 * (s : ℝ) * ‖f‖ / (Tseq n : ℝ) := by
      filter_upwards [hlarge] with n hn
      simpa [observe, advance, seq] using
        S.occupation_shift_bound
          (Tseq n) s (ne_of_gt (zero_lt_one.trans_le hn)) f
    rw [tendsto_zero_iff_abs_tendsto_zero]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hbound
      (Eventually.of_forall fun n =>
        abs_nonneg (observe f (advance s (seq n)) - observe f (seq n))) hle
  have hinv : ∀ s, advance s ν = ν :=
    invariant_of_continuous_observable_residual
      observe advance seq ν hconv hObserve hAdvanceObserve hseparates hres
  intro s
  have hs := congrArg (fun μ : ProbabilityMeasure X => (μ : Measure X)) (hinv s)
  simpa [advance] using hs

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
