import UEOT.V3.TVSpan
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Tactic

/-!
# P-PER-02 — Feller occupation persistence

Source-faithful Krylov--Bogoliubov bridge for a continuous-time Feller Markov
semigroup on a Polish state space. Occupation averages are represented
extensionally by their literal time-average identities; invariance and weak
subsequential limits are derived, never assumed.
-/

namespace UEOT.V3.PersistenceOccupation

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ProbabilityTheory

universe uX

variable {X : Type uX}
variable [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompleteSpace X] [SecondCountableTopology X]

/-- The literal marginal obtained by pushing the initial law through a Markov
kernel family.  This helper exists only to keep the source object identity
visible inside the interface below. -/
noncomputable def evolvedLaw
    (P : NNReal → Kernel X X) (hP : ∀ t, IsMarkovKernel (P t))
    (μ₀ : ProbabilityMeasure X) (t : NNReal) : ProbabilityMeasure X := by
  letI : IsMarkovKernel (P t) := hP t
  exact ⟨P t ∘ₘ (μ₀ : Measure X), inferInstance⟩

/-- Source continuous-time Markov/Feller/occupation interface. The two
occupation identities are extensional faces of the literal source definition
of the time-averaged marginal measure, not invariance assumptions. -/
structure FellerOccupationSystem (X : Type uX)
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X] where
  P : NNReal → Kernel X X
  markov : ∀ t, IsMarkovKernel (P t)
  zero : P 0 = Kernel.id
  semigroup : ∀ s t, P (s + t) = P t ∘ₖ P s
  action : NNReal → (BoundedContinuousFunction X ℝ) → BoundedContinuousFunction X ℝ
  action_apply :
    ∀ s f x, action s f x = ∫ y, f y ∂P s x
  initial : ProbabilityMeasure X
  occupation : NNReal → ProbabilityMeasure X
  /-- `C_b`-observable face of the literal measure average
  `T⁻¹ ∫₀ᵀ μ₀P_t dt`. This identifies `occupation T`; it does not assume
  invariance or any limiting property. -/
  occupation_integral :
    ∀ (T : NNReal), T ≠ 0 → ∀ f : BoundedContinuousFunction X ℝ,
      (∫ x, f x ∂(occupation T : Measure X)) =
        (T : ℝ)⁻¹ *
          ∫ t in (0 : ℝ)..(T : ℝ),
            (∫ x, f x ∂(evolvedLaw P markov initial (Real.toNNReal t) : Measure X))
  /-- Measurable-event face of the same literal measure average. It is used to
  derive support retention from the source marginal laws rather than assuming
  support directly for the occupation measures. -/
  occupation_event_real :
    ∀ (T : NNReal), T ≠ 0 → ∀ A : Set X, MeasurableSet A →
      (occupation T : Measure X).real A =
        (T : ℝ)⁻¹ *
          ∫ t in (0 : ℝ)..(T : ℝ),
            ((evolvedLaw P markov initial (Real.toNNReal t) : Measure X).real A)
  /-- Minimal local-in-time regularity used to translate and split the scalar
  occupation integrals in the Krylov--Bogoliubov shift estimate. -/
  time_intervalIntegrable :
    ∀ f : BoundedContinuousFunction X ℝ, ∀ a b : ℝ,
      0 ≤ a → 0 ≤ b →
      IntervalIntegrable
        (fun t => ∫ x, f x ∂(evolvedLaw P markov initial (Real.toNNReal t) : Measure X))
        volume a b

namespace FellerOccupationSystem

/-- The source time marginal μ₀ P_t. -/
noncomputable def marginal (S : FellerOccupationSystem X) (t : NNReal) :
    ProbabilityMeasure X :=
  evolvedLaw S.P S.markov S.initial t

@[simp] theorem marginal_toMeasure (S : FellerOccupationSystem X) (t : NNReal) :
    (S.marginal t : Measure X) = S.P t ∘ₘ (S.initial : Measure X) := rfl

/-- Integrating a bounded continuous observable through a Markov kernel. -/
theorem integral_comp_measure
    (μ : Measure X) [IsProbabilityMeasure μ]
    (κ : Kernel X X) [IsMarkovKernel κ]
    (f : BoundedContinuousFunction X ℝ) :
    ∫ y, f y ∂(κ ∘ₘ μ) = ∫ x, (∫ y, f y ∂κ x) ∂μ := by
  have hfcomp : Integrable (fun y => f y) (κ ∘ₘ μ) := by
    exact UEOT.V3.TVSpan.integrable_of_interval
      (κ ∘ₘ μ) f f.continuous.measurable (-‖f‖) ‖f‖
      (fun y => BoundedContinuousFunction.neg_norm_le_apply f y)
      (fun y => BoundedContinuousFunction.apply_le_norm f y)
  rw [Measure.comp_eq_comp_const_apply]
  exact Kernel.integral_comp hfcomp

/-- Semigroup evolution of the literal source marginals. -/
theorem marginal_add (S : FellerOccupationSystem X) (s t : NNReal) :
    (S.P t ∘ₘ (S.marginal s : Measure X)) =
      (S.marginal (s + t) : Measure X) := by
  letI : IsMarkovKernel (S.P s) := S.markov s
  letI : IsMarkovKernel (S.P t) := S.markov t
  rw [marginal_toMeasure, Measure.comp_assoc, ← S.semigroup]
  rfl

/-- Feller action converts semigroup evolution to time shift on test functions. -/
theorem expectation_action_eq_shift
    (S : FellerOccupationSystem X) (s t : NNReal)
    (f : BoundedContinuousFunction X ℝ) :
    (∫ x, S.action t f x ∂(S.marginal s : Measure X)) =
      ∫ x, f x ∂(S.marginal (s + t) : Measure X) := by
  letI : IsMarkovKernel (S.P t) := S.markov t
  rw [← S.marginal_add s t, integral_comp_measure]
  apply integral_congr_ae
  exact ae_of_all _ fun x => S.action_apply t f x

/-- Probability expectation is bounded by the sup norm. -/
theorem abs_integral_marginal_le
    (S : FellerOccupationSystem X) (t : NNReal)
    (f : BoundedContinuousFunction X ℝ) :
    |∫ x, f x ∂(S.marginal t : Measure X)| ≤ ‖f‖ := by
  have h := norm_integral_le_of_norm_le_const
    (μ := (S.marginal t : Measure X))
    (f := fun x => f x) (C := ‖f‖)
    (ae_of_all _ fun x => f.norm_coe_le_norm x)
  rw [probReal_univ, mul_one] at h
  simpa [Real.norm_eq_abs] using h

/-- Pure interval-integral Krylov--Bogoliubov shift bound. -/
theorem shift_average_bound
    (F : ℝ → ℝ) (T s M : ℝ)
    (hT : 0 < T) (hs : 0 ≤ s)
    (hF : ∀ t, |F t| ≤ M)
    (hint : ∀ a b, 0 ≤ a → 0 ≤ b → IntervalIntegrable F volume a b) :
    |((∫ t in 0..T, F (t + s)) - ∫ t in 0..T, F t) / T| ≤
      2 * s * M / T := by
  have htrans :
      (∫ t in 0..T, F (t + s)) = ∫ t in s..T + s, F t := by
    simpa using intervalIntegral.integral_comp_add_right F s (a := 0) (b := T)
  have hdecomp :
      (∫ t in s..T + s, F t) - ∫ t in 0..T, F t =
        (∫ t in T..T + s, F t) - ∫ t in 0..s, F t := by
    have h0s := hint 0 s (by positivity) hs
    have hsT := hint s T hs hT.le
    have hTTs := hint T (T + s) hT.le (add_nonneg hT.le hs)
    rw [← intervalIntegral.integral_add_adjacent_intervals h0s hsT,
        ← intervalIntegral.integral_add_adjacent_intervals hsT hTTs]
    ring
  have htail : |∫ t in T..T + s, F t| ≤ M * s := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := T) (b := T + s) (C := M) (f := F) (fun x hx => by
        simpa [Real.norm_eq_abs] using hF x)
    simpa [Real.norm_eq_abs, abs_of_nonneg hs] using h
  have hhead : |∫ t in 0..s, F t| ≤ M * s := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := s) (C := M) (f := F) (fun x hx => by
        simpa [Real.norm_eq_abs] using hF x)
    simpa [Real.norm_eq_abs, abs_of_nonneg hs] using h
  rw [htrans, hdecomp, abs_div]
  have hnum :
      |(∫ t in T..T + s, F t) - ∫ t in 0..s, F t| ≤ 2 * s * M := by
    calc
      |(∫ t in T..T + s, F t) - ∫ t in 0..s, F t|
          ≤ |∫ t in T..T + s, F t| + |∫ t in 0..s, F t| := abs_sub _ _
      _ ≤ M * s + M * s := add_le_add htail hhead
      _ = 2 * s * M := by ring
  rw [abs_of_pos hT]
  exact (div_le_div_iff_of_pos_right hT).2 hnum

/-- Source Krylov--Bogoliubov estimate: evolving an occupation average for a
fixed time s changes any bounded continuous expectation by at most
2 s ‖f‖ / T. -/
theorem occupation_shift_bound
    (S : FellerOccupationSystem X) (T s : NNReal) (hT : T ≠ 0)
    (f : BoundedContinuousFunction X ℝ) :
    |(∫ x, f x ∂(S.P s ∘ₘ (S.occupation T : Measure X))) -
      ∫ x, f x ∂(S.occupation T : Measure X)| ≤
      2 * (s : ℝ) * ‖f‖ / (T : ℝ) := by
  letI : IsMarkovKernel (S.P s) := S.markov s
  let F : ℝ → ℝ := fun t =>
    ∫ x, f x ∂(S.marginal (Real.toNNReal t) : Measure X)
  have hcomp :
      (∫ x, f x ∂(S.P s ∘ₘ (S.occupation T : Measure X))) =
        ∫ x, S.action s f x ∂(S.occupation T : Measure X) := by
    rw [integral_comp_measure]
    apply integral_congr_ae
    exact ae_of_all _ fun x => (S.action_apply s f x).symm
  have hshift :
      (∫ t in (0 : ℝ)..(T : ℝ),
          ∫ x, S.action s f x ∂(S.marginal (Real.toNNReal t) : Measure X)) =
        ∫ t in (0 : ℝ)..(T : ℝ), F (t + (s : ℝ)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht0 : 0 ≤ t := by
      rw [uIcc_of_le (show (0 : ℝ) ≤ (T : ℝ) by positivity)] at ht
      exact ht.1
    change (∫ x, S.action s f x ∂(S.marginal (Real.toNNReal t) : Measure X)) =
      F (t + (s : ℝ))
    rw [expectation_action_eq_shift]
    unfold F
    congr 2
    rw [Real.toNNReal_add ht0 (NNReal.coe_nonneg s), Real.toNNReal_coe]
  have hoccAction :
      (∫ x, S.action s f x ∂(S.occupation T : Measure X)) =
        (T : ℝ)⁻¹ *
          ∫ t in (0 : ℝ)..(T : ℝ),
            ∫ x, S.action s f x ∂(S.marginal (Real.toNNReal t) : Measure X) := by
    simpa [marginal] using S.occupation_integral T hT (S.action s f)
  have hoccF :
      (∫ x, f x ∂(S.occupation T : Measure X)) =
        (T : ℝ)⁻¹ *
          ∫ t in (0 : ℝ)..(T : ℝ),
            ∫ x, f x ∂(S.marginal (Real.toNNReal t) : Measure X) := by
    simpa [marginal] using S.occupation_integral T hT f
  have hdiff :
      (∫ x, f x ∂(S.P s ∘ₘ (S.occupation T : Measure X))) -
          ∫ x, f x ∂(S.occupation T : Measure X) =
        ((∫ t in (0 : ℝ)..(T : ℝ), F (t + (s : ℝ))) -
          ∫ t in (0 : ℝ)..(T : ℝ), F t) / (T : ℝ) := by
    rw [hcomp, hoccAction, hoccF, hshift]
    rw [div_eq_inv_mul]
    ring
  rw [hdiff]
  apply shift_average_bound F (T : ℝ) (s : ℝ) ‖f‖
  · exact_mod_cast (pos_iff_ne_zero.mpr hT)
  · exact NNReal.coe_nonneg s
  · intro t
    exact abs_integral_marginal_le S (Real.toNNReal t) f
  · intro a b ha hb
    exact S.time_intervalIntegrable f a b ha hb

/-- Occupation laws with time horizon at least one. -/
def occupationFamily (S : FellerOccupationSystem X) : Set (ProbabilityMeasure X) :=
  {ν | ∃ T : NNReal, 1 ≤ T ∧ ν = S.occupation T}

/-- Prokhorov extraction for every diverging time sequence. The extracted
subsequence of time horizons still diverges to infinity. -/
theorem occupation_tendsto_subseq_of_tight
    (S : FellerOccupationSystem X)
    (hTight : IsTightMeasureSet
      {((ν : ProbabilityMeasure X) : Measure X) | ν ∈ occupationFamily S})
    (Tseq : ℕ → NNReal) (hTseq : Tendsto Tseq atTop atTop) :
    ∃ (ν : ProbabilityMeasure X) (φ : ℕ → ℕ),
      StrictMono φ ∧
      Tendsto (fun n => S.occupation (Tseq (φ n))) atTop (𝓝 ν) ∧
      Tendsto (fun n => Tseq (φ n)) atTop atTop := by
  have hcompact : IsCompact (closure (occupationFamily S)) :=
    isCompact_closure_of_isTightMeasureSet hTight
  have hlarge : ∀ᶠ n in atTop, (1 : NNReal) ≤ Tseq n :=
    (tendsto_atTop.1 hTseq) 1
  have hmem : ∀ᶠ n in atTop, S.occupation (Tseq n) ∈ closure (occupationFamily S) := by
    filter_upwards [hlarge] with n hn
    exact subset_closure ⟨Tseq n, hn, rfl⟩
  obtain ⟨ν, -, φ, hφ, hconv⟩ :=
    hcompact.tendsto_subseq' hmem.frequently
  refine ⟨ν, φ, hφ, hconv, ?_⟩
  exact hTseq.comp hφ.tendsto_atTop

/-- Feller action is exactly integration after pushing a probability law
through the time-s kernel. -/
theorem integral_push_eq_action
    (S : FellerOccupationSystem X) (s : NNReal)
    (μ : ProbabilityMeasure X) (f : BoundedContinuousFunction X ℝ) :
    (∫ x, f x ∂(S.P s ∘ₘ (μ : Measure X))) =
      ∫ x, S.action s f x ∂(μ : Measure X) := by
  letI : IsMarkovKernel (S.P s) := S.markov s
  rw [integral_comp_measure]
  apply integral_congr_ae
  exact ae_of_all _ fun x => (S.action_apply s f x).symm

/-- Any weak limit of occupation averages along diverging horizons is
invariant under every fixed time of the Feller semigroup. -/
theorem invariant_of_occupation_tendsto
    (S : FellerOccupationSystem X)
    (Tseq : ℕ → NNReal) (hTseq : Tendsto Tseq atTop atTop)
    (ν : ProbabilityMeasure X)
    (hconv : Tendsto (fun n => S.occupation (Tseq n)) atTop (𝓝 ν)) :
    ∀ s : NNReal, S.P s ∘ₘ (ν : Measure X) = (ν : Measure X) := by
  intro s
  letI : IsMarkovKernel (S.P s) := S.markov s
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have hbase :
      Tendsto (fun n => ∫ x, f x ∂(S.occupation (Tseq n) : Measure X))
        atTop (𝓝 (∫ x, f x ∂(ν : Measure X))) :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv) f
  have haction :
      Tendsto (fun n => ∫ x, S.action s f x ∂(S.occupation (Tseq n) : Measure X))
        atTop (𝓝 (∫ x, S.action s f x ∂(ν : Measure X))) :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv) (S.action s f)
  have hpush :
      Tendsto
        (fun n => ∫ x, f x ∂(S.P s ∘ₘ (S.occupation (Tseq n) : Measure X)))
        atTop (𝓝 (∫ x, f x ∂(S.P s ∘ₘ (ν : Measure X)))) := by
    simpa only [integral_push_eq_action] using haction
  have hdiff :
      Tendsto
        (fun n =>
          (∫ x, f x ∂(S.P s ∘ₘ (S.occupation (Tseq n) : Measure X))) -
            ∫ x, f x ∂(S.occupation (Tseq n) : Measure X))
        atTop
        (𝓝 ((∫ x, f x ∂(S.P s ∘ₘ (ν : Measure X))) -
          ∫ x, f x ∂(ν : Measure X))) :=
    hpush.sub hbase
  have hcoe : Tendsto (fun n => (Tseq n : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.2 hTseq
  have hbound :
      Tendsto (fun n => 2 * (s : ℝ) * ‖f‖ / (Tseq n : ℝ)) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n => ((Tseq n : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hcoe
    simpa [div_eq_mul_inv] using hinv.const_mul (2 * (s : ℝ) * ‖f‖)
  have hlarge : ∀ᶠ n in atTop, (1 : NNReal) ≤ Tseq n :=
    (tendsto_atTop.1 hTseq) 1
  have hle : ∀ᶠ n in atTop,
      |(∫ x, f x ∂(S.P s ∘ₘ (S.occupation (Tseq n) : Measure X))) -
        ∫ x, f x ∂(S.occupation (Tseq n) : Measure X)| ≤
        2 * (s : ℝ) * ‖f‖ / (Tseq n : ℝ) := by
    filter_upwards [hlarge] with n hn
    exact S.occupation_shift_bound (Tseq n) s (ne_of_gt (zero_lt_one.trans_le hn)) f
  have hzero :
      Tendsto
        (fun n =>
          (∫ x, f x ∂(S.P s ∘ₘ (S.occupation (Tseq n) : Measure X))) -
            ∫ x, f x ∂(S.occupation (Tseq n) : Measure X))
        atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hbound
      (Eventually.of_forall fun n => abs_nonneg
        ((∫ x, f x ∂(S.P s ∘ₘ (S.occupation (Tseq n) : Measure X))) -
          ∫ x, f x ∂(S.occupation (Tseq n) : Measure X))) hle
  have hz :
      (∫ x, f x ∂(S.P s ∘ₘ (ν : Measure X))) -
          ∫ x, f x ∂(ν : Measure X) = 0 :=
    tendsto_nhds_unique hdiff hzero
  exact sub_eq_zero.mp hz

/-- If every source marginal is concentrated on a closed set, then every
positive-horizon literal occupation average is concentrated on the same set.
The conclusion is derived from the event face of the occupation average. -/
theorem occupation_closed_support
    (S : FellerOccupationSystem X) (K : Set X) (hK : IsClosed K)
    (hstay : ∀ t : NNReal, (S.marginal t : Measure X) K = 1)
    (T : NNReal) (hT : T ≠ 0) :
    (S.occupation T : Measure X) K = 1 := by
  have hrealMarginal : ∀ t : ℝ,
      (evolvedLaw S.P S.markov S.initial (Real.toNNReal t) : Measure X).real K = 1 := by
    intro t
    simpa [Measure.real, marginal] using
      congrArg ENNReal.toReal (hstay (Real.toNNReal t))
  have hrealOcc : (S.occupation T : Measure X).real K = 1 := by
    rw [S.occupation_event_real T hT K hK.measurableSet]
    simp_rw [hrealMarginal]
    simp [hT]
  have hEqUniv :
      (S.occupation T : Measure X) K =
        (S.occupation T : Measure X) Set.univ := by
    exact (measureReal_eq_measureReal_iff
      (μ := (S.occupation T : Measure X))
      (ν := (S.occupation T : Measure X))
      (s := K) (t := Set.univ)).mp (by simpa using hrealOcc)
  simpa using hEqUniv

/-- Closed support is preserved under a weak occupation limit. Only eventual
positive horizons are needed; they follow from the source assumption
`Tseq → ∞`. Portmanteau supplies the closed-set passage to the limit. -/
theorem closed_support_of_occupation_tendsto
    (S : FellerOccupationSystem X)
    (Tseq : ℕ → NNReal) (hTseq : Tendsto Tseq atTop atTop)
    (ν : ProbabilityMeasure X)
    (hconv : Tendsto (fun n => S.occupation (Tseq n)) atTop (𝓝 ν))
    (K : Set X) (hK : IsClosed K)
    (hstay : ∀ t : NNReal, (S.marginal t : Measure X) K = 1) :
    (ν : Measure X) K = 1 := by
  have hlarge : ∀ᶠ n in atTop, (1 : NNReal) ≤ Tseq n :=
    (tendsto_atTop.1 hTseq) 1
  have hocc : ∀ᶠ n in atTop,
      (S.occupation (Tseq n) : Measure X) K = 1 := by
    filter_upwards [hlarge] with n hn
    exact S.occupation_closed_support K hK hstay (Tseq n)
      (ne_of_gt (zero_lt_one.trans_le hn))
  have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hconv hK
  have hlimsup :
      atTop.limsup (fun n => (S.occupation (Tseq n) : Measure X) K) = 1 := by
    rw [limsup_congr hocc]
    exact limsup_const 1
  rw [hlimsup] at hport
  exact le_antisymm (prob_le_one (μ := (ν : Measure X))) hport

/-- **P-PER-02 — continuous-time Feller occupation persistence.**

For every diverging horizon sequence, tightness of the literal occupation
family yields a weakly convergent subsequence. Its limit is invariant under the
whole Feller semigroup, and every closed set carrying every evolved source law
also carries the limit. -/
theorem p_per_02
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
  · exact S.invariant_of_occupation_tendsto
      (fun n => Tseq (φ n)) htime ν hconv
  · intro K hK hstay
    exact S.closed_support_of_occupation_tendsto
      (fun n => Tseq (φ n)) htime ν hconv K hK hstay
  · intro U ν' hU hUconv
    refine ⟨S.invariant_of_occupation_tendsto U hU ν' hUconv, ?_⟩
    intro K hK hstay
    exact S.closed_support_of_occupation_tendsto U hU ν' hUconv K hK hstay

end FellerOccupationSystem
end UEOT.V3.PersistenceOccupation
