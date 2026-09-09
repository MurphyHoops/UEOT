import UEOT.V3.TotalVariation
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.Ring

/-!
# P-DYN-03 foundation — accumulated path-error algebra

The source path-error theorem has the sharp finite-horizon factor

  1 - ∏ t<T (1 - ε_t)

and the looser additive union bound.

This module machine-checks the deterministic algebraic part under the source
probability-error range 0 ≤ ε_t ≤ 1. The stochastic coupling/path-law bridge
is a separate theorem layer and is not claimed here.
-/

namespace UEOT.V3.PathError

open MeasureTheory
open UEOT.V3.TotalVariation
open scoped BigOperators symmDiff

theorem complErrorProduct_mem_unit
    (ε : ℕ → ℝ)
    (h0 : ∀ i, 0 ≤ ε i)
    (h1 : ∀ i, ε i ≤ 1)
    (n : ℕ) :
    0 ≤ (∏ i ∈ Finset.range n, (1 - ε i)) ∧
      (∏ i ∈ Finset.range n, (1 - ε i)) ≤ 1 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.prod_range_succ]
      have hb0 : 0 ≤ 1 - ε n := sub_nonneg.mpr (h1 n)
      have hb1 : 1 - ε n ≤ 1 := sub_le_self 1 (h0 n)
      constructor
      · exact mul_nonneg ih.1 hb0
      · calc
          (∏ i ∈ Finset.range n, (1 - ε i)) * (1 - ε n)
              ≤ 1 * (1 - ε n) :=
            mul_le_mul_of_nonneg_right ih.2 hb0
          _ ≤ 1 := by simpa using hb1

/-- The source's product-form error bound is always no larger than the
additive union bound. -/
theorem one_sub_prod_one_sub_le_sum
    (ε : ℕ → ℝ)
    (h0 : ∀ i, 0 ≤ ε i)
    (h1 : ∀ i, ε i ≤ 1) :
    ∀ n,
      1 - (∏ i ∈ Finset.range n, (1 - ε i))
        ≤ ∑ i ∈ Finset.range n, ε i := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hp :=
        complErrorProduct_mem_unit ε h0 h1 n
      have he0 : 0 ≤ ε n := h0 n
      have hp_mul : (∏ i ∈ Finset.range n, (1 - ε i)) * ε n ≤ ε n :=
        mul_le_of_le_one_left he0 hp.2
      rw [Finset.prod_range_succ, Finset.sum_range_succ]
      calc
        1 - (∏ i ∈ Finset.range n, (1 - ε i)) * (1 - ε n) =
            (1 - ∏ i ∈ Finset.range n, (1 - ε i)) +
              (∏ i ∈ Finset.range n, (1 - ε i)) * ε n := by
                ring
        _ ≤ (∑ i ∈ Finset.range n, ε i) +
              (∏ i ∈ Finset.range n, (1 - ε i)) * ε n :=
            add_le_add ih (le_refl _)
        _ ≤ (∑ i ∈ Finset.range n, ε i) + ε n :=
            add_le_add (le_refl _) hp_mul


/-- Abstract survival recursion behind the source coupling proof.  If `s n`
is the probability that the two coupled records are still identical after
`n` steps, and conditioned on survival the next step preserves equality with
probability at least `1 - ε n`, then survival dominates the product of all
one-step success factors. -/
theorem coupling_survival_product_lower_bound
    (ε s : ℕ → ℝ)
    (hε0 : ∀ n, 0 ≤ ε n)
    (hε1 : ∀ n, ε n ≤ 1)
    (hs0 : 1 ≤ s 0)
    (hstep : ∀ n, s n * (1 - ε n) ≤ s (n + 1)) :
    ∀ n, (∏ i ∈ Finset.range n, (1 - ε i)) ≤ s n := by
  intro n
  induction n with
  | zero =>
      simpa using hs0
  | succ n ih =>
      rw [Finset.prod_range_succ]
      have hnonneg : 0 ≤ 1 - ε n := sub_nonneg.mpr (hε1 n)
      exact
        (mul_le_mul_of_nonneg_right ih hnonneg).trans (hstep n)

/-- Converting a coupled path-agreement lower bound into a mismatch upper
bound is the deterministic last step before the total-variation coupling
inequality is invoked. -/
theorem mismatch_le_one_sub_product
    (ε s : ℕ → ℝ)
    (hε0 : ∀ n, 0 ≤ ε n)
    (hε1 : ∀ n, ε n ≤ 1)
    (hs0 : 1 ≤ s 0)
    (hstep : ∀ n, s n * (1 - ε n) ≤ s (n + 1))
    (n : ℕ) :
    1 - s n ≤ 1 - (∏ i ∈ Finset.range n, (1 - ε i)) := by
  exact sub_le_sub_left
    (coupling_survival_product_lower_bound ε s hε0 hε1 hs0 hstep n) 1


/-- Coupling inequality in the source TV convention.  For any probability
coupling whose marginals are `μ` and `ν`, the total-variation distance is
at most the probability that the two coupled coordinates disagree. -/
theorem tvDist_le_coupling_mismatch
    {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (γ : Measure (α × α)) [IsProbabilityMeasure γ]
    (hfst : γ.map (fun p : α × α => p.1) = μ)
    (hsnd : γ.map (fun p : α × α => p.2) = ν) :
    tvDist μ ν ≤ γ.real {p : α × α | p.1 ≠ p.2} := by
  change sSup (tvEventSet μ ν) ≤ γ.real {p : α × α | p.1 ≠ p.2}
  refine csSup_le (tvEventSet_nonempty μ ν) ?_
  intro r hr
  rcases hr with ⟨A, hA, rfl⟩
  have hμA :
      μ.real A = γ.real ((fun p : α × α => p.1) ⁻¹' A) := by
    rw [← hfst]
    simp [Measure.real, Measure.map_apply measurable_fst hA]
  have hνA :
      ν.real A = γ.real ((fun p : α × α => p.2) ⁻¹' A) := by
    rw [← hsnd]
    simp [Measure.real, Measure.map_apply measurable_snd hA]
  rw [hμA, hνA]
  have hfstMeas : MeasurableSet ((fun p : α × α => p.1) ⁻¹' A) :=
    hA.preimage measurable_fst
  have hsndMeas : MeasurableSet ((fun p : α × α => p.2) ⁻¹' A) :=
    hA.preimage measurable_snd
  have hsym :=
    abs_measureReal_sub_le_measureReal_symmDiff
      (μ := γ) hfstMeas.nullMeasurableSet hsndMeas.nullMeasurableSet
  refine hsym.trans (measureReal_mono ?_)
  intro p hp hEq
  rw [Set.mem_symmDiff] at hp
  rcases hp with hp | hp
  · apply hp.2
    change p.2 ∈ A
    rw [← hEq]
    exact hp.1
  · apply hp.2
    change p.1 ∈ A
    rw [hEq]
    exact hp.1


/-- The common point-mass shared by two PMFs on a finite alphabet. -/
noncomputable def pmfCommonMass
    {α : Type*} [Fintype α] (p q : PMF α) : ℝ :=
  ∑ x, min (p x).toReal (q x).toReal

/-- Finite-alphabet residual mass is bounded by the event-supremum total
variation distance.  This is the numerical half of the maximal-coupling
argument: after coupling the common mass diagonally, the remaining mass is no
larger than TV. -/
theorem one_sub_pmfCommonMass_le_tvDist
    {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α]
    (p q : PMF α) :
    1 - pmfCommonMass p q ≤ tvDist p.toMeasure q.toMeasure := by
  classical
  let A : Finset α :=
    Finset.univ.filter fun x => (q x).toReal ≤ (p x).toReal
  have hp_sum : (∑ x, (p x).toReal) = 1 := by
    have h := congrArg ENNReal.toReal (PMF.tsum_coe p)
    rw [tsum_fintype, ENNReal.toReal_sum
      (fun x _ => PMF.apply_ne_top p x)] at h
    simpa using h
  have hcommon_le : pmfCommonMass p q ≤ 1 := by
    rw [← hp_sum]
    unfold pmfCommonMass
    exact Finset.sum_le_sum fun x _ => min_le_left _ _
  have hres :
      1 - pmfCommonMass p q =
        ∑ x ∈ A, ((p x).toReal - (q x).toReal) := by
    rw [← hp_sum]
    unfold pmfCommonMass
    rw [← Finset.sum_sub_distrib]
    change
      (∑ x ∈ Finset.univ,
        ((p x).toReal - min (p x).toReal (q x).toReal)) =
      ∑ x ∈ Finset.univ.filter
        (fun x => (q x).toReal ≤ (p x).toReal),
        ((p x).toReal - (q x).toReal)
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hqp : (q x).toReal ≤ (p x).toReal
    · simp [hqp, min_eq_right hqp]
    · have hpq : (p x).toReal ≤ (q x).toReal := le_of_not_ge hqp
      simp [hqp, min_eq_left hpq]
  have hgap :
      p.toMeasure.real (A : Set α) - q.toMeasure.real (A : Set α) =
        ∑ x ∈ A, ((p x).toReal - (q x).toReal) := by
    simp only [Measure.real]
    rw [PMF.toMeasure_apply_finset p A, PMF.toMeasure_apply_finset q A]
    rw [ENNReal.toReal_sum (fun x _ => PMF.apply_ne_top p x)]
    rw [ENNReal.toReal_sum (fun x _ => PMF.apply_ne_top q x)]
    rw [Finset.sum_sub_distrib]
  have hresgap :
      1 - pmfCommonMass p q =
        p.toMeasure.real (A : Set α) - q.toMeasure.real (A : Set α) :=
    hres.trans hgap.symm
  have hgap_nonneg :
      0 ≤ p.toMeasure.real (A : Set α) - q.toMeasure.real (A : Set α) := by
    rw [← hresgap]
    exact sub_nonneg.mpr hcommon_le
  have hA : MeasurableSet ((A : Finset α) : Set α) :=
    Finset.measurableSet A
  calc
    1 - pmfCommonMass p q =
        |p.toMeasure.real (A : Set α) - q.toMeasure.real (A : Set α)| := by
          rw [abs_of_nonneg hgap_nonneg]
          exact hresgap
    _ ≤ tvDist p.toMeasure q.toMeasure :=
      tvEvent_le p.toMeasure q.toMeasure (A : Set α) hA



/-- On a finite measurable alphabet, the real mass of a finite event is the
finite sum of its point masses.  Arbitrary sets are converted to a finset only
inside proofs, so no decidable-membership assumption leaks into theorem types. -/
theorem pmfMeasureReal_eq_sum_finset
    {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α]
    (p : PMF α) (S : Finset α) :
    p.toMeasure.real (S : Set α) =
      ∑ x ∈ S, (p x).toReal := by
  simp only [Measure.real]
  rw [PMF.toMeasure_apply_finset p S]
  rw [ENNReal.toReal_sum (fun x _ => PMF.apply_ne_top p x)]

/-- The left real residual masses sum to `1 - commonMass`. -/
theorem sum_leftResidualReal
    {α : Type*} [Fintype α] (p q : PMF α) :
    (∑ x, ((p x).toReal - min (p x).toReal (q x).toReal)) =
      1 - pmfCommonMass p q := by
  have hp_sum : (∑ x, (p x).toReal) = 1 := by
    have h := congrArg ENNReal.toReal (PMF.tsum_coe p)
    rw [tsum_fintype, ENNReal.toReal_sum
      (fun x _ => PMF.apply_ne_top p x)] at h
    simpa using h
  unfold pmfCommonMass
  rw [Finset.sum_sub_distrib, hp_sum]

/-- The right real residual masses have the same total. -/
theorem sum_rightResidualReal
    {α : Type*} [Fintype α] (p q : PMF α) :
    (∑ x, ((q x).toReal - min (p x).toReal (q x).toReal)) =
      1 - pmfCommonMass p q := by
  have hq_sum : (∑ x, (q x).toReal) = 1 := by
    have h := congrArg ENNReal.toReal (PMF.tsum_coe q)
    rw [tsum_fintype, ENNReal.toReal_sum
      (fun x _ => PMF.apply_ne_top q x)] at h
    simpa using h
  unfold pmfCommonMass
  rw [Finset.sum_sub_distrib, hq_sum]

/-- Reverse finite-overlap inequality.  Together with
`one_sub_pmfCommonMass_le_tvDist`, this gives the exact finite-alphabet
identity `TV = 1 - overlap`. -/
theorem tvDist_le_one_sub_pmfCommonMass
    {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α]
    (p q : PMF α) :
    tvDist p.toMeasure q.toMeasure ≤ 1 - pmfCommonMass p q := by
  classical
  change sSup (tvEventSet p.toMeasure q.toMeasure) ≤
    1 - pmfCommonMass p q
  refine csSup_le (tvEventSet_nonempty p.toMeasure q.toMeasure) ?_
  intro r hr
  rcases hr with ⟨A, hA, rfl⟩
  let S : Finset α := Finset.univ.filter (fun x => x ∈ A)
  have hSA : ((S : Finset α) : Set α) = A := by
    ext x
    simp [S]
  have hgap :
      p.toMeasure.real A - q.toMeasure.real A =
        ∑ x ∈ S, ((p x).toReal - (q x).toReal) := by
    rw [← hSA, pmfMeasureReal_eq_sum_finset p S,
      pmfMeasureReal_eq_sum_finset q S]
    rw [← Finset.sum_sub_distrib]

  have hupper :
      p.toMeasure.real A - q.toMeasure.real A ≤
        1 - pmfCommonMass p q := by
    rw [hgap]
    calc
      (∑ x ∈ S, ((p x).toReal - (q x).toReal))
          ≤ ∑ x ∈ S,
              ((p x).toReal - min (p x).toReal (q x).toReal) := by
        apply Finset.sum_le_sum
        intro x hx
        linarith [min_le_right (p x).toReal (q x).toReal]
      _ ≤ ∑ x,
              ((p x).toReal - min (p x).toReal (q x).toReal) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro x hx hnot
          exact sub_nonneg.mpr (min_le_left _ _)
      _ = 1 - pmfCommonMass p q :=
        sum_leftResidualReal p q

  have hlower :
      -(1 - pmfCommonMass p q) ≤
        p.toMeasure.real A - q.toMeasure.real A := by
    have hrev :
        q.toMeasure.real A - p.toMeasure.real A ≤
          1 - pmfCommonMass p q := by
      rw [← hSA, pmfMeasureReal_eq_sum_finset q S,
        pmfMeasureReal_eq_sum_finset p S]
      rw [← Finset.sum_sub_distrib]
      calc
        (∑ x ∈ S, ((q x).toReal - (p x).toReal))
            ≤ ∑ x ∈ S,
              ((q x).toReal - min (p x).toReal (q x).toReal) := by
          apply Finset.sum_le_sum
          intro x hx
          linarith [min_le_left (p x).toReal (q x).toReal]
        _ ≤ ∑ x,
              ((q x).toReal - min (p x).toReal (q x).toReal) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.filter_subset _ _
          · intro x hx hnot
            exact sub_nonneg.mpr (min_le_right _ _)
        _ = 1 - pmfCommonMass p q :=
          sum_rightResidualReal p q
    linarith
  exact (abs_le.2 ⟨hlower, hupper⟩)

/-- Exact finite-alphabet overlap representation of the source TV metric. -/
theorem tvDist_eq_one_sub_pmfCommonMass
    {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α]
    (p q : PMF α) :
    tvDist p.toMeasure q.toMeasure = 1 - pmfCommonMass p q :=
  le_antisymm
    (tvDist_le_one_sub_pmfCommonMass p q)
    (one_sub_pmfCommonMass_le_tvDist p q)

/-! ## Finite maximal-coupling mass algebra -/

/-- A PMF point mass viewed in `NNReal`; PMF values are always finite. -/
noncomputable def pmfNNMass
    {α : Type*} (p : PMF α) (x : α) : NNReal :=
  (p x).toNNReal

@[simp] theorem coe_pmfNNMass
    {α : Type*} (p : PMF α) (x : α) :
    ENNReal.ofNNReal (pmfNNMass p x) = p x := by
  exact ENNReal.coe_toNNReal (PMF.apply_ne_top p x)

/-- The finite `NNReal` point masses of a PMF sum to one. -/
theorem sum_pmfNNMass
    {α : Type*} [Fintype α] (p : PMF α) :
    ∑ x : α, pmfNNMass p x = 1 := by
  apply NNReal.eq
  simp only [NNReal.coe_sum, pmfNNMass, NNReal.coe_one]
  have h := congrArg ENNReal.toReal (PMF.tsum_coe p)
  rw [tsum_fintype, ENNReal.toReal_sum
    (fun x _ => PMF.apply_ne_top p x)] at h
  simpa [ENNReal.toReal] using h

/-- Pointwise mass that can be coupled diagonally. -/
noncomputable def pmfCommonNN
    {α : Type*} (p q : PMF α) (x : α) : NNReal :=
  min (pmfNNMass p x) (pmfNNMass q x)

/-- Residual probability mass left after removing the common diagonal mass. -/
noncomputable def pmfResidualNN
    {α : Type*} [Fintype α] (p q : PMF α) : NNReal :=
  1 - ∑ x : α, pmfCommonNN p q x

theorem sum_pmfCommonNN_le_one
    {α : Type*} [Fintype α] (p q : PMF α) :
    (∑ x : α, pmfCommonNN p q x) ≤ 1 := by
  rw [← sum_pmfNNMass p]
  exact Finset.sum_le_sum fun x _ => min_le_left _ _

/-- Left residual masses sum to the common residual probability. -/
theorem sum_leftResidualNN
    {α : Type*} [Fintype α] (p q : PMF α) :
    (∑ x : α, (pmfNNMass p x - pmfCommonNN p q x)) =
      pmfResidualNN p q := by
  unfold pmfResidualNN
  rw [Finset.sum_tsub_distrib]
  · rw [sum_pmfNNMass]
  · intro x hx
    exact min_le_left _ _

/-- Right residual masses have the same total mass. -/
theorem sum_rightResidualNN
    {α : Type*} [Fintype α] (p q : PMF α) :
    (∑ x : α, (pmfNNMass q x - pmfCommonNN p q x)) =
      pmfResidualNN p q := by
  unfold pmfResidualNN
  rw [Finset.sum_tsub_distrib]
  · rw [sum_pmfNNMass]
  · intro x hx
    exact min_le_right _ _

/-- At each alphabet symbol at least one residual side is zero.  Therefore the
product residual coupling carries no diagonal mass. -/
theorem leftResidual_mul_rightResidual_eq_zero
    {α : Type*} (p q : PMF α) (x : α) :
    (pmfNNMass p x - pmfCommonNN p q x) *
        (pmfNNMass q x - pmfCommonNN p q x) = 0 := by
  unfold pmfCommonNN
  rcases le_total (pmfNNMass p x) (pmfNNMass q x) with hpq | hqp
  · rw [min_eq_left hpq, tsub_self, zero_mul]
  · rw [min_eq_right hqp, tsub_self, mul_zero]


/-! ## Finite causal-PMF extension and overlap recursion -/

/-- Extend a finite history law by a history-dependent next-record PMF. -/
noncomputable def pmfExtend
    {H : Type*} {Z : Type*}
    (p : PMF H) (K : H → PMF Z) : PMF (H × Z) :=
  p.bind fun h => (K h).map (fun z => (h, z))

@[simp] theorem pmfExtend_apply
    {H : Type*} {Z : Type*}
    [Fintype H] [Fintype Z]
    (p : PMF H) (K : H → PMF Z) (h : H) (z : Z) :
    pmfExtend p K (h, z) = p h * K h z := by
  classical
  unfold pmfExtend
  rw [PMF.bind_apply, tsum_fintype]
  rw [Finset.sum_eq_single h]
  · simp [PMF.map_apply, tsum_fintype]
  · intro a ha hne
    have hha : h ≠ a := Ne.symm hne
    simp [PMF.map_apply, tsum_fintype, hha]
  · simp

/-- Elementary multiplicative overlap inequality used in the path induction. -/
theorem min_mul_min_le_min_mul
    {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    min a b * min c d ≤ min (a * c) (b * d) := by
  apply le_min
  · exact mul_le_mul (min_le_left _ _) (min_le_left _ _) (le_min hc hd) ha
  · exact mul_le_mul (min_le_right _ _) (min_le_right _ _) (le_min hc hd) hb

/-- One-step overlap survival: if every same-history next-record pair has
overlap at least `s`, then extending the two history laws preserves at least
the current overlap times `s`. -/
theorem pmfCommonMass_extend_lower_bound
    {H : Type*} {Z : Type*}
    [Fintype H] [Fintype Z]
    (p q : PMF H) (K L : H → PMF Z)
    (s : ℝ)
    (hs : ∀ h, s ≤ pmfCommonMass (K h) (L h))
    (hs0 : 0 ≤ s) :
    pmfCommonMass p q * s ≤
      pmfCommonMass (pmfExtend p K) (pmfExtend q L) := by
  classical
  unfold pmfCommonMass
  rw [← Finset.univ_product_univ, Finset.sum_product]
  calc
    (∑ h, min (p h).toReal (q h).toReal) * s
        = ∑ h, (min (p h).toReal (q h).toReal) * s := by
            rw [Finset.sum_mul]
    _ ≤ ∑ h,
        (min (p h).toReal (q h).toReal) *
          (∑ z, min (K h z).toReal (L h z).toReal) := by
      apply Finset.sum_le_sum
      intro h hh
      exact mul_le_mul_of_nonneg_left (hs h)
        (le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    _ = ∑ h, ∑ z,
        (min (p h).toReal (q h).toReal) *
          min (K h z).toReal (L h z).toReal := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [Finset.mul_sum]
    _ ≤ ∑ h, ∑ z,
        min ((p h).toReal * (K h z).toReal)
          ((q h).toReal * (L h z).toReal) := by
      apply Finset.sum_le_sum
      intro h hh
      apply Finset.sum_le_sum
      intro z hz
      exact min_mul_min_le_min_mul
        ENNReal.toReal_nonneg ENNReal.toReal_nonneg
        ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    _ = ∑ h, ∑ z,
        min (pmfExtend p K (h, z)).toReal
          (pmfExtend q L (h, z)).toReal := by
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro z hz
      rw [pmfExtend_apply, pmfExtend_apply,
        ENNReal.toReal_mul, ENNReal.toReal_mul]

/-- A finite next-record TV bound supplies the overlap factor required by the
previous theorem. -/
theorem pmfCommonMass_ge_one_sub_tvBound
    {Z : Type*} [Fintype Z] [MeasurableSpace Z]
    [MeasurableSingletonClass Z]
    (p q : PMF Z) {ε : ℝ}
    (hTV : tvDist p.toMeasure q.toMeasure ≤ ε) :
    1 - ε ≤ pmfCommonMass p q := by
  have hres := one_sub_pmfCommonMass_le_tvDist p q
  linarith

/-- Sharp one-step causal extension bound in overlap form. -/
theorem pmfCommonMass_extend_of_tv
    {H : Type*} {Z : Type*}
    [Fintype H] [Fintype Z]
    [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (p q : PMF H) (K L : H → PMF Z)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hTV : ∀ h, tvDist (K h).toMeasure (L h).toMeasure ≤ ε) :
    pmfCommonMass p q * (1 - ε) ≤
      pmfCommonMass (pmfExtend p K) (pmfExtend q L) := by
  apply pmfCommonMass_extend_lower_bound p q K L (1 - ε)
  · intro h
    exact pmfCommonMass_ge_one_sub_tvBound (K h) (L h) (hTV h)
  · exact sub_nonneg.mpr hε1


/-! ## Finite-horizon causal path recursion -/

universe uHist

/-- Recursive finite record type: the initial record is in `H₀`, and each
step appends one symbol from `Z`.  Both alphabets are placed in one Lean
universe; this is universe bookkeeping only, not a mathematical restriction. -/
def CausalHistory (H₀ Z : Type uHist) : ℕ → Type uHist
  | 0 => H₀
  | n + 1 => CausalHistory H₀ Z n × Z

instance causalHistoryFintype
    {H₀ Z : Type uHist} [Fintype H₀] [Fintype Z] (n : ℕ) :
    Fintype (CausalHistory H₀ Z n) := by
  induction n with
  | zero =>
      change Fintype H₀
      infer_instance
  | succ n ih =>
      change Fintype (CausalHistory H₀ Z n × Z)
      letI := ih
      infer_instance

instance causalHistoryMeasurableSpace
    {H₀ Z : Type uHist} [MeasurableSpace H₀] [MeasurableSpace Z] (n : ℕ) :
    MeasurableSpace (CausalHistory H₀ Z n) := by
  induction n with
  | zero =>
      change MeasurableSpace H₀
      infer_instance
  | succ n ih =>
      change MeasurableSpace (CausalHistory H₀ Z n × Z)
      letI := ih
      infer_instance

instance causalHistoryMeasurableSingleton
    {H₀ Z : Type uHist}
    [MeasurableSpace H₀] [MeasurableSingletonClass H₀]
    [MeasurableSpace Z] [MeasurableSingletonClass Z] (n : ℕ) :
    MeasurableSingletonClass (CausalHistory H₀ Z n) := by
  induction n with
  | zero =>
      change MeasurableSingletonClass H₀
      infer_instance
  | succ n ih =>
      change MeasurableSingletonClass (CausalHistory H₀ Z n × Z)
      letI := ih
      infer_instance

/-- Path law generated by a history-dependent family of next-record PMFs. -/
noncomputable def causalLaw
    {H₀ Z : Type uHist}
    (p₀ : PMF H₀)
    (K : ∀ n, CausalHistory H₀ Z n → PMF Z) :
    ∀ n, PMF (CausalHistory H₀ Z n)
  | 0 => p₀
  | n + 1 => pmfExtend (causalLaw p₀ K n) (K n)

theorem pmfCommonMass_self
    {α : Type*} [Fintype α] (p : PMF α) :
    pmfCommonMass p p = 1 := by
  unfold pmfCommonMass
  simp only [min_self]
  have h := congrArg ENNReal.toReal (PMF.tsum_coe p)
  rw [tsum_fintype, ENNReal.toReal_sum
    (fun x _ => PMF.apply_ne_top p x)] at h
  simpa using h

/-- The overlap of two finite causal path laws with the same initial law
dominates the product of their one-step overlap guarantees. -/
theorem causalLaw_commonMass_lower_bound
    {H₀ Z : Type uHist}
    [Fintype H₀] [Fintype Z]
    [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (p₀ : PMF H₀)
    (K L : ∀ n, CausalHistory H₀ Z n → PMF Z)
    (ε : ℕ → ℝ)
    (hε0 : ∀ n, 0 ≤ ε n)
    (hε1 : ∀ n, ε n ≤ 1)
    (hTV : ∀ n h,
      tvDist (K n h).toMeasure (L n h).toMeasure ≤ ε n) :
    ∀ n,
      (∏ i ∈ Finset.range n, (1 - ε i)) ≤
        pmfCommonMass (causalLaw p₀ K n) (causalLaw p₀ L n) := by
  intro n
  induction n with
  | zero =>
      change (1 : ℝ) ≤ pmfCommonMass p₀ p₀
      rw [pmfCommonMass_self]
  | succ n ih =>
      rw [Finset.prod_range_succ]
      have hfac0 : 0 ≤ 1 - ε n := sub_nonneg.mpr (hε1 n)
      calc
        (∏ i ∈ Finset.range n, (1 - ε i)) * (1 - ε n)
            ≤ pmfCommonMass (causalLaw p₀ K n) (causalLaw p₀ L n) *
                (1 - ε n) :=
          mul_le_mul_of_nonneg_right ih hfac0
        _ ≤ pmfCommonMass
              (causalLaw p₀ K (n + 1))
              (causalLaw p₀ L (n + 1)) := by
          change
            pmfCommonMass (causalLaw p₀ K n) (causalLaw p₀ L n) *
                (1 - ε n) ≤
              pmfCommonMass
                (pmfExtend (causalLaw p₀ K n) (K n))
                (pmfExtend (causalLaw p₀ L n) (L n))
          exact
            pmfCommonMass_extend_of_tv
              (causalLaw p₀ K n) (causalLaw p₀ L n)
              (K n) (L n)
              (hε0 n) (hε1 n) (hTV n)

/-- Finite-horizon source bound: same initial law and uniformly controlled
next-record TV errors imply the sharp product path-TV estimate.  A common
causal policy can be composed into the next-record kernels `K` and `L`;
the theorem then applies verbatim to the resulting controlled record laws. -/
theorem causalLaw_tv_bound
    {H₀ Z : Type uHist}
    [Fintype H₀] [Fintype Z]
    [MeasurableSpace H₀] [MeasurableSingletonClass H₀]
    [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (p₀ : PMF H₀)
    (K L : ∀ n, CausalHistory H₀ Z n → PMF Z)
    (ε : ℕ → ℝ)
    (hε0 : ∀ n, 0 ≤ ε n)
    (hε1 : ∀ n, ε n ≤ 1)
    (hTV : ∀ n h,
      tvDist (K n h).toMeasure (L n h).toMeasure ≤ ε n) :
    ∀ T,
      tvDist
          (causalLaw p₀ K T).toMeasure
          (causalLaw p₀ L T).toMeasure
        ≤ 1 - (∏ i ∈ Finset.range T, (1 - ε i)) := by
  intro T
  rw [tvDist_eq_one_sub_pmfCommonMass]
  exact sub_le_sub_left
    (causalLaw_commonMass_lower_bound p₀ K L ε hε0 hε1 hTV T) 1

/-- Full product-plus-union-bound form written in P-DYN-03. -/
theorem p_dyn_03_finite_path_error
    {H₀ Z : Type uHist}
    [Fintype H₀] [Fintype Z]
    [MeasurableSpace H₀] [MeasurableSingletonClass H₀]
    [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (p₀ : PMF H₀)
    (K L : ∀ n, CausalHistory H₀ Z n → PMF Z)
    (ε : ℕ → ℝ)
    (hε0 : ∀ n, 0 ≤ ε n)
    (hε1 : ∀ n, ε n ≤ 1)
    (hTV : ∀ n h,
      tvDist (K n h).toMeasure (L n h).toMeasure ≤ ε n) :
    ∀ T,
      tvDist
          (causalLaw p₀ K T).toMeasure
          (causalLaw p₀ L T).toMeasure
        ≤ 1 - (∏ i ∈ Finset.range T, (1 - ε i)) ∧
      1 - (∏ i ∈ Finset.range T, (1 - ε i))
        ≤ ∑ i ∈ Finset.range T, ε i := by
  intro T
  exact ⟨causalLaw_tv_bound p₀ K L ε hε0 hε1 hTV T,
    one_sub_prod_one_sub_le_sum ε hε0 hε1 T⟩

end UEOT.V3.PathError
