import UEOT.V3.TVSpan
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Data.ENNReal.Inv
import Mathlib.Algebra.Module.Rat
import Mathlib.Topology.DenseEmbedding
import Mathlib.Tactic

/-!
# P-QSD-01 — TV stabilization implies quasi-stationarity

This module formalizes the frozen §10.1 reverse QSD statement at its source strength.
It keeps a genuine continuous-time killed/subprobability kernel semigroup and one
initial probability law.  The conditional marginals are defined literally by
normalizing `μ P_t`, rather than supplied as an unrelated family.

The source-facing theorem `p_qsd_01` assumes total-variation convergence of those
conditional marginals to `q`, positivity of `q P_s 1` for every finite `s > 0`,
and right continuity of the survival function at zero.  Since the time domain is
`NNReal`, `ContinuousAt ... 0` is precisely one-sided/right continuity.  The
survival mass is proved to lie in `[0,1]`, so representing it by `ENNReal.toReal`
does not strengthen that regularity assumption.

The proof derives, rather than assumes, the conditional time-shift identity, the
QSD eigenmeasure law, multiplicativity of survival, and finally
`q P_s = exp (-rate * s) q` with `rate ≥ 0`.
-/

namespace UEOT.V3.QSDTVLimit

open MeasureTheory ProbabilityTheory Filter Set
open scoped ProbabilityTheory ENNReal Topology NNRat

universe uX uY
variable {X : Type uX} {Y : Type uY}
variable [MeasurableSpace X] [MeasurableSpace Y]

noncomputable def normalizePositive
    (μ : Measure X) [IsFiniteMeasure μ]
    (hpos : 0 < μ Set.univ) : ProbabilityMeasure X := by
  let ν : Measure X := (μ Set.univ)⁻¹ • μ
  have htop : μ Set.univ ≠ ∞ := (measure_lt_top μ Set.univ).ne
  have hzero : μ Set.univ ≠ 0 := ne_of_gt hpos
  have hprob : IsProbabilityMeasure ν := by
    refine ⟨?_⟩
    simp only [ν, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hzero htop
  exact ⟨ν, hprob⟩

structure KilledSemigroup (X : Type uX) [MeasurableSpace X] where
  P : NNReal → Kernel X X
  subprob : ∀ t x, P t x Set.univ ≤ 1
  zero : P 0 = Kernel.id
  semigroup : ∀ s t, P (s + t) = P t ∘ₖ P s
  initial : ProbabilityMeasure X
  initialSurvivalPos :
    ∀ t, 0 < (P t ∘ₘ (initial : Measure X)) Set.univ

namespace KilledSemigroup

theorem isFiniteKernel (S : KilledSemigroup X) (t : NNReal) :
    IsFiniteKernel (S.P t) := by
  refine ⟨1, by simp, ?_⟩
  exact S.subprob t

noncomputable def evolved (S : KilledSemigroup X) (t : NNReal) : Measure X :=
  S.P t ∘ₘ (S.initial : Measure X)

noncomputable def survival (S : KilledSemigroup X) (t : NNReal) : ENNReal :=
  (S.evolved t) Set.univ

theorem survival_pos (S : KilledSemigroup X) (t : NNReal) :
    0 < S.survival t := S.initialSurvivalPos t

noncomputable def conditioned (S : KilledSemigroup X) (t : NNReal) :
    ProbabilityMeasure X := by
  letI : IsFiniteKernel (S.P t) := S.isFiniteKernel t
  letI : IsFiniteMeasure (S.evolved t) := by
    unfold evolved
    infer_instance
  exact normalizePositive (S.evolved t) (S.survival_pos t)

theorem conditioned_toMeasure (S : KilledSemigroup X) (t : NNReal) :
    (S.conditioned t : Measure X) =
      (S.survival t)⁻¹ • S.evolved t := by
  letI : IsFiniteKernel (S.P t) := S.isFiniteKernel t
  letI : IsFiniteMeasure (S.evolved t) := by
    unfold evolved
    infer_instance
  unfold conditioned normalizePositive
  rfl

theorem evolved_eq_survival_smul_conditioned
    (S : KilledSemigroup X) (t : NNReal) :
    S.evolved t = S.survival t • (S.conditioned t : Measure X) := by
  rw [conditioned_toMeasure]
  rw [smul_smul]
  have h0 : S.survival t ≠ 0 := (S.survival_pos t).ne'
  have htop : S.survival t ≠ ∞ := by
    unfold survival evolved
    letI : IsFiniteKernel (S.P t) := S.isFiniteKernel t
    exact (measure_lt_top (S.P t ∘ₘ (S.initial : Measure X)) Set.univ).ne
  rw [ENNReal.mul_inv_cancel h0 htop, one_smul]

theorem evolved_add (S : KilledSemigroup X) (s t : NNReal) :
    S.P t ∘ₘ S.evolved s = S.evolved (s + t) := by
  unfold evolved
  letI : IsFiniteKernel (S.P s) := S.isFiniteKernel s
  letI : IsFiniteKernel (S.P t) := S.isFiniteKernel t
  rw [Measure.comp_assoc, ← S.semigroup]

theorem scaled_shift
    (S : KilledSemigroup X) (s t : NNReal) :
    S.survival s • (S.P t ∘ₘ (S.conditioned s : Measure X)) =
      S.survival (s + t) • (S.conditioned (s + t) : Measure X) := by
  rw [← Measure.comp_smul, ← S.evolved_eq_survival_smul_conditioned s]
  rw [S.evolved_add s t, S.evolved_eq_survival_smul_conditioned]

end KilledSemigroup


namespace KilledSemigroup

theorem conditioned_shift_eq_mass_smul
    (S : KilledSemigroup X) (t s : NNReal) :
    S.P s ∘ₘ (S.conditioned t : Measure X) =
      (S.P s ∘ₘ (S.conditioned t : Measure X)) Set.univ •
        (S.conditioned (t + s) : Measure X) := by
  let lhs : Measure X := S.P s ∘ₘ (S.conditioned t : Measure X)
  have hscaled :
      S.survival t • lhs =
        S.survival (t + s) • (S.conditioned (t + s) : Measure X) := by
    simpa [lhs] using S.scaled_shift t s
  have hmass :
      S.survival t * lhs Set.univ = S.survival (t + s) := by
    have h := congrArg (fun μ : Measure X => μ Set.univ) hscaled
    simpa [Measure.smul_apply, smul_eq_mul] using h
  have h0 : S.survival t ≠ 0 := (S.survival_pos t).ne'
  have htop : S.survival t ≠ ∞ := by
    unfold survival evolved
    letI : IsFiniteKernel (S.P t) := S.isFiniteKernel t
    exact (measure_lt_top (S.P t ∘ₘ (S.initial : Measure X)) Set.univ).ne
  have hcoef :
      (S.survival t)⁻¹ * S.survival (t + s) = lhs Set.univ := by
    rw [← hmass, ← mul_assoc, ENNReal.inv_mul_cancel h0 htop, one_mul]
  calc
    lhs = (S.survival t)⁻¹ • (S.survival t • lhs) := by
      rw [smul_smul, ENNReal.inv_mul_cancel h0 htop, one_smul]
    _ = (S.survival t)⁻¹ •
          (S.survival (t + s) • (S.conditioned (t + s) : Measure X)) := by
      rw [hscaled]
    _ = ((S.survival t)⁻¹ * S.survival (t + s)) •
          (S.conditioned (t + s) : Measure X) := by
      rw [smul_smul]
    _ = lhs Set.univ • (S.conditioned (t + s) : Measure X) := by
      rw [hcoef]

end KilledSemigroup

theorem comp_measureReal_eq_integral_finite
    (μ : Measure X) [IsProbabilityMeasure μ]
    (κ : Kernel X Y) [IsFiniteKernel κ]
    (B : Set Y) (hB : MeasurableSet B) :
    (κ ∘ₘ μ).real B = ∫ x, (κ x).real B ∂μ := by
  rw [measureReal_def, Measure.bind_apply hB κ.aemeasurable]
  simp_rw [measureReal_def]
  symm
  exact integral_toReal
    (κ.measurable_coe hB).aemeasurable
    (ae_of_all μ fun x => measure_lt_top (κ x) B)

theorem comp_event_tv_bound_subprob
    (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (κ : Kernel X Y) [IsFiniteKernel κ]
    (hsub : ∀ x, κ x Set.univ ≤ 1)
    (B : Set Y) (hB : MeasurableSet B) :
    |(κ ∘ₘ μ).real B - (κ ∘ₘ ν).real B| ≤
      UEOT.V3.TotalVariation.tvDist μ ν := by
  let g : X → ℝ := fun x => (κ x).real B
  have hg : Measurable g := (κ.measurable_coe hB).ennreal_toReal
  have h0 : ∀ x, (0 : ℝ) ≤ g x := fun _ => measureReal_nonneg
  have h1 : ∀ x, g x ≤ (1 : ℝ) := by
    intro x
    have hBuniv : (κ x).real B ≤ (κ x).real Set.univ :=
      measureReal_mono (Set.subset_univ B)
    have huniv : (κ x).real Set.univ ≤ (1 : ℝ) := by
      rw [measureReal_def]
      have h := ENNReal.toReal_mono (by simp) (hsub x)
      simpa using h
    exact hBuniv.trans huniv
  have hspan :=
    UEOT.V3.TVSpan.abs_integral_sub_le_span_tvDist
      μ ν g hg 0 1 (by norm_num) h0 h1
  rw [comp_measureReal_eq_integral_finite μ κ B hB,
      comp_measureReal_eq_integral_finite ν κ B hB]
  simpa using hspan

theorem tendsto_measureReal_of_tv
    {ι : Type*} {l : Filter ι}
    (μ : ι → ProbabilityMeasure X) (ν : ProbabilityMeasure X)
    (hTV : Tendsto
      (fun i => UEOT.V3.TotalVariation.tvDist
        (μ i : Measure X) (ν : Measure X)) l (𝓝 0))
    (A : Set X) (hA : MeasurableSet A) :
    Tendsto (fun i => (μ i : Measure X).real A) l
      (𝓝 ((ν : Measure X).real A)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have habs : Tendsto
      (fun i => |(μ i : Measure X).real A - (ν : Measure X).real A|)
      l (𝓝 0) := by
    apply squeeze_zero
    · intro i
      exact abs_nonneg _
    · intro i
      exact UEOT.V3.TotalVariation.tvEvent_le
        (μ i : Measure X) (ν : Measure X) A hA
    · exact hTV
  simpa [Real.dist_eq] using habs

theorem tendsto_comp_measureReal_of_tv
    {ι : Type*} {l : Filter ι}
    (μ : ι → ProbabilityMeasure X) (ν : ProbabilityMeasure X)
    (hTV : Tendsto
      (fun i => UEOT.V3.TotalVariation.tvDist
        (μ i : Measure X) (ν : Measure X)) l (𝓝 0))
    (κ : Kernel X Y) [IsFiniteKernel κ]
    (hsub : ∀ x, κ x Set.univ ≤ 1)
    (B : Set Y) (hB : MeasurableSet B) :
    Tendsto (fun i => (κ ∘ₘ (μ i : Measure X)).real B) l
      (𝓝 ((κ ∘ₘ (ν : Measure X)).real B)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero
  · intro i
    exact dist_nonneg
  · intro i
    simpa [Real.dist_eq] using
      comp_event_tv_bound_subprob
        (μ i : Measure X) (ν : Measure X) κ hsub B hB
  · exact hTV

theorem eigenmeasure_of_tv_limit
    (S : KilledSemigroup X)
    (q : ProbabilityMeasure X)
    (hTV : Tendsto
      (fun t : NNReal => UEOT.V3.TotalVariation.tvDist
        (S.conditioned t : Measure X) (q : Measure X))
      atTop (𝓝 0)) :
    ∀ s : NNReal,
      S.P s ∘ₘ (q : Measure X) =
        (S.P s ∘ₘ (q : Measure X)) Set.univ • (q : Measure X) := by
  intro s
  letI : IsFiniteKernel (S.P s) := S.isFiniteKernel s
  let lhsQ : Measure X := S.P s ∘ₘ (q : Measure X)
  have hshift : Tendsto (fun t : NNReal => t + s) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with t ht
    exact ht.trans (le_add_of_nonneg_right zero_le)
  have hTVshift : Tendsto
      (fun t : NNReal => UEOT.V3.TotalVariation.tvDist
        (S.conditioned (t + s) : Measure X) (q : Measure X))
      atTop (𝓝 0) := hTV.comp hshift
  rw [Measure.ext_iff]
  intro A hA
  have hleft : Tendsto
      (fun t : NNReal => (S.P s ∘ₘ (S.conditioned t : Measure X)).real A)
      atTop (𝓝 (lhsQ.real A)) := by
    exact tendsto_comp_measureReal_of_tv
      S.conditioned q hTV (S.P s) (S.subprob s) A hA
  have hmass : Tendsto
      (fun t : NNReal => (S.P s ∘ₘ (S.conditioned t : Measure X)).real Set.univ)
      atTop (𝓝 (lhsQ.real Set.univ)) := by
    exact tendsto_comp_measureReal_of_tv
      S.conditioned q hTV (S.P s) (S.subprob s) Set.univ MeasurableSet.univ
  have hcondShift : Tendsto
      (fun t : NNReal => (S.conditioned (t + s) : Measure X).real A)
      atTop (𝓝 ((q : Measure X).real A)) := by
    exact tendsto_measureReal_of_tv
      (fun t : NNReal => S.conditioned (t + s)) q hTVshift A hA
  have hright : Tendsto
      (fun t : NNReal =>
        (S.P s ∘ₘ (S.conditioned t : Measure X)).real Set.univ *
          (S.conditioned (t + s) : Measure X).real A)
      atTop (𝓝 (lhsQ.real Set.univ * (q : Measure X).real A)) :=
    hmass.mul hcondShift
  have hleft' : Tendsto
      (fun t : NNReal =>
        (S.P s ∘ₘ (S.conditioned t : Measure X)).real Set.univ *
          (S.conditioned (t + s) : Measure X).real A)
      atTop (𝓝 (lhsQ.real A)) := by
    convert hleft using 1
    funext t
    have h := congrArg (fun μ : Measure X => μ.real A)
      (S.conditioned_shift_eq_mass_smul t s)
    simpa [measureReal_def] using h.symm
  have hreal : lhsQ.real A = lhsQ.real Set.univ * (q : Measure X).real A :=
    tendsto_nhds_unique hleft' hright
  have hLtop : lhsQ A ≠ ∞ := by
    unfold lhsQ
    exact measure_ne_top _ _
  have hmassTop : lhsQ Set.univ ≠ ∞ := by
    unfold lhsQ
    exact measure_ne_top _ _
  have hqTop : (q : Measure X) A ≠ ∞ := measure_ne_top _ _
  have hRtop : (lhsQ Set.univ • (q : Measure X)) A ≠ ∞ := by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top hmassTop hqTop
  apply (ENNReal.toReal_eq_toReal_iff' hLtop hRtop).mp
  simpa [measureReal_def] using hreal

noncomputable def qSurvival
    (S : KilledSemigroup X) (q : ProbabilityMeasure X) (t : NNReal) : ENNReal :=
  (S.P t ∘ₘ (q : Measure X)) Set.univ

theorem qSurvival_le_one
    (S : KilledSemigroup X) (q : ProbabilityMeasure X) (t : NNReal) :
    qSurvival S q t ≤ 1 := by
  unfold qSurvival
  rw [Measure.bind_apply MeasurableSet.univ (S.P t).aemeasurable]
  calc
    ∫⁻ x, S.P t x Set.univ ∂(q : Measure X)
        ≤ ∫⁻ _x, (1 : ENNReal) ∂(q : Measure X) :=
      lintegral_mono fun x => S.subprob t x
    _ = 1 := by simp

theorem qSurvival_zero
    (S : KilledSemigroup X) (q : ProbabilityMeasure X) :
    qSurvival S q 0 = 1 := by
  unfold qSurvival
  rw [S.zero]
  simp

theorem qSurvival_add
    (S : KilledSemigroup X) (q : ProbabilityMeasure X)
    (heig : ∀ s : NNReal,
      S.P s ∘ₘ (q : Measure X) =
        (S.P s ∘ₘ (q : Measure X)) Set.univ • (q : Measure X))
    (s t : NNReal) :
    qSurvival S q (s + t) = qSurvival S q s * qSurvival S q t := by
  unfold qSurvival
  letI : IsFiniteKernel (S.P s) := S.isFiniteKernel s
  letI : IsFiniteKernel (S.P t) := S.isFiniteKernel t
  rw [S.semigroup, ← Measure.comp_assoc]
  rw [heig s, Measure.comp_smul]
  simp [Measure.smul_apply, smul_eq_mul]

theorem nnrat_dense_nnreal :
    DenseRange (fun q : NNRat => (q : NNReal)) := by
  change Dense (Set.range fun q : NNRat => (q : NNReal))
  apply dense_of_exists_between
  intro a b hab
  rcases (NNReal.lt_iff_exists_rat_btwn a b).1 hab with ⟨q, hq, haq, hqb⟩
  let r : NNRat := q.toNNRat
  have hr_eq : (r : NNReal) = Real.toNNReal q := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (Rat.cast_nonneg.mpr hq)]
    change (r : ℝ) = (q : ℝ)
    exact_mod_cast (Rat.coe_toNNRat q hq)
  refine ⟨(r : NNReal), ⟨r, rfl⟩, ?_⟩
  rw [hr_eq]
  exact ⟨haq, hqb⟩

theorem continuous_of_additive_nonneg_continuousAt_zero
    (g : NNReal →+ ℝ)
    (h_nonneg : ∀ t, 0 ≤ g t)
    (h0 : ContinuousAt g 0) :
    Continuous g := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [Metric.continuousAt_iff]
  rw [Metric.continuousAt_iff] at h0
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ := h0 ε hε
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  rcases le_total x y with hxy | hyx
  · let z : NNReal := y - x
    have hzadd : x + z = y := by
      dsimp [z]
      exact add_tsub_cancel_of_le hxy
    have hzdist : dist z 0 = dist y x := by
      rw [NNReal.dist_eq, NNReal.dist_eq]
      dsimp [z]
      rw [NNReal.coe_sub hxy]
      simp only [sub_zero]
    have hzsmall : dist (g z) (g 0) < ε :=
      hsmall (by simpa [hzdist] using hy)
    have hgy : g y = g x + g z := by
      rw [← hzadd, map_add]
    have hzval : g z < ε := by
      simpa [Real.dist_eq, abs_of_nonneg (h_nonneg z)] using hzsmall
    rw [Real.dist_eq, hgy, add_sub_cancel_left, abs_of_nonneg (h_nonneg z)]
    exact hzval
  · let z : NNReal := x - y
    have hzadd : y + z = x := by
      dsimp [z]
      exact add_tsub_cancel_of_le hyx
    have hzdist : dist z 0 = dist y x := by
      rw [NNReal.dist_eq, NNReal.dist_eq]
      dsimp [z]
      rw [NNReal.coe_sub hyx]
      simp only [sub_zero]
      exact abs_sub_comm _ _
    have hzsmall : dist (g z) (g 0) < ε :=
      hsmall (by simpa [hzdist] using hy)
    have hgx : g x = g y + g z := by
      rw [← hzadd, map_add]
    have hzval : g z < ε := by
      simpa [Real.dist_eq, abs_of_nonneg (h_nonneg z)] using hzsmall
    rw [Real.dist_eq, hgx]
    simpa [abs_of_nonneg (h_nonneg z)] using hzval

theorem additive_nonneg_eq_mul_one
    (g : NNReal →+ ℝ)
    (h_nonneg : ∀ t, 0 ≤ g t)
    (h0 : ContinuousAt g 0) :
    ∀ t : NNReal, g t = (t : ℝ) * g 1 := by
  have hg : Continuous g :=
    continuous_of_additive_nonneg_continuousAt_zero g h_nonneg h0
  let h : NNReal → ℝ := fun t => (t : ℝ) * g 1
  have hh : Continuous h := by
    exact NNReal.continuous_coe.mul continuous_const
  have heq : g = h := nnrat_dense_nnreal.equalizer hg hh (by
    funext q
    change g (q : NNReal) = (q : ℝ) * g 1
    have hm := map_nnrat_smul g q (1 : NNReal)
    simpa [NNRat.smul_def] using hm)
  intro t
  exact congrFun heq t

theorem exponential_qSurvival
    (S : KilledSemigroup X) (q : ProbabilityMeasure X)
    (heig : ∀ s : NNReal,
      S.P s ∘ₘ (q : Measure X) =
        (S.P s ∘ₘ (q : Measure X)) Set.univ • (q : Measure X))
    (hpos : ∀ t : NNReal, 0 < qSurvival S q t)
    (hcont : ContinuousAt (fun t : NNReal => (qSurvival S q t).toReal) 0) :
    ∃ rate : ℝ, 0 ≤ rate ∧
      ∀ t : NNReal,
        (qSurvival S q t).toReal = Real.exp (-rate * (t : ℝ)) := by
  let a : NNReal → ℝ := fun t => (qSurvival S q t).toReal
  have atop : ∀ t : NNReal, qSurvival S q t ≠ ∞ := by
    intro t
    exact ne_of_lt ((qSurvival_le_one S q t).trans_lt ENNReal.one_lt_top)
  have apos : ∀ t : NNReal, 0 < a t := by
    intro t
    exact ENNReal.toReal_pos (ne_of_gt (hpos t)) (atop t)
  have ale : ∀ t : NNReal, a t ≤ 1 := by
    intro t
    have h := ENNReal.toReal_mono (by simp) (qSurvival_le_one S q t)
    simpa [a] using h
  let g : NNReal →+ ℝ :=
    { toFun := fun t => -Real.log (a t)
      map_zero' := by
        simp [a, qSurvival_zero]
      map_add' := by
        intro s t
        have hs0 : a s ≠ 0 := ne_of_gt (apos s)
        have ht0 : a t ≠ 0 := ne_of_gt (apos t)
        have hadd : a (s + t) = a s * a t := by
          simp only [a, qSurvival_add S q heig, ENNReal.toReal_mul]
        rw [hadd, Real.log_mul hs0 ht0]
        ring }
  have hg_nonneg : ∀ t : NNReal, 0 ≤ g t := by
    intro t
    change 0 ≤ -Real.log (a t)
    exact neg_nonneg.mpr (Real.log_nonpos (le_of_lt (apos t)) (ale t))
  have hg_cont : ContinuousAt g 0 := by
    change ContinuousAt (fun t : NNReal => -Real.log (a t)) 0
    have ha0 : a 0 ≠ 0 := ne_of_gt (apos 0)
    exact (hcont.log ha0).neg
  have hlin := additive_nonneg_eq_mul_one g hg_nonneg hg_cont
  let rate : ℝ := g 1
  refine ⟨rate, hg_nonneg 1, ?_⟩
  intro t
  have ht := hlin t
  have hlog : Real.log (a t) = -rate * (t : ℝ) := by
    change -Real.log (a t) = (t : ℝ) * rate at ht
    linarith [ht]
  calc
    a t = Real.exp (Real.log (a t)) := (Real.exp_log (apos t)).symm
    _ = Real.exp (-rate * (t : ℝ)) := by rw [hlog]

theorem p_qsd_01
    (S : KilledSemigroup X)
    (q : ProbabilityMeasure X)
    (hTV : Tendsto
      (fun t : NNReal => UEOT.V3.TotalVariation.tvDist
        (S.conditioned t : Measure X) (q : Measure X)) atTop (𝓝 0))
    (hpos : ∀ t : NNReal, t ≠ 0 → 0 < qSurvival S q t)
    (hcont : ContinuousAt (fun t : NNReal => (qSurvival S q t).toReal) 0) :
    ∃ rate : ℝ, 0 ≤ rate ∧
      (∀ s : NNReal,
        S.P s ∘ₘ (q : Measure X) = qSurvival S q s • (q : Measure X)) ∧
      (∀ s : NNReal,
        (qSurvival S q s).toReal = Real.exp (-rate * (s : ℝ))) ∧
      (∀ s : NNReal,
        S.P s ∘ₘ (q : Measure X) =
          ENNReal.ofReal (Real.exp (-rate * (s : ℝ))) • (q : Measure X)) := by
  have heig := eigenmeasure_of_tv_limit S q hTV
  have hposAll : ∀ t : NNReal, 0 < qSurvival S q t := by
    intro t
    by_cases ht : t = 0
    · subst t
      rw [qSurvival_zero]
      exact zero_lt_one
    · exact hpos t ht
  obtain ⟨rate, hrate, hexp⟩ := exponential_qSurvival S q heig hposAll hcont
  refine ⟨rate, hrate, ?_, hexp, ?_⟩
  · intro s
    simpa [qSurvival] using heig s
  · intro s
    rw [heig s]
    have htop : qSurvival S q s ≠ ∞ :=
      ne_of_lt ((qSurvival_le_one S q s).trans_lt ENNReal.one_lt_top)
    have hcoeff : qSurvival S q s = ENNReal.ofReal (Real.exp (-rate * (s : ℝ))) := by
      apply (ENNReal.toReal_eq_toReal_iff' htop (by simp)).mp
      rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
      exact hexp s
    change qSurvival S q s • (q : Measure X) =
      ENNReal.ofReal (Real.exp (-rate * (s : ℝ))) • (q : Measure X)
    rw [hcoeff]

end UEOT.V3.QSDTVLimit
