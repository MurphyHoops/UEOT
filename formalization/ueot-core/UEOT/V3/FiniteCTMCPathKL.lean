import UEOT.V3.CTMCLumpability
import UEOT.V3.ThirdParty.CrooksJarzynski.ContinuousTimeJumpTrajectory
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# P-KL-04 — finite continuous-time Markov-chain path KL

This file is the source-facing UEOT layer for Core v3 §22.4.  The underlying
finite-jump path law is the explicit, normalized, non-explosive construction in
`UEOT.V3.ThirdParty.CrooksJarzynski`: an `n`-jump trajectory carries its state
sequence and all `n+1` holding intervals, and the full path law is the countable
sum over the jump-count sectors.

The proof developed here is deliberately about that actual path law.  In
particular, support inclusion is converted into absolute continuity through the
common counting/simplex reference measure; no path likelihood, compensator, or
KL identity is postulated as a certificate.
-/

namespace UEOT.V3.FiniteCTMCPathKL

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal BigOperators unitInterval
open UEOT.V3.CTMCLumpability
open CrooksJarzynski.MeasureProtocol.ContinuousTimeJump
open CrooksJarzynski.MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator

universe u

variable {X : Type u} [Fintype X] [DecidableEq X]
variable [MeasurableSpace X] [MeasurableSingletonClass X]

/-- Algebraic common-reference lemma used below.  When the support of `f` is
contained in the support of a finite-valued `g`, reweighting first by `g` and
then by `f/g` gives exactly the direct `f`-weighted measure. -/
theorem withDensity_factor_div
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f g : α → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (hg_top : ∀ x, g x ≠ ∞)
    (hsupp : ∀ x, f x ≠ 0 → g x ≠ 0) :
    μ.withDensity f =
      (μ.withDensity g).withDensity (fun x => f x / g x) := by
  have hfg :
      μ.withDensity f =
        μ.withDensity (g * fun x => f x / g x) := by
    apply MeasureTheory.withDensity_congr_ae
    filter_upwards with x
    simp only [Pi.mul_apply]
    by_cases hfx : f x = 0
    · simp [hfx]
    · exact (ENNReal.mul_div_cancel (hsupp x hfx) (hg_top x)).symm
  calc
    μ.withDensity f =
        μ.withDensity (g * fun x => f x / g x) := hfg
    _ = (μ.withDensity g).withDensity (fun x => f x / g x) :=
      MeasureTheory.withDensity_mul₀
        hg.aemeasurable (hf.div hg).aemeasurable

theorem withDensity_ac_of_support
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f g : α → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (hg_top : ∀ x, g x ≠ ∞)
    (hsupp : ∀ x, f x ≠ 0 → g x ≠ 0) :
    μ.withDensity f ≪ μ.withDensity g := by
  rw [withDensity_factor_div μ f g hf hg hg_top hsupp]
  exact MeasureTheory.withDensity_absolutelyContinuous _ _

/-- The source support condition: every positive controlled off-diagonal rate is
also positive under the baseline chain.  The diagonal is zero in both chains by
construction. -/
def SupportIncluded (controlled baseline : FiniteJumpGenerator X) : Prop :=
  ∀ x y, 0 < controlled.jumpRate x y → 0 < baseline.jumpRate x y

/-- The Crooks finite-jump generator has exactly the algebraic matrix properties
of the pre-existing UEOT finite CTMC generator predicate.  This statement is
only the generator-matrix bridge; the path law used below is the explicit
finite-jump construction developed in the vendored module. -/
theorem generator_isCTMCGenerator (G : FiniteJumpGenerator X) :
    IsCTMCGenerator G.generator := by
  constructor
  · intro x y hxy
    exact G.generator_offDiagonal_nonneg hxy.symm
  · exact G.generator_row_sum

/-- The raw counting/simplex reference measure does not depend on the jump
rates. -/
theorem rawCountingReference_eq
    (G H : FiniteJumpGenerator X) (T : NNReal) (n : ℕ) :
    G.rawCountingReference T n = H.rawCountingReference T n := by
  unfold FiniteJumpGenerator.rawCountingReference
    FiniteJumpGenerator.stateSequenceCountingReference
  rfl

/-- The fixed-initial sector density used by the actual finite CTMC path law. -/
noncomputable def sectorDensity
    (G : FiniteJumpGenerator X) (x : X) (n : ℕ) :
    JumpPath X n → ℝ≥0∞ :=
  JumpPath.rateDensity (fixedInitialWeight x)
    G.pathEscapeRate G.pathJumpRate

theorem measurable_sectorDensity
    (G : FiniteJumpGenerator X) (x : X) (n : ℕ) :
    Measurable (sectorDensity G x n) := by
  simpa [sectorDensity] using G.measurable_rateDensity (fixedInitialWeight x) n

theorem sectorDensity_ne_top
    (G : FiniteJumpGenerator X) (x : X) (n : ℕ)
    (γ : JumpPath X n) :
    sectorDensity G x n γ ≠ ∞ := by
  unfold sectorDensity JumpPath.rateDensity JumpPath.density
  apply ENNReal.mul_ne_top
  · apply ENNReal.mul_ne_top
    · unfold fixedInitialWeight
      split <;> simp
    · apply ENNReal.prod_ne_top
      intro i hi
      apply ENNReal.mul_ne_top
      · simp [JumpPath.holdingWeightOfEscapeRate]
      · simp [JumpPath.jumpWeightOfRate]
  · simp [JumpPath.holdingWeightOfEscapeRate]

theorem sectorDensity_ne_zero_iff
    (G : FiniteJumpGenerator X) (x : X) (n : ℕ)
    (γ : JumpPath X n) :
    sectorDensity G x n γ ≠ 0 ↔
      γ.1 0 = x ∧
        ∀ i : Fin n,
          G.jumpRate (γ.1 i.castSucc) (γ.1 i.succ) ≠ 0 := by
  unfold sectorDensity JumpPath.rateDensity JumpPath.density
  simp [fixedInitialWeight,
    JumpPath.holdingWeightOfEscapeRate,
    JumpPath.jumpWeightOfRate,
    FiniteJumpGenerator.pathEscapeRate,
    FiniteJumpGenerator.pathJumpRate,
    Finset.prod_ne_zero_iff, Real.exp_pos]

theorem sectorDensity_support_mono
    (Gu G0 : FiniteJumpGenerator X)
    (hsupport : SupportIncluded Gu G0)
    (x : X) (n : ℕ) (γ : JumpPath X n) :
    sectorDensity Gu x n γ ≠ 0 →
      sectorDensity G0 x n γ ≠ 0 := by
  rw [sectorDensity_ne_zero_iff, sectorDensity_ne_zero_iff]
  rintro ⟨hinit, hjump⟩
  refine ⟨hinit, ?_⟩
  intro i
  have hu : 0 < Gu.jumpRate (γ.1 i.castSucc) (γ.1 i.succ) :=
    bot_lt_iff_ne_bot.mpr (hjump i)
  exact (hsupport _ _ hu).ne'

/-- Real form of a nonzero finite-jump sector density.  The initial delta has
become one; all remaining factors are the exponential holding weights and the
real jump rates. -/
theorem sectorDensity_toReal
    (G : FiniteJumpGenerator X) (x : X) (n : ℕ)
    (γ : JumpPath X n) (h : sectorDensity G x n γ ≠ 0) :
    (sectorDensity G x n γ).toReal =
      (∏ i : Fin n,
        Real.exp (-((G.escapeRate (γ.1 i.castSucc) : ℝ) *
          (γ.2 i.castSucc : ℝ))) *
          (G.jumpRate (γ.1 i.castSucc) (γ.1 i.succ) : ℝ)) *
        Real.exp (-((G.escapeRate (γ.1 (Fin.last n)) : ℝ) *
          (γ.2 (Fin.last n) : ℝ))) := by
  have hs := (sectorDensity_ne_zero_iff G x n γ).mp h
  rcases hs with ⟨hinit, hjump⟩
  unfold sectorDensity JumpPath.rateDensity JumpPath.density
  simp only [hinit, fixedInitialWeight_self, ENNReal.toReal_mul, ENNReal.toReal_prod,
    JumpPath.holdingWeightOfEscapeRate, JumpPath.jumpWeightOfRate,
    FiniteJumpGenerator.pathEscapeRate, FiniteJumpGenerator.pathJumpRate,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.coe_toReal, one_mul]

/-- Log-density of one nonzero sector path. -/
noncomputable def sectorLogDensity
    (G : FiniteJumpGenerator X) {n : ℕ} (γ : JumpPath X n) : ℝ :=
  (∑ i : Fin n,
      Real.log (G.jumpRate (γ.1 i.castSucc) (γ.1 i.succ) : ℝ)) -
    ((∑ i : Fin n,
        (G.escapeRate (γ.1 i.castSucc) : ℝ) * (γ.2 i.castSucc : ℝ)) +
      (G.escapeRate (γ.1 (Fin.last n)) : ℝ) * (γ.2 (Fin.last n) : ℝ))

theorem log_sectorDensity_toReal
    (G : FiniteJumpGenerator X) (x : X) (n : ℕ)
    (γ : JumpPath X n) (h : sectorDensity G x n γ ≠ 0) :
    Real.log (sectorDensity G x n γ).toReal = sectorLogDensity G γ := by
  have hs := (sectorDensity_ne_zero_iff G x n γ).mp h
  rcases hs with ⟨_hinit, hjump⟩
  rw [sectorDensity_toReal G x n γ h]
  have hprod :
      (∏ i : Fin n,
        Real.exp (-((G.escapeRate (γ.1 i.castSucc) : ℝ) *
          (γ.2 i.castSucc : ℝ))) *
          (G.jumpRate (γ.1 i.castSucc) (γ.1 i.succ) : ℝ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.2
    intro i hi
    exact mul_ne_zero (Real.exp_ne_zero _) (by exact_mod_cast hjump i)
  rw [Real.log_mul hprod (Real.exp_ne_zero _), Real.log_prod]
  · have hterm : ∀ i : Fin n,
        Real.log
          (Real.exp (-((G.escapeRate (γ.1 i.castSucc) : ℝ) *
              (γ.2 i.castSucc : ℝ))) *
            (G.jumpRate (γ.1 i.castSucc) (γ.1 i.succ) : ℝ)) =
          -((G.escapeRate (γ.1 i.castSucc) : ℝ) *
              (γ.2 i.castSucc : ℝ)) +
            Real.log (G.jumpRate (γ.1 i.castSucc) (γ.1 i.succ) : ℝ) := by
      intro i
      rw [Real.log_mul (Real.exp_ne_zero _)
        (by exact_mod_cast hjump i), Real.log_exp]
    simp_rw [hterm, Real.log_exp]
    unfold sectorLogDensity
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_neg_distrib]
    ring
  · intro i hi
    exact mul_ne_zero (Real.exp_ne_zero _) (by exact_mod_cast hjump i)

/-- Sector law, restated as a density against the rate-independent reference. -/
theorem sectorLawFrom_eq_withDensity
    (G : FiniteJumpGenerator X) (T : NNReal) (x : X) (n : ℕ) :
    G.sectorLawFrom T x n =
      (G.rawCountingReference T n).withDensity (sectorDensity G x n) := by
  rfl

/-- Generic chart expansion for one fixed jump-count sector.  This is the
measure-theoretic bridge used by the Campbell proof below: it reduces an
arbitrary nonnegative measurable path observable to the explicit finite state
sequence / simplex representation from which the renewal identities apply. -/
theorem lintegral_sectorLawFrom_eq_sum_chart
    (G : FiniteJumpGenerator X) (T : NNReal) (x : X) (n : ℕ)
    (q : JumpPath X n → ℝ≥0∞) (hq : Measurable q) :
    ∫⁻ γ, q γ ∂(G.sectorLawFrom T x n) =
      ∑ states : Fin (n + 1) → X,
        ∫⁻ u,
          JumpPath.rateDensity (fixedInitialWeight x) G.pathEscapeRate
              G.pathJumpRate (Simplex.assemblePath T (states, u)) *
            q (Simplex.assemblePath T (states, u))
          ∂((T : ℝ≥0∞) ^ n •
            (volume : Measure (Fin n → I)).restrict
              (Simplex.freeSimplexSet n)) := by
  have hdensity := G.measurable_rateDensity (fixedInitialWeight x) n
  have hjoint : Measurable fun γ : JumpPath X n =>
      JumpPath.rateDensity (fixedInitialWeight x) G.pathEscapeRate
          G.pathJumpRate γ * q γ := hdensity.mul hq
  unfold FiniteJumpGenerator.sectorLawFrom pathMeasure
  rw [lintegral_withDensity_eq_lintegral_mul _ hdensity hq]
  simp only [Pi.mul_apply]
  have hpull : Measurable fun p : (Fin (n + 1) → X) × (Fin n → I) =>
      JumpPath.rateDensity (fixedInitialWeight x) G.pathEscapeRate
          G.pathJumpRate (Simplex.assemblePath T p) *
        q (Simplex.assemblePath T p) :=
    hjoint.comp (Simplex.measurable_assemblePath T)
  rw [G.rawCountingReference_eq T n,
    lintegral_map' hjoint.aemeasurable
      (Simplex.measurable_assemblePath T).aemeasurable,
    lintegral_prod _ hpull.aemeasurable, lintegral_fintype]
  refine Finset.sum_congr rfl fun states _ => ?_
  rw [G.stateSequenceCountingReference_singleton n states, mul_one]

/-! ### Marked renewal / Campbell layer -/

/-- Instantaneous intensity of a nonnegative edge reward. -/
noncomputable def edgeRewardRate
    (G : FiniteJumpGenerator X) (h : X → X → ℝ≥0∞) (i : X) : ℝ≥0∞ :=
  ∑ j : X, (G.jumpRate i j : ℝ≥0∞) * h i j

/-- Reward accumulated at the actual jumps of a fixed-sector path. -/
noncomputable def sectorJumpReward
    (h : X → X → ℝ≥0∞) {n : ℕ} (γ : JumpPath X n) : ℝ≥0∞ :=
  ∑ i : Fin n, h (γ.1 i.castSucc) (γ.1 i.succ)

/-- The same jump reward on a bare state sequence. -/
noncomputable def sequenceJumpReward
    (h : X → X → ℝ≥0∞) {n : ℕ} (states : Fin (n + 1) → X) : ℝ≥0∞ :=
  ∑ i : Fin n, h (states i.castSucc) (states i.succ)

@[simp]
theorem sequenceJumpReward_zero
    (h : X → X → ℝ≥0∞) (states : Fin 1 → X) :
    sequenceJumpReward h states = 0 := by
  simp [sequenceJumpReward]

theorem sequenceJumpReward_snoc
    (h : X → X → ℝ≥0∞) {n : ℕ}
    (init : Fin (n + 1) → X) (z : X) :
    sequenceJumpReward h (Fin.snoc init z) =
      sequenceJumpReward h init + h (init (Fin.last n)) z := by
  unfold sequenceJumpReward
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · simp

/-- Occupation-time integral of the edge-reward intensity, represented in the
holding-time chart. -/
noncomputable def sectorHoldingReward
    (G : FiniteJumpGenerator X) (h : X → X → ℝ≥0∞)
    {n : ℕ} (γ : JumpPath X n) : ℝ≥0∞ :=
  ∑ i : Fin (n + 1),
    (γ.2 i : ℝ≥0∞) * edgeRewardRate G h (γ.1 i)

/-- Prefix occupation mass used in the marked-renewal proof.  It is the
arrival mass with one additional time factor and no next-edge rate. -/
noncomputable def sequenceOccupationMass
    (G : FiniteJumpGenerator X) (T : NNReal) {n : ℕ}
    (states : Fin (n + 1) → X) : ℝ≥0∞ :=
  (T : ℝ≥0∞) ^ (n + 1) * G.jumpProduct states *
    arrivalOn (fun i : Fin (n + 1) => G.escapeRate (states i)) T

/-- Marked branching atom: occupation of the terminal prefix state multiplied
by its reward intensity equals the sum of marked arrival masses after one more
jump. -/
theorem sequenceOccupationMass_mul_edgeRewardRate
    (G : FiniteJumpGenerator X) (T : NNReal)
    (h : X → X → ℝ≥0∞) {n : ℕ}
    (init : Fin (n + 1) → X) :
    sequenceOccupationMass G T init *
        edgeRewardRate G h (init (Fin.last n)) =
      ∑ z : X,
        h (init (Fin.last n)) z *
          G.sequenceArrivalMass T (Fin.snoc init z) := by
  unfold sequenceOccupationMass edgeRewardRate
  have hsnoc : ∀ z : X,
      G.sequenceArrivalMass T (Fin.snoc init z) =
        (T : ℝ≥0∞) ^ (n + 1) *
          (G.jumpProduct init *
            (G.jumpRate (init (Fin.last n)) z : ℝ≥0∞)) *
          arrivalOn (fun i : Fin (n + 1) => G.escapeRate (init i)) T := by
    intro z
    unfold FiniteJumpGenerator.sequenceArrivalMass
    rw [G.jumpProduct_snoc init z, G.stateEscapeRates_snoc init z]
  simp_rw [hsnoc]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  ring

/-- Weighted mass of the jump reward in the exact-`n` sector. -/
noncomputable def sectorJumpMass
    (G : FiniteJumpGenerator X) (T : NNReal) (x : X)
    (h : X → X → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ∑ states : Fin (n + 1) → X,
    fixedInitialWeight x (states 0) * G.sequenceMass T states *
      sequenceJumpReward h states

/-- Weighted jump reward carried by paths whose first `n` jumps have arrived. -/
noncomputable def arrivalJumpMass
    (G : FiniteJumpGenerator X) (T : NNReal) (x : X)
    (h : X → X → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ∑ states : Fin (n + 1) → X,
    fixedInitialWeight x (states 0) * G.sequenceArrivalMass T states *
      sequenceJumpReward h states

/-- Reward-intensity mass emitted by all `n`-jump prefixes. -/
noncomputable def nextJumpRewardMass
    (G : FiniteJumpGenerator X) (T : NNReal) (x : X)
    (h : X → X → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ∑ states : Fin (n + 1) → X,
    fixedInitialWeight x (states 0) * sequenceOccupationMass G T states *
      edgeRewardRate G h (states (Fin.last n))

@[simp]
theorem arrivalJumpMass_zero
    (G : FiniteJumpGenerator X) (T : NNReal) (x : X)
    (h : X → X → ℝ≥0∞) :
    arrivalJumpMass G T x h 0 = 0 := by
  unfold arrivalJumpMass
  simp

/-- Marked renewal recurrence for accumulated jump reward. -/
theorem sectorJumpMass_add_arrivalJumpMass_succ
    (G : FiniteJumpGenerator X) (T : NNReal) (x : X)
    (h : X → X → ℝ≥0∞) (n : ℕ) :
    sectorJumpMass G T x h n + arrivalJumpMass G T x h (n + 1) =
      arrivalJumpMass G T x h n + nextJumpRewardMass G T x h n := by
  classical
  have harrival :
      arrivalJumpMass G T x h (n + 1) =
        ∑ init : Fin (n + 1) → X,
          fixedInitialWeight x (init 0) *
            ∑ z : X,
              G.sequenceArrivalMass T (Fin.snoc init z) *
                (sequenceJumpReward h init + h (init (Fin.last n)) z) := by
    unfold arrivalJumpMass
    rw [← Fintype.sum_equiv (FiniteJumpGenerator.snocEquiv X n)
      (fun p : ((Fin (n + 1) → X) × X) =>
        fixedInitialWeight x ((Fin.snoc p.1 p.2 : Fin (n + 2) → X) 0) *
          G.sequenceArrivalMass T (Fin.snoc p.1 p.2) *
            sequenceJumpReward h (Fin.snoc p.1 p.2))
      _ (fun p => rfl)]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro init hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    simp only [FiniteJumpGenerator.snoc_zero, sequenceJumpReward_snoc]
    ring
  rw [harrival]
  unfold sectorJumpMass arrivalJumpMass nextJumpRewardMass
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro init hi
  have hmass := G.sequenceMass_add_sum_sequenceArrivalMass_snoc T init
  have hatom := sequenceOccupationMass_mul_edgeRewardRate G T h init
  have hsplit :
      (∑ z : X,
          G.sequenceArrivalMass T (Fin.snoc init z) *
            (sequenceJumpReward h init + h (init (Fin.last n)) z)) =
        (∑ z : X, G.sequenceArrivalMass T (Fin.snoc init z)) *
            sequenceJumpReward h init +
          ∑ z : X,
            h (init (Fin.last n)) z *
              G.sequenceArrivalMass T (Fin.snoc init z) := by
    simp_rw [mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul]
    apply congrArg₂ (· + ·) rfl
    apply Finset.sum_congr rfl
    intro z hz
    ring
  rw [hsplit, ← hatom]
  calc
    fixedInitialWeight x (init 0) * G.sequenceMass T init *
          sequenceJumpReward h init +
        fixedInitialWeight x (init 0) *
          ((∑ z, G.sequenceArrivalMass T (Fin.snoc init z)) *
              sequenceJumpReward h init +
            sequenceOccupationMass G T init *
              edgeRewardRate G h (init (Fin.last n)))
        = fixedInitialWeight x (init 0) *
            ((G.sequenceMass T init +
                ∑ z, G.sequenceArrivalMass T (Fin.snoc init z)) *
              sequenceJumpReward h init +
              sequenceOccupationMass G T init *
                edgeRewardRate G h (init (Fin.last n))) := by ring
    _ = fixedInitialWeight x (init 0) *
          (G.sequenceArrivalMass T init * sequenceJumpReward h init +
            sequenceOccupationMass G T init *
              edgeRewardRate G h (init (Fin.last n))) := by
          rw [hmass]
    _ = fixedInitialWeight x (init 0) * G.sequenceArrivalMass T init *
          sequenceJumpReward h init +
        fixedInitialWeight x (init 0) * sequenceOccupationMass G T init *
          edgeRewardRate G h (init (Fin.last n)) := by ring

theorem measurable_sectorJumpReward
    (h : X → X → ℝ≥0∞) (n : ℕ) :
    Measurable (sectorJumpReward h : JumpPath X n → ℝ≥0∞) := by
  unfold sectorJumpReward
  fun_prop

theorem sequenceJumpReward_ne_top
    (h : X → X → ℝ≥0∞) (hh : ∀ i j, h i j ≠ ∞)
    {n : ℕ} (states : Fin (n + 1) → X) :
    sequenceJumpReward h states ≠ ∞ := by
  unfold sequenceJumpReward
  exact ENNReal.sum_ne_top.mpr fun i hi => hh _ _

theorem lintegral_sectorJumpReward_eq_sectorJumpMass
    (G : FiniteJumpGenerator X) (T : NNReal) (x : X)
    (h : X → X → ℝ≥0∞) (hh : ∀ i j, h i j ≠ ∞) (n : ℕ) :
    ∫⁻ γ, sectorJumpReward h γ ∂(G.sectorLawFrom T x n) =
      sectorJumpMass G T x h n := by
  rw [lintegral_sectorLawFrom_eq_sum_chart G T x n
    (sectorJumpReward h) (measurable_sectorJumpReward h n)]
  unfold sectorJumpMass
  apply Finset.sum_congr rfl
  intro states hs
  have hconst : ∀ u : Fin n → I,
      sectorJumpReward h (Simplex.assemblePath T (states, u)) =
        sequenceJumpReward h states := by
    intro u
    rfl
  simp_rw [hconst]
  rw [lintegral_mul_const' _ _ (sequenceJumpReward_ne_top h hh states)]
  rw [G.lintegral_rateDensity_assemblePath (fixedInitialWeight x) T states (by
    unfold fixedInitialWeight
    split <;> simp)]

/-- Full-path version of the realized jump reward. -/
noncomputable def fullJumpReward
    (h : X → X → ℝ≥0∞) : FullPath X → ℝ≥0∞ :=
  FullPath.weight (fun n => sectorJumpReward h)

theorem measurable_fullJumpReward (h : X → X → ℝ≥0∞) :
    Measurable (fullJumpReward h) := by
  exact FullPath.measurable_weight _ (measurable_sectorJumpReward h)

theorem lintegral_fullJumpReward_eq_tsum_sectorJumpMass
    (G : FiniteJumpGenerator X) (T : NNReal) (x : X)
    (h : X → X → ℝ≥0∞) (hh : ∀ i j, h i j ≠ ∞) :
    ∫⁻ γ, fullJumpReward h γ ∂(G.pathLawFrom T x) =
      ∑' n, sectorJumpMass G T x h n := by
  unfold FiniteJumpGenerator.pathLawFrom FullPath.measure
  rw [lintegral_sum_measure]
  apply tsum_congr
  intro n
  unfold FullPath.liftMeasure
  rw [lintegral_map' (measurable_fullJumpReward h).aemeasurable
    (FullPath.measurable_mk n).aemeasurable]
  change (∫⁻ γ, sectorJumpReward h γ ∂G.sectorLawFrom T x n) = _
  exact lintegral_sectorJumpReward_eq_sectorJumpMass G T x h hh n

/-- A finite global bound for a finite-valued nonnegative edge reward. -/
noncomputable def rewardTotal (h : X → X → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ i : X, ∑ j : X, h i j

theorem reward_le_rewardTotal
    (h : X → X → ℝ≥0∞) (i j : X) :
    h i j ≤ rewardTotal h := by
  unfold rewardTotal
  calc
    h i j ≤ ∑ z : X, h i z := by
      exact Finset.single_le_sum
        (fun z hz => show (0 : ℝ≥0∞) ≤ h i z from bot_le)
        (Finset.mem_univ j)
    _ ≤ ∑ y : X, ∑ z : X, h y z := by
      exact Finset.single_le_sum
        (fun y hy => show (0 : ℝ≥0∞) ≤ ∑ z : X, h y z from bot_le)
        (Finset.mem_univ i)

theorem rewardTotal_ne_top
    (h : X → X → ℝ≥0∞) (hh : ∀ i j, h i j ≠ ∞) :
    rewardTotal h ≠ ∞ := by
  unfold rewardTotal
  exact ENNReal.sum_ne_top.mpr fun i hi =>
    ENNReal.sum_ne_top.mpr fun j hj => hh i j

theorem sequenceJumpReward_le
    (h : X → X → ℝ≥0∞) {n : ℕ} (states : Fin (n + 1) → X) :
    sequenceJumpReward h states ≤ (n : ℝ≥0∞) * rewardTotal h := by
  unfold sequenceJumpReward
  calc
    (∑ i : Fin n, h (states i.castSucc) (states i.succ))
        ≤ ∑ _i : Fin n, rewardTotal h :=
      Finset.sum_le_sum fun i hi => reward_le_rewardTotal h _ _
    _ = (n : ℝ≥0∞) * rewardTotal h := by simp

theorem arrivalJumpMass_le
    (G : FiniteJumpGenerator X) (T : NNReal) (x : X)
    (h : X → X → ℝ≥0∞) (n : ℕ) :
    arrivalJumpMass G T x h n ≤
      ((n : ℝ≥0∞) * rewardTotal h) * G.arrivalMassFrom T x n := by
  unfold arrivalJumpMass FiniteJumpGenerator.arrivalMassFrom
  calc
    (∑ states : Fin (n + 1) → X,
        fixedInitialWeight x (states 0) * G.sequenceArrivalMass T states *
          sequenceJumpReward h states)
        ≤ ∑ states : Fin (n + 1) → X,
            fixedInitialWeight x (states 0) * G.sequenceArrivalMass T states *
              ((n : ℝ≥0∞) * rewardTotal h) := by
          exact Finset.sum_le_sum fun states hs => by
            gcongr
            exact sequenceJumpReward_le h states
    _ = (∑ states : Fin (n + 1) → X,
            fixedInitialWeight x (states 0) * G.sequenceArrivalMass T states) *
          ((n : ℝ≥0∞) * rewardTotal h) := by
          rw [Finset.sum_mul]
    _ = ((n : ℝ≥0∞) * rewardTotal h) *
          ∑ states : Fin (n + 1) → X,
            fixedInitialWeight x (states 0) * G.sequenceArrivalMass T states := by
          rw [mul_comm]

/-- Elementary domination used to kill the marked-renewal tail. -/
theorem natCast_le_two_pow (n : ℕ) :
    (n : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ n := by
  exact_mod_cast (Nat.le_of_lt n.lt_two_pow_self)

theorem markedPoissonTail_tendsto_zero
    (G : FiniteJumpGenerator X) (T : NNReal)
    (h : X → X → ℝ≥0∞) (hh : ∀ i j, h i j ≠ ∞) :
    Filter.Tendsto
      (fun n : ℕ =>
        ((n : ℝ≥0∞) * rewardTotal h) *
          (((G.rateBound : ℝ≥0∞) * (T : ℝ≥0∞)) ^ n *
            ENNReal.ofReal (1 / (n.factorial : ℝ))))
      Filter.atTop (nhds 0) := by
  let R2 : NNReal := 2 * G.rateBound
  have hbase := Renewal.tendsto_pow_mul_factorial_inv T R2
  have hconst := ENNReal.Tendsto.const_mul hbase
    (Or.inr (rewardTotal_ne_top h hh))
  have hconst0 : Filter.Tendsto
      (fun n : ℕ => rewardTotal h *
        (((R2 : ℝ≥0∞) * (T : ℝ≥0∞)) ^ n *
          ENNReal.ofReal (1 / (n.factorial : ℝ))))
      Filter.atTop (nhds 0) := by
    simpa using hconst
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun _ : ℕ => (0 : ℝ≥0∞))
    (h := fun n : ℕ => rewardTotal h *
      (((R2 : ℝ≥0∞) * (T : ℝ≥0∞)) ^ n *
        ENNReal.ofReal (1 / (n.factorial : ℝ))))
    tendsto_const_nhds
    hconst0
    (fun n => bot_le)
  intro n
  have hn := natCast_le_two_pow n
  have hpow :
      (n : ℝ≥0∞) *
          ((G.rateBound : ℝ≥0∞) * (T : ℝ≥0∞)) ^ n ≤
        (((R2 : ℝ≥0∞) * (T : ℝ≥0∞)) ^ n) := by
    calc
      (n : ℝ≥0∞) *
          ((G.rateBound : ℝ≥0∞) * (T : ℝ≥0∞)) ^ n
          ≤ (2 : ℝ≥0∞) ^ n *
              ((G.rateBound : ℝ≥0∞) * (T : ℝ≥0∞)) ^ n := by gcongr
      _ = (((R2 : ℝ≥0∞) * (T : ℝ≥0∞)) ^ n) := by
        simp [R2, mul_pow]
        ring
  calc
    ((n : ℝ≥0∞) * rewardTotal h) *
        (((G.rateBound : ℝ≥0∞) * (T : ℝ≥0∞)) ^ n *
          ENNReal.ofReal (1 / (n.factorial : ℝ)))
        = rewardTotal h *
            (((n : ℝ≥0∞) *
              ((G.rateBound : ℝ≥0∞) * (T : ℝ≥0∞)) ^ n) *
              ENNReal.ofReal (1 / (n.factorial : ℝ))) := by ring
    _ ≤ rewardTotal h *
        ((((R2 : ℝ≥0∞) * (T : ℝ≥0∞)) ^ n) *
          ENNReal.ofReal (1 / (n.factorial : ℝ))) := by gcongr

theorem tendsto_arrivalJumpMass
    (G : FiniteJumpGenerator X) (T : NNReal) (x : X)
    (h : X → X → ℝ≥0∞) (hh : ∀ i j, h i j ≠ ∞) :
    Filter.Tendsto (fun n => arrivalJumpMass G T x h n)
      Filter.atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun _ : ℕ => (0 : ℝ≥0∞))
    (h := fun n : ℕ =>
      ((n : ℝ≥0∞) * rewardTotal h) *
        (((G.rateBound : ℝ≥0∞) * (T : ℝ≥0∞)) ^ n *
          ENNReal.ofReal (1 / (n.factorial : ℝ))))
    tendsto_const_nhds
    (markedPoissonTail_tendsto_zero G T h hh)
    (fun n => bot_le)
  intro n
  calc
    arrivalJumpMass G T x h n
        ≤ ((n : ℝ≥0∞) * rewardTotal h) * G.arrivalMassFrom T x n :=
      arrivalJumpMass_le G T x h n
    _ ≤ ((n : ℝ≥0∞) * rewardTotal h) *
        (((G.rateBound : ℝ≥0∞) * (T : ℝ≥0∞)) ^ n *
          ENNReal.ofReal (1 / (n.factorial : ℝ))) := by
      gcongr
      exact G.arrivalMassFrom_le T x n

/-- Finite marked-renewal telescoping identity. -/
theorem sum_sectorJumpMass_add_arrivalJumpMass
    (G : FiniteJumpGenerator X) (T : NNReal) (x : X)
    (h : X → X → ℝ≥0∞) (N : ℕ) :
    (∑ n ∈ Finset.range N, sectorJumpMass G T x h n) +
        arrivalJumpMass G T x h N =
      ∑ n ∈ Finset.range N, nextJumpRewardMass G T x h n := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, add_assoc,
        sectorJumpMass_add_arrivalJumpMass_succ G T x h N,
        ← add_assoc, ih]

/-- Global marked-renewal identity.  This is the compensator equality at the
explicit path-measure level, before translating occupation time to a clock-time
integral. -/
theorem tsum_sectorJumpMass_eq_tsum_nextJumpRewardMass
    (G : FiniteJumpGenerator X) (T : NNReal) (x : X)
    (h : X → X → ℝ≥0∞) (hh : ∀ i j, h i j ≠ ∞) :
    (∑' n, sectorJumpMass G T x h n) =
      ∑' n, nextJumpRewardMass G T x h n := by
  have hsector :
      Filter.Tendsto
        (fun N => ∑ n ∈ Finset.range N, sectorJumpMass G T x h n)
        Filter.atTop (nhds (∑' n, sectorJumpMass G T x h n)) :=
    ENNReal.tendsto_nat_tsum _
  have harrival := tendsto_arrivalJumpMass G T x h hh
  have hleft :
      Filter.Tendsto
        (fun N =>
          (∑ n ∈ Finset.range N, sectorJumpMass G T x h n) +
            arrivalJumpMass G T x h N)
        Filter.atTop (nhds (∑' n, sectorJumpMass G T x h n)) := by
    have hlim := hsector.add harrival
    simpa using hlim
  have hright :
      Filter.Tendsto
        (fun N => ∑ n ∈ Finset.range N, nextJumpRewardMass G T x h n)
        Filter.atTop (nhds (∑' n, nextJumpRewardMass G T x h n)) :=
    ENNReal.tendsto_nat_tsum _
  have heq :
      (fun N =>
        (∑ n ∈ Finset.range N, sectorJumpMass G T x h n) +
          arrivalJumpMass G T x h N) =
      (fun N => ∑ n ∈ Finset.range N, nextJumpRewardMass G T x h n) := by
    funext N
    exact sum_sectorJumpMass_add_arrivalJumpMass G T x h N
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

/-! ### Holding-time side of the compensator identity -/

/-- Reward already accumulated in the completed holding intervals of an
`n`-jump arrival chart.  The residual terminal interval is deliberately omitted:
an arrival prefix has not yet decided whether it stops or jumps again. -/
noncomputable def arrivalHoldingReward
    (G : FiniteJumpGenerator X) (T : NNReal)
    (h : X → X → ℝ≥0∞) {n : ℕ}
    (states : Fin (n + 1) → X) (u : Fin n → I) : ℝ≥0∞ :=
  ∑ i : Fin n,
    (Simplex.holdingTimesOfFree T u i.castSucc : ℝ≥0∞) *
      edgeRewardRate G h (states i.castSucc)

/-- Weighted arrival-prefix holding reward for one state sequence. -/
noncomputable def sequenceHoldingMass
    (G : FiniteJumpGenerator X) (T : NNReal)
    (h : X → X → ℝ≥0∞) {n : ℕ}
    (states : Fin (n + 1) → X) : ℝ≥0∞ :=
  (T : ℝ≥0∞) ^ n * G.jumpProduct states *
    ∫⁻ u in Simplex.freeSimplexSet n,
      Simplex.cubeExpWeight (G.stateEscapeRates states) T u *
        arrivalHoldingReward G T h states u

/-- Weighted exact-sector holding reward for one state sequence. -/
noncomputable def sequenceSectorHoldingMass
    (G : FiniteJumpGenerator X) (T : NNReal)
    (h : X → X → ℝ≥0∞) {n : ℕ}
    (states : Fin (n + 1) → X) : ℝ≥0∞ :=
  (T : ℝ≥0∞) ^ n * G.jumpProduct states *
    ∫⁻ u in Simplex.freeSimplexSet n,
      Simplex.cubeExpWeight (G.stateEscapeRates states) T u *
        ENNReal.ofReal
          (Real.exp
            (-((G.escapeRate (states (Fin.last n)) : ℝ) *
              (T : ℝ) * Simplex.residual u))) *
        (∑ i : Fin (n + 1),
          (Simplex.holdingTimesOfFree T u i : ℝ≥0∞) *
            edgeRewardRate G h (states i))

/-- Holding reward carried by the exact-`n` sector. -/
noncomputable def sectorHoldingMass
    (G : FiniteJumpGenerator X) (T : NNReal) (x : X)
    (h : X → X → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ∑ states : Fin (n + 1) → X,
    fixedInitialWeight x (states 0) *
      sequenceSectorHoldingMass G T h states

/-- Holding reward carried by all prefixes whose first `n` jumps have arrived. -/
noncomputable def arrivalHoldingMass
    (G : FiniteJumpGenerator X) (T : NNReal) (x : X)
    (h : X → X → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ∑ states : Fin (n + 1) → X,
    fixedInitialWeight x (states 0) * sequenceHoldingMass G T h states

@[simp]
theorem arrivalHoldingMass_zero
    (G : FiniteJumpGenerator X) (T : NNReal) (x : X)
    (h : X → X → ℝ≥0∞) :
    arrivalHoldingMass G T x h 0 = 0 := by
  unfold arrivalHoldingMass sequenceHoldingMass arrivalHoldingReward
  simp

theorem measurable_sectorHoldingReward
    (G : FiniteJumpGenerator X) (h : X → X → ℝ≥0∞) (n : ℕ) :
    Measurable (sectorHoldingReward G h : JumpPath X n → ℝ≥0∞) := by
  unfold sectorHoldingReward edgeRewardRate
  fun_prop

theorem lintegral_sectorHoldingReward_eq_sectorHoldingMass
    (G : FiniteJumpGenerator X) (T : NNReal) (x : X)
    (h : X → X → ℝ≥0∞) (n : ℕ) :
    ∫⁻ γ, sectorHoldingReward G h γ ∂(G.sectorLawFrom T x n) =
      sectorHoldingMass G T x h n := by
  rw [lintegral_sectorLawFrom_eq_sum_chart G T x n
    (sectorHoldingReward G h) (measurable_sectorHoldingReward G h n)]
  unfold sectorHoldingMass sequenceSectorHoldingMass
  apply Finset.sum_congr rfl
  intro states hs
  rw [lintegral_smul_measure, smul_eq_mul]
  have hreward : ∀ u : Fin n → I,
      sectorHoldingReward G h (Simplex.assemblePath T (states, u)) =
        ∑ i : Fin (n + 1),
          (Simplex.holdingTimesOfFree T u i : ℝ≥0∞) *
            edgeRewardRate G h (states i) := by
    intro u
    rfl
  simp_rw [hreward]
  rw [setLIntegral_congr_fun (Simplex.measurableSet_freeSimplexSet n)
    (fun u hu => by
      rw [G.rateDensity_assemblePath (fixedInitialWeight x) T states u hu])]
  have hreorder : ∀ u : Fin n → I,
      fixedInitialWeight x (states 0) *
          Simplex.cubeExpWeight (G.stateEscapeRates states) T u *
          G.jumpProduct states *
          ENNReal.ofReal
            (Real.exp
              (-((G.escapeRate (states (Fin.last n)) : ℝ) *
                (T : ℝ) * Simplex.residual u))) *
          (∑ i : Fin (n + 1),
            (Simplex.holdingTimesOfFree T u i : ℝ≥0∞) *
              edgeRewardRate G h (states i)) =
        (fixedInitialWeight x (states 0) * G.jumpProduct states) *
          (Simplex.cubeExpWeight (G.stateEscapeRates states) T u *
            ENNReal.ofReal
              (Real.exp
                (-((G.escapeRate (states (Fin.last n)) : ℝ) *
                  (T : ℝ) * Simplex.residual u))) *
            (∑ i : Fin (n + 1),
              (Simplex.holdingTimesOfFree T u i : ℝ≥0∞) *
                edgeRewardRate G h (states i))) := by
    intro u
    ring
  simp_rw [hreorder]
  rw [lintegral_const_mul' _ _ (by
    apply ENNReal.mul_ne_top
    · unfold fixedInitialWeight
      split <;> simp
    · exact G.jumpProduct_ne_top states)]
  ring

/-- Full-path occupation-time reward. -/
noncomputable def fullHoldingReward
    (G : FiniteJumpGenerator X) (h : X → X → ℝ≥0∞) :
    FullPath X → ℝ≥0∞ :=
  FullPath.weight (fun n => sectorHoldingReward G h)

theorem measurable_fullHoldingReward
    (G : FiniteJumpGenerator X) (h : X → X → ℝ≥0∞) :
    Measurable (fullHoldingReward G h) := by
  exact FullPath.measurable_weight _ (measurable_sectorHoldingReward G h)

theorem lintegral_fullHoldingReward_eq_tsum_sectorHoldingMass
    (G : FiniteJumpGenerator X) (T : NNReal) (x : X)
    (h : X → X → ℝ≥0∞) :
    ∫⁻ γ, fullHoldingReward G h γ ∂(G.pathLawFrom T x) =
      ∑' n, sectorHoldingMass G T x h n := by
  unfold FiniteJumpGenerator.pathLawFrom FullPath.measure
  rw [lintegral_sum_measure]
  apply tsum_congr
  intro n
  unfold FullPath.liftMeasure
  rw [lintegral_map' (measurable_fullHoldingReward G h).aemeasurable
    (FullPath.measurable_mk n).aemeasurable]
  change (∫⁻ γ, sectorHoldingReward G h γ ∂G.sectorLawFrom T x n) = _
  exact lintegral_sectorHoldingReward_eq_sectorHoldingMass G T x h n

/-! ### Horizon identity on the constructed full path law -/

/-- Total holding time of a path in the disjoint union of jump-count sectors. -/
def fullTotalHoldingTime : FullPath X → NNReal
  | ⟨_, γ⟩ => JumpPath.totalHoldingTime γ

theorem measurable_fullTotalHoldingTime :
    Measurable (fullTotalHoldingTime : FullPath X → NNReal) := by
  intro s hs
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro n
  change MeasurableSet
    ((fun γ : JumpPath X n => JumpPath.totalHoldingTime γ) ⁻¹' s)
  exact JumpPath.measurable_totalHoldingTime hs

theorem rawCountingReference_ae_totalHoldingTime
    (G : FiniteJumpGenerator X) (T : NNReal) (n : ℕ) :
    ∀ᵐ γ ∂G.rawCountingReference T n,
      JumpPath.totalHoldingTime γ = T := by
  unfold FiniteJumpGenerator.rawCountingReference
  apply Measure.ae_smul_measure
  simpa [JumpPath.horizonSet] using
    (Simplex.rawPathProbability_ae_horizon T
      (G.stateSequenceCountingReference n))

theorem sectorLawFrom_ae_totalHoldingTime
    (G : FiniteJumpGenerator X) (T : NNReal) (x : X) (n : ℕ) :
    ∀ᵐ γ ∂G.sectorLawFrom T x n,
      JumpPath.totalHoldingTime γ = T := by
  have hraw := rawCountingReference_ae_totalHoldingTime G T n
  unfold FiniteJumpGenerator.sectorLawFrom pathMeasure
  exact (withDensity_absolutelyContinuous _ _).ae_le hraw

theorem pathLawFrom_ae_totalHoldingTime
    (G : FiniteJumpGenerator X) (T : NNReal) (x : X) :
    ∀ᵐ γ ∂G.pathLawFrom T x, fullTotalHoldingTime γ = T := by
  have hset : MeasurableSet {γ : FullPath X | fullTotalHoldingTime γ = T} :=
    (measurable_fullTotalHoldingTime.eq_const T).setOf
  unfold FiniteJumpGenerator.pathLawFrom FullPath.measure
  apply Measure.ae_sum_iff.2
  intro n
  unfold FullPath.liftMeasure
  rw [ae_map_iff (FullPath.measurable_mk n).aemeasurable hset]
  exact sectorLawFrom_ae_totalHoldingTime G T x n

/-! ### Deterministic clock-time/holding-time bridge

The following lemmas are purely pathwise.  They identify the chart sum over
holding intervals with the ordinary real-time integral of the associated step
trajectory.  No compensator or stochastic-process theorem is used here. -/

theorem measurable_trajectory_time {n : ℕ} (γ : JumpPath X n) :
    Measurable (JumpPath.trajectory γ) := by
  induction n with
  | zero =>
      simp only [JumpPath.trajectory]
      fun_prop
  | succ n ih =>
      simp only [JumpPath.trajectory]
      exact Measurable.ite
        (measurableSet_le measurable_const measurable_id)
        measurable_const (ih (JumpPath.dropLast γ))

noncomputable def trajectoryStateBound (q : X → ℝ) : ℝ :=
  ∑ x : X, |q x|

theorem norm_stateReward_le_trajectoryStateBound (q : X → ℝ) (x : X) :
    ‖q x‖ ≤ trajectoryStateBound q := by
  simpa [trajectoryStateBound, Real.norm_eq_abs] using
    (Finset.single_le_sum (fun y hy => abs_nonneg (q y)) (Finset.mem_univ x))

theorem intervalIntegrable_stateTrajectory (q : X → ℝ) {n : ℕ}
    (γ : JumpPath X n) (a b : ℝ) :
    IntervalIntegrable (fun t => q (JumpPath.trajectory γ t)) volume a b := by
  have hmeas : Measurable (fun t => q (JumpPath.trajectory γ t)) :=
    (measurable_of_finite q).comp (measurable_trajectory_time γ)
  constructor
  · apply IntegrableOn.of_bound measure_Ioc_lt_top hmeas.aestronglyMeasurable
      (trajectoryStateBound q)
    filter_upwards [] with t
    exact norm_stateReward_le_trajectoryStateBound q _
  · apply IntegrableOn.of_bound measure_Ioc_lt_top hmeas.aestronglyMeasurable
      (trajectoryStateBound q)
    filter_upwards [] with t
    exact norm_stateReward_le_trajectoryStateBound q _

noncomputable def holdingRealReward (q : X → ℝ) {n : ℕ}
    (γ : JumpPath X n) : ℝ :=
  ∑ i : Fin (n + 1), (γ.2 i : ℝ) * q (γ.1 i)

theorem totalHoldingTime_dropLast_add_last {n : ℕ}
    (γ : JumpPath X (n + 1)) :
    (JumpPath.totalHoldingTime (JumpPath.dropLast γ) : ℝ) +
        (γ.2 (Fin.last (n + 1)) : ℝ) =
      (JumpPath.totalHoldingTime γ : ℝ) := by
  have hNN :
      JumpPath.totalHoldingTime (JumpPath.dropLast γ) +
          γ.2 (Fin.last (n + 1)) = JumpPath.totalHoldingTime γ := by
    unfold JumpPath.totalHoldingTime JumpPath.dropLast
    simpa using
      (Fin.sum_univ_castSucc (fun i : Fin (n + 2) => γ.2 i)).symm
  exact_mod_cast hNN

theorem holdingRealReward_succ (q : X → ℝ) {n : ℕ}
    (γ : JumpPath X (n + 1)) :
    holdingRealReward q γ =
      holdingRealReward q (JumpPath.dropLast γ) +
        (γ.2 (Fin.last (n + 1)) : ℝ) * q (γ.1 (Fin.last (n + 1))) := by
  unfold holdingRealReward JumpPath.dropLast
  rw [Fin.sum_univ_castSucc]

/-- The real-time integral of a finite-jump step trajectory is exactly its
holding-time sum, path by path. -/
theorem trajectory_intervalIntegral_eq_holding (q : X → ℝ) {n : ℕ}
    (γ : JumpPath X n) :
    (∫ t : ℝ in (0 : ℝ)..(JumpPath.totalHoldingTime γ : ℝ),
      q (JumpPath.trajectory γ t)) = holdingRealReward q γ := by
  induction n with
  | zero =>
      unfold holdingRealReward JumpPath.totalHoldingTime
      simp [JumpPath.trajectory, intervalIntegral.integral_const]
  | succ n ih =>
      let δ : JumpPath X n := JumpPath.dropLast γ
      let S : ℝ := (JumpPath.totalHoldingTime δ : ℝ)
      let R : ℝ := (JumpPath.totalHoldingTime γ : ℝ)
      have hS0 : 0 ≤ S := by
        dsimp [S]
        positivity
      have hSR : S ≤ R := by
        have hdecomp := totalHoldingTime_dropLast_add_last γ
        dsimp [S, R, δ]
        linarith [NNReal.coe_nonneg (γ.2 (Fin.last (n + 1)))]
      have hjump :
          JumpPath.jumpTimes γ (Fin.last (n + 1)) = S := by
        dsimp [S, δ]
        unfold JumpPath.jumpTimes JumpPath.totalHoldingTime JumpPath.dropLast
        rw [Fin.Iio_last_eq_map, NNReal.coe_sum]
        simp
      have hfirst :
          (∫ t : ℝ in (0 : ℝ)..S, q (JumpPath.trajectory γ t)) =
            ∫ t : ℝ in (0 : ℝ)..S, q (JumpPath.trajectory δ t) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hS0
        intro t ht
        simp only [JumpPath.trajectory]
        rw [if_neg]
        rw [hjump]
        exact not_le.mpr ht.2
      have hlast :
          (∫ t : ℝ in S..R, q (JumpPath.trajectory γ t)) =
            (R - S) * q (γ.1 (Fin.last (n + 1))) := by
        calc
          (∫ t : ℝ in S..R, q (JumpPath.trajectory γ t)) =
              ∫ _t : ℝ in S..R, q (γ.1 (Fin.last (n + 1))) := by
                apply intervalIntegral.integral_congr_Ioo_of_le hSR
                intro t ht
                simp only [JumpPath.trajectory]
                rw [if_pos]
                rw [hjump]
                exact ht.1.le
          _ = (R - S) * q (γ.1 (Fin.last (n + 1))) := by
                simp [intervalIntegral.integral_const, smul_eq_mul]
      have hsplit :
          (∫ t : ℝ in (0 : ℝ)..R, q (JumpPath.trajectory γ t)) =
            (∫ t : ℝ in (0 : ℝ)..S, q (JumpPath.trajectory γ t)) +
              ∫ t : ℝ in S..R, q (JumpPath.trajectory γ t) := by
        rw [intervalIntegral.integral_add_adjacent_intervals
          (intervalIntegrable_stateTrajectory q γ 0 S)
          (intervalIntegrable_stateTrajectory q γ S R)]
      rw [hsplit, hfirst, hlast]
      have ihδ := ih δ
      change (∫ t : ℝ in (0 : ℝ)..S, q (JumpPath.trajectory δ t)) =
        holdingRealReward q δ at ihδ
      rw [ihδ, holdingRealReward_succ]
      have hdecomp := totalHoldingTime_dropLast_add_last γ
      change S + (γ.2 (Fin.last (n + 1)) : ℝ) = R at hdecomp
      rw [show R - S = (γ.2 (Fin.last (n + 1)) : ℝ) by linarith]

theorem edgeRewardRate_le
    (G : FiniteJumpGenerator X) (h : X → X → ℝ≥0∞) (i : X) :
    edgeRewardRate G h i ≤
      (G.rateBound : ℝ≥0∞) * rewardTotal h := by
  unfold edgeRewardRate rewardTotal
  calc
    (∑ j : X, (G.jumpRate i j : ℝ≥0∞) * h i j)
        ≤ ∑ j : X, (G.jumpRate i j : ℝ≥0∞) * (∑ a : X, ∑ b : X, h a b) := by
          exact Finset.sum_le_sum fun j hj => by
            gcongr
            exact reward_le_rewardTotal h i j
    _ = (∑ j : X, (G.jumpRate i j : ℝ≥0∞)) *
          (∑ a : X, ∑ b : X, h a b) := by
          rw [Finset.sum_mul]
    _ = (G.escapeRate i : ℝ≥0∞) * rewardTotal h := by
          simp [FiniteJumpGenerator.escapeRate, rewardTotal]
    _ ≤ (G.rateBound : ℝ≥0∞) * rewardTotal h := by
          gcongr
          exact_mod_cast G.escapeRate_le_rateBound i

/-- On every finite-jump chart the occupation reward is bounded by total elapsed
time times a finite global intensity bound. -/
theorem sectorHoldingReward_le
    (G : FiniteJumpGenerator X) (h : X → X → ℝ≥0∞)
    {n : ℕ} (γ : JumpPath X n) :
    sectorHoldingReward G h γ ≤
      (JumpPath.totalHoldingTime γ : ℝ≥0∞) *
        ((G.rateBound : ℝ≥0∞) * rewardTotal h) := by
  unfold sectorHoldingReward JumpPath.totalHoldingTime
  calc
    (∑ i : Fin (n + 1),
        (γ.2 i : ℝ≥0∞) * edgeRewardRate G h (γ.1 i))
        ≤ ∑ i : Fin (n + 1),
            (γ.2 i : ℝ≥0∞) *
              ((G.rateBound : ℝ≥0∞) * rewardTotal h) := by
          exact Finset.sum_le_sum fun i hi => by
            gcongr
            exact edgeRewardRate_le G h _
    _ = (∑ i : Fin (n + 1), (γ.2 i : ℝ≥0∞)) *
          ((G.rateBound : ℝ≥0∞) * rewardTotal h) := by
          rw [Finset.sum_mul]
    _ = ((∑ i : Fin (n + 1), γ.2 i : NNReal) : ℝ≥0∞) *
          ((G.rateBound : ℝ≥0∞) * rewardTotal h) := by simp

theorem fullHoldingReward_le
    (G : FiniteJumpGenerator X) (h : X → X → ℝ≥0∞) (γ : FullPath X) :
    fullHoldingReward G h γ ≤
      (fullTotalHoldingTime γ : ℝ≥0∞) *
        ((G.rateBound : ℝ≥0∞) * rewardTotal h) := by
  rcases γ with ⟨n, γ⟩
  exact sectorHoldingReward_le G h γ

/-- Finite-valued edge rewards have finite expected occupation reward on the
explicit non-explosive path law. -/
theorem lintegral_fullHoldingReward_ne_top
    (G : FiniteJumpGenerator X) (T : NNReal) (x : X)
    (h : X → X → ℝ≥0∞) (hh : ∀ i j, h i j ≠ ∞) :
    (∫⁻ γ, fullHoldingReward G h γ ∂G.pathLawFrom T x) ≠ ∞ := by
  let C : ℝ≥0∞ := (T : ℝ≥0∞) *
    ((G.rateBound : ℝ≥0∞) * rewardTotal h)
  have hCtop : C ≠ ∞ := by
    dsimp [C]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (rewardTotal_ne_top h hh))
  have hle : fullHoldingReward G h ≤ᵐ[G.pathLawFrom T x] fun _ => C := by
    filter_upwards [pathLawFrom_ae_totalHoldingTime G T x] with γ hγ
    calc
      fullHoldingReward G h γ ≤
          (fullTotalHoldingTime γ : ℝ≥0∞) *
            ((G.rateBound : ℝ≥0∞) * rewardTotal h) :=
        fullHoldingReward_le G h γ
      _ = C := by simp [hγ, C]
  have hlinle :
      (∫⁻ γ, fullHoldingReward G h γ ∂G.pathLawFrom T x) ≤ C := by
    calc
      (∫⁻ γ, fullHoldingReward G h γ ∂G.pathLawFrom T x)
          ≤ ∫⁻ _γ : FullPath X, C ∂G.pathLawFrom T x := lintegral_mono_ae hle
      _ = C := by simp
  exact ne_top_of_le_ne_top hCtop hlinle

/-! Generic finite-state holding rewards used below for the two escape-rate
terms in the signed source likelihood. -/

noncomputable def sectorStateHoldingReward
    (r : X → ℝ≥0∞) {n : ℕ} (γ : JumpPath X n) : ℝ≥0∞ :=
  ∑ i : Fin (n + 1), (γ.2 i : ℝ≥0∞) * r (γ.1 i)

noncomputable def fullStateHoldingReward
    (r : X → ℝ≥0∞) : FullPath X → ℝ≥0∞ :=
  FullPath.weight (fun n => sectorStateHoldingReward r)

noncomputable def stateRewardTotal (r : X → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ i : X, r i

theorem measurable_fullStateHoldingReward (r : X → ℝ≥0∞) :
    Measurable (fullStateHoldingReward r) := by
  apply FullPath.measurable_weight
  intro n
  unfold sectorStateHoldingReward
  fun_prop

theorem stateReward_le_total (r : X → ℝ≥0∞) (i : X) :
    r i ≤ stateRewardTotal r := by
  unfold stateRewardTotal
  exact Finset.single_le_sum (fun j hj => bot_le) (Finset.mem_univ i)

theorem sectorStateHoldingReward_le
    (r : X → ℝ≥0∞) {n : ℕ} (γ : JumpPath X n) :
    sectorStateHoldingReward r γ ≤
      (JumpPath.totalHoldingTime γ : ℝ≥0∞) * stateRewardTotal r := by
  unfold sectorStateHoldingReward JumpPath.totalHoldingTime
  calc
    (∑ i : Fin (n + 1), (γ.2 i : ℝ≥0∞) * r (γ.1 i))
        ≤ ∑ i : Fin (n + 1),
            (γ.2 i : ℝ≥0∞) * stateRewardTotal r := by
          exact Finset.sum_le_sum fun i hi => by
            gcongr
            exact stateReward_le_total r _
    _ = (∑ i : Fin (n + 1), (γ.2 i : ℝ≥0∞)) * stateRewardTotal r := by
          rw [Finset.sum_mul]
    _ = ((∑ i : Fin (n + 1), γ.2 i : NNReal) : ℝ≥0∞) *
          stateRewardTotal r := by simp

theorem fullStateHoldingReward_le
    (r : X → ℝ≥0∞) (γ : FullPath X) :
    fullStateHoldingReward r γ ≤
      (fullTotalHoldingTime γ : ℝ≥0∞) * stateRewardTotal r := by
  rcases γ with ⟨n, γ⟩
  exact sectorStateHoldingReward_le r γ

theorem stateRewardTotal_ne_top
    (r : X → ℝ≥0∞) (hr : ∀ i, r i ≠ ∞) :
    stateRewardTotal r ≠ ∞ := by
  unfold stateRewardTotal
  exact ENNReal.sum_ne_top.mpr fun i hi => hr i

theorem lintegral_fullStateHoldingReward_ne_top
    (G : FiniteJumpGenerator X) (T : NNReal) (x : X)
    (r : X → ℝ≥0∞) (hr : ∀ i, r i ≠ ∞) :
    (∫⁻ γ, fullStateHoldingReward r γ ∂G.pathLawFrom T x) ≠ ∞ := by
  let C : ℝ≥0∞ := (T : ℝ≥0∞) * stateRewardTotal r
  have hCtop : C ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (stateRewardTotal_ne_top r hr)
  have hle : fullStateHoldingReward r ≤ᵐ[G.pathLawFrom T x] fun _ => C := by
    filter_upwards [pathLawFrom_ae_totalHoldingTime G T x] with γ hγ
    calc
      fullStateHoldingReward r γ ≤
          (fullTotalHoldingTime γ : ℝ≥0∞) * stateRewardTotal r :=
        fullStateHoldingReward_le r γ
      _ = C := by simp [hγ, C]
  have hlinle :
      (∫⁻ γ, fullStateHoldingReward r γ ∂G.pathLawFrom T x) ≤ C := by
    calc
      (∫⁻ γ, fullStateHoldingReward r γ ∂G.pathLawFrom T x)
          ≤ ∫⁻ _γ : FullPath X, C ∂G.pathLawFrom T x := lintegral_mono_ae hle
      _ = C := by simp
  exact ne_top_of_le_ne_top hCtop hlinle

theorem integrable_fullStateHoldingReward_toReal
    (G : FiniteJumpGenerator X) (T : NNReal) (x : X)
    (r : X → ℝ≥0∞) (hr : ∀ i, r i ≠ ∞) :
    Integrable (fun γ => (fullStateHoldingReward r γ).toReal)
      (G.pathLawFrom T x) := by
  exact integrable_toReal_of_lintegral_ne_top
    (measurable_fullStateHoldingReward r).aemeasurable
    (lintegral_fullStateHoldingReward_ne_top G T x r hr)

theorem arrivalHoldingReward_le
    (G : FiniteJumpGenerator X) (T : NNReal)
    (h : X → X → ℝ≥0∞) {n : ℕ}
    (states : Fin (n + 1) → X) (u : Fin n → I)
    (hu : u ∈ Simplex.freeSimplexSet n) :
    arrivalHoldingReward G T h states u ≤
      (T : ℝ≥0∞) * ((G.rateBound : ℝ≥0∞) * rewardTotal h) := by
  unfold arrivalHoldingReward
  have hfirstNN :
      (∑ i : Fin n, Simplex.holdingTimesOfFree T u i.castSucc) ≤ T := by
    have hall := Simplex.sum_holdingTimesOfFree T u hu
    rw [Fin.sum_univ_castSucc] at hall
    calc
      (∑ i : Fin n, Simplex.holdingTimesOfFree T u i.castSucc)
          ≤ (∑ i : Fin n, Simplex.holdingTimesOfFree T u i.castSucc) +
              Simplex.holdingTimesOfFree T u (Fin.last n) :=
        le_add_of_nonneg_right bot_le
      _ = T := hall
  calc
    (∑ i : Fin n,
        (Simplex.holdingTimesOfFree T u i.castSucc : ℝ≥0∞) *
          edgeRewardRate G h (states i.castSucc))
        ≤ ∑ i : Fin n,
            (Simplex.holdingTimesOfFree T u i.castSucc : ℝ≥0∞) *
              ((G.rateBound : ℝ≥0∞) * rewardTotal h) := by
          exact Finset.sum_le_sum fun i hi => by
            gcongr
            exact edgeRewardRate_le G h _
    _ = (∑ i : Fin n,
            (Simplex.holdingTimesOfFree T u i.castSucc : ℝ≥0∞)) *
          ((G.rateBound : ℝ≥0∞) * rewardTotal h) := by
          rw [Finset.sum_mul]
    _ ≤ (T : ℝ≥0∞) * ((G.rateBound : ℝ≥0∞) * rewardTotal h) := by
          gcongr
          exact_mod_cast hfirstNN

theorem sequenceHoldingMass_le
    (G : FiniteJumpGenerator X) (T : NNReal)
    (h : X → X → ℝ≥0∞) (hh : ∀ i j, h i j ≠ ∞)
    {n : ℕ} (states : Fin (n + 1) → X) :
    sequenceHoldingMass G T h states ≤
      ((T : ℝ≥0∞) * ((G.rateBound : ℝ≥0∞) * rewardTotal h)) *
        G.sequenceArrivalMass T states := by
  let C : ℝ≥0∞ :=
    (T : ℝ≥0∞) * ((G.rateBound : ℝ≥0∞) * rewardTotal h)
  have hCtop : C ≠ ∞ := by
    dsimp [C]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (rewardTotal_ne_top h hh))
  have hint :
      (∫⁻ u in Simplex.freeSimplexSet n,
          Simplex.cubeExpWeight (G.stateEscapeRates states) T u *
            arrivalHoldingReward G T h states u) ≤
        C * arrivalOn (G.stateEscapeRates states) T := by
    calc
      (∫⁻ u in Simplex.freeSimplexSet n,
          Simplex.cubeExpWeight (G.stateEscapeRates states) T u *
            arrivalHoldingReward G T h states u)
          ≤ ∫⁻ u in Simplex.freeSimplexSet n,
              Simplex.cubeExpWeight (G.stateEscapeRates states) T u * C := by
            apply setLIntegral_mono' (Simplex.measurableSet_freeSimplexSet n)
            intro u hu
            gcongr
            exact arrivalHoldingReward_le G T h states u hu
      _ = C * arrivalOn (G.stateEscapeRates states) T := by
            rw [lintegral_mul_const' _ _ hCtop]
            rw [mul_comm]
            rfl
  unfold sequenceHoldingMass FiniteJumpGenerator.sequenceArrivalMass
  calc
    (T : ℝ≥0∞) ^ n * G.jumpProduct states *
          ∫⁻ u in Simplex.freeSimplexSet n,
            Simplex.cubeExpWeight (G.stateEscapeRates states) T u *
              arrivalHoldingReward G T h states u
        ≤ (T : ℝ≥0∞) ^ n * G.jumpProduct states *
            (C * arrivalOn (G.stateEscapeRates states) T) := by gcongr
    _ = C *
        ((T : ℝ≥0∞) ^ n * G.jumpProduct states *
          arrivalOn (G.stateEscapeRates states) T) := by ring

theorem arrivalHoldingMass_le
    (G : FiniteJumpGenerator X) (T : NNReal) (x : X)
    (h : X → X → ℝ≥0∞) (hh : ∀ i j, h i j ≠ ∞) (n : ℕ) :
    arrivalHoldingMass G T x h n ≤
      ((T : ℝ≥0∞) * ((G.rateBound : ℝ≥0∞) * rewardTotal h)) *
        G.arrivalMassFrom T x n := by
  unfold arrivalHoldingMass FiniteJumpGenerator.arrivalMassFrom
  calc
    (∑ states : Fin (n + 1) → X,
        fixedInitialWeight x (states 0) * sequenceHoldingMass G T h states)
        ≤ ∑ states : Fin (n + 1) → X,
            fixedInitialWeight x (states 0) *
              (((T : ℝ≥0∞) * ((G.rateBound : ℝ≥0∞) * rewardTotal h)) *
                G.sequenceArrivalMass T states) := by
          exact Finset.sum_le_sum fun states hs => by
            gcongr
            exact sequenceHoldingMass_le G T h hh states
    _ = ∑ states : Fin (n + 1) → X,
          ((T : ℝ≥0∞) * ((G.rateBound : ℝ≥0∞) * rewardTotal h)) *
            (fixedInitialWeight x (states 0) * G.sequenceArrivalMass T states) := by
          apply Finset.sum_congr rfl
          intro states hs
          ring
    _ = ((T : ℝ≥0∞) * ((G.rateBound : ℝ≥0∞) * rewardTotal h)) *
          ∑ states : Fin (n + 1) → X,
            fixedInitialWeight x (states 0) * G.sequenceArrivalMass T states := by
          exact (Finset.mul_sum _ _ _).symm

theorem tendsto_arrivalHoldingMass
    (G : FiniteJumpGenerator X) (T : NNReal) (x : X)
    (h : X → X → ℝ≥0∞) (hh : ∀ i j, h i j ≠ ∞) :
    Filter.Tendsto (fun n => arrivalHoldingMass G T x h n)
      Filter.atTop (nhds 0) := by
  let C : ℝ≥0∞ :=
    (T : ℝ≥0∞) * ((G.rateBound : ℝ≥0∞) * rewardTotal h)
  have hCtop : C ≠ ∞ := by
    dsimp [C]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (rewardTotal_ne_top h hh))
  have htail := ENNReal.Tendsto.const_mul (G.tendsto_arrivalMassFrom T x)
    (Or.inr hCtop)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun _ : ℕ => (0 : ℝ≥0∞))
    (h := fun n : ℕ => C * G.arrivalMassFrom T x n)
    tendsto_const_nhds
    (by simpa [C] using htail)
    (fun n => bot_le)
  intro n
  simpa [C] using arrivalHoldingMass_le G T x h hh n

/-! ### Holding-time renewal and Campbell identity -/

theorem holdingExpZeroMomentBalanceReal
    (c ρ : ℝ) (hc : 0 ≤ c) :
    Real.exp (-(c * ρ)) +
        c * (∫ a : ℝ in (0 : ℝ)..ρ, Real.exp (-(c * a))) = 1 := by
  rcases eq_or_lt_of_le hc with rfl | hcpos
  · simp
  · have hcomp :
        (fun x : ℝ => Real.exp (-(c * x))) =
          fun x : ℝ => Real.exp ((-c) * x) := by
      funext x
      congr 1
      ring
    have hc' : -c ≠ 0 := neg_ne_zero.mpr hcpos.ne'
    have hint :
        (∫ x : ℝ in (0 : ℝ)..ρ, Real.exp (-(c * x))) =
          (1 - Real.exp (-(c * ρ))) / c := by
      rw [hcomp]
      rw [intervalIntegral.integral_comp_mul_left
        (a := (0 : ℝ)) (b := ρ) (fun x : ℝ => Real.exp x) hc',
        integral_exp]
      simp only [smul_eq_mul, mul_zero, Real.exp_zero]
      field_simp
      ring
    rw [hint]
    field_simp [hcpos.ne']
    ring

theorem holdingExpFirstMomentBalanceReal
    (c ρ : ℝ) :
    ρ * Real.exp (-(c * ρ)) +
        c * (∫ a : ℝ in (0 : ℝ)..ρ,
          a * Real.exp (-(c * a))) =
      ∫ a : ℝ in (0 : ℝ)..ρ, Real.exp (-(c * a)) := by
  have hu : ∀ x ∈ Set.uIcc (0 : ℝ) ρ,
      HasDerivAt (fun y : ℝ => y) 1 x := by
    intro x hx
    exact hasDerivAt_id' x
  have hv : ∀ x ∈ Set.uIcc (0 : ℝ) ρ,
      HasDerivAt (fun y : ℝ => Real.exp (-(c * y)))
        (-c * Real.exp (-(c * x))) x := by
    intro x hx
    have hlin : HasDerivAt (fun y : ℝ => -(c * y)) (-c) x := by
      simpa [neg_mul] using (hasDerivAt_id' x).const_mul (-c)
    simpa [mul_comm] using hlin.exp
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)
  have hscale :
      (∫ x : ℝ in (0 : ℝ)..ρ,
          x * (-c * Real.exp (-(c * x)))) =
        -c * (∫ x : ℝ in (0 : ℝ)..ρ,
          x * Real.exp (-(c * x))) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  rw [hscale] at hparts
  simp only [one_mul, zero_mul, sub_zero] at hparts
  linarith

theorem holdingExpZeroMomentUnit
    (c ρ : ℝ) (hc : 0 ≤ c) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ENNReal.ofReal (Real.exp (-(c * ρ))) +
        ENNReal.ofReal c *
          ∫⁻ a : I in {a : I | (a : ℝ) ≤ ρ},
            ENNReal.ofReal (Real.exp (-(c * (a : ℝ)))) = 1 := by
  have htrans := Simplex.lintegral_unitInterval_Iic_of_continuous_nonneg
    (fun z : ℝ => Real.exp (-(c * z))) ρ hρ0 hρ1
    (by fun_prop) (fun z hz => (Real.exp_pos _).le)
  have hintnn :
      0 ≤ ∫ z : ℝ in (0 : ℝ)..ρ, Real.exp (-(c * z)) := by
    exact intervalIntegral.integral_nonneg hρ0 fun z hz => (Real.exp_pos _).le
  rw [htrans, ← ENNReal.ofReal_mul hc,
    ← ENNReal.ofReal_add (Real.exp_nonneg _) (mul_nonneg hc hintnn)]
  rw [holdingExpZeroMomentBalanceReal c ρ hc]
  simp

theorem holdingExpFirstMomentBalanceUnit
    (c ρ : ℝ) (hc : 0 ≤ c) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ENNReal.ofReal ρ * ENNReal.ofReal (Real.exp (-(c * ρ))) +
        ENNReal.ofReal c *
          ∫⁻ a : I in {a : I | (a : ℝ) ≤ ρ},
            ENNReal.ofReal ((a : ℝ) * Real.exp (-(c * (a : ℝ)))) =
      ∫⁻ a : I in {a : I | (a : ℝ) ≤ ρ},
        ENNReal.ofReal (Real.exp (-(c * (a : ℝ)))) := by
  have htrans0 := Simplex.lintegral_unitInterval_Iic_of_continuous_nonneg
    (fun z : ℝ => Real.exp (-(c * z))) ρ hρ0 hρ1
    (by fun_prop) (fun z hz => (Real.exp_pos _).le)
  have htrans1 := Simplex.lintegral_unitInterval_Iic_of_continuous_nonneg
    (fun z : ℝ => z * Real.exp (-(c * z))) ρ hρ0 hρ1
    (by fun_prop) (fun z hz => mul_nonneg hz.1 (Real.exp_nonneg _))
  have hint1nn :
      0 ≤ ∫ z : ℝ in (0 : ℝ)..ρ,
        z * Real.exp (-(c * z)) := by
    exact intervalIntegral.integral_nonneg hρ0 fun z hz =>
      mul_nonneg hz.1 (Real.exp_nonneg _)
  have hρexp :
      ENNReal.ofReal ρ * ENNReal.ofReal (Real.exp (-(c * ρ))) =
        ENNReal.ofReal (ρ * Real.exp (-(c * ρ))) := by
    rw [ENNReal.ofReal_mul hρ0]
  rw [htrans0, htrans1, hρexp, ← ENNReal.ofReal_mul hc,
    ← ENNReal.ofReal_add (mul_nonneg hρ0 (Real.exp_nonneg _))
      (mul_nonneg hc hint1nn)]
  rw [holdingExpFirstMomentBalanceReal c ρ]

theorem holdingWeightedRenewalSection
    (c ρ : ℝ) (τ H w : ℝ≥0∞)
    (hc : 0 ≤ c) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ENNReal.ofReal (Real.exp (-(c * ρ))) *
          (H + τ * ENNReal.ofReal ρ * w) +
        ENNReal.ofReal c *
          (∫⁻ a : I in {a : I | (a : ℝ) ≤ ρ},
            ENNReal.ofReal (Real.exp (-(c * (a : ℝ)))) *
              (H + τ * ENNReal.ofReal (a : ℝ) * w)) =
      H + τ * w *
        (∫⁻ a : I in {a : I | (a : ℝ) ≤ ρ},
          ENNReal.ofReal (Real.exp (-(c * (a : ℝ))))) := by
  let S : Set I := {a : I | (a : ℝ) ≤ ρ}
  let I0 : ℝ≥0∞ :=
    ∫⁻ a : I in S, ENNReal.ofReal (Real.exp (-(c * (a : ℝ))))
  let I1 : ℝ≥0∞ :=
    ∫⁻ a : I in S,
      ENNReal.ofReal (Real.exp (-(c * (a : ℝ)))) * ENNReal.ofReal (a : ℝ)
  have hsplit :
      (∫⁻ a : I in S,
          ENNReal.ofReal (Real.exp (-(c * (a : ℝ)))) *
            (H + τ * ENNReal.ofReal (a : ℝ) * w)) =
        I0 * H + I1 * (τ * w) := by
    have hmeas0 : Measurable fun a : I =>
        ENNReal.ofReal (Real.exp (-(c * (a : ℝ)))) * H := by
      fun_prop
    have hfun :
        (fun a : I =>
          ENNReal.ofReal (Real.exp (-(c * (a : ℝ)))) *
            (H + τ * ENNReal.ofReal (a : ℝ) * w)) =
        (fun a : I =>
          ENNReal.ofReal (Real.exp (-(c * (a : ℝ)))) * H +
            (ENNReal.ofReal (Real.exp (-(c * (a : ℝ)))) *
              ENNReal.ofReal (a : ℝ)) * (τ * w)) := by
      funext a
      ring
    rw [hfun]
    rw [lintegral_add_left hmeas0]
    rw [lintegral_mul_const H (by fun_prop)]
    rw [lintegral_mul_const (τ * w) (by fun_prop)]
  have hzero := holdingExpZeroMomentUnit c ρ hc hρ0 hρ1
  have hfirst := holdingExpFirstMomentBalanceUnit c ρ hc hρ0 hρ1
  have hI1 : I1 =
      ∫⁻ a : I in S,
        ENNReal.ofReal ((a : ℝ) * Real.exp (-(c * (a : ℝ)))) := by
    apply setLIntegral_congr_fun
      (measurableSet_le (by fun_prop) measurable_const)
    intro a ha
    change ENNReal.ofReal (Real.exp (-(c * (a : ℝ)))) *
        ENNReal.ofReal (a : ℝ) =
      ENNReal.ofReal ((a : ℝ) * Real.exp (-(c * (a : ℝ))))
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    congr 1
    ring
  change ENNReal.ofReal (Real.exp (-(c * ρ))) *
        (H + τ * ENNReal.ofReal ρ * w) +
      ENNReal.ofReal c *
        (∫⁻ a : I in S,
          ENNReal.ofReal (Real.exp (-(c * (a : ℝ)))) *
            (H + τ * ENNReal.ofReal (a : ℝ) * w)) =
    H + τ * w * I0
  rw [hsplit]
  change ENNReal.ofReal (Real.exp (-(c * ρ))) +
      ENNReal.ofReal c * I0 = 1 at hzero
  change ENNReal.ofReal ρ * ENNReal.ofReal (Real.exp (-(c * ρ))) +
      ENNReal.ofReal c *
        (∫⁻ a : I in S,
          ENNReal.ofReal ((a : ℝ) * Real.exp (-(c * (a : ℝ))))) = I0 at hfirst
  rw [← hI1] at hfirst
  calc
    ENNReal.ofReal (Real.exp (-(c * ρ))) *
          (H + τ * ENNReal.ofReal ρ * w) +
        ENNReal.ofReal c * (I0 * H + I1 * (τ * w)) =
      H * (ENNReal.ofReal (Real.exp (-(c * ρ))) +
          ENNReal.ofReal c * I0) +
        (τ * w) *
          (ENNReal.ofReal ρ * ENNReal.ofReal (Real.exp (-(c * ρ))) +
            ENNReal.ofReal c * I1) := by ring
    _ = H + τ * w * I0 := by rw [hzero, hfirst]; simp

theorem mem_freeSimplexSet_iff {m : ℕ} (u : Fin m → I) :
    u ∈ Simplex.freeSimplexSet m ↔ (∑ i, ((u i : ℝ))) ≤ 1 := by
  simp [Simplex.freeSimplexSet]

/-- Fubini peel of the last free simplex coordinate with an arbitrary
nonnegative measurable mark. -/
theorem lintegral_cubeExpWeight_succ_weighted
    {n : ℕ} (r : Fin (n + 1) → NNReal) (T : NNReal)
    (Q : (Fin (n + 1) → I) → ℝ≥0∞) (hQ : Measurable Q) :
    (∫⁻ u in Simplex.freeSimplexSet (n + 1),
        Simplex.cubeExpWeight r T u * Q u) =
      ∫⁻ v in Simplex.freeSimplexSet n,
        Simplex.cubeExpWeight (fun i : Fin n => r i.castSucc) T v *
          (∫⁻ a : I in {a : I | (a : ℝ) ≤ Simplex.residual v},
            ENNReal.ofReal
              (Real.exp
                (-((r (Fin.last n) : ℝ) * (T : ℝ) * (a : ℝ)))) *
              Q (Fin.snoc v a : Fin (n + 1) → I)) := by
  classical
  set c : NNReal := r (Fin.last n) with hc
  set F : I × (Fin n → I) → ℝ≥0∞ := fun p =>
    Set.indicator
      {q : I × (Fin n → I) |
        (q.1 : ℝ) + ∑ i, ((q.2 i : ℝ)) ≤ 1}
      (fun q =>
        Simplex.cubeExpWeight (fun i : Fin n => r i.castSucc) T q.2 *
          ENNReal.ofReal
            (Real.exp (-((c : ℝ) * (T : ℝ) * (q.1 : ℝ)))) *
          Q (Fin.snoc q.2 q.1 : Fin (n + 1) → I)) p
    with hFdef
  have hsnocMeas : Measurable
      (fun q : I × (Fin n → I) =>
        (Fin.snoc q.2 q.1 : Fin (n + 1) → I)) := by
    fun_prop
  have hFmeas : Measurable F := by
    have hbase : Measurable fun q : I × (Fin n → I) =>
        Simplex.cubeExpWeight (fun i : Fin n => r i.castSucc) T q.2 *
          ENNReal.ofReal
            (Real.exp (-((c : ℝ) * (T : ℝ) * (q.1 : ℝ)))) *
          Q (Fin.snoc q.2 q.1 : Fin (n + 1) → I) := by
      apply Measurable.mul
      · apply Measurable.mul
        · exact (Simplex.measurable_cubeExpWeight
            (fun i : Fin n => r i.castSucc) T).comp measurable_snd
        · fun_prop
      · exact hQ.comp hsnocMeas
    exact hbase.indicator (measurableSet_le (by fun_prop) measurable_const)
  have hmp := MeasureTheory.volume_preserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => I) (Fin.last n)
  set e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => I) (Fin.last n) with he
  have happly : ∀ u : Fin (n + 1) → I,
      e u = (u (Fin.last n), fun j : Fin n => u j.castSucc) := by
    intro u
    simp only [he, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv,
      MeasurableEquiv.coe_mk, Equiv.symm_mk, Equiv.coe_fn_mk]
    refine congrArg (Prod.mk _) ?_
    funext j
    simp [Fin.removeNth_apply, Fin.succAbove_last]
  have hFe : ∀ u : Fin (n + 1) → I,
      F (e u) =
        (Simplex.freeSimplexSet (n + 1)).indicator
          (fun u => Simplex.cubeExpWeight r T u * Q u) u := by
    intro u
    rw [happly u]
    by_cases hu : u ∈ Simplex.freeSimplexSet (n + 1)
    · have hsum := (mem_freeSimplexSet_iff u).1 hu
      rw [Fin.sum_univ_castSucc] at hsum
      have hmem :
          ((u (Fin.last n), fun j : Fin n => u j.castSucc) :
              I × (Fin n → I)) ∈
            {q : I × (Fin n → I) |
              (q.1 : ℝ) + ∑ i, ((q.2 i : ℝ)) ≤ 1} := by
        change ((u (Fin.last n) : ℝ)) +
            ∑ j : Fin n, ((u j.castSucc : ℝ)) ≤ 1
        linarith
      simp only [hFdef]
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hu]
      unfold Simplex.cubeExpWeight
      rw [Fin.prod_univ_castSucc]
      have hsnoc :
          Fin.snoc (fun j : Fin n => u j.castSucc) (u (Fin.last n)) = u := by
        change Fin.snoc (Fin.init u) (u (Fin.last n)) = u
        exact Fin.snoc_init_self u
      rw [hsnoc]
    · have hnotmem :
          ((u (Fin.last n), fun j : Fin n => u j.castSucc) :
              I × (Fin n → I)) ∉
            {q : I × (Fin n → I) |
              (q.1 : ℝ) + ∑ i, ((q.2 i : ℝ)) ≤ 1} := by
        intro hmem'
        apply hu
        rw [mem_freeSimplexSet_iff, Fin.sum_univ_castSucc]
        have : ((u (Fin.last n) : ℝ)) +
            ∑ j : Fin n, ((u j.castSucc : ℝ)) ≤ 1 := hmem'
        linarith
      simp only [hFdef]
      rw [Set.indicator_of_notMem hnotmem, Set.indicator_of_notMem hu]
  have hsection : ∀ v : Fin n → I,
      ∫⁻ a : I, F (a, v) =
        (Simplex.freeSimplexSet n).indicator
          (fun v : Fin n → I =>
            Simplex.cubeExpWeight (fun i : Fin n => r i.castSucc) T v *
              (∫⁻ a : I in {a : I | (a : ℝ) ≤ Simplex.residual v},
                ENNReal.ofReal
                  (Real.exp (-((c : ℝ) * (T : ℝ) * (a : ℝ)))) *
                  Q (Fin.snoc v a : Fin (n + 1) → I))) v := by
    intro v
    by_cases hv : v ∈ Simplex.freeSimplexSet n
    · have hsum : (∑ i, ((v i : ℝ))) ≤ 1 :=
        (mem_freeSimplexSet_iff v).1 hv
      have hsum0 : 0 ≤ ∑ i, ((v i : ℝ)) :=
        Finset.sum_nonneg fun i _ => (v i).2.1
      have hres0 : 0 ≤ Simplex.residual v := by
        unfold Simplex.residual
        linarith
      have hFav : ∀ a : I,
          F (a, v) =
            ({a : I | (a : ℝ) ≤ Simplex.residual v}).indicator
              (fun a : I =>
                Simplex.cubeExpWeight (fun i : Fin n => r i.castSucc) T v *
                  (ENNReal.ofReal
                    (Real.exp (-((c : ℝ) * (T : ℝ) * (a : ℝ)))) *
                    Q (Fin.snoc v a : Fin (n + 1) → I))) a := by
        intro a
        simp only [hFdef]
        by_cases ha : (a : ℝ) ≤ Simplex.residual v
        · have hmem' : ((a, v) : I × (Fin n → I)) ∈
              {q : I × (Fin n → I) |
                (q.1 : ℝ) + ∑ i, ((q.2 i : ℝ)) ≤ 1} := by
            change (a : ℝ) + ∑ i, ((v i : ℝ)) ≤ 1
            unfold Simplex.residual at ha
            linarith
          rw [Set.indicator_of_mem hmem',
            Set.indicator_of_mem
              (show a ∈ {a : I | (a : ℝ) ≤ Simplex.residual v} from ha)]
          ring
        · have hnotmem' : ((a, v) : I × (Fin n → I)) ∉
              {q : I × (Fin n → I) |
                (q.1 : ℝ) + ∑ i, ((q.2 i : ℝ)) ≤ 1} := by
            intro hmem'
            apply ha
            have : (a : ℝ) + ∑ i, ((v i : ℝ)) ≤ 1 := hmem'
            unfold Simplex.residual
            linarith
          rw [Set.indicator_of_notMem hnotmem',
            Set.indicator_of_notMem
              (show a ∉ {a : I | (a : ℝ) ≤ Simplex.residual v} from ha)]
      have hmeasSec : MeasurableSet
          {a : I | (a : ℝ) ≤ Simplex.residual v} :=
        measurableSet_le (by fun_prop) measurable_const
      have hQv : Measurable
          (fun a : I => Q (Fin.snoc v a : Fin (n + 1) → I)) := by
        apply hQ.comp
        fun_prop
      calc
        (∫⁻ a : I, F (a, v)) =
            ∫⁻ a : I in {a : I | (a : ℝ) ≤ Simplex.residual v},
              Simplex.cubeExpWeight (fun i : Fin n => r i.castSucc) T v *
                (ENNReal.ofReal
                  (Real.exp (-((c : ℝ) * (T : ℝ) * (a : ℝ)))) *
                  Q (Fin.snoc v a : Fin (n + 1) → I)) := by
              rw [lintegral_congr hFav, lintegral_indicator hmeasSec]
        _ = Simplex.cubeExpWeight (fun i : Fin n => r i.castSucc) T v *
              (∫⁻ a : I in {a : I | (a : ℝ) ≤ Simplex.residual v},
                ENNReal.ofReal
                  (Real.exp (-((c : ℝ) * (T : ℝ) * (a : ℝ)))) *
                  Q (Fin.snoc v a : Fin (n + 1) → I)) := by
              rw [lintegral_const_mul _ ((by fun_prop : Measurable fun a : I =>
                ENNReal.ofReal
                  (Real.exp (-((c : ℝ) * (T : ℝ) * (a : ℝ)))) *
                  Q (Fin.snoc v a : Fin (n + 1) → I)))]
        _ = (Simplex.freeSimplexSet n).indicator
              (fun v : Fin n → I =>
                Simplex.cubeExpWeight (fun i : Fin n => r i.castSucc) T v *
                  (∫⁻ a : I in {a : I | (a : ℝ) ≤ Simplex.residual v},
                    ENNReal.ofReal
                      (Real.exp (-((c : ℝ) * (T : ℝ) * (a : ℝ)))) *
                      Q (Fin.snoc v a : Fin (n + 1) → I))) v := by
              rw [Set.indicator_of_mem hv]
    · have h0 : ∀ a : I, F (a, v) = 0 := by
        intro a
        simp only [hFdef]
        apply Set.indicator_of_notMem
        intro hmem'
        apply hv
        rw [mem_freeSimplexSet_iff]
        have h1 : (a : ℝ) + ∑ i, ((v i : ℝ)) ≤ 1 := hmem'
        have h2 : 0 ≤ (a : ℝ) := a.2.1
        linarith
      rw [Set.indicator_of_notMem hv]
      simp [h0]
  calc
    (∫⁻ u in Simplex.freeSimplexSet (n + 1),
        Simplex.cubeExpWeight r T u * Q u) =
      ∫⁻ u,
        (Simplex.freeSimplexSet (n + 1)).indicator
          (fun u => Simplex.cubeExpWeight r T u * Q u) u := by
            rw [lintegral_indicator
              (Simplex.measurableSet_freeSimplexSet (n + 1))]
    _ = ∫⁻ u, F (e u) := by
          exact lintegral_congr fun u => (hFe u).symm
    _ = ∫⁻ p, F p := by
          rw [hmp.lintegral_comp hFmeas]
    _ = ∫⁻ v : Fin n → I, ∫⁻ a : I, F (a, v) := by
          rw [Measure.volume_eq_prod,
            lintegral_prod_symm F hFmeas.aemeasurable]
    _ = ∫⁻ v : Fin n → I,
          (Simplex.freeSimplexSet n).indicator
            (fun v : Fin n → I =>
              Simplex.cubeExpWeight (fun i : Fin n => r i.castSucc) T v *
                (∫⁻ a : I in {a : I | (a : ℝ) ≤ Simplex.residual v},
                  ENNReal.ofReal
                    (Real.exp (-((c : ℝ) * (T : ℝ) * (a : ℝ)))) *
                    Q (Fin.snoc v a : Fin (n + 1) → I))) v :=
          lintegral_congr hsection
    _ = ∫⁻ v in Simplex.freeSimplexSet n,
          Simplex.cubeExpWeight (fun i : Fin n => r i.castSucc) T v *
            (∫⁻ a : I in {a : I | (a : ℝ) ≤ Simplex.residual v},
              ENNReal.ofReal
                (Real.exp
                  (-((r (Fin.last n) : ℝ) * (T : ℝ) * (a : ℝ)))) *
                Q (Fin.snoc v a : Fin (n + 1) → I)) := by
          rw [lintegral_indicator (Simplex.measurableSet_freeSimplexSet n)]

theorem measurable_weightedPeelSection
    {n : ℕ} (c T : NNReal)
    (Q : (Fin (n + 1) → I) → ℝ≥0∞) (hQ : Measurable Q) :
    Measurable fun v : Fin n → I =>
      ∫⁻ a : I in {a : I | (a : ℝ) ≤ Simplex.residual v},
        ENNReal.ofReal
          (Real.exp (-((c : ℝ) * (T : ℝ) * (a : ℝ)))) *
          Q (Fin.snoc v a : Fin (n + 1) → I) := by
  let F : (Fin n → I) × I → ℝ≥0∞ := fun p =>
    Set.indicator
      {q : (Fin n → I) × I | (q.2 : ℝ) ≤ Simplex.residual q.1}
      (fun q =>
        ENNReal.ofReal
          (Real.exp (-((c : ℝ) * (T : ℝ) * (q.2 : ℝ)))) *
          Q (Fin.snoc q.1 q.2 : Fin (n + 1) → I)) p
  have hsnoc : Measurable
      (fun q : (Fin n → I) × I =>
        (Fin.snoc q.1 q.2 : Fin (n + 1) → I)) := by
    fun_prop
  have hF : Measurable F := by
    have hbase : Measurable fun q : (Fin n → I) × I =>
        ENNReal.ofReal
            (Real.exp (-((c : ℝ) * (T : ℝ) * (q.2 : ℝ)))) *
          Q (Fin.snoc q.1 q.2 : Fin (n + 1) → I) := by
      have hexp : Measurable fun q : (Fin n → I) × I =>
          ENNReal.ofReal
            (Real.exp (-((c : ℝ) * (T : ℝ) * (q.2 : ℝ)))) := by
        fun_prop
      exact hexp.mul (hQ.comp hsnoc)
    exact hbase.indicator (measurableSet_le (by fun_prop) (by fun_prop))
  have hlin : Measurable fun v : Fin n → I =>
      ∫⁻ a : I, F (v, a) := by
    exact hF.lintegral_prod_right'
  convert hlin using 1
  funext v
  change
    (∫⁻ a : I in {a : I | (a : ℝ) ≤ Simplex.residual v},
      ENNReal.ofReal
        (Real.exp (-((c : ℝ) * (T : ℝ) * (a : ℝ)))) *
        Q (Fin.snoc v a : Fin (n + 1) → I)) =
      ∫⁻ a : I,
        ({a : I | (a : ℝ) ≤ Simplex.residual v}).indicator
          (fun a =>
            ENNReal.ofReal
              (Real.exp (-((c : ℝ) * (T : ℝ) * (a : ℝ)))) *
            Q (Fin.snoc v a : Fin (n + 1) → I)) a
  rw [lintegral_indicator (measurableSet_le (by fun_prop) measurable_const)]

theorem terminalHolding_eq
    (T : NNReal) {n : ℕ} (v : Fin n → I)
    (hv : v ∈ Simplex.freeSimplexSet n) :
    (Simplex.holdingTimesOfFree T v (Fin.last n) : ℝ≥0∞) =
      (T : ℝ≥0∞) * ENNReal.ofReal (Simplex.residual v) := by
  have hsum : (∑ i, (v i : ℝ)) ≤ 1 :=
    (mem_freeSimplexSet_iff v).1 hv
  have hres0 : 0 ≤ Simplex.residual v := by
    unfold Simplex.residual
    have hnon : 0 ≤ ∑ i, (v i : ℝ) :=
      Finset.sum_nonneg fun i hi => (v i).2.1
    linarith
  have hscaled :
      (∑ i : Fin n, T * Simplex.unitNNReal (v i)) ≤ T := by
    have hsumNN : (∑ i : Fin n, Simplex.unitNNReal (v i)) ≤ (1 : NNReal) := by
      have hsum' :
          (∑ i : Fin n, (Simplex.unitNNReal (v i) : ℝ)) ≤ 1 := by
        simpa only [Simplex.coe_unitNNReal] using hsum
      exact_mod_cast hsum'
    rw [← Finset.mul_sum]
    simpa using mul_le_mul_right hsumNN T
  have hreal :
      (Simplex.holdingTimesOfFree T v (Fin.last n) : ℝ) =
        (T : ℝ) * Simplex.residual v := by
    unfold Simplex.holdingTimesOfFree
    rw [Fin.snoc_last, NNReal.coe_sub hscaled, NNReal.coe_sum]
    simp_rw [NNReal.coe_mul, Simplex.coe_unitNNReal]
    unfold Simplex.residual
    rw [← Finset.mul_sum]
    ring
  calc
    (Simplex.holdingTimesOfFree T v (Fin.last n) : ℝ≥0∞) =
        ENNReal.ofReal
          (Simplex.holdingTimesOfFree T v (Fin.last n) : ℝ) := by
      rw [ENNReal.ofReal_coe_nnreal]
    _ = ENNReal.ofReal ((T : ℝ) * Simplex.residual v) := by rw [hreal]
    _ = ENNReal.ofReal (T : ℝ) * ENNReal.ofReal (Simplex.residual v) := by
      rw [ENNReal.ofReal_mul (NNReal.coe_nonneg T)]
    _ = (T : ℝ≥0∞) * ENNReal.ofReal (Simplex.residual v) := by
      rw [ENNReal.ofReal_coe_nnreal]

theorem holdingRewardSum_decomp
    (G : FiniteJumpGenerator X) (T : NNReal)
    (h : X → X → ℝ≥0∞) {n : ℕ}
    (states : Fin (n + 1) → X) (v : Fin n → I) :
    (∑ i : Fin (n + 1),
        (Simplex.holdingTimesOfFree T v i : ℝ≥0∞) *
          edgeRewardRate G h (states i)) =
      arrivalHoldingReward G T h states v +
        (Simplex.holdingTimesOfFree T v (Fin.last n) : ℝ≥0∞) *
          edgeRewardRate G h (states (Fin.last n)) := by
  unfold arrivalHoldingReward
  rw [Fin.sum_univ_castSucc]

theorem arrivalHoldingReward_succ_decomp
    (G : FiniteJumpGenerator X) (T : NNReal)
    (h : X → X → ℝ≥0∞) {n : ℕ}
    (init : Fin (n + 1) → X) (z : X) (u : Fin (n + 1) → I) :
    arrivalHoldingReward G T h (Fin.snoc init z) u =
      arrivalHoldingReward G T h init (fun i : Fin n => u i.castSucc) +
        (T : ℝ≥0∞) * ENNReal.ofReal (u (Fin.last n) : ℝ) *
          edgeRewardRate G h (init (Fin.last n)) := by
  unfold arrivalHoldingReward
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    simp [Simplex.holdingTimesOfFree]
  · change
      (Simplex.holdingTimesOfFree T u (Fin.last n).castSucc : ℝ≥0∞) *
          edgeRewardRate G h
            ((Fin.snoc init z : Fin (n + 2) → X) (Fin.last n).castSucc) =
        (T : ℝ≥0∞) * ENNReal.ofReal (u (Fin.last n) : ℝ) *
          edgeRewardRate G h (init (Fin.last n))
    rw [show Simplex.holdingTimesOfFree T u (Fin.last n).castSucc =
        T * Simplex.unitNNReal (u (Fin.last n)) by
          simp [Simplex.holdingTimesOfFree],
      Fin.snoc_castSucc]
    change
      ((T * Simplex.unitNNReal (u (Fin.last n)) : NNReal) : ℝ≥0∞) *
          edgeRewardRate G h (init (Fin.last n)) =
        (T : ℝ≥0∞) * ENNReal.ofReal (u (Fin.last n) : ℝ) *
          edgeRewardRate G h (init (Fin.last n))
    rw [ENNReal.coe_mul,
      ENNReal.ofReal_eq_coe_nnreal (u (Fin.last n)).2.1]
    congr 2

theorem holdingRenewalCore
    {n : ℕ} (r : Fin (n + 1) → NNReal) (T : NNReal)
    (H : (Fin n → I) → ℝ≥0∞) (hH : Measurable H) (w : ℝ≥0∞) :
    (∫⁻ v in Simplex.freeSimplexSet n,
        Simplex.cubeExpWeight (fun i : Fin n => r i.castSucc) T v *
          ENNReal.ofReal
            (Real.exp
              (-((r (Fin.last n) : ℝ) * (T : ℝ) * Simplex.residual v))) *
          (H v + (T : ℝ≥0∞) * ENNReal.ofReal (Simplex.residual v) * w)) +
      ((r (Fin.last n) : ℝ≥0∞) * (T : ℝ≥0∞)) *
        (∫⁻ u in Simplex.freeSimplexSet (n + 1),
          Simplex.cubeExpWeight r T u *
            (H (fun i : Fin n => u i.castSucc) +
              (T : ℝ≥0∞) * ENNReal.ofReal (u (Fin.last n) : ℝ) * w)) =
    (∫⁻ v in Simplex.freeSimplexSet n,
        Simplex.cubeExpWeight (fun i : Fin n => r i.castSucc) T v * H v) +
      (T : ℝ≥0∞) * w * arrivalOn r T := by
  let c : NNReal := r (Fin.last n)
  let Q : (Fin (n + 1) → I) → ℝ≥0∞ := fun u =>
    H (fun i : Fin n => u i.castSucc) +
      (T : ℝ≥0∞) * ENNReal.ofReal (u (Fin.last n) : ℝ) * w
  have hQ : Measurable Q := by
    dsimp [Q]
    exact (hH.comp (by fun_prop)).add (by fun_prop)
  have hpeel := lintegral_cubeExpWeight_succ_weighted r T Q hQ
  have hpeel1 := lintegral_cubeExpWeight_succ_weighted r T
    (fun _ : Fin (n + 1) → I => (1 : ℝ≥0∞)) (by fun_prop)
  have hinner : Measurable fun v : Fin n → I =>
      ∫⁻ a : I in {a : I | (a : ℝ) ≤ Simplex.residual v},
        ENNReal.ofReal
          (Real.exp (-((c : ℝ) * (T : ℝ) * (a : ℝ)))) *
          Q (Fin.snoc v a : Fin (n + 1) → I) :=
    measurable_weightedPeelSection c T Q hQ
  have hinner1 : Measurable fun v : Fin n → I =>
      ∫⁻ a : I in {a : I | (a : ℝ) ≤ Simplex.residual v},
        ENNReal.ofReal
          (Real.exp (-((c : ℝ) * (T : ℝ) * (a : ℝ)))) := by
    have h := measurable_weightedPeelSection c T
      (fun _ : Fin (n + 1) → I => (1 : ℝ≥0∞)) (by fun_prop)
    simpa using h
  have hcTtop :
      (r (Fin.last n) : ℝ≥0∞) * (T : ℝ≥0∞) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
  have hTwtop : (T : ℝ≥0∞) * w = ∞ ∨ (T : ℝ≥0∞) * w ≠ ∞ :=
    eq_or_ne _ _
  rw [hpeel]
  have hcCast :
      ((r (Fin.last n) : ℝ≥0∞) * (T : ℝ≥0∞)) =
        ENNReal.ofReal ((c : ℝ) * (T : ℝ)) := by
    dsimp [c]
    rw [← ENNReal.coe_mul, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_mul]
  have hleftMeas : Measurable fun v : Fin n → I =>
      Simplex.cubeExpWeight (fun i : Fin n => r i.castSucc) T v *
        ENNReal.ofReal
          (Real.exp
            (-((r (Fin.last n) : ℝ) * (T : ℝ) * Simplex.residual v))) *
        (H v + (T : ℝ≥0∞) * ENNReal.ofReal (Simplex.residual v) * w) := by
    fun_prop
  rw [← lintegral_const_mul' _ _ hcTtop]
  rw [← lintegral_add_left hleftMeas]
  have hpoint : ∀ v ∈ Simplex.freeSimplexSet n,
      Simplex.cubeExpWeight (fun i : Fin n => r i.castSucc) T v *
            ENNReal.ofReal
              (Real.exp
                (-((r (Fin.last n) : ℝ) * (T : ℝ) * Simplex.residual v))) *
            (H v + (T : ℝ≥0∞) * ENNReal.ofReal (Simplex.residual v) * w) +
          ((r (Fin.last n) : ℝ≥0∞) * (T : ℝ≥0∞)) *
            (Simplex.cubeExpWeight (fun i : Fin n => r i.castSucc) T v *
              (∫⁻ a : I in {a : I | (a : ℝ) ≤ Simplex.residual v},
                ENNReal.ofReal
                  (Real.exp (-((c : ℝ) * (T : ℝ) * (a : ℝ)))) *
                  Q (Fin.snoc v a : Fin (n + 1) → I))) =
        Simplex.cubeExpWeight (fun i : Fin n => r i.castSucc) T v *
          (H v + (T : ℝ≥0∞) * w *
            (∫⁻ a : I in {a : I | (a : ℝ) ≤ Simplex.residual v},
              ENNReal.ofReal
                (Real.exp (-((c : ℝ) * (T : ℝ) * (a : ℝ)))))) := by
    intro v hv
    have hsum : (∑ i, (v i : ℝ)) ≤ 1 :=
      (mem_freeSimplexSet_iff v).1 hv
    have hsum0 : 0 ≤ ∑ i, (v i : ℝ) :=
      Finset.sum_nonneg fun i hi => (v i).2.1
    have hρ0 : 0 ≤ Simplex.residual v := by
      unfold Simplex.residual
      linarith
    have hρ1 : Simplex.residual v ≤ 1 := by
      unfold Simplex.residual
      linarith
    have hsec := holdingWeightedRenewalSection
      ((c : ℝ) * (T : ℝ)) (Simplex.residual v)
      (T : ℝ≥0∞) (H v) w (by positivity) hρ0 hρ1
    have hQeval : ∀ a : I,
        Q (Fin.snoc v a : Fin (n + 1) → I) =
          H v + (T : ℝ≥0∞) * ENNReal.ofReal (a : ℝ) * w := by
      intro a
      dsimp [Q]
      congr 1
      · congr 1
        funext i
        simp
      · simp
    have hinnerQeq :
        (∫⁻ a : I in {a : I | (a : ℝ) ≤ Simplex.residual v},
            ENNReal.ofReal
              (Real.exp (-((c : ℝ) * (T : ℝ) * (a : ℝ)))) *
            Q (Fin.snoc v a : Fin (n + 1) → I)) =
          ∫⁻ a : I in {a : I | (a : ℝ) ≤ Simplex.residual v},
            ENNReal.ofReal
              (Real.exp (-((c : ℝ) * (T : ℝ) * (a : ℝ)))) *
            (H v + (T : ℝ≥0∞) * ENNReal.ofReal (a : ℝ) * w) := by
      apply setLIntegral_congr_fun
        (measurableSet_le (by fun_prop) measurable_const)
      intro a ha
      change
        ENNReal.ofReal
            (Real.exp (-((c : ℝ) * (T : ℝ) * (a : ℝ)))) *
            Q (Fin.snoc v a : Fin (n + 1) → I) =
          ENNReal.ofReal
            (Real.exp (-((c : ℝ) * (T : ℝ) * (a : ℝ)))) *
            (H v + (T : ℝ≥0∞) * ENNReal.ofReal (a : ℝ) * w)
      rw [hQeval a]
    dsimp [c] at hsec
    rw [← hcCast] at hsec
    rw [hinnerQeq]
    calc
      _ = Simplex.cubeExpWeight (fun i : Fin n => r i.castSucc) T v *
          (ENNReal.ofReal
              (Real.exp
                (-((r (Fin.last n) : ℝ) * (T : ℝ) * Simplex.residual v))) *
              (H v + (T : ℝ≥0∞) * ENNReal.ofReal (Simplex.residual v) * w) +
            ((r (Fin.last n) : ℝ≥0∞) * (T : ℝ≥0∞)) *
              (∫⁻ a : I in {a : I | (a : ℝ) ≤ Simplex.residual v},
                ENNReal.ofReal
                  (Real.exp (-((c : ℝ) * (T : ℝ) * (a : ℝ)))) *
                  (H v + (T : ℝ≥0∞) * ENNReal.ofReal (a : ℝ) * w))) := by
            ring
      _ = _ := by rw [hsec]
  rw [setLIntegral_congr_fun (Simplex.measurableSet_freeSimplexSet n) hpoint]
  dsimp [c]
  have harrivalPeel :
      arrivalOn r T =
        ∫⁻ v in Simplex.freeSimplexSet n,
          Simplex.cubeExpWeight (fun i : Fin n => r i.castSucc) T v *
            (∫⁻ a : I in {a : I | (a : ℝ) ≤ Simplex.residual v},
              ENNReal.ofReal
                (Real.exp
                  (-((r (Fin.last n) : ℝ) * (T : ℝ) * (a : ℝ))))) := by
    unfold arrivalOn
    simpa only [mul_one] using hpeel1
  rw [harrivalPeel]
  dsimp [c] at hinner1
  have hrightMeas : Measurable fun v : Fin n → I =>
      Simplex.cubeExpWeight (fun i : Fin n => r i.castSucc) T v * H v := by
    fun_prop
  have hsecondMeas : Measurable fun v : Fin n → I =>
      Simplex.cubeExpWeight (fun i : Fin n => r i.castSucc) T v *
        (∫⁻ a : I in {a : I | (a : ℝ) ≤ Simplex.residual v},
          ENNReal.ofReal
            (Real.exp
              (-((r (Fin.last n) : ℝ) * (T : ℝ) * (a : ℝ))))) := by
    exact (Simplex.measurable_cubeExpWeight
      (fun i : Fin n => r i.castSucc) T).mul hinner1
  rw [← lintegral_const_mul ((T : ℝ≥0∞) * w) hsecondMeas]
  rw [← lintegral_add_left hrightMeas]
  apply setLIntegral_congr_fun (Simplex.measurableSet_freeSimplexSet n)
  intro v hv
  ring

theorem sequenceHoldingMass_recurrence
    (G : FiniteJumpGenerator X) (T : NNReal)
    (h : X → X → ℝ≥0∞) {n : ℕ}
    (init : Fin (n + 1) → X) :
    sequenceSectorHoldingMass G T h init +
        ∑ z : X, sequenceHoldingMass G T h (Fin.snoc init z) =
      sequenceHoldingMass G T h init +
        sequenceOccupationMass G T init *
          edgeRewardRate G h (init (Fin.last n)) := by
  let r : Fin (n + 1) → NNReal := fun i => G.escapeRate (init i)
  let H : (Fin n → I) → ℝ≥0∞ := arrivalHoldingReward G T h init
  let w : ℝ≥0∞ := edgeRewardRate G h (init (Fin.last n))
  have hH : Measurable H := by
    dsimp [H, arrivalHoldingReward]
    apply Finset.measurable_sum
    intro i hi
    exact (by fun_prop)
  have hcore := holdingRenewalCore r T H hH w
  have hsector :
      (∫⁻ v in Simplex.freeSimplexSet n,
          Simplex.cubeExpWeight (G.stateEscapeRates init) T v *
            ENNReal.ofReal
              (Real.exp
                (-((G.escapeRate (init (Fin.last n)) : ℝ) *
                  (T : ℝ) * Simplex.residual v))) *
            (∑ i : Fin (n + 1),
              (Simplex.holdingTimesOfFree T v i : ℝ≥0∞) *
                edgeRewardRate G h (init i))) =
        ∫⁻ v in Simplex.freeSimplexSet n,
          Simplex.cubeExpWeight (fun i : Fin n => r i.castSucc) T v *
            ENNReal.ofReal
              (Real.exp
                (-((r (Fin.last n) : ℝ) *
                  (T : ℝ) * Simplex.residual v))) *
            (H v + (T : ℝ≥0∞) *
              ENNReal.ofReal (Simplex.residual v) * w) := by
    apply setLIntegral_congr_fun (Simplex.measurableSet_freeSimplexSet n)
    intro v hv
    have hsum := holdingRewardSum_decomp G T h init v
    have hterminal := terminalHolding_eq T v hv
    change
      Simplex.cubeExpWeight (G.stateEscapeRates init) T v *
          ENNReal.ofReal
            (Real.exp
              (-((G.escapeRate (init (Fin.last n)) : ℝ) *
                (T : ℝ) * Simplex.residual v))) *
          (∑ i : Fin (n + 1),
            (Simplex.holdingTimesOfFree T v i : ℝ≥0∞) *
              edgeRewardRate G h (init i)) =
        Simplex.cubeExpWeight (fun i : Fin n => r i.castSucc) T v *
          ENNReal.ofReal
            (Real.exp
              (-((r (Fin.last n) : ℝ) *
                (T : ℝ) * Simplex.residual v))) *
          (H v + (T : ℝ≥0∞) *
            ENNReal.ofReal (Simplex.residual v) * w)
    rw [hsum, hterminal]
    rfl
  have hsucc : ∀ z : X,
      (∫⁻ u in Simplex.freeSimplexSet (n + 1),
          Simplex.cubeExpWeight
              (G.stateEscapeRates (Fin.snoc init z)) T u *
            arrivalHoldingReward G T h (Fin.snoc init z) u) =
        ∫⁻ u in Simplex.freeSimplexSet (n + 1),
          Simplex.cubeExpWeight r T u *
            (H (fun i : Fin n => u i.castSucc) +
              (T : ℝ≥0∞) * ENNReal.ofReal (u (Fin.last n) : ℝ) * w) := by
    intro z
    apply setLIntegral_congr_fun
      (Simplex.measurableSet_freeSimplexSet (n + 1))
    intro u hu
    change
      Simplex.cubeExpWeight
          (G.stateEscapeRates (Fin.snoc init z)) T u *
          arrivalHoldingReward G T h (Fin.snoc init z) u =
        Simplex.cubeExpWeight r T u *
          (H (fun i : Fin n => u i.castSucc) +
            (T : ℝ≥0∞) * ENNReal.ofReal (u (Fin.last n) : ℝ) * w)
    rw [G.stateEscapeRates_snoc init z]
    rw [arrivalHoldingReward_succ_decomp G T h init z u]
  unfold sequenceSectorHoldingMass sequenceHoldingMass sequenceOccupationMass
  rw [hsector]
  simp_rw [G.jumpProduct_snoc init]
  simp_rw [hsucc]
  have hsumRates :
      (∑ z : X, (G.jumpRate (init (Fin.last n)) z : ℝ≥0∞)) =
        (G.escapeRate (init (Fin.last n)) : ℝ≥0∞) := by
    simp [FiniteJumpGenerator.escapeRate]
  have hsumSucc :
      (∑ z : X,
        (T : ℝ≥0∞) ^ (n + 1) *
          (G.jumpProduct init *
            (G.jumpRate (init (Fin.last n)) z : ℝ≥0∞)) *
          (∫⁻ u in Simplex.freeSimplexSet (n + 1),
            Simplex.cubeExpWeight r T u *
              (H (fun i : Fin n => u i.castSucc) +
                (T : ℝ≥0∞) * ENNReal.ofReal (u (Fin.last n) : ℝ) * w))) =
        ((T : ℝ≥0∞) ^ n * G.jumpProduct init) *
          (((r (Fin.last n) : ℝ≥0∞) * (T : ℝ≥0∞)) *
            (∫⁻ u in Simplex.freeSimplexSet (n + 1),
              Simplex.cubeExpWeight r T u *
                (H (fun i : Fin n => u i.castSucc) +
                  (T : ℝ≥0∞) * ENNReal.ofReal (u (Fin.last n) : ℝ) * w))) := by
    rw [← Finset.sum_mul]
    rw [← Finset.mul_sum]
    rw [← Finset.mul_sum]
    rw [hsumRates]
    dsimp [r]
    rw [pow_succ]
    ring
  rw [hsumSucc]
  change
    ((T : ℝ≥0∞) ^ n * G.jumpProduct init) *
        (∫⁻ v in Simplex.freeSimplexSet n,
          Simplex.cubeExpWeight (fun i : Fin n => r i.castSucc) T v *
            ENNReal.ofReal
              (Real.exp
                (-((r (Fin.last n) : ℝ) * (T : ℝ) * Simplex.residual v))) *
            (H v + (T : ℝ≥0∞) * ENNReal.ofReal (Simplex.residual v) * w)) +
      ((T : ℝ≥0∞) ^ n * G.jumpProduct init) *
        (((r (Fin.last n) : ℝ≥0∞) * (T : ℝ≥0∞)) *
          (∫⁻ u in Simplex.freeSimplexSet (n + 1),
            Simplex.cubeExpWeight r T u *
              (H (fun i : Fin n => u i.castSucc) +
                (T : ℝ≥0∞) * ENNReal.ofReal (u (Fin.last n) : ℝ) * w))) =
      ((T : ℝ≥0∞) ^ n * G.jumpProduct init) *
        (∫⁻ v in Simplex.freeSimplexSet n,
          Simplex.cubeExpWeight (fun i : Fin n => r i.castSucc) T v * H v) +
        ((T : ℝ≥0∞) ^ (n + 1) * G.jumpProduct init *
          arrivalOn r T) * w
  rw [← mul_add]
  rw [hcore]
  rw [pow_succ]
  ring

theorem sectorHoldingMass_add_arrivalHoldingMass_succ
    (G : FiniteJumpGenerator X) (T : NNReal) (x : X)
    (h : X → X → ℝ≥0∞) (n : ℕ) :
    sectorHoldingMass G T x h n + arrivalHoldingMass G T x h (n + 1) =
      arrivalHoldingMass G T x h n + nextJumpRewardMass G T x h n := by
  have hreindex :
      arrivalHoldingMass G T x h (n + 1) =
        ∑ init : Fin (n + 1) → X,
          fixedInitialWeight x (init 0) *
            ∑ z : X, sequenceHoldingMass G T h (Fin.snoc init z) := by
    unfold arrivalHoldingMass
    rw [← Fintype.sum_equiv (FiniteJumpGenerator.snocEquiv X n)
      (fun p : (Fin (n + 1) → X) × X =>
        fixedInitialWeight x
            ((Fin.snoc p.1 p.2 : Fin (n + 2) → X) 0) *
          sequenceHoldingMass G T h (Fin.snoc p.1 p.2))
      _ (fun p => rfl)]
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun init _ => by
      simp [FiniteJumpGenerator.snoc_zero, Finset.mul_sum]
  rw [hreindex]
  unfold sectorHoldingMass arrivalHoldingMass nextJumpRewardMass
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro init hinit
  rw [← mul_add, sequenceHoldingMass_recurrence G T h init]
  ring

theorem sum_sectorHoldingMass_add_arrivalHoldingMass
    (G : FiniteJumpGenerator X) (T : NNReal) (x : X)
    (h : X → X → ℝ≥0∞) (N : ℕ) :
    (∑ n ∈ Finset.range N, sectorHoldingMass G T x h n) +
        arrivalHoldingMass G T x h N =
      ∑ n ∈ Finset.range N, nextJumpRewardMass G T x h n := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, add_assoc,
        sectorHoldingMass_add_arrivalHoldingMass_succ G T x h N,
        ← add_assoc, ih]

theorem tsum_sectorHoldingMass_eq_tsum_nextJumpRewardMass
    (G : FiniteJumpGenerator X) (T : NNReal) (x : X)
    (h : X → X → ℝ≥0∞) (hh : ∀ i j, h i j ≠ ∞) :
    (∑' n, sectorHoldingMass G T x h n) =
      ∑' n, nextJumpRewardMass G T x h n := by
  have hsector :
      Filter.Tendsto
        (fun N => ∑ n ∈ Finset.range N, sectorHoldingMass G T x h n)
        Filter.atTop (nhds (∑' n, sectorHoldingMass G T x h n)) :=
    ENNReal.tendsto_nat_tsum _
  have harrival := tendsto_arrivalHoldingMass G T x h hh
  have hleft :
      Filter.Tendsto
        (fun N =>
          (∑ n ∈ Finset.range N, sectorHoldingMass G T x h n) +
            arrivalHoldingMass G T x h N)
        Filter.atTop (nhds (∑' n, sectorHoldingMass G T x h n)) := by
    have hlim := hsector.add harrival
    simpa using hlim
  have hright :
      Filter.Tendsto
        (fun N => ∑ n ∈ Finset.range N, nextJumpRewardMass G T x h n)
        Filter.atTop (nhds (∑' n, nextJumpRewardMass G T x h n)) :=
    ENNReal.tendsto_nat_tsum _
  have heq :
      (fun N =>
        (∑ n ∈ Finset.range N, sectorHoldingMass G T x h n) +
          arrivalHoldingMass G T x h N) =
      (fun N => ∑ n ∈ Finset.range N, nextJumpRewardMass G T x h n) := by
    funext N
    exact sum_sectorHoldingMass_add_arrivalHoldingMass G T x h N
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

theorem lintegral_fullHoldingReward_eq_tsum_nextJumpRewardMass
    (G : FiniteJumpGenerator X) (T : NNReal) (x : X)
    (h : X → X → ℝ≥0∞) (hh : ∀ i j, h i j ≠ ∞) :
    ∫⁻ γ, fullHoldingReward G h γ ∂G.pathLawFrom T x =
      ∑' n, nextJumpRewardMass G T x h n := by
  rw [lintegral_fullHoldingReward_eq_tsum_sectorHoldingMass G T x h]
  exact tsum_sectorHoldingMass_eq_tsum_nextJumpRewardMass G T x h hh



/-- Full-path reference obtained by summing the rate-independent references over
all finite jump counts. -/
noncomputable def fullReference
    (G : FiniteJumpGenerator X) (T : NNReal) : Measure (FullPath X) :=
  FullPath.measure (G.rawCountingReference T)

/-- The full reference is independent of the generator. -/
theorem fullReference_eq
    (G H : FiniteJumpGenerator X) (T : NNReal) :
    fullReference G T = fullReference H T := by
  unfold fullReference FiniteJumpGenerator.rawCountingReference
    FiniteJumpGenerator.stateSequenceCountingReference
  rfl

/-- Full-path density assembled from the sector densities. -/
noncomputable def fullDensity
    (G : FiniteJumpGenerator X) (x : X) : FullPath X → ℝ≥0∞ :=
  FullPath.weight (fun n => sectorDensity G x n)

theorem measurable_fullDensity
    (G : FiniteJumpGenerator X) (x : X) :
    Measurable (fullDensity G x) := by
  exact FullPath.measurable_weight _ (fun n => measurable_sectorDensity G x n)

theorem fullDensity_ne_top
    (G : FiniteJumpGenerator X) (x : X) (γ : FullPath X) :
    fullDensity G x γ ≠ ∞ := by
  rcases γ with ⟨n, γ⟩
  exact sectorDensity_ne_top G x n γ

theorem fullDensity_support_mono
    (Gu G0 : FiniteJumpGenerator X)
    (hsupport : SupportIncluded Gu G0)
    (x : X) (γ : FullPath X) :
    fullDensity Gu x γ ≠ 0 →
      fullDensity G0 x γ ≠ 0 := by
  rcases γ with ⟨n, γ⟩
  exact sectorDensity_support_mono Gu G0 hsupport x n γ

/-- The explicit CTMC path law is a density against one full, rate-independent
reference measure. -/
theorem pathLawFrom_eq_fullReference_withDensity
    (G Gref : FiniteJumpGenerator X) (T : NNReal) (x : X) :
    G.pathLawFrom T x =
      (fullReference Gref T).withDensity (fullDensity G x) := by
  rw [fullReference_eq Gref G T]
  unfold FiniteJumpGenerator.pathLawFrom fullReference fullDensity FullPath.measure
  rw [MeasureTheory.withDensity_sum]
  congr 1
  funext n
  rw [FullPath.liftMeasure_withDensity n
    (G.rawCountingReference T n) (sectorDensity G x)
    (fun m => measurable_sectorDensity G x m)]
  rfl

/-- Likelihood density of the controlled path law with respect to the baseline
path law.  Support inclusion makes this finite on every controlled-supported
path. -/
noncomputable def pathLikelihood
    (Gu G0 : FiniteJumpGenerator X) (x : X) :
    FullPath X → ℝ≥0∞ :=
  fun γ => fullDensity Gu x γ / fullDensity G0 x γ

theorem measurable_pathLikelihood
    (Gu G0 : FiniteJumpGenerator X) (x : X) :
    Measurable (pathLikelihood Gu G0 x) := by
  exact (measurable_fullDensity Gu x).div (measurable_fullDensity G0 x)

theorem pathLikelihood_ne_top
    (Gu G0 : FiniteJumpGenerator X)
    (hsupport : SupportIncluded Gu G0)
    (x : X) (γ : FullPath X) :
    pathLikelihood Gu G0 x γ ≠ ∞ := by
  unfold pathLikelihood
  by_cases hu0 : fullDensity Gu x γ = 0
  · simp [hu0]
  · exact ENNReal.div_ne_top
      (fullDensity_ne_top Gu x γ)
      (fullDensity_support_mono Gu G0 hsupport x γ hu0)

/-- Log likelihood on one fixed-jump-count sector. -/
noncomputable def sectorLogLikelihood
    (Gu G0 : FiniteJumpGenerator X) {n : ℕ} (γ : JumpPath X n) : ℝ :=
  sectorLogDensity Gu γ - sectorLogDensity G0 γ

/-- Source convention for the logarithmic rate ratio.  A zero controlled rate
contributes zero because such an edge is never taken under the controlled path
law. -/
noncomputable def jumpLogRatio
    (Gu G0 : FiniteJumpGenerator X) (i j : X) : ℝ :=
  if Gu.jumpRate i j = 0 then 0
  else Real.log ((Gu.jumpRate i j : ℝ) / (G0.jumpRate i j : ℝ))

/-- Positive part of the logarithmic jump-rate ratio, packaged as a finite
nonnegative edge reward for the Campbell identity. -/
noncomputable def jumpLogPos
    (Gu G0 : FiniteJumpGenerator X) (i j : X) : ℝ≥0∞ :=
  ENNReal.ofReal (jumpLogRatio Gu G0 i j)

/-- Negative part of the logarithmic jump-rate ratio, packaged as a finite
nonnegative edge reward for the Campbell identity. -/
noncomputable def jumpLogNeg
    (Gu G0 : FiniteJumpGenerator X) (i j : X) : ℝ≥0∞ :=
  ENNReal.ofReal (-jumpLogRatio Gu G0 i j)

theorem jumpLogPos_ne_top
    (Gu G0 : FiniteJumpGenerator X) (i j : X) :
    jumpLogPos Gu G0 i j ≠ ∞ := by
  simp [jumpLogPos]

theorem jumpLogNeg_ne_top
    (Gu G0 : FiniteJumpGenerator X) (i j : X) :
    jumpLogNeg Gu G0 i j ≠ ∞ := by
  simp [jumpLogNeg]

theorem jumpLogRatio_eq_pos_sub_neg
    (Gu G0 : FiniteJumpGenerator X) (i j : X) :
    jumpLogRatio Gu G0 i j =
      (jumpLogPos Gu G0 i j).toReal - (jumpLogNeg Gu G0 i j).toReal := by
  rw [jumpLogPos, jumpLogNeg, ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
  exact (max_zero_sub_max_neg_zero_eq_self (jumpLogRatio Gu G0 i j)).symm

/-- One edge of the frozen §22.4 CTMC entropy-production integrand.  The
`jumpLogRatio` convention makes the `lᵘ=0` contribution exactly `l⁰`. -/
noncomputable def sourceEdgeCost
    (Gu G0 : FiniteJumpGenerator X) (i j : X) : ℝ :=
  (Gu.jumpRate i j : ℝ) * jumpLogRatio Gu G0 i j -
    (Gu.jumpRate i j : ℝ) + (G0.jumpRate i j : ℝ)

/-- Frozen §22.4 instantaneous rate integrand at one state. -/
noncomputable def sourceRateIntegrand
    (Gu G0 : FiniteJumpGenerator X) (i : X) : ℝ :=
  ∑ j : X, sourceEdgeCost Gu G0 i j

theorem sourceEdgeCost_eq_klFun
    (Gu G0 : FiniteJumpGenerator X)
    (hsupport : SupportIncluded Gu G0) (i j : X) :
    sourceEdgeCost Gu G0 i j =
      (G0.jumpRate i j : ℝ) *
        klFun ((Gu.jumpRate i j : ℝ) / (G0.jumpRate i j : ℝ)) := by
  by_cases hu : Gu.jumpRate i j = 0
  · have huR : (Gu.jumpRate i j : ℝ) = 0 := by simp [hu]
    simp [sourceEdgeCost, jumpLogRatio, hu, huR, klFun_zero]
  · have hup : 0 < Gu.jumpRate i j := bot_lt_iff_ne_bot.mpr hu
    have h0p : 0 < G0.jumpRate i j := hsupport i j hup
    have h0 : (G0.jumpRate i j : ℝ) ≠ 0 := by exact_mod_cast h0p.ne'
    rw [sourceEdgeCost, jumpLogRatio, if_neg hu, klFun_apply]
    rw [Real.log_div (by exact_mod_cast hu) h0]
    field_simp [h0]
    ring

theorem sourceEdgeCost_nonneg
    (Gu G0 : FiniteJumpGenerator X)
    (hsupport : SupportIncluded Gu G0) (i j : X) :
    0 ≤ sourceEdgeCost Gu G0 i j := by
  rw [sourceEdgeCost_eq_klFun Gu G0 hsupport i j]
  exact mul_nonneg (by positivity)
    (klFun_nonneg (div_nonneg (by positivity) (by positivity)))

theorem sourceRateIntegrand_nonneg
    (Gu G0 : FiniteJumpGenerator X)
    (hsupport : SupportIncluded Gu G0) (i : X) :
    0 ≤ sourceRateIntegrand Gu G0 i := by
  unfold sourceRateIntegrand
  exact Finset.sum_nonneg fun j hj => sourceEdgeCost_nonneg Gu G0 hsupport i j

/-- The nonnegative ENNReal packaging of the frozen instantaneous source
integrand. -/
noncomputable def sourceRateReward
    (Gu G0 : FiniteJumpGenerator X) (i : X) : ℝ≥0∞ :=
  ENNReal.ofReal (sourceRateIntegrand Gu G0 i)

theorem sourceRateReward_ne_top
    (Gu G0 : FiniteJumpGenerator X) (i : X) :
    sourceRateReward Gu G0 i ≠ ∞ := by
  simp [sourceRateReward]

/-- Holding-time form of the frozen source integrand on one jump sector. -/
noncomputable def sectorSourceRateHolding
    (Gu G0 : FiniteJumpGenerator X) {n : ℕ} (γ : JumpPath X n) : ℝ :=
  holdingRealReward (sourceRateIntegrand Gu G0) γ

noncomputable def fullSourceRateHolding
    (Gu G0 : FiniteJumpGenerator X) : FullPath X → ℝ
  | ⟨n, γ⟩ => sectorSourceRateHolding Gu G0 γ

theorem sectorSourceRateHolding_eq_toReal
    (Gu G0 : FiniteJumpGenerator X)
    (hsupport : SupportIncluded Gu G0) {n : ℕ} (γ : JumpPath X n) :
    sectorSourceRateHolding Gu G0 γ =
      (sectorStateHoldingReward (sourceRateReward Gu G0) γ).toReal := by
  unfold sectorSourceRateHolding holdingRealReward sectorStateHoldingReward
  rw [ENNReal.toReal_sum (fun a ha =>
    ENNReal.mul_ne_top ENNReal.coe_ne_top
      (sourceRateReward_ne_top Gu G0 (γ.1 a)))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ENNReal.toReal_mul]
  simp [sourceRateReward,
    ENNReal.toReal_ofReal (sourceRateIntegrand_nonneg Gu G0 hsupport _)]

theorem fullSourceRateHolding_eq_toReal
    (Gu G0 : FiniteJumpGenerator X)
    (hsupport : SupportIncluded Gu G0) (γ : FullPath X) :
    fullSourceRateHolding Gu G0 γ =
      (fullStateHoldingReward (sourceRateReward Gu G0) γ).toReal := by
  rcases γ with ⟨n, γ⟩
  exact sectorSourceRateHolding_eq_toReal Gu G0 hsupport γ

theorem integrable_fullSourceRateHolding
    (Gu G0 : FiniteJumpGenerator X)
    (hsupport : SupportIncluded Gu G0) (T : NNReal) (x : X) :
    Integrable (fullSourceRateHolding Gu G0) (Gu.pathLawFrom T x) := by
  have hbase := integrable_fullStateHoldingReward_toReal
    Gu T x (sourceRateReward Gu G0) (sourceRateReward_ne_top Gu G0)
  exact hbase.congr (ae_of_all _ fun γ =>
    (fullSourceRateHolding_eq_toReal Gu G0 hsupport γ).symm)

/-- Literal clock-time form of the source integrand along the real-time step
trajectory. -/
noncomputable def sourceClockIntegral
    (Gu G0 : FiniteJumpGenerator X) (T : NNReal) (γ : FullPath X) : ℝ :=
  ∫ t : ℝ in (0 : ℝ)..(T : ℝ),
    sourceRateIntegrand Gu G0 (FullPath.trajectory γ t)

theorem sourceClockIntegral_eq_holding_of_total
    (Gu G0 : FiniteJumpGenerator X) (T : NNReal) (γ : FullPath X)
    (htotal : fullTotalHoldingTime γ = T) :
    sourceClockIntegral Gu G0 T γ = fullSourceRateHolding Gu G0 γ := by
  rcases γ with ⟨n, γ⟩
  change (∫ t : ℝ in (0 : ℝ)..(T : ℝ),
      sourceRateIntegrand Gu G0 (JumpPath.trajectory γ t)) =
    holdingRealReward (sourceRateIntegrand Gu G0) γ
  have h := trajectory_intervalIntegral_eq_holding
    (sourceRateIntegrand Gu G0) γ
  have hcast : (JumpPath.totalHoldingTime γ : ℝ) = (T : ℝ) := by
    exact_mod_cast htotal
  simpa [hcast] using h

theorem sourceClockIntegral_ae_eq_holding
    (Gu G0 : FiniteJumpGenerator X) (T : NNReal) (x : X) :
    sourceClockIntegral Gu G0 T =ᵐ[Gu.pathLawFrom T x]
      fullSourceRateHolding Gu G0 := by
  filter_upwards [pathLawFrom_ae_totalHoldingTime Gu T x] with γ hγ
  exact sourceClockIntegral_eq_holding_of_total Gu G0 T γ hγ

/-- Sum of the source jump-log terms along a fixed path. -/
noncomputable def sectorJumpLogSum
    (Gu G0 : FiniteJumpGenerator X) {n : ℕ} (γ : JumpPath X n) : ℝ :=
  ∑ i : Fin n, jumpLogRatio Gu G0 (γ.1 i.castSucc) (γ.1 i.succ)

/-- The integrated escape-rate difference on the piecewise-constant chart,
written as the exact holding-time sum. -/
noncomputable def sectorEscapeDifference
    (Gu G0 : FiniteJumpGenerator X) {n : ℕ} (γ : JumpPath X n) : ℝ :=
  (∑ i : Fin n,
      ((Gu.escapeRate (γ.1 i.castSucc) : ℝ) -
        (G0.escapeRate (γ.1 i.castSucc) : ℝ)) *
          (γ.2 i.castSucc : ℝ)) +
    ((Gu.escapeRate (γ.1 (Fin.last n)) : ℝ) -
      (G0.escapeRate (γ.1 (Fin.last n)) : ℝ)) *
        (γ.2 (Fin.last n) : ℝ)

/-- Frozen-source path log-likelihood formula on a fixed sector. -/
noncomputable def sectorSourceLogLikelihood
    (Gu G0 : FiniteJumpGenerator X) {n : ℕ} (γ : JumpPath X n) : ℝ :=
  sectorJumpLogSum Gu G0 γ - sectorEscapeDifference Gu G0 γ

theorem sectorLogLikelihood_eq_source
    (Gu G0 : FiniteJumpGenerator X)
    (hsupport : SupportIncluded Gu G0)
    (x : X) {n : ℕ} (γ : JumpPath X n)
    (hu : sectorDensity Gu x n γ ≠ 0) :
    sectorLogLikelihood Gu G0 γ = sectorSourceLogLikelihood Gu G0 γ := by
  have hju := (sectorDensity_ne_zero_iff Gu x n γ).mp hu |>.2
  have hj0 : ∀ i : Fin n,
      G0.jumpRate (γ.1 i.castSucc) (γ.1 i.succ) ≠ 0 := by
    intro i
    exact (hsupport _ _ (bot_lt_iff_ne_bot.mpr (hju i))).ne'
  unfold sectorLogLikelihood sectorLogDensity sectorSourceLogLikelihood
    sectorJumpLogSum sectorEscapeDifference jumpLogRatio
  have hlog : ∀ i : Fin n,
      Real.log (Gu.jumpRate (γ.1 i.castSucc) (γ.1 i.succ) : ℝ) -
          Real.log (G0.jumpRate (γ.1 i.castSucc) (γ.1 i.succ) : ℝ) =
        (if Gu.jumpRate (γ.1 i.castSucc) (γ.1 i.succ) = 0 then 0
          else Real.log
            ((Gu.jumpRate (γ.1 i.castSucc) (γ.1 i.succ) : ℝ) /
              (G0.jumpRate (γ.1 i.castSucc) (γ.1 i.succ) : ℝ))) := by
    intro i
    simp only [hju i, if_false]
    rw [Real.log_div (by exact_mod_cast hju i) (by exact_mod_cast hj0 i)]
  have hsum :
      (∑ i : Fin n,
          Real.log (Gu.jumpRate (γ.1 i.castSucc) (γ.1 i.succ) : ℝ)) -
        ∑ i : Fin n,
          Real.log (G0.jumpRate (γ.1 i.castSucc) (γ.1 i.succ) : ℝ) =
      ∑ i : Fin n,
        (if Gu.jumpRate (γ.1 i.castSucc) (γ.1 i.succ) = 0 then 0
          else Real.log
            ((Gu.jumpRate (γ.1 i.castSucc) (γ.1 i.succ) : ℝ) /
              (G0.jumpRate (γ.1 i.castSucc) (γ.1 i.succ) : ℝ))) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => hlog i)
  have hesc :
      (∑ i : Fin n,
          (Gu.escapeRate (γ.1 i.castSucc) : ℝ) * (γ.2 i.castSucc : ℝ)) -
        ∑ i : Fin n,
          (G0.escapeRate (γ.1 i.castSucc) : ℝ) * (γ.2 i.castSucc : ℝ) =
      ∑ i : Fin n,
        ((Gu.escapeRate (γ.1 i.castSucc) : ℝ) -
          (G0.escapeRate (γ.1 i.castSucc) : ℝ)) *
            (γ.2 i.castSucc : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  calc
    _ = ((∑ i : Fin n,
            Real.log (Gu.jumpRate (γ.1 i.castSucc) (γ.1 i.succ) : ℝ)) -
          ∑ i : Fin n,
            Real.log (G0.jumpRate (γ.1 i.castSucc) (γ.1 i.succ) : ℝ)) -
        (((∑ i : Fin n,
              (Gu.escapeRate (γ.1 i.castSucc) : ℝ) * (γ.2 i.castSucc : ℝ)) -
            ∑ i : Fin n,
              (G0.escapeRate (γ.1 i.castSucc) : ℝ) * (γ.2 i.castSucc : ℝ)) +
          (((Gu.escapeRate (γ.1 (Fin.last n)) : ℝ) -
              (G0.escapeRate (γ.1 (Fin.last n)) : ℝ)) *
                (γ.2 (Fin.last n) : ℝ))) := by ring
    _ = _ := by rw [hsum, hesc]

/-- The same observable assembled on the full finite-jump path space. -/
noncomputable def fullLogLikelihood
    (Gu G0 : FiniteJumpGenerator X) : FullPath X → ℝ
  | ⟨n, γ⟩ => sectorLogLikelihood Gu G0 γ

noncomputable def fullSourceLogLikelihood
    (Gu G0 : FiniteJumpGenerator X) : FullPath X → ℝ
  | ⟨n, γ⟩ => sectorSourceLogLikelihood Gu G0 γ

theorem log_pathLikelihood_mk_eq
    (Gu G0 : FiniteJumpGenerator X)
    (hsupport : SupportIncluded Gu G0)
    (x : X) (n : ℕ) (γ : JumpPath X n)
    (hu : sectorDensity Gu x n γ ≠ 0) :
    Real.log (pathLikelihood Gu G0 x ⟨n, γ⟩).toReal =
      sectorLogLikelihood Gu G0 γ := by
  have h0 : sectorDensity G0 x n γ ≠ 0 :=
    sectorDensity_support_mono Gu G0 hsupport x n γ hu
  have hu_top := sectorDensity_ne_top Gu x n γ
  have h0_top := sectorDensity_ne_top G0 x n γ
  change Real.log ((sectorDensity Gu x n γ / sectorDensity G0 x n γ).toReal) = _
  rw [ENNReal.toReal_div,
    Real.log_div ((ENNReal.toReal_ne_zero.mpr ⟨hu, hu_top⟩))
      (ENNReal.toReal_ne_zero.mpr ⟨h0, h0_top⟩),
    log_sectorDensity_toReal Gu x n γ hu,
    log_sectorDensity_toReal G0 x n γ h0]
  rfl

theorem pathLawFrom_eq_baseline_withDensity
    (Gu G0 : FiniteJumpGenerator X)
    (hsupport : SupportIncluded Gu G0)
    (T : NNReal) (x : X) :
    Gu.pathLawFrom T x =
      (G0.pathLawFrom T x).withDensity (pathLikelihood Gu G0 x) := by
  rw [pathLawFrom_eq_fullReference_withDensity Gu G0 T x,
    pathLawFrom_eq_fullReference_withDensity G0 G0 T x]
  exact withDensity_factor_div
    (fullReference G0 T) (fullDensity Gu x) (fullDensity G0 x)
    (measurable_fullDensity Gu x) (measurable_fullDensity G0 x)
    (fullDensity_ne_top G0 x)
    (fullDensity_support_mono Gu G0 hsupport x)

theorem pathLawFrom_absolutelyContinuous
    (Gu G0 : FiniteJumpGenerator X)
    (hsupport : SupportIncluded Gu G0)
    (T : NNReal) (x : X) :
    Gu.pathLawFrom T x ≪ G0.pathLawFrom T x := by
  rw [pathLawFrom_eq_fullReference_withDensity Gu G0 T x,
    pathLawFrom_eq_fullReference_withDensity G0 G0 T x]
  exact withDensity_ac_of_support
    (fullReference G0 T) (fullDensity Gu x) (fullDensity G0 x)
    (measurable_fullDensity Gu x) (measurable_fullDensity G0 x)
    (fullDensity_ne_top G0 x)
    (fullDensity_support_mono Gu G0 hsupport x)

theorem rnDeriv_pathLawFrom_eq_pathLikelihood
    (Gu G0 : FiniteJumpGenerator X)
    (hsupport : SupportIncluded Gu G0)
    (T : NNReal) (x : X) :
    (Gu.pathLawFrom T x).rnDeriv (G0.pathLawFrom T x)
      =ᵐ[G0.pathLawFrom T x] pathLikelihood Gu G0 x := by
  rw [pathLawFrom_eq_baseline_withDensity Gu G0 hsupport T x]
  exact Measure.rnDeriv_withDensity _ (measurable_pathLikelihood Gu G0 x)

/-- Under its own path law the physical density is nonzero almost surely.  This
is the precise fact that lets the logarithmic likelihood algebra discard paths
containing a zero controlled jump rate. -/
theorem pathLawFrom_ae_fullDensity_ne_zero
    (G : FiniteJumpGenerator X) (T : NNReal) (x : X) :
    ∀ᵐ γ ∂G.pathLawFrom T x, fullDensity G x γ ≠ 0 := by
  rw [pathLawFrom_eq_fullReference_withDensity G G T x]
  rw [ae_withDensity_iff (measurable_fullDensity G x)]
  filter_upwards [] with γ hγ
  exact hγ

/-- Mathlib's log-likelihood ratio is the logarithm of the explicit CTMC path
likelihood, controlled-law almost everywhere. -/
theorem llr_pathLawFrom_eq_log_pathLikelihood
    (Gu G0 : FiniteJumpGenerator X)
    (hsupport : SupportIncluded Gu G0)
    (T : NNReal) (x : X) :
    llr (Gu.pathLawFrom T x) (G0.pathLawFrom T x)
      =ᵐ[Gu.pathLawFrom T x]
        fun γ => Real.log (pathLikelihood Gu G0 x γ).toReal := by
  have hac := pathLawFrom_absolutelyContinuous Gu G0 hsupport T x
  have hrn := hac.ae_le
    (rnDeriv_pathLawFrom_eq_pathLikelihood Gu G0 hsupport T x)
  filter_upwards [hrn] with γ hγ
  simp [llr, hγ]

/-- Under the controlled path law, Mathlib's log-likelihood ratio is exactly the
frozen-source jump-log minus escape-rate observable. -/
theorem llr_pathLawFrom_eq_fullSourceLogLikelihood
    (Gu G0 : FiniteJumpGenerator X)
    (hsupport : SupportIncluded Gu G0)
    (T : NNReal) (x : X) :
    llr (Gu.pathLawFrom T x) (G0.pathLawFrom T x)
      =ᵐ[Gu.pathLawFrom T x] fullSourceLogLikelihood Gu G0 := by
  filter_upwards [llr_pathLawFrom_eq_log_pathLikelihood Gu G0 hsupport T x,
    pathLawFrom_ae_fullDensity_ne_zero Gu T x] with γ hllr hden
  rw [hllr]
  rcases γ with ⟨n, γ⟩
  change Real.log (pathLikelihood Gu G0 x ⟨n, γ⟩).toReal =
    sectorSourceLogLikelihood Gu G0 γ
  rw [log_pathLikelihood_mk_eq Gu G0 hsupport x n γ hden]
  exact sectorLogLikelihood_eq_source Gu G0 hsupport x γ hden


/-! ### Signed KL recombination and frozen P-KL-04 -/

/-- Finite-state nonnegative Campbell identity on the explicit CTMC path law. -/
theorem lintegral_fullJumpReward_eq_fullHoldingReward
    (G : FiniteJumpGenerator X) (T : NNReal) (x : X)
    (h : X → X → ℝ≥0∞) (hh : ∀ i j, h i j ≠ ∞) :
    (∫⁻ γ, fullJumpReward h γ ∂G.pathLawFrom T x) =
      ∫⁻ γ, fullHoldingReward G h γ ∂G.pathLawFrom T x := by
  rw [lintegral_fullJumpReward_eq_tsum_sectorJumpMass G T x h hh,
    tsum_sectorJumpMass_eq_tsum_nextJumpRewardMass G T x h hh,
    ← lintegral_fullHoldingReward_eq_tsum_nextJumpRewardMass G T x h hh]

/-- Every realized finite-jump reward is finite when the edge reward is finite. -/
theorem fullJumpReward_ne_top
    (h : X → X → ℝ≥0∞) (hh : ∀ i j, h i j ≠ ∞)
    (γ : FullPath X) :
    fullJumpReward h γ ≠ ∞ := by
  rcases γ with ⟨n, γ⟩
  unfold fullJumpReward FullPath.weight sectorJumpReward
  exact ENNReal.sum_ne_top.mpr fun i hi => hh _ _

theorem edgeRewardRate_ne_top
    (G : FiniteJumpGenerator X) (h : X → X → ℝ≥0∞)
    (hh : ∀ i j, h i j ≠ ∞) (i : X) :
    edgeRewardRate G h i ≠ ∞ := by
  unfold edgeRewardRate
  exact ENNReal.sum_ne_top.mpr fun j hj =>
    ENNReal.mul_ne_top ENNReal.coe_ne_top (hh i j)

theorem fullHoldingReward_ne_top
    (G : FiniteJumpGenerator X) (h : X → X → ℝ≥0∞)
    (hh : ∀ i j, h i j ≠ ∞) (γ : FullPath X) :
    fullHoldingReward G h γ ≠ ∞ := by
  rcases γ with ⟨n, γ⟩
  unfold fullHoldingReward FullPath.weight sectorHoldingReward
  exact ENNReal.sum_ne_top.mpr fun i hi =>
    ENNReal.mul_ne_top ENNReal.coe_ne_top
      (edgeRewardRate_ne_top G h hh _)

theorem integrable_fullHoldingReward_toReal
    (G : FiniteJumpGenerator X) (T : NNReal) (x : X)
    (h : X → X → ℝ≥0∞) (hh : ∀ i j, h i j ≠ ∞) :
    Integrable (fun γ => (fullHoldingReward G h γ).toReal)
      (G.pathLawFrom T x) := by
  exact integrable_toReal_of_lintegral_ne_top
    (measurable_fullHoldingReward G h).aemeasurable
    (lintegral_fullHoldingReward_ne_top G T x h hh)

theorem integrable_fullJumpReward_toReal
    (G : FiniteJumpGenerator X) (T : NNReal) (x : X)
    (h : X → X → ℝ≥0∞) (hh : ∀ i j, h i j ≠ ∞) :
    Integrable (fun γ => (fullJumpReward h γ).toReal)
      (G.pathLawFrom T x) := by
  apply integrable_toReal_of_lintegral_ne_top
    (measurable_fullJumpReward h).aemeasurable
  rw [lintegral_fullJumpReward_eq_fullHoldingReward G T x h hh]
  exact lintegral_fullHoldingReward_ne_top G T x h hh

/-- Real-valued Campbell identity obtained from the finite ENNReal identity. -/
theorem integral_fullJumpReward_eq_fullHoldingReward
    (G : FiniteJumpGenerator X) (T : NNReal) (x : X)
    (h : X → X → ℝ≥0∞) (hh : ∀ i j, h i j ≠ ∞) :
    (∫ γ, (fullJumpReward h γ).toReal ∂G.pathLawFrom T x) =
      ∫ γ, (fullHoldingReward G h γ).toReal ∂G.pathLawFrom T x := by
  rw [integral_toReal
      (measurable_fullJumpReward h).aemeasurable
      (ae_of_all _ fun γ =>
        lt_top_iff_ne_top.mpr (fullJumpReward_ne_top h hh γ)),
    integral_toReal
      (measurable_fullHoldingReward G h).aemeasurable
      (ae_of_all _ fun γ =>
        lt_top_iff_ne_top.mpr (fullHoldingReward_ne_top G h hh γ))]
  exact congrArg ENNReal.toReal
    (lintegral_fullJumpReward_eq_fullHoldingReward G T x h hh)

/-- ENNReal packaging of one escape rate. -/
noncomputable def escapeRateReward
    (G : FiniteJumpGenerator X) (i : X) : ℝ≥0∞ :=
  (G.escapeRate i : ℝ≥0∞)

theorem sectorJumpLogSum_eq_parts
    (Gu G0 : FiniteJumpGenerator X) {n : ℕ} (γ : JumpPath X n) :
    sectorJumpLogSum Gu G0 γ =
      (sectorJumpReward (jumpLogPos Gu G0) γ).toReal -
        (sectorJumpReward (jumpLogNeg Gu G0) γ).toReal := by
  unfold sectorJumpLogSum sectorJumpReward
  rw [ENNReal.toReal_sum (fun i hi => jumpLogPos_ne_top Gu G0 _ _),
      ENNReal.toReal_sum (fun i hi => jumpLogNeg_ne_top Gu G0 _ _),
      ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i hi =>
    jumpLogRatio_eq_pos_sub_neg Gu G0 _ _

theorem sectorStateHolding_escape_toReal
    (G : FiniteJumpGenerator X) {n : ℕ} (γ : JumpPath X n) :
    (sectorStateHoldingReward (escapeRateReward G) γ).toReal =
      holdingRealReward (fun i => (G.escapeRate i : ℝ)) γ := by
  unfold sectorStateHoldingReward holdingRealReward escapeRateReward
  rw [ENNReal.toReal_sum (fun i hi =>
    ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ENNReal.toReal_mul]
  simp

theorem sectorEscapeDifference_eq_parts
    (Gu G0 : FiniteJumpGenerator X) {n : ℕ} (γ : JumpPath X n) :
    sectorEscapeDifference Gu G0 γ =
      (sectorStateHoldingReward (escapeRateReward Gu) γ).toReal -
        (sectorStateHoldingReward (escapeRateReward G0) γ).toReal := by
  rw [sectorStateHolding_escape_toReal Gu γ,
      sectorStateHolding_escape_toReal G0 γ]
  unfold sectorEscapeDifference holdingRealReward
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have hsum :
      (∑ i : Fin n,
          ((Gu.escapeRate (γ.1 i.castSucc) : ℝ) -
            (G0.escapeRate (γ.1 i.castSucc) : ℝ)) *
              (γ.2 i.castSucc : ℝ)) =
        (∑ i : Fin n,
            (γ.2 i.castSucc : ℝ) *
              (Gu.escapeRate (γ.1 i.castSucc) : ℝ)) -
          ∑ i : Fin n,
            (γ.2 i.castSucc : ℝ) *
              (G0.escapeRate (γ.1 i.castSucc) : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum]
  ring

/-- Pointwise signed decomposition of the source log-likelihood. -/
theorem fullSourceLogLikelihood_eq_parts
    (Gu G0 : FiniteJumpGenerator X) (γ : FullPath X) :
    fullSourceLogLikelihood Gu G0 γ =
      (fullJumpReward (jumpLogPos Gu G0) γ).toReal -
        (fullJumpReward (jumpLogNeg Gu G0) γ).toReal -
        (fullStateHoldingReward (escapeRateReward Gu) γ).toReal +
        (fullStateHoldingReward (escapeRateReward G0) γ).toReal := by
  rcases γ with ⟨n, γ⟩
  change sectorSourceLogLikelihood Gu G0 γ = _
  unfold sectorSourceLogLikelihood
  rw [sectorJumpLogSum_eq_parts Gu G0 γ,
      sectorEscapeDifference_eq_parts Gu G0 γ]
  simp only [fullJumpReward, fullStateHoldingReward, FullPath.weight]
  ring

theorem edgeRewardRate_toReal
    (G : FiniteJumpGenerator X) (h : X → X → ℝ≥0∞)
    (hh : ∀ i j, h i j ≠ ∞) (i : X) :
    (edgeRewardRate G h i).toReal =
      ∑ j : X, (G.jumpRate i j : ℝ) * (h i j).toReal := by
  unfold edgeRewardRate
  rw [ENNReal.toReal_sum (fun j hj =>
    ENNReal.mul_ne_top ENNReal.coe_ne_top (hh i j))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [ENNReal.toReal_mul]
  simp

theorem sourceRateIntegrand_eq_parts
    (Gu G0 : FiniteJumpGenerator X) (i : X) :
    sourceRateIntegrand Gu G0 i =
      (edgeRewardRate Gu (jumpLogPos Gu G0) i).toReal -
        (edgeRewardRate Gu (jumpLogNeg Gu G0) i).toReal -
        (Gu.escapeRate i : ℝ) + (G0.escapeRate i : ℝ) := by
  rw [edgeRewardRate_toReal Gu (jumpLogPos Gu G0)
        (jumpLogPos_ne_top Gu G0) i,
      edgeRewardRate_toReal Gu (jumpLogNeg Gu G0)
        (jumpLogNeg_ne_top Gu G0) i]
  unfold sourceRateIntegrand sourceEdgeCost FiniteJumpGenerator.escapeRate
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hlog :
      (∑ j : X,
        (Gu.jumpRate i j : ℝ) * jumpLogRatio Gu G0 i j) =
      (∑ j : X,
        (Gu.jumpRate i j : ℝ) * (jumpLogPos Gu G0 i j).toReal) -
      (∑ j : X,
        (Gu.jumpRate i j : ℝ) * (jumpLogNeg Gu G0 i j).toReal) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [jumpLogRatio_eq_pos_sub_neg Gu G0 i j]
    ring
  rw [hlog]
  push_cast
  ring

theorem sectorHoldingReward_toReal
    (G : FiniteJumpGenerator X) (h : X → X → ℝ≥0∞)
    (hh : ∀ i j, h i j ≠ ∞) {n : ℕ} (γ : JumpPath X n) :
    (sectorHoldingReward G h γ).toReal =
      holdingRealReward (fun i => (edgeRewardRate G h i).toReal) γ := by
  unfold sectorHoldingReward holdingRealReward
  rw [ENNReal.toReal_sum (fun i hi =>
    ENNReal.mul_ne_top ENNReal.coe_ne_top
      (edgeRewardRate_ne_top G h hh _))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ENNReal.toReal_mul]
  simp

theorem sectorSourceRateHolding_eq_parts
    (Gu G0 : FiniteJumpGenerator X) {n : ℕ} (γ : JumpPath X n) :
    sectorSourceRateHolding Gu G0 γ =
      (sectorHoldingReward Gu (jumpLogPos Gu G0) γ).toReal -
        (sectorHoldingReward Gu (jumpLogNeg Gu G0) γ).toReal -
        (sectorStateHoldingReward (escapeRateReward Gu) γ).toReal +
        (sectorStateHoldingReward (escapeRateReward G0) γ).toReal := by
  rw [sectorHoldingReward_toReal Gu (jumpLogPos Gu G0)
        (jumpLogPos_ne_top Gu G0) γ,
      sectorHoldingReward_toReal Gu (jumpLogNeg Gu G0)
        (jumpLogNeg_ne_top Gu G0) γ,
      sectorStateHolding_escape_toReal Gu γ,
      sectorStateHolding_escape_toReal G0 γ]
  unfold sectorSourceRateHolding holdingRealReward
  calc
    (∑ i : Fin (n + 1),
        (γ.2 i : ℝ) * sourceRateIntegrand Gu G0 (γ.1 i))
        =
      ∑ i : Fin (n + 1),
        ((γ.2 i : ℝ) *
            (edgeRewardRate Gu (jumpLogPos Gu G0) (γ.1 i)).toReal -
          (γ.2 i : ℝ) *
            (edgeRewardRate Gu (jumpLogNeg Gu G0) (γ.1 i)).toReal -
          (γ.2 i : ℝ) * (Gu.escapeRate (γ.1 i) : ℝ) +
          (γ.2 i : ℝ) * (G0.escapeRate (γ.1 i) : ℝ)) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [sourceRateIntegrand_eq_parts Gu G0 (γ.1 i)]
            ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_sub_distrib]

theorem fullSourceRateHolding_eq_parts
    (Gu G0 : FiniteJumpGenerator X) (γ : FullPath X) :
    fullSourceRateHolding Gu G0 γ =
      (fullHoldingReward Gu (jumpLogPos Gu G0) γ).toReal -
        (fullHoldingReward Gu (jumpLogNeg Gu G0) γ).toReal -
        (fullStateHoldingReward (escapeRateReward Gu) γ).toReal +
        (fullStateHoldingReward (escapeRateReward G0) γ).toReal := by
  rcases γ with ⟨n, γ⟩
  change sectorSourceRateHolding Gu G0 γ = _
  rw [sectorSourceRateHolding_eq_parts Gu G0 γ]
  rfl

theorem integral_four
    {μ : Measure (FullPath X)} {a b c d : FullPath X → ℝ}
    (ha : Integrable a μ) (hb : Integrable b μ)
    (hc : Integrable c μ) (hd : Integrable d μ) :
    (∫ γ, a γ - b γ - c γ + d γ ∂μ) =
      (∫ γ, a γ ∂μ) - (∫ γ, b γ ∂μ) -
        (∫ γ, c γ ∂μ) + (∫ γ, d γ ∂μ) := by
  have h1 :
      (∫ γ, a γ - b γ ∂μ) =
        (∫ γ, a γ ∂μ) - (∫ γ, b γ ∂μ) := by
    simpa only [Pi.sub_apply] using integral_sub ha hb
  have h2 :
      (∫ γ, a γ - b γ - c γ ∂μ) =
        (∫ γ, a γ - b γ ∂μ) - (∫ γ, c γ ∂μ) := by
    simpa only [Pi.sub_apply] using integral_sub (ha.sub hb) hc
  have h3 :
      (∫ γ, a γ - b γ - c γ + d γ ∂μ) =
        (∫ γ, a γ - b γ - c γ ∂μ) + (∫ γ, d γ ∂μ) := by
    simpa only [Pi.add_apply, Pi.sub_apply] using
      integral_add ((ha.sub hb).sub hc) hd
  rw [h3, h2, h1]

theorem integral_fullSourceLogLikelihood_eq_sourceRateHolding
    (Gu G0 : FiniteJumpGenerator X) (T : NNReal) (x : X) :
    (∫ γ, fullSourceLogLikelihood Gu G0 γ ∂Gu.pathLawFrom T x) =
      ∫ γ, fullSourceRateHolding Gu G0 γ ∂Gu.pathLawFrom T x := by
  have hJp := integrable_fullJumpReward_toReal
    Gu T x (jumpLogPos Gu G0) (jumpLogPos_ne_top Gu G0)
  have hJn := integrable_fullJumpReward_toReal
    Gu T x (jumpLogNeg Gu G0) (jumpLogNeg_ne_top Gu G0)
  have hHp := integrable_fullHoldingReward_toReal
    Gu T x (jumpLogPos Gu G0) (jumpLogPos_ne_top Gu G0)
  have hHn := integrable_fullHoldingReward_toReal
    Gu T x (jumpLogNeg Gu G0) (jumpLogNeg_ne_top Gu G0)
  have hEu := integrable_fullStateHoldingReward_toReal
    Gu T x (escapeRateReward Gu) (fun i => by simp [escapeRateReward])
  have hE0 := integrable_fullStateHoldingReward_toReal
    Gu T x (escapeRateReward G0) (fun i => by simp [escapeRateReward])
  calc
    (∫ γ, fullSourceLogLikelihood Gu G0 γ ∂Gu.pathLawFrom T x)
        =
      ∫ γ,
        ((fullJumpReward (jumpLogPos Gu G0) γ).toReal -
          (fullJumpReward (jumpLogNeg Gu G0) γ).toReal -
          (fullStateHoldingReward (escapeRateReward Gu) γ).toReal +
          (fullStateHoldingReward (escapeRateReward G0) γ).toReal)
        ∂Gu.pathLawFrom T x := by
          apply integral_congr_ae
          exact ae_of_all _ fun γ =>
            fullSourceLogLikelihood_eq_parts Gu G0 γ
    _ =
      (∫ γ, (fullJumpReward (jumpLogPos Gu G0) γ).toReal
          ∂Gu.pathLawFrom T x) -
      (∫ γ, (fullJumpReward (jumpLogNeg Gu G0) γ).toReal
          ∂Gu.pathLawFrom T x) -
      (∫ γ, (fullStateHoldingReward (escapeRateReward Gu) γ).toReal
          ∂Gu.pathLawFrom T x) +
      (∫ γ, (fullStateHoldingReward (escapeRateReward G0) γ).toReal
          ∂Gu.pathLawFrom T x) :=
        integral_four hJp hJn hEu hE0
    _ =
      (∫ γ, (fullHoldingReward Gu (jumpLogPos Gu G0) γ).toReal
          ∂Gu.pathLawFrom T x) -
      (∫ γ, (fullHoldingReward Gu (jumpLogNeg Gu G0) γ).toReal
          ∂Gu.pathLawFrom T x) -
      (∫ γ, (fullStateHoldingReward (escapeRateReward Gu) γ).toReal
          ∂Gu.pathLawFrom T x) +
      (∫ γ, (fullStateHoldingReward (escapeRateReward G0) γ).toReal
          ∂Gu.pathLawFrom T x) := by
          rw [integral_fullJumpReward_eq_fullHoldingReward
                Gu T x (jumpLogPos Gu G0) (jumpLogPos_ne_top Gu G0),
              integral_fullJumpReward_eq_fullHoldingReward
                Gu T x (jumpLogNeg Gu G0) (jumpLogNeg_ne_top Gu G0)]
    _ =
      ∫ γ,
        ((fullHoldingReward Gu (jumpLogPos Gu G0) γ).toReal -
          (fullHoldingReward Gu (jumpLogNeg Gu G0) γ).toReal -
          (fullStateHoldingReward (escapeRateReward Gu) γ).toReal +
          (fullStateHoldingReward (escapeRateReward G0) γ).toReal)
        ∂Gu.pathLawFrom T x :=
        (integral_four hHp hHn hEu hE0).symm
    _ = ∫ γ, fullSourceRateHolding Gu G0 γ
          ∂Gu.pathLawFrom T x := by
          apply integral_congr_ae
          exact ae_of_all _ fun γ =>
            (fullSourceRateHolding_eq_parts Gu G0 γ).symm

theorem integrable_fullSourceLogLikelihood
    (Gu G0 : FiniteJumpGenerator X) (T : NNReal) (x : X) :
    Integrable (fullSourceLogLikelihood Gu G0) (Gu.pathLawFrom T x) := by
  have hJp := integrable_fullJumpReward_toReal
    Gu T x (jumpLogPos Gu G0) (jumpLogPos_ne_top Gu G0)
  have hJn := integrable_fullJumpReward_toReal
    Gu T x (jumpLogNeg Gu G0) (jumpLogNeg_ne_top Gu G0)
  have hEu := integrable_fullStateHoldingReward_toReal
    Gu T x (escapeRateReward Gu) (fun i => by simp [escapeRateReward])
  have hE0 := integrable_fullStateHoldingReward_toReal
    Gu T x (escapeRateReward G0) (fun i => by simp [escapeRateReward])
  exact (((hJp.sub hJn).sub hEu).add hE0).congr
    (ae_of_all _ fun γ => (fullSourceLogLikelihood_eq_parts Gu G0 γ).symm)

theorem integrable_llr_pathLawFrom
    (Gu G0 : FiniteJumpGenerator X)
    (hsupport : SupportIncluded Gu G0) (T : NNReal) (x : X) :
    Integrable (llr (Gu.pathLawFrom T x) (G0.pathLawFrom T x))
      (Gu.pathLawFrom T x) := by
  exact (integrable_fullSourceLogLikelihood Gu G0 T x).congr
    (llr_pathLawFrom_eq_fullSourceLogLikelihood Gu G0 hsupport T x).symm

/-- P-KL-04 in holding-time chart form. -/
theorem p_kl_04_holding
    (Gu G0 : FiniteJumpGenerator X) (T : NNReal) (x : X)
    (hsupport : SupportIncluded Gu G0) :
    klDiv (Gu.pathLawFrom T x) (G0.pathLawFrom T x) =
      ENNReal.ofReal
        (∫ γ, fullSourceRateHolding Gu G0 γ ∂Gu.pathLawFrom T x) := by
  have hac := pathLawFrom_absolutelyContinuous Gu G0 hsupport T x
  have hint := integrable_llr_pathLawFrom Gu G0 hsupport T x
  rw [klDiv_of_ac_of_integrable hac hint]
  rw [integral_congr_ae
    (llr_pathLawFrom_eq_fullSourceLogLikelihood Gu G0 hsupport T x)]
  rw [integral_fullSourceLogLikelihood_eq_sourceRateHolding Gu G0 T x]
  simp

/-- P-KL-04 in named literal clock-time form. -/
theorem p_kl_04_clock
    (Gu G0 : FiniteJumpGenerator X) (T : NNReal) (x : X)
    (hsupport : SupportIncluded Gu G0) :
    klDiv (Gu.pathLawFrom T x) (G0.pathLawFrom T x) =
      ENNReal.ofReal
        (∫ γ, sourceClockIntegral Gu G0 T γ ∂Gu.pathLawFrom T x) := by
  rw [p_kl_04_holding Gu G0 T x hsupport]
  apply congrArg ENNReal.ofReal
  exact (integral_congr_ae
    (sourceClockIntegral_ae_eq_holding Gu G0 T x)).symm

/-- P-KL-04, frozen section 22.4 literal clock-time formula.  The displayed
finite sum is written over all `j`; both generators have zero diagonal jump
rates, so its `j = X_t` summand is zero and this is exactly the source's
`j ≠ X_t` sum. -/
theorem p_kl_04
    (Gu G0 : FiniteJumpGenerator X) (T : NNReal) (x : X)
    (hsupport : SupportIncluded Gu G0) :
    klDiv (Gu.pathLawFrom T x) (G0.pathLawFrom T x) =
      ENNReal.ofReal
        (∫ γ,
          (∫ t : ℝ in (0 : ℝ)..(T : ℝ),
            ∑ j : X,
              ((Gu.jumpRate (FullPath.trajectory γ t) j : ℝ) *
                    jumpLogRatio Gu G0 (FullPath.trajectory γ t) j -
                (Gu.jumpRate (FullPath.trajectory γ t) j : ℝ) +
                (G0.jumpRate (FullPath.trajectory γ t) j : ℝ)))
          ∂Gu.pathLawFrom T x) := by
  rw [p_kl_04_clock Gu G0 T x hsupport]
  rfl

end

end UEOT.V3.FiniteCTMCPathKL
