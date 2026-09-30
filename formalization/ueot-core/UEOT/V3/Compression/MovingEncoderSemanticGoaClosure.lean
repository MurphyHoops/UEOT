import UEOT.V3.Compression.ActionGapGaugeStability
import UEOT.V3.Compression.MovingEncoderGaugeClosure
import UEOT.V3.Compression.OccupationLimitInvariance

/-!
# Moving encoder semantic and GOA closure

`MovingEncoderGaugeClosure` proves that, on a finite full-support source, a
weighted representation-gauge mismatch converging to zero eventually becomes
an exact fibre gauge lock.  This module carries that representation-level fact
through the semantic and long-run control layers.

The result deliberately separates three notions of convergence:

* reward/transition semantic envelopes converge from their own defect bounds;
* fixed-policy GOA tracking needs only transition-defect convergence plus a
  source contraction margin;
* literal optimal-policy lock additionally needs the P-QUO value radius `D` to
  vanish relative to a positive source action gap.

The third requirement is not redundant: `εr_n → 0` and `εp_n → 0` alone do not
formally imply `D_n → 0` when the macro optimal-value span is allowed to vary
without a uniform bound.
-/

namespace UEOT.V3.Compression.MovingEncoderSemanticGoaClosure

open Filter Topology Function
open UEOT.V3
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.QuotientGauge
open UEOT.V3.Compression.WeightedQuotientGauge
open UEOT.V3.Compression.MovingEncoderGaugeClosure
open UEOT.V3.Compression.ApproximateSemanticGauge
open UEOT.V3.Compression.ApproximateGoaGaugeStability
open UEOT.V3.Compression.ActionGapGaugeStability
open UEOT.V3.Compression.GoaGaugeInvariance
open UEOT.V3.Compression.OccupationLimitInvariance

universe uX uS uA

noncomputable section

variable {X : Type uX} [Fintype X] [Nonempty X]
variable {S : Type uS} [Fintype S] [Nonempty S]
variable {Act : Type uA} [Fintype Act] [Nonempty Act]

noncomputable local instance stateDecidableEq : DecidableEq S :=
  Classical.decEq S

/-- Every finite deterministic-selector closed loop has at least one invariant
law.  This is the existence half of M-OI/P-GOA-01 specialized to the policy
kernel. -/
theorem selectorClosedLoop_exists_invariant
    (M : Model S (fun _ => Act)) (sigma : S → Act)
    (mu0 : stdSimplex ℝ S) :
    ∃ nu : stdSimplex ℝ S,
      step (selectorClosedLoopMatrix M sigma)
        (selectorClosedLoopMatrix_rowStochastic M sigma) nu = nu := by
  let P := selectorClosedLoopMatrix M sigma
  let hP : P ∈ Matrix.rowStochastic ℝ S :=
    selectorClosedLoopMatrix_rowStochastic M sigma
  have h := p_goa_01_via_occupationLimit P hP mu0
  rcases h.1 with ⟨nu, phi, hphi, hlim⟩
  refine ⟨nu, ?_⟩
  have hv := h.2 nu phi hphi hlim
  apply Subtype.ext
  exact hv

/-- Reward semantic comparison envelope between a fixed reference quotient and
the `n`th moving quotient. -/
def movingRewardGaugeEnvelope
    (Qref : ApproxControlQuotient X S (fun _ => Act))
    (Qseq : ℕ → ApproxControlQuotient X S (fun _ => Act))
    (n : ℕ) : ℝ :=
  Qref.epsilonReward + (Qseq n).epsilonReward

/-- Transition semantic comparison envelope. -/
def movingTransitionGaugeEnvelope
    (Qref : ApproxControlQuotient X S (fun _ => Act))
    (Qseq : ℕ → ApproxControlQuotient X S (fun _ => Act))
    (n : ℕ) : ℝ :=
  Qref.epsilonTransition + (Qseq n).epsilonTransition

/-- Optimal-value / optimal-Q comparison envelope. -/
def movingValueGaugeEnvelope
    (Qref : ApproxControlQuotient X S (fun _ => Act))
    (Qseq : ℕ → ApproxControlQuotient X S (fun _ => Act))
    (n : ℕ) : ℝ :=
  Qref.D + (Qseq n).D

/-- Stationary near-GOA radius for one fixed reference policy. -/
def movingNearGoaRadius
    (Qref : ApproxControlQuotient X S (fun _ => Act))
    (Qseq : ℕ → ApproxControlQuotient X S (fun _ => Act))
    (sigma : S → Act) (n : ℕ) : ℝ :=
  movingTransitionGaugeEnvelope Qref Qseq n /
    (1 - dobrushinAlpha
      (selectorClosedLoopMatrix Qref.macroModel sigma)
      (selectorClosedLoopMatrix_rowStochastic Qref.macroModel sigma))

theorem movingRewardGaugeEnvelope_tendsto_zero
    (Qref : ApproxControlQuotient X S (fun _ => Act))
    (Qseq : ℕ → ApproxControlQuotient X S (fun _ => Act))
    (href : Qref.epsilonReward = 0)
    (hseq : Tendsto (fun n => (Qseq n).epsilonReward) atTop (𝓝 0)) :
    Tendsto (movingRewardGaugeEnvelope Qref Qseq) atTop (𝓝 0) := by
  change Tendsto
    (fun n => Qref.epsilonReward + (Qseq n).epsilonReward) atTop (𝓝 0)
  simpa [movingRewardGaugeEnvelope, href] using hseq

theorem movingTransitionGaugeEnvelope_tendsto_zero
    (Qref : ApproxControlQuotient X S (fun _ => Act))
    (Qseq : ℕ → ApproxControlQuotient X S (fun _ => Act))
    (href : Qref.epsilonTransition = 0)
    (hseq : Tendsto (fun n => (Qseq n).epsilonTransition) atTop (𝓝 0)) :
    Tendsto (movingTransitionGaugeEnvelope Qref Qseq) atTop (𝓝 0) := by
  change Tendsto
    (fun n => Qref.epsilonTransition + (Qseq n).epsilonTransition) atTop (𝓝 0)
  simpa [movingTransitionGaugeEnvelope, href] using hseq

theorem movingValueGaugeEnvelope_tendsto_zero
    (Qref : ApproxControlQuotient X S (fun _ => Act))
    (Qseq : ℕ → ApproxControlQuotient X S (fun _ => Act))
    (href : Qref.D = 0)
    (hseq : Tendsto (fun n => (Qseq n).D) atTop (𝓝 0)) :
    Tendsto (movingValueGaugeEnvelope Qref Qseq) atTop (𝓝 0) := by
  change Tendsto (fun n => Qref.D + (Qseq n).D) atTop (𝓝 0)
  simpa [movingValueGaugeEnvelope, href] using hseq

theorem movingNearGoaRadius_tendsto_zero
    (Qref : ApproxControlQuotient X S (fun _ => Act))
    (Qseq : ℕ → ApproxControlQuotient X S (fun _ => Act))
    (sigma : S → Act)
    (href : Qref.epsilonTransition = 0)
    (hseq : Tendsto (fun n => (Qseq n).epsilonTransition) atTop (𝓝 0)) :
    Tendsto (movingNearGoaRadius Qref Qseq sigma) atTop (𝓝 0) := by
  have hnum := movingTransitionGaugeEnvelope_tendsto_zero Qref Qseq href hseq
  change Tendsto
    (fun n => movingTransitionGaugeEnvelope Qref Qseq n /
      (1 - dobrushinAlpha
        (selectorClosedLoopMatrix Qref.macroModel sigma)
        (selectorClosedLoopMatrix_rowStochastic Qref.macroModel sigma)))
    atTop (𝓝 0)
  convert hnum.div_const (1 - dobrushinAlpha
    (selectorClosedLoopMatrix Qref.macroModel sigma)
    (selectorClosedLoopMatrix_rowStochastic Qref.macroModel sigma)) using 1 <;> simp

/-- Moving representation convergence yields eventual unique approximate
semantic relabeling once the finite full-support weighted gauge locks exactly. -/
theorem eventually_existsUnique_approxSemanticRelabel
    (mu : stdSimplex ℝ X) (hfull : ∀ x, 0 < mu x)
    (Qref : ApproxControlQuotient X S (fun _ => Act))
    (Qseq : ℕ → ApproxControlQuotient X S (fun _ => Act))
    (hGauge : Tendsto
      (fun n => weightedGaugeMismatch mu (Qseq n).f Qref.f)
      atTop (𝓝 0))
    (hMicro : ∀ n, Qref.micro = (Qseq n).micro) :
    ∀ᶠ n in atTop,
      ∃! e : S ≃ S, ApproxSemanticRelabel Qref (Qseq n) e := by
  have hsame : ∀ᶠ n in atTop, SameFibers (Qseq n).f Qref.f :=
    eventually_sameFibers_of_weightedGaugeMismatch_tendsto_zero
      mu hfull Qref.f Qref.surjective
      (fun n => (Qseq n).f) (fun n => (Qseq n).surjective) hGauge
  filter_upwards [hsame] with n hn
  exact existsUnique_approxSemanticRelabel_of_sameFibers
    Qref (Qseq n) (hMicro n) (sameFibers_symm hn)

/-- Full reward/transition/value semantic gauges become arbitrarily tight once
the encoder gauge locks and all three certified envelopes vanish.  The explicit
`D_n → 0` hypothesis is intentional and records the value-span boundary. -/
theorem eventually_approxSemanticRelabel_arbitrarily_close
    (mu : stdSimplex ℝ X) (hfull : ∀ x, 0 < mu x)
    (Qref : ApproxControlQuotient X S (fun _ => Act))
    (Qseq : ℕ → ApproxControlQuotient X S (fun _ => Act))
    (hGauge : Tendsto
      (fun n => weightedGaugeMismatch mu (Qseq n).f Qref.f)
      atTop (𝓝 0))
    (hMicro : ∀ n, Qref.micro = (Qseq n).micro)
    (hrefR : Qref.epsilonReward = 0)
    (hrefP : Qref.epsilonTransition = 0)
    (hrefD : Qref.D = 0)
    (hR : Tendsto (fun n => (Qseq n).epsilonReward) atTop (𝓝 0))
    (hP : Tendsto (fun n => (Qseq n).epsilonTransition) atTop (𝓝 0))
    (hD : Tendsto (fun n => (Qseq n).D) atTop (𝓝 0))
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ n in atTop,
      ∃! e : S ≃ S,
        ApproxSemanticRelabel Qref (Qseq n) e ∧
        movingRewardGaugeEnvelope Qref Qseq n < eta ∧
        movingTransitionGaugeEnvelope Qref Qseq n < eta ∧
        movingValueGaugeEnvelope Qref Qseq n < eta := by
  have hsem := eventually_existsUnique_approxSemanticRelabel
    mu hfull Qref Qseq hGauge hMicro
  have hrsmall : ∀ᶠ n in atTop, movingRewardGaugeEnvelope Qref Qseq n < eta :=
    (tendsto_order.1
      (movingRewardGaugeEnvelope_tendsto_zero Qref Qseq hrefR hR)).2 eta heta
  have hpsmall : ∀ᶠ n in atTop, movingTransitionGaugeEnvelope Qref Qseq n < eta :=
    (tendsto_order.1
      (movingTransitionGaugeEnvelope_tendsto_zero Qref Qseq hrefP hP)).2 eta heta
  have hdsmall : ∀ᶠ n in atTop, movingValueGaugeEnvelope Qref Qseq n < eta :=
    (tendsto_order.1
      (movingValueGaugeEnvelope_tendsto_zero Qref Qseq hrefD hD)).2 eta heta
  filter_upwards [hsem, hrsmall, hpsmall, hdsmall] with n hnsem hnr hnp hnd
  rcases hnsem with ⟨e, he, huniq⟩
  refine ⟨e, ⟨he, hnr, hnp, hnd⟩, ?_⟩
  intro e' he'
  exact huniq e' he'.1

/-- Fixed-policy long-run gauge certificate at one moving-encoder index. -/
def FixedPolicyNearGoaGaugeAt
    (Qref Qn : ApproxControlQuotient X S (fun _ => Act))
    (sigma : S → Act) (e : S ≃ S) : Prop :=
  e ∘ Qref.f = Qn.f ∧
  ∃ mustarRef : stdSimplex ℝ S,
    step
        (selectorClosedLoopMatrix Qref.macroModel sigma)
        (selectorClosedLoopMatrix_rowStochastic Qref.macroModel sigma)
        mustarRef = mustarRef ∧
    (∀ nu : stdSimplex ℝ S,
      step
          (selectorClosedLoopMatrix Qref.macroModel sigma)
          (selectorClosedLoopMatrix_rowStochastic Qref.macroModel sigma)
          nu = nu → nu = mustarRef) ∧
    ∀ muN : stdSimplex ℝ S,
      step
          (selectorClosedLoopMatrix Qn.macroModel (transportSelector e sigma))
          (selectorClosedLoopMatrix_rowStochastic Qn.macroModel
            (transportSelector e sigma))
          muN = muN →
      lawTV (relabelSimplex e mustarRef) muN ≤
        movingNearGoaRadius Qref (fun _ => Qn) sigma 0

/-- A fixed-policy near-GOA gauge certificate is nonvacuous: the finite target
closed loop has an invariant law, and every such law satisfies the certified
TV tube. -/
theorem FixedPolicyNearGoaGaugeAt.exists_target_invariant
    {Qref Qn : ApproxControlQuotient X S (fun _ => Act)}
    {sigma : S → Act} {e : S ≃ S}
    (h : FixedPolicyNearGoaGaugeAt Qref Qn sigma e) :
    ∃ muN : stdSimplex ℝ S,
      step
          (selectorClosedLoopMatrix Qn.macroModel (transportSelector e sigma))
          (selectorClosedLoopMatrix_rowStochastic Qn.macroModel
            (transportSelector e sigma))
          muN = muN ∧
      ∃ mustarRef : stdSimplex ℝ S,
        step
            (selectorClosedLoopMatrix Qref.macroModel sigma)
            (selectorClosedLoopMatrix_rowStochastic Qref.macroModel sigma)
            mustarRef = mustarRef ∧
        lawTV (relabelSimplex e mustarRef) muN ≤
          movingNearGoaRadius Qref (fun _ => Qn) sigma 0 := by
  rcases h.2 with ⟨mustarRef, hfixRef, _, hbound⟩
  rcases selectorClosedLoop_exists_invariant
      Qn.macroModel (transportSelector e sigma) (relabelSimplex e mustarRef) with
    ⟨muN, hfixN⟩
  exact ⟨muN, hfixN, mustarRef, hfixRef, hbound muN hfixN⟩

/-- Eventual exact gauge lock promotes to an eventual unique fixed-policy
near-GOA gauge certificate. -/
theorem eventually_existsUnique_fixedPolicyNearGoaGaugeAt
    (mu : stdSimplex ℝ X) (hfull : ∀ x, 0 < mu x)
    (Qref : ApproxControlQuotient X S (fun _ => Act))
    (Qseq : ℕ → ApproxControlQuotient X S (fun _ => Act))
    (hGauge : Tendsto
      (fun n => weightedGaugeMismatch mu (Qseq n).f Qref.f)
      atTop (𝓝 0))
    (hMicro : ∀ n, Qref.micro = (Qseq n).micro)
    (sigma : S → Act)
    (halpha :
      dobrushinAlpha
        (selectorClosedLoopMatrix Qref.macroModel sigma)
        (selectorClosedLoopMatrix_rowStochastic Qref.macroModel sigma) < 1) :
    ∀ᶠ n in atTop,
      ∃! e : S ≃ S, FixedPolicyNearGoaGaugeAt Qref (Qseq n) sigma e := by
  have hsame : ∀ᶠ n in atTop, SameFibers (Qseq n).f Qref.f :=
    eventually_sameFibers_of_weightedGaugeMismatch_tendsto_zero
      mu hfull Qref.f Qref.surjective
      (fun n => (Qseq n).f) (fun n => (Qseq n).surjective) hGauge
  filter_upwards [hsame] with n hn
  have hsame' : SameFibers Qref.f (Qseq n).f := sameFibers_symm hn
  let e : S ≃ S := quotientEquiv Qref.f (Qseq n).f
    Qref.surjective (Qseq n).surjective hsame'
  have he : e ∘ Qref.f = (Qseq n).f :=
    quotientEquiv_comp Qref.f (Qseq n).f
      Qref.surjective (Qseq n).surjective hsame'
  rcases fixedPolicy_near_goa_gauge_stability
      Qref (Qseq n) (hMicro n) e he sigma halpha with
    ⟨mustarRef, hfix, huniq, hbound⟩
  refine ⟨e, ⟨he, mustarRef, hfix, huniq, ?_⟩, ?_⟩
  · intro muN hmuN
    simpa [movingNearGoaRadius, movingTransitionGaugeEnvelope] using hbound muN hmuN
  · intro e' he'
    exact quotientEquiv_unique
      Qref.f (Qseq n).f Qref.surjective (Qseq n).surjective hsame' e' he'.1

/-- The eventual fixed-policy certificate has a radius tending to zero when
the reference transition defect is zero and moving transition defects vanish. -/
theorem eventually_fixedPolicyNearGoa_arbitrarily_close
    (mu : stdSimplex ℝ X) (hfull : ∀ x, 0 < mu x)
    (Qref : ApproxControlQuotient X S (fun _ => Act))
    (Qseq : ℕ → ApproxControlQuotient X S (fun _ => Act))
    (hGauge : Tendsto
      (fun n => weightedGaugeMismatch mu (Qseq n).f Qref.f)
      atTop (𝓝 0))
    (hMicro : ∀ n, Qref.micro = (Qseq n).micro)
    (sigma : S → Act)
    (halpha :
      dobrushinAlpha
        (selectorClosedLoopMatrix Qref.macroModel sigma)
        (selectorClosedLoopMatrix_rowStochastic Qref.macroModel sigma) < 1)
    (hrefP : Qref.epsilonTransition = 0)
    (hP : Tendsto (fun n => (Qseq n).epsilonTransition) atTop (𝓝 0))
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ n in atTop,
      ∃! e : S ≃ S,
        FixedPolicyNearGoaGaugeAt Qref (Qseq n) sigma e ∧
        movingNearGoaRadius Qref Qseq sigma n < eta := by
  have hcert := eventually_existsUnique_fixedPolicyNearGoaGaugeAt
    mu hfull Qref Qseq hGauge hMicro sigma halpha
  have hrsmall : ∀ᶠ n in atTop, movingNearGoaRadius Qref Qseq sigma n < eta :=
    (tendsto_order.1
      (movingNearGoaRadius_tendsto_zero Qref Qseq sigma hrefP hP)).2 eta heta
  filter_upwards [hcert, hrsmall] with n hncert hnrad
  rcases hncert with ⟨e, he, huniq⟩
  refine ⟨e, ⟨he, hnrad⟩, ?_⟩
  intro e' he'
  exact huniq e' he'.1

/-- Exact reward and transition certificates force the P-QUO global value
radius to vanish for the fixed reference quotient. -/
theorem D_eq_zero_of_exact_defects
    (Q : ApproxControlQuotient X S (fun _ => Act))
    (hr : Q.epsilonReward = 0) (hp : Q.epsilonTransition = 0) :
    Q.D = 0 := by
  simp [ApproxControlQuotient.D, ApproxControlQuotient.delta, hr, hp]

/-- If the moving P-QUO value radius tends to zero and the reference has a
strict uniform action gap, then the quantitative action-gap condition required
for policy identity eventually holds. -/
theorem eventually_actionGap_of_D_tendsto_zero
    (Qref : ApproxControlQuotient X S (fun _ => Act))
    (Qseq : ℕ → ApproxControlQuotient X S (fun _ => Act))
    (hrefD : Qref.D = 0)
    (hD : Tendsto (fun n => (Qseq n).D) atTop (𝓝 0))
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hsourceGap : ∀ s a, a ≠ Qref.macroModel.greedyAction s →
      gamma ≤
        Qref.macroModel.qValue Qref.macroModel.optimalValue s
            (Qref.macroModel.greedyAction s) -
          Qref.macroModel.qValue Qref.macroModel.optimalValue s a) :
    ∀ᶠ n in atTop, ∀ s a, a ≠ Qref.macroModel.greedyAction s →
      2 * (Qref.D + (Qseq n).D) <
        Qref.macroModel.qValue Qref.macroModel.optimalValue s
            (Qref.macroModel.greedyAction s) -
          Qref.macroModel.qValue Qref.macroModel.optimalValue s a := by
  have hhalf : 0 < gamma / 2 := by linarith
  have hsmall : ∀ᶠ n in atTop, (Qseq n).D < gamma / 2 :=
    (tendsto_order.1 hD).2 (gamma / 2) hhalf
  filter_upwards [hsmall] with n hn
  intro s a hne
  have hgap := hsourceGap s a hne
  rw [hrefD]
  linarith

/-- Optimal-policy long-run certificate for one moving quotient. -/
def OptimalPolicyNearGoaGaugeAt
    (Qref Qn : ApproxControlQuotient X S (fun _ => Act))
    (e : S ≃ S) : Prop :=
  e ∘ Qref.f = Qn.f ∧
  (∀ s, Qn.macroModel.greedyAction (e s) = Qref.macroModel.greedyAction s) ∧
  ∃ mustarRef : stdSimplex ℝ S,
    step
        (selectorClosedLoopMatrix Qref.macroModel Qref.macroModel.greedyAction)
        (selectorClosedLoopMatrix_rowStochastic
          Qref.macroModel Qref.macroModel.greedyAction)
        mustarRef = mustarRef ∧
    (∀ nu : stdSimplex ℝ S,
      step
          (selectorClosedLoopMatrix Qref.macroModel Qref.macroModel.greedyAction)
          (selectorClosedLoopMatrix_rowStochastic
            Qref.macroModel Qref.macroModel.greedyAction)
          nu = nu → nu = mustarRef) ∧
    ∀ muN : stdSimplex ℝ S,
      step
          (selectorClosedLoopMatrix Qn.macroModel Qn.macroModel.greedyAction)
          (selectorClosedLoopMatrix_rowStochastic
            Qn.macroModel Qn.macroModel.greedyAction)
          muN = muN →
      lawTV (relabelSimplex e mustarRef) muN ≤
        movingNearGoaRadius Qref (fun _ => Qn)
          Qref.macroModel.greedyAction 0

/-- The optimal-policy certificate likewise contains an actually existing
target greedy invariant law inside the certified tube. -/
theorem OptimalPolicyNearGoaGaugeAt.exists_target_invariant
    {Qref Qn : ApproxControlQuotient X S (fun _ => Act)}
    {e : S ≃ S}
    (h : OptimalPolicyNearGoaGaugeAt Qref Qn e) :
    ∃ muN : stdSimplex ℝ S,
      step
          (selectorClosedLoopMatrix Qn.macroModel Qn.macroModel.greedyAction)
          (selectorClosedLoopMatrix_rowStochastic
            Qn.macroModel Qn.macroModel.greedyAction)
          muN = muN ∧
      ∃ mustarRef : stdSimplex ℝ S,
        step
            (selectorClosedLoopMatrix Qref.macroModel Qref.macroModel.greedyAction)
            (selectorClosedLoopMatrix_rowStochastic
              Qref.macroModel Qref.macroModel.greedyAction)
            mustarRef = mustarRef ∧
        lawTV (relabelSimplex e mustarRef) muN ≤
          movingNearGoaRadius Qref (fun _ => Qn)
            Qref.macroModel.greedyAction 0 := by
  rcases h.2.2 with ⟨mustarRef, hfixRef, _, hbound⟩
  rcases selectorClosedLoop_exists_invariant
      Qn.macroModel Qn.macroModel.greedyAction (relabelSimplex e mustarRef) with
    ⟨muN, hfixN⟩
  exact ⟨muN, hfixN, mustarRef, hfixRef, hbound muN hfixN⟩

/-- Moving representation lock plus vanishing P-QUO radius and a positive
source action gap eventually identify the target's own greedy policy and its
near-GOA invariant structure modulo the unique quotient gauge. -/
theorem eventually_existsUnique_optimalPolicyNearGoaGaugeAt
    (mu : stdSimplex ℝ X) (hfull : ∀ x, 0 < mu x)
    (Qref : ApproxControlQuotient X S (fun _ => Act))
    (Qseq : ℕ → ApproxControlQuotient X S (fun _ => Act))
    (hGauge : Tendsto
      (fun n => weightedGaugeMismatch mu (Qseq n).f Qref.f)
      atTop (𝓝 0))
    (hMicro : ∀ n, Qref.micro = (Qseq n).micro)
    (hrefD : Qref.D = 0)
    (hD : Tendsto (fun n => (Qseq n).D) atTop (𝓝 0))
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hsourceGap : ∀ s a, a ≠ Qref.macroModel.greedyAction s →
      gamma ≤
        Qref.macroModel.qValue Qref.macroModel.optimalValue s
            (Qref.macroModel.greedyAction s) -
          Qref.macroModel.qValue Qref.macroModel.optimalValue s a)
    (halpha :
      dobrushinAlpha
        (selectorClosedLoopMatrix Qref.macroModel Qref.macroModel.greedyAction)
        (selectorClosedLoopMatrix_rowStochastic
          Qref.macroModel Qref.macroModel.greedyAction) < 1) :
    ∀ᶠ n in atTop,
      ∃! e : S ≃ S, OptimalPolicyNearGoaGaugeAt Qref (Qseq n) e := by
  have hsame : ∀ᶠ n in atTop, SameFibers (Qseq n).f Qref.f :=
    eventually_sameFibers_of_weightedGaugeMismatch_tendsto_zero
      mu hfull Qref.f Qref.surjective
      (fun n => (Qseq n).f) (fun n => (Qseq n).surjective) hGauge
  have hgap := eventually_actionGap_of_D_tendsto_zero
    Qref Qseq hrefD hD gamma hgamma hsourceGap
  filter_upwards [hsame, hgap] with n hnSame hnGap
  have hsame' : SameFibers Qref.f (Qseq n).f := sameFibers_symm hnSame
  let e : S ≃ S := quotientEquiv Qref.f (Qseq n).f
    Qref.surjective (Qseq n).surjective hsame'
  have he : e ∘ Qref.f = (Qseq n).f :=
    quotientEquiv_comp Qref.f (Qseq n).f
      Qref.surjective (Qseq n).surjective hsame'
  rcases optimalPolicy_near_goa_gauge_stability
      Qref (Qseq n) (hMicro n) e he hnGap halpha with
    ⟨hpolicy, mustarRef, hfix, huniq, hbound⟩
  refine ⟨e, ⟨he, hpolicy, mustarRef, hfix, huniq, ?_⟩, ?_⟩
  · intro muN hmuN
    simpa [movingNearGoaRadius, movingTransitionGaugeEnvelope] using hbound muN hmuN
  · intro e' he'
    exact quotientEquiv_unique
      Qref.f (Qseq n).f Qref.surjective (Qseq n).surjective hsame' e' he'.1

/-- Final tail theorem: with vanishing transition defects, the eventual
optimal-policy gauge certificates have an arbitrarily small near-GOA radius. -/
theorem eventually_optimalPolicyNearGoa_arbitrarily_close
    (mu : stdSimplex ℝ X) (hfull : ∀ x, 0 < mu x)
    (Qref : ApproxControlQuotient X S (fun _ => Act))
    (Qseq : ℕ → ApproxControlQuotient X S (fun _ => Act))
    (hGauge : Tendsto
      (fun n => weightedGaugeMismatch mu (Qseq n).f Qref.f)
      atTop (𝓝 0))
    (hMicro : ∀ n, Qref.micro = (Qseq n).micro)
    (hrefD : Qref.D = 0)
    (hD : Tendsto (fun n => (Qseq n).D) atTop (𝓝 0))
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hsourceGap : ∀ s a, a ≠ Qref.macroModel.greedyAction s →
      gamma ≤
        Qref.macroModel.qValue Qref.macroModel.optimalValue s
            (Qref.macroModel.greedyAction s) -
          Qref.macroModel.qValue Qref.macroModel.optimalValue s a)
    (halpha :
      dobrushinAlpha
        (selectorClosedLoopMatrix Qref.macroModel Qref.macroModel.greedyAction)
        (selectorClosedLoopMatrix_rowStochastic
          Qref.macroModel Qref.macroModel.greedyAction) < 1)
    (hrefP : Qref.epsilonTransition = 0)
    (hP : Tendsto (fun n => (Qseq n).epsilonTransition) atTop (𝓝 0))
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ n in atTop,
      ∃! e : S ≃ S,
        OptimalPolicyNearGoaGaugeAt Qref (Qseq n) e ∧
        movingNearGoaRadius Qref Qseq Qref.macroModel.greedyAction n < eta := by
  have hcert := eventually_existsUnique_optimalPolicyNearGoaGaugeAt
    mu hfull Qref Qseq hGauge hMicro hrefD hD gamma hgamma hsourceGap halpha
  have hrsmall :
      ∀ᶠ n in atTop,
        movingNearGoaRadius Qref Qseq Qref.macroModel.greedyAction n < eta :=
    (tendsto_order.1
      (movingNearGoaRadius_tendsto_zero
        Qref Qseq Qref.macroModel.greedyAction hrefP hP)).2 eta heta
  filter_upwards [hcert, hrsmall] with n hncert hnrad
  rcases hncert with ⟨e, he, huniq⟩
  refine ⟨e, ⟨he, hnrad⟩, ?_⟩
  intro e' he'
  exact huniq e' he'.1

end

end UEOT.V3.Compression.MovingEncoderSemanticGoaClosure
