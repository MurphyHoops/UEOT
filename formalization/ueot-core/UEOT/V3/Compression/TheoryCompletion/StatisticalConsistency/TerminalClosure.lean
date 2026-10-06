import UEOT.V3.Compression.TheoryCompletion.StatisticalConsistency.Contract
import UEOT.V3.Compression.TheoryCompletion.StatisticalConsistency.GoaConsistency

/-!
# P3.8 — terminal statistical-to-control closure and boundary synthesis

P3 closes in two deliberately separate layers.

* A changing-sample-space confidence contract proves marginal bad-event
  probabilities vanish.  It does **not** manufacture a common probability
  space or an almost-sure sample path across sample sizes.
* A realized estimator sequence with vanishing reward/transition error radii
  exactifies one fixed source model and one fixed encoder.  This yields exact
  value descent and exact **set-valued** Bellman-GOD correspondence without an
  action-gap assumption.

Canonical greedy-selector identity requires a positive action gap.  Unique,
stable GOA convergence additionally requires a Dobrushin isolation condition.
Thus tied GOD actions and nonisolated GOA structures are not silently promoted
to unique objects.

The reward side remains an explicit adapter boundary: response-TV consistency
alone does not identify reward semantics.  `RealizedControlEstimator` requires
a domain-supplied reward-estimation bridge.

P3.2 predictive recovery and P3.3 carrier recovery are parallel finite
identification surfaces, not hidden premises of the control theorem.  P3 does
not prove that either recovered partition is the supplied control encoder `C`;
that inverse-identification bridge belongs to P4 Inverse Objecthood.  Likewise,
P2 already supplies same-object Objecthood -> control/GOD/GOA semantics; P3
keeps the literal source model and encoder fixed rather than rediscovering that
Objecthood anchor from raw observations.

The whole P3 theorem surface is finite-state; arbitrary/infinite-state object
discovery is deferred to later Theory Completion stages, especially P4.
-/

namespace UEOT.V3.Compression.TheoryCompletion.StatisticalConsistency

open Filter Topology
open UEOT.V3
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.MovingEncoderSemanticGoaClosure

universe uΩ uX uS uA

/-- Marginal high-probability closure for genuinely changing sample spaces.
This is intentionally not an almost-sure path theorem. -/
theorem p3_marginal_failure_tendsto_zero
    {Ω : ℕ → Type uΩ} [∀ n, MeasurableSpace (Ω n)]
    (C : ChangingSampleEventContract Ω) :
    Tendsto (fun n => (C.μ n).real ((C.good n)ᶜ)) atTop (𝓝 0) :=
  C.bad_probability_tendsto_zero

/-- Strongest unconditional deterministic P3 terminal closure for one fixed
source model and fixed encoder.

Estimator consistency exactifies the quotient.  Value descent, action-value
descent, causal optimality and the entire Bellman-GOD action correspondence are
then exact.  No positive action gap and no GOA isolation are used here. -/
theorem p3_exact_structural_value_god_closure
    {X : Type uX} [Fintype X]
    {S : Type uS} [Fintype S]
    {Act : Type uA} [Fintype Act] [Nonempty Act]
    (C : X → S) (hC : Function.Surjective C)
    (micro : Model X (fun _ => Act))
    (E : RealizedControlEstimator C micro) :
    let Q := exactControlQuotient_of_realizedEstimator C hC micro E
    (∀ x : X,
      BellmanGODCorrespondence micro x =
        BellmanGODCorrespondence Q.macroModel (C x)) ∧
    (∀ x : X,
      micro.optimalValue x = Q.macroModel.optimalValue (C x)) ∧
    (∀ (x : X) (a : Act),
      micro.qValue micro.optimalValue x a =
        Q.macroModel.qValue Q.macroModel.optimalValue (C x) a) ∧
    (∀ {t : ℕ} (x : X),
      CausalPolicy.infiniteValue
        (selectorPolicy (Q.liftSelector Q.macroModel.greedyAction))
        micro (t := t) x = micro.optimalValue x) ∧
    (∀ (π : CausalPolicy X (fun _ => Act)) {t : ℕ} (h : π.Memory t),
      CausalPolicy.infiniteValue π micro h ≤ micro.optimalValue (π.current h)) := by
  dsimp only
  let Q := exactControlQuotient_of_realizedEstimator C hC micro E
  have hquo := p_quo_01_of_realizedEstimator C hC micro E
  refine ⟨?_, hquo.1, hquo.2.1, hquo.2.2.1, hquo.2.2.2⟩
  intro x
  exact exact_bellmanGODCorrespondence_eq Q x

/-- Fully strengthened P3 terminal closure.

A fixed known discount is needed to interpret each estimated macro model as an
approximate quotient of the same source.  A positive source action gap upgrades
set-valued GOD consistency to exact canonical-selector recovery.  Dobrushin
isolation upgrades policy consistency to a unique/stable GOA certificate whose
stationary-law radius vanishes. -/
theorem p3_policy_goa_terminal_closure
    {X : Type uX} [Fintype X] [Nonempty X]
    {S : Type uS} [Fintype S] [Nonempty S]
    {Act : Type uA} [Fintype Act] [Nonempty Act]
    (C : X → S) (hC : Function.Surjective C)
    (micro : Model X (fun _ => Act))
    (E : RealizedControlEstimator C micro)
    (hdiscount : ∀ n, micro.discount = (E.macroHat n).discount)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hsourceGap :
      let Qexact := exactControlQuotient_of_realizedEstimator C hC micro E
      ∀ s a, a ≠ Qexact.macroModel.greedyAction s →
        gamma ≤
          Qexact.macroModel.qValue Qexact.macroModel.optimalValue s
              (Qexact.macroModel.greedyAction s) -
            Qexact.macroModel.qValue Qexact.macroModel.optimalValue s a)
    (halpha :
      let Qexact := exactControlQuotient_of_realizedEstimator C hC micro E
      FiniteDobrushin.dobrushinAlpha
        (GoaGaugeInvariance.selectorClosedLoopMatrix
          Qexact.macroModel Qexact.macroModel.greedyAction)
        (GoaGaugeInvariance.selectorClosedLoopMatrix_rowStochastic
          Qexact.macroModel Qexact.macroModel.greedyAction) < 1) :
    let Qexact := exactControlQuotient_of_realizedEstimator C hC micro E
    let Qref : ApproxControlQuotient X S (fun _ => Act) := exactAsApprox Qexact
    let Qseq : ℕ → ApproxControlQuotient X S (fun _ => Act) :=
      fun n => estimatedApproxControlQuotient E hC hdiscount n
    (∀ᶠ n in atTop, ∀ s,
      (E.macroHat n).greedyAction s = Qexact.macroModel.greedyAction s) ∧
    (∀ eta : ℝ, 0 < eta →
      ∀ᶠ n in atTop,
        ∃! e : S ≃ S,
          OptimalPolicyNearGoaGaugeAt Qref (Qseq n) e ∧
          movingNearGoaRadius Qref Qseq Qref.macroModel.greedyAction n < eta) := by
  dsimp only
  constructor
  · exact eventually_estimatedGreedy_eq_canonical
      C hC micro E hdiscount gamma hgamma hsourceGap
  · intro eta heta
    exact eventually_goa_consistent_of_realizedEstimator
      C hC micro E hdiscount gamma hgamma hsourceGap halpha eta heta

end UEOT.V3.Compression.TheoryCompletion.StatisticalConsistency
