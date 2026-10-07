import UEOT.V3.Compression.TheoryCompletion.InverseObjecthood.FiniteCandidateRecovery
import UEOT.V3.Compression.TheoryCompletion.InverseObjecthood.OperationalValidity
import UEOT.V3.Compression.TheoryCompletion.InverseObjecthood.InteractionClassRecovery
import UEOT.V3.Compression.TheoryCompletion.StatisticalConsistency.Contract
import UEOT.V3.FiniteCandidatePStat08

/-!
# P4.5 — high-probability finite object-class discovery

The statistical endpoint of P4 remains sample-space agnostic.  Different
sample sizes may live on genuinely different probability spaces, exactly as in
P3.  The recovered target is a declared object-equivalence `Setoid`, not
necessarily literal candidate equality.

A discovery contract additionally records a validity predicate.  Both the true
candidate and every reported estimate must satisfy that gate.  This prevents a
statistically well-fitting but uncertified candidate from being silently called
an Operational Object.

The generic constructor consumes a P3 changing-sample event contract plus a
deterministic theorem saying that the P3 good event implies object-class
recovery.  No common sample path is introduced.

A second theorem specializes frozen P-STAT-08: under a unique strict true-risk
minimizer, its excess-risk probability bound becomes an exact candidate-
selection failure bound once the finite validation radius is below the
canonical P4.1 risk gap.
-/

namespace UEOT.V3.Compression.TheoryCompletion.InverseObjecthood

open Filter Topology MeasureTheory ProbabilityTheory Real
open UEOT.V3.BoundedLossSampling
open UEOT.V3.FiniteCandidateDiscovery
open UEOT.V3.FiniteCandidatePStat08
open UEOT.V3.Compression.CrossTrack
open UEOT.V3.Compression.TheoryCompletion.StatisticalConsistency

universe uOmega uCandidate uZ uI uY

/-- Sample-size-indexed object-class discovery contract with explicit validity
gating and genuinely changing sample spaces. -/
structure ChangingObjectClassDiscoveryContract
    (Omega : ℕ → Type uOmega) [∀ n, MeasurableSpace (Omega n)]
    (Candidate : Type uCandidate) where
  schedule : ConfidenceSchedule
  mu : ∀ n, Measure (Omega n)
  probability : ∀ n, IsProbabilityMeasure (mu n)
  valid : Candidate → Prop
  objectClass : Setoid Candidate
  truth : Candidate
  truth_valid : valid truth
  estimate : ∀ n, Omega n → Candidate
  estimate_valid : ∀ n omega, valid (estimate n omega)
  classFailure_le : ∀ n,
    (mu n).real {omega | ¬ objectClass.r (estimate n omega) truth} ≤
      schedule.failure n

namespace ChangingObjectClassDiscoveryContract

/-- The marginal probability of returning the wrong declared object class tends
to zero.  This is convergence in probability across changing sample spaces,
not almost-sure convergence on a common path. -/
theorem classFailure_tendsto_zero
    {Omega : ℕ → Type uOmega} [∀ n, MeasurableSpace (Omega n)]
    {Candidate : Type uCandidate}
    (C : ChangingObjectClassDiscoveryContract Omega Candidate) :
    Tendsto
      (fun n => (C.mu n).real
        {omega | ¬ C.objectClass.r (C.estimate n omega) C.truth})
      atTop (𝓝 0) := by
  exact squeeze_zero
    (fun _ => measureReal_nonneg)
    C.classFailure_le
    C.schedule.failure_tendsto_zero

end ChangingObjectClassDiscoveryContract

/-- Any P3 high-probability good-event contract becomes an object-class
discovery contract once a deterministic P4 theorem proves class recovery on
that good event and both truth/estimates pass the declared validity gate. -/
noncomputable def objectClassDiscoveryContract_of_goodEvent
    {Omega : ℕ → Type uOmega} [∀ n, MeasurableSpace (Omega n)]
    {Candidate : Type uCandidate}
    (C : ChangingSampleEventContract Omega)
    (valid : Candidate → Prop)
    (objectClass : Setoid Candidate)
    (truth : Candidate)
    (estimate : ∀ n, Omega n → Candidate)
    (htruth : valid truth)
    (hestimate : ∀ n omega, valid (estimate n omega))
    (hgood : ∀ n omega, omega ∈ C.good n →
      objectClass.r (estimate n omega) truth) :
    ChangingObjectClassDiscoveryContract Omega Candidate where
  schedule := C.schedule
  mu := C.μ
  probability := C.probability
  valid := valid
  objectClass := objectClass
  truth := truth
  truth_valid := htruth
  estimate := estimate
  estimate_valid := hestimate
  classFailure_le := by
    intro n
    have hsubset :
        {omega | ¬ objectClass.r (estimate n omega) truth} ⊆ (C.good n)ᶜ := by
      intro omega hbad hmem
      exact hbad (hgood n omega hmem)
    let _ : IsProbabilityMeasure (C.μ n) := C.probability n
    exact (measureReal_mono hsubset).trans (C.bad_le_failure n)

/-- A P3 good-event contract plus uniformly small interaction-fingerprint error
constructs a valid-candidate discovery contract for the probe-relative evidence
class.  The validity predicate is explicit: callers may include exact candidate-
universe membership and any P4.4 operational certificate gate they have proved. -/
noncomputable def interactionClassDiscoveryContract_of_goodEvent
    {Omega : ℕ → Type uOmega} [∀ n, MeasurableSpace (Omega n)]
    {Candidate : Type uCandidate} [Fintype Candidate] [Nonempty Candidate]
    {I : Type uI} {Y : Type uY} [MeasurableSpace Y]
    (C : ChangingSampleEventContract Omega)
    (F : InteractionResponseFamily Candidate I Y)
    (probes : Finset I) (hprobes : probes.Nonempty)
    (observed : ∀ n, Omega n → I → Measure Y)
    (hobserved : ∀ n omega i, IsProbabilityMeasure (observed n omega i))
    (valid : Candidate → Prop)
    (truth : Candidate)
    (estimate : ∀ n, Omega n → Candidate)
    (htruth : valid truth)
    (hestimate : ∀ n omega, valid (estimate n omega))
    (eta : ℕ → ℝ)
    (hfit : ∀ n omega, omega ∈ C.good n →
      interactionObservationError F probes hprobes (observed n omega)
          (estimate n omega) ≤ eta n ∧
      interactionObservationError F probes hprobes (observed n omega)
          truth ≤ eta n)
    (hsmall : ∀ n,
      2 * eta n < canonicalInteractionEvidenceGap F probes hprobes) :
    ChangingObjectClassDiscoveryContract Omega Candidate := by
  apply objectClassDiscoveryContract_of_goodEvent
    C valid (interactionEvidenceSetoid F probes) truth estimate htruth hestimate
  intro n omega hgood
  exact evidenceEquivalent_of_commonObservation
    F probes hprobes (observed n omega) (hobserved n omega) (eta n)
    (hfit n omega hgood).1 (hfit n omega hgood).2 (hsmall n)

/-- Under pairwise separating probes, the same high-probability interaction
contract upgrades evidence-class recovery to literal candidate recovery. -/
noncomputable def exactCandidateDiscoveryContract_of_goodEvent
    {Omega : ℕ → Type uOmega} [∀ n, MeasurableSpace (Omega n)]
    {Candidate : Type uCandidate} [Fintype Candidate] [Nonempty Candidate]
    {I : Type uI} {Y : Type uY} [MeasurableSpace Y]
    (C : ChangingSampleEventContract Omega)
    (F : InteractionResponseFamily Candidate I Y)
    (probes : Finset I) (hprobes : probes.Nonempty)
    (hsep : PairwiseInteractionSeparating F probes)
    (observed : ∀ n, Omega n → I → Measure Y)
    (hobserved : ∀ n omega i, IsProbabilityMeasure (observed n omega i))
    (valid : Candidate → Prop)
    (truth : Candidate)
    (estimate : ∀ n, Omega n → Candidate)
    (htruth : valid truth)
    (hestimate : ∀ n omega, valid (estimate n omega))
    (eta : ℕ → ℝ)
    (hfit : ∀ n omega, omega ∈ C.good n →
      interactionObservationError F probes hprobes (observed n omega)
          (estimate n omega) ≤ eta n ∧
      interactionObservationError F probes hprobes (observed n omega)
          truth ≤ eta n)
    (hsmall : ∀ n,
      2 * eta n < canonicalInteractionEvidenceGap F probes hprobes) :
    ChangingObjectClassDiscoveryContract Omega Candidate := by
  apply objectClassDiscoveryContract_of_goodEvent
    C valid (equalitySetoid Candidate) truth estimate htruth hestimate
  intro n omega hgood
  exact exactCandidate_of_commonObservation_of_pairwiseSeparating
    F probes hprobes hsep (observed n omega) (hobserved n omega) (eta n)
    (hfit n omega hgood).1 (hfit n omega hgood).2 (hsmall n)

/-- Vanishing good-event fingerprint radius makes the marginal probability of
returning the wrong interaction-evidence class tend to zero.  Small-error
separation is required only eventually; early sample sizes may be ambiguous. -/
theorem interactionClassFailure_tendsto_zero_of_vanishing_goodEvent_error
    {Omega : ℕ → Type uOmega} [∀ n, MeasurableSpace (Omega n)]
    {Candidate : Type uCandidate} [Fintype Candidate] [Nonempty Candidate]
    {I : Type uI} {Y : Type uY} [MeasurableSpace Y]
    (C : ChangingSampleEventContract Omega)
    (F : InteractionResponseFamily Candidate I Y)
    (probes : Finset I) (hprobes : probes.Nonempty)
    (observed : ∀ n, Omega n → I → Measure Y)
    (hobserved : ∀ n omega i, IsProbabilityMeasure (observed n omega i))
    (truth : Candidate)
    (estimate : ∀ n, Omega n → Candidate)
    (eta : ℕ → ℝ) (heta : Tendsto eta atTop (𝓝 0))
    (hfit : ∀ n omega, omega ∈ C.good n →
      interactionObservationError F probes hprobes (observed n omega)
          (estimate n omega) ≤ eta n ∧
      interactionObservationError F probes hprobes (observed n omega)
          truth ≤ eta n) :
    Tendsto
      (fun n => (C.μ n).real
        {omega | ¬ InteractionEvidenceEquivalent F probes (estimate n omega) truth})
      atTop (𝓝 0) := by
  have hgap : 0 < canonicalInteractionEvidenceGap F probes hprobes :=
    canonicalInteractionEvidenceGap_pos F probes hprobes
  have hsmall : ∀ᶠ n in atTop,
      2 * eta n < canonicalInteractionEvidenceGap F probes hprobes := by
    have htwo : Tendsto (fun n => 2 * eta n) atTop (𝓝 0) := by
      simpa using heta.const_mul (2 : ℝ)
    exact (tendsto_order.1 htwo).2 _ hgap
  have hbound : ∀ᶠ n in atTop,
      (C.μ n).real
          {omega | ¬ InteractionEvidenceEquivalent F probes (estimate n omega) truth} ≤
        C.schedule.failure n := by
    filter_upwards [hsmall] with n hn
    have hsubset :
        {omega | ¬ InteractionEvidenceEquivalent F probes (estimate n omega) truth} ⊆
          (C.good n)ᶜ := by
      intro omega hbad hgood
      exact hbad (evidenceEquivalent_of_commonObservation
        F probes hprobes (observed n omega) (hobserved n omega) (eta n)
        (hfit n omega hgood).1 (hfit n omega hgood).2 hn)
    let _ : IsProbabilityMeasure (C.μ n) := C.probability n
    exact (measureReal_mono hsubset).trans (C.bad_le_failure n)
  exact squeeze_zero'
    (Filter.Eventually.of_forall (fun _ => measureReal_nonneg))
    hbound C.schedule.failure_tendsto_zero

/-- **Exact finite-candidate P-STAT-08 corollary.**

The frozen theorem controls excess true risk.  For a finite candidate family
with a strict unique true-risk minimizer, P4.1 supplies a canonical positive
risk gap.  If twice the validation radius lies below that gap, selecting the
wrong candidate implies the P-STAT-08 excess-risk bad event, so exact selection
failure has probability at most `alpha`. -/
theorem p_stat_08_exactCandidate_failure_le
    {Omega : Type uOmega} {Z : Type uZ} {Candidate : Type uCandidate}
    [MeasurableSpace Omega] [MeasurableSpace Z]
    [Fintype Candidate] [Nonempty Candidate]
    {N : ℕ} (hN : 0 < N)
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (P : Measure Z)
    (loss : Candidate → Z → ℝ)
    (hloss : ∀ f, Measurable (loss f))
    (hloss01 : ∀ f z, loss f z ∈ Set.Icc (0 : ℝ) 1)
    (sample : Fin N → Omega → Z)
    (hmeas : ∀ n, Measurable (sample n))
    (hindep : iIndepFun sample mu)
    (hlaw : ∀ n, mu.map (sample n) = P)
    (fHat : Omega → Candidate) (fStar : Candidate)
    (hERM : ∀ omega f,
      empiricalRisk (loss (fHat omega)) sample omega ≤
        empiricalRisk (loss f) sample omega)
    (hStrict : ∀ f, f ≠ fStar →
      trueRisk P (loss fStar) < trueRisk P (loss f))
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hsmall :
      2 * pStat08Radius N (Fintype.card Candidate) alpha <
        canonicalRiskGap (fun f => trueRisk P (loss f)) fStar) :
    mu.real {omega | fHat omega ≠ fStar} ≤ alpha := by
  let R : Candidate → ℝ := fun f => trueRisk P (loss f)
  let u := pStat08Radius N (Fintype.card Candidate) alpha
  have hStar : ∀ f, R fStar ≤ R f := by
    intro f
    by_cases h : f = fStar
    · subst f
      exact le_rfl
    · exact (hStrict f h).le
  have htail := p_stat_08 hN mu P loss hloss hloss01
    sample hmeas hindep hlaw fHat fStar hERM hStar halpha0 halpha1
  have hsubset :
      {omega | fHat omega ≠ fStar} ⊆
        {omega | R (fHat omega) > R fStar + 2 * u} := by
    intro omega hwrong
    have hgap := canonicalRiskGap_le_excess R fStar (fHat omega) hwrong
    change R (fHat omega) > R fStar + 2 * u
    have hsmall' : 2 * u < canonicalRiskGap R fStar := by
      simpa [R, u] using hsmall
    linarith
  exact (measureReal_mono hsubset).trans (by simpa [R, u] using htail)

end UEOT.V3.Compression.TheoryCompletion.InverseObjecthood
