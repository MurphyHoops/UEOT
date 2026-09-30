import UEOT.V3.Compression.ApproximateSemanticGauge

/-!
# Approximate GOA gauge stability

Approximate semantic gauge control of transition rows can be lifted one more
step, from actionwise model semantics to stationary closed-loop behavior.

The comparison is intentionally policy-fixed.  A source deterministic selector
is transported through the exact quotient-state gauge, the source closed-loop
kernel is relabeled into target coordinates, and only then are the two kernels
compared.  Under a source Dobrushin margin, M-CF converts the rowwise transition
error into a stationary-law perturbation tube.

No claim is made here that a small semantic error preserves the target's own
greedy selector.  That requires a separate action-gap stability theorem.
-/

namespace UEOT.V3.Compression.ApproximateGoaGaugeStability

open Function
open UEOT.V3
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.GoaGaugeInvariance
open UEOT.V3.Compression.MetricGaugeInvariance
open UEOT.V3.Compression.ApproximateSemanticGauge
open UEOT.V3.Compression.ContractiveFixedPoint

universe uX uS uA

noncomputable section

variable {X : Type uX} [Fintype X] [Nonempty X]
variable {S : Type uS} [Fintype S] [Nonempty S]
variable {Act : Type uA} [Fintype Act] [Nonempty Act]

noncomputable local instance stateDecidableEq : DecidableEq S :=
  Classical.decEq S

/-- The PMF row of a deterministic-selector closed loop is the model
transition PMF at the selected action. -/
theorem rowPMF_selectorClosedLoopMatrix
    (M : Model S (fun _ => Act)) (sigma : S → Act) (s : S) :
    rowPMF (selectorClosedLoopMatrix M sigma)
      (selectorClosedLoopMatrix_rowStochastic M sigma) s =
      M.transitionPMF s (sigma s) := by
  apply PMF.ext
  intro t
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top
      (rowPMF (selectorClosedLoopMatrix M sigma)
        (selectorClosedLoopMatrix_rowStochastic M sigma) s) t)
    (PMF.apply_ne_top (M.transitionPMF s (sigma s)) t)).mp
  rw [rowPMF_toReal, Model.transitionPMF_apply_toReal,
    selectorClosedLoopMatrix_apply]

/-- Under one exact quotient-state gauge, the source fixed-policy closed loop,
relabelled into target coordinates, is rowwise close to the target fixed-policy
closed loop by the sum of the two transition-defect envelopes. -/
theorem fixedPolicy_closedLoop_relabel_tv_le
    (Q R : ApproxControlQuotient X S (fun _ => Act))
    (hMicro : Q.micro = R.micro)
    (e : S ≃ S) (he : e ∘ Q.f = R.f)
    (sigma : S → Act) :
    let PQ := selectorClosedLoopMatrix Q.macroModel sigma
    let sigmaR := transportSelector e sigma
    let PR := selectorClosedLoopMatrix R.macroModel sigmaR
    let hPQ := selectorClosedLoopMatrix_rowStochastic Q.macroModel sigma
    let hPR := selectorClosedLoopMatrix_rowStochastic R.macroModel sigmaR
    let Pbar := PQ.reindex e e
    let hPbar : Pbar ∈ Matrix.rowStochastic ℝ S :=
      Matrix.reindex_mem_rowStochastic hPQ
    ∀ y, crossRowTV Pbar hPbar PR hPR y ≤
      Q.epsilonTransition + R.epsilonTransition := by
  dsimp only
  intro y
  rcases e.surjective y with ⟨s, rfl⟩
  let PQ := selectorClosedLoopMatrix Q.macroModel sigma
  let sigmaR := transportSelector e sigma
  let PR := selectorClosedLoopMatrix R.macroModel sigmaR
  let hPQ : PQ ∈ Matrix.rowStochastic ℝ S :=
    selectorClosedLoopMatrix_rowStochastic Q.macroModel sigma
  let hPR : PR ∈ Matrix.rowStochastic ℝ S :=
    selectorClosedLoopMatrix_rowStochastic R.macroModel sigmaR
  let Pbar := PQ.reindex e e
  let hPbar : Pbar ∈ Matrix.rowStochastic ℝ S :=
    Matrix.reindex_mem_rowStochastic hPQ
  have hconj : ∀ x z, PQ x z = Pbar (e x) (e z) := by
    intro x z
    simp [Pbar]
  unfold crossRowTV
  rw [rowPMF_relabel_of_conjugate PQ Pbar hPQ hPbar e hconj s]
  rw [rowPMF_selectorClosedLoopMatrix Q.macroModel sigma s]
  rw [rowPMF_selectorClosedLoopMatrix R.macroModel sigmaR (e s)]
  simpa [sigmaR, transportSelector] using
    (macroTransition_relabel_tv_le Q R hMicro e he s (sigma s))

/-- Approximate semantic gauge stability lifts to stationary near-GOA
stability for one fixed transported policy.

The source closed loop is Dobrushin contractive.  Its unique invariant law is
relabelled into target coordinates.  Every invariant law of the target closed
loop under the transported same policy lies within
`(εp_Q + εp_R) / (1 - α_Q)` in canonical TV.

The target need not itself have a unique invariant law.  Literal target-greedy
policy stability is deliberately not claimed here. -/
theorem fixedPolicy_near_goa_gauge_stability
    (Q R : ApproxControlQuotient X S (fun _ => Act))
    (hMicro : Q.micro = R.micro)
    (e : S ≃ S) (he : e ∘ Q.f = R.f)
    (sigma : S → Act)
    (halpha :
      dobrushinAlpha
        (selectorClosedLoopMatrix Q.macroModel sigma)
        (selectorClosedLoopMatrix_rowStochastic Q.macroModel sigma) < 1) :
    ∃ mustarQ : stdSimplex ℝ S,
      step
          (selectorClosedLoopMatrix Q.macroModel sigma)
          (selectorClosedLoopMatrix_rowStochastic Q.macroModel sigma)
          mustarQ = mustarQ ∧
      (∀ nu : stdSimplex ℝ S,
        step
            (selectorClosedLoopMatrix Q.macroModel sigma)
            (selectorClosedLoopMatrix_rowStochastic Q.macroModel sigma)
            nu = nu → nu = mustarQ) ∧
      ∀ muR : stdSimplex ℝ S,
        step
            (selectorClosedLoopMatrix R.macroModel (transportSelector e sigma))
            (selectorClosedLoopMatrix_rowStochastic R.macroModel
              (transportSelector e sigma))
            muR = muR →
        lawTV (relabelSimplex e mustarQ) muR ≤
          (Q.epsilonTransition + R.epsilonTransition) /
            (1 - dobrushinAlpha
              (selectorClosedLoopMatrix Q.macroModel sigma)
              (selectorClosedLoopMatrix_rowStochastic Q.macroModel sigma)) := by
  let PQ := selectorClosedLoopMatrix Q.macroModel sigma
  let sigmaR := transportSelector e sigma
  let PR := selectorClosedLoopMatrix R.macroModel sigmaR
  let hPQ : PQ ∈ Matrix.rowStochastic ℝ S :=
    selectorClosedLoopMatrix_rowStochastic Q.macroModel sigma
  let hPR : PR ∈ Matrix.rowStochastic ℝ S :=
    selectorClosedLoopMatrix_rowStochastic R.macroModel sigmaR
  let Pbar := PQ.reindex e e
  let hPbar : Pbar ∈ Matrix.rowStochastic ℝ S :=
    Matrix.reindex_mem_rowStochastic hPQ
  have halphaPQ : dobrushinAlpha PQ hPQ < 1 := by
    simpa [PQ, hPQ] using halpha
  rcases (p_goa_02_via_mcf PQ hPQ halphaPQ).1 with
    ⟨mustarQ, hmustarQ, huniqueQ⟩
  refine ⟨mustarQ, ?_, ?_, ?_⟩
  · simpa [PQ, hPQ] using hmustarQ
  · intro nu hnu
    apply huniqueQ nu
    simpa [PQ, hPQ] using hnu
  · intro muR hmuR
    have hconj : ∀ x z, PQ x z = Pbar (e x) (e z) := by
      intro x z
      simp [Pbar]
    have hmustarBar :
        step Pbar hPbar (relabelSimplex e mustarQ) =
          relabelSimplex e mustarQ :=
      invariant_relabel_of_conjugate
        PQ Pbar hPQ hPbar e hconj mustarQ hmustarQ
    have halphaBar : dobrushinAlpha Pbar hPbar < 1 := by
      rw [dobrushinAlpha_relabel_of_conjugate PQ Pbar hPQ hPbar e hconj]
      exact halphaPQ
    have hrow : ∀ y, crossRowTV Pbar hPbar PR hPR y ≤
        Q.epsilonTransition + R.epsilonTransition := by
      simpa [PQ, PR, sigmaR, hPQ, hPR, Pbar, hPbar] using
        fixedPolicy_closedLoop_relabel_tv_le Q R hMicro e he sigma
    have hmuR' : step PR hPR muR = muR := by
      simpa [PR, sigmaR, hPR] using hmuR
    have hbound := stationary_perturbation_via_mcf
      Pbar hPbar PR hPR halphaBar
      (relabelSimplex e mustarQ) muR hmustarBar hmuR'
      (Q.epsilonTransition + R.epsilonTransition) hrow
    rw [dobrushinAlpha_relabel_of_conjugate PQ Pbar hPQ hPbar e hconj] at hbound
    simpa [PQ, hPQ] using hbound

end

end UEOT.V3.Compression.ApproximateGoaGaugeStability
