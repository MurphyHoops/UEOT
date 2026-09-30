import UEOT.V3.Compression.GoaGaugeInvariance
import UEOT.V3.TotalVariation

/-!
# TV / Dobrushin metric gauge invariance

Finite state relabeling should preserve not only the identity of a unique
invariant GOA, but also the numerical stability certificate used to prove
attraction to that GOA.

This module proves, for a state equivalence `e : S ≃ S`:

* simplex PMFs commute with relabeling;
* finite-law total variation is exactly invariant;
* row PMFs of conjugate kernels commute with relabeling;
* row TV is exactly invariant;
* the Dobrushin coefficient is exactly invariant;
* therefore M-CF geometric mixing bounds transport with the same numerical
  contraction factor.

The proof stays with UEOT's canonical event-supremum TV.  No L1 surrogate or
factor-two renormalization is introduced.
-/

namespace UEOT.V3.Compression.MetricGaugeInvariance

open Function
open UEOT.V3
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.GoaGaugeInvariance
open UEOT.V3.Compression.GaugeSemanticTransfer
open UEOT.V3.Compression.ContractiveFixedPoint

universe uX uS uA

noncomputable section

variable {S : Type uS} [Fintype S] [Nonempty S]

noncomputable local instance stateDecidableEq : DecidableEq S :=
  Classical.decEq S
local instance stateMeasurableSpace : MeasurableSpace S := ⊤

/-- Any equivalence of a finite discrete state space is a measurable
equivalence. -/
def stateMeasurableEquiv (e : S ≃ S) : S ≃ᵐ S :=
  MeasurableEquiv.mk e Measurable.of_discrete Measurable.of_discrete

/-- PMF map by an equivalence has exactly one contributing preimage. -/
theorem pmf_map_equiv_apply_toReal
    (e : S ≃ S) (p : PMF S) (y : S) :
    (((p.map e) y).toReal) = (p (e.symm y)).toReal := by
  rw [PMF.map_apply, tsum_fintype]
  rw [Finset.sum_eq_single (e.symm y)]
  · simp
  · intro b hb hne
    simp only [ite_eq_right_iff]
    intro hy
    exfalso
    apply hne
    apply e.injective
    simpa using hy.symm
  · simp

/-- The simplex relabeling used by the GOA gauge lane is exactly PMF pushforward
by the same state equivalence. -/
theorem simplexPMF_relabel
    (e : S ≃ S) (mu : stdSimplex ℝ S) :
    simplexPMF (relabelSimplex e mu) = (simplexPMF mu).map e := by
  apply PMF.ext
  intro y
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top (simplexPMF (relabelSimplex e mu)) y)
    (PMF.apply_ne_top ((simplexPMF mu).map e) y)).mp
  rw [simplexPMF_toReal]
  rw [PMF.map_apply, tsum_fintype]
  rw [Finset.sum_eq_single (e.symm y)]
  · simp only [Equiv.apply_symm_apply, if_pos, simplexPMF_toReal]
    rfl
  · intro b hb hne
    simp only [ite_eq_right_iff]
    intro hy
    exfalso
    apply hne
    apply e.injective
    simpa using hy.symm
  · simp

/-- Canonical finite-law TV is exactly invariant under state relabeling. -/
theorem lawTV_relabel
    (e : S ≃ S) (mu nu : stdSimplex ℝ S) :
    lawTV (relabelSimplex e mu) (relabelSimplex e nu) = lawTV mu nu := by
  let em : S ≃ᵐ S := stateMeasurableEquiv e
  unfold lawTV FiniteProbabilityRow.tvDist
  rw [simplexPMF_relabel, simplexPMF_relabel]
  rw [← PMF.toMeasure_map e (simplexPMF mu) Measurable.of_discrete,
      ← PMF.toMeasure_map e (simplexPMF nu) Measurable.of_discrete]
  exact UEOT.V3.TotalVariation.tvDist_map_measurableEquiv
    (simplexPMF mu).toMeasure (simplexPMF nu).toMeasure em

/-- Rows of conjugate stochastic matrices are exact PMF pushforwards of one
another. -/
theorem rowPMF_relabel_of_conjugate
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (e : S ≃ S)
    (hconj : ∀ s t, P s t = Q (e s) (e t))
    (s : S) :
    rowPMF Q hQ (e s) = (rowPMF P hP s).map e := by
  apply PMF.ext
  intro y
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top (rowPMF Q hQ (e s)) y)
    (PMF.apply_ne_top ((rowPMF P hP s).map e) y)).mp
  rw [rowPMF_toReal, pmf_map_equiv_apply_toReal, rowPMF_toReal]
  rcases e.surjective y with ⟨t, rfl⟩
  simpa using (hconj s t).symm

/-- Row TV of conjugate kernels is exactly preserved. -/
theorem rowTV_relabel_of_conjugate
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (e : S ≃ S)
    (hconj : ∀ s t, P s t = Q (e s) (e t))
    (s t : S) :
    rowTV Q hQ (e s) (e t) = rowTV P hP s t := by
  let em : S ≃ᵐ S := stateMeasurableEquiv e
  unfold rowTV FiniteProbabilityRow.tvDist
  rw [rowPMF_relabel_of_conjugate P Q hP hQ e hconj s,
      rowPMF_relabel_of_conjugate P Q hP hQ e hconj t]
  rw [← PMF.toMeasure_map e (rowPMF P hP s) Measurable.of_discrete,
      ← PMF.toMeasure_map e (rowPMF P hP t) Measurable.of_discrete]
  exact UEOT.V3.TotalVariation.tvDist_map_measurableEquiv
    (rowPMF P hP s).toMeasure (rowPMF P hP t).toMeasure em

/-- Dobrushin's finite max-row-TV coefficient is a conjugacy invariant. -/
theorem dobrushinAlpha_relabel_of_conjugate
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (e : S ≃ S)
    (hconj : ∀ s t, P s t = Q (e s) (e t)) :
    dobrushinAlpha Q hQ = dobrushinAlpha P hP := by
  have hQ_le_P : ∀ y z, rowTV Q hQ y z ≤ dobrushinAlpha P hP := by
    intro y z
    rcases e.surjective y with ⟨s, rfl⟩
    rcases e.surjective z with ⟨t, rfl⟩
    rw [rowTV_relabel_of_conjugate P Q hP hQ e hconj s t]
    exact rowTV_le_dobrushinAlpha P hP s t
  have hP_le_Q : ∀ s t, rowTV P hP s t ≤ dobrushinAlpha Q hQ := by
    intro s t
    rw [← rowTV_relabel_of_conjugate P Q hP hQ e hconj s t]
    exact rowTV_le_dobrushinAlpha Q hQ (e s) (e t)
  apply le_antisymm
  · unfold dobrushinAlpha
    apply Finset.sup'_le
    intro z hz
    exact hQ_le_P z.1 z.2
  · unfold dobrushinAlpha
    apply Finset.sup'_le
    intro z hz
    exact hP_le_Q z.1 z.2

/-- Geometric M-CF attraction transports across a conjugacy with exactly the
same numerical Dobrushin rate and exactly the same initial TV error. -/
theorem geometricMixing_relabel_of_conjugate
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (e : S ≃ S)
    (hconj : ∀ s t, P s t = Q (e s) (e t))
    (halpha : dobrushinAlpha P hP < 1)
    (mu mustar : stdSimplex ℝ S)
    (hmustar : step P hP mustar = mustar)
    (n : ℕ) :
    lawTV (((step Q hQ)^[n]) (relabelSimplex e mu))
        (relabelSimplex e mustar) ≤
      dobrushinAlpha P hP ^ n * lawTV mu mustar := by
  have halphaQ : dobrushinAlpha Q hQ < 1 := by
    rw [dobrushinAlpha_relabel_of_conjugate P Q hP hQ e hconj]
    exact halpha
  have hmustarQ :
      step Q hQ (relabelSimplex e mustar) = relabelSimplex e mustar :=
    invariant_relabel_of_conjugate P Q hP hQ e hconj mustar hmustar
  have hmix := dobrushin_iterate_to_invariant_le_via_mcf
    Q hQ halphaQ (relabelSimplex e mu) (relabelSimplex e mustar) hmustarQ n
  rw [dobrushinAlpha_relabel_of_conjugate P Q hP hQ e hconj] at hmix
  rw [lawTV_relabel e mu mustar] at hmix
  exact hmix

/-! ## Exact-control / GOA adapter -/

section ControlGauge

variable {X : Type uX} [Fintype X] [Nonempty X]
variable {Act : Type uA} [Fintype Act] [Nonempty Act]

/-- The Dobrushin coefficient of the optimal deterministic closed loop is
exactly quotient-gauge invariant when the target uses the transported source
greedy selector. -/
theorem greedyDobrushinAlpha_gaugeInvariant
    (Q R : ExactControlQuotient X S (fun _ => Act))
    (e : S ≃ S)
    (hsem : SemanticRelabel Q R e) :
    dobrushinAlpha
        (selectorClosedLoopMatrix R.macroModel
          (transportSelector e Q.macroModel.greedyAction))
        (selectorClosedLoopMatrix_rowStochastic R.macroModel
          (transportSelector e Q.macroModel.greedyAction)) =
      dobrushinAlpha
        (selectorClosedLoopMatrix Q.macroModel Q.macroModel.greedyAction)
        (selectorClosedLoopMatrix_rowStochastic
          Q.macroModel Q.macroModel.greedyAction) := by
  apply dobrushinAlpha_relabel_of_conjugate
  intro s t
  exact selectorClosedLoop_conjugate_of_semanticRelabel
    Q R e hsem Q.macroModel.greedyAction s t

/-- Full geometric GOA mixing certificate transported through exact quotient
gauge with no numerical loss.

One source Dobrushin margin supplies a source invariant law by M-CF.  For every
initial source law and every time `n`, both the source chain and the relabeled
target chain satisfy the same geometric TV bound with the same coefficient and
the same initial TV error. -/
theorem greedyGeometricMixing_gaugeInvariant
    (Q R : ExactControlQuotient X S (fun _ => Act))
    (e : S ≃ S)
    (hsem : SemanticRelabel Q R e)
    (halpha :
      dobrushinAlpha
          (selectorClosedLoopMatrix Q.macroModel Q.macroModel.greedyAction)
          (selectorClosedLoopMatrix_rowStochastic
            Q.macroModel Q.macroModel.greedyAction) < 1) :
    ∃ mustarQ : stdSimplex ℝ S,
      let PQ := selectorClosedLoopMatrix Q.macroModel Q.macroModel.greedyAction
      let sigmaR := transportSelector e Q.macroModel.greedyAction
      let PR := selectorClosedLoopMatrix R.macroModel sigmaR
      let hPQ := selectorClosedLoopMatrix_rowStochastic
        Q.macroModel Q.macroModel.greedyAction
      let hPR := selectorClosedLoopMatrix_rowStochastic R.macroModel sigmaR
      step PQ hPQ mustarQ = mustarQ ∧
      dobrushinAlpha PR hPR = dobrushinAlpha PQ hPQ ∧
      (∀ (mu : stdSimplex ℝ S) (n : ℕ),
        lawTV (((step PQ hPQ)^[n]) mu) mustarQ ≤
          dobrushinAlpha PQ hPQ ^ n * lawTV mu mustarQ) ∧
      (∀ (mu : stdSimplex ℝ S) (n : ℕ),
        lawTV (((step PR hPR)^[n]) (relabelSimplex e mu))
            (relabelSimplex e mustarQ) ≤
          dobrushinAlpha PQ hPQ ^ n * lawTV mu mustarQ) := by
  let PQ := selectorClosedLoopMatrix Q.macroModel Q.macroModel.greedyAction
  let sigmaR := transportSelector e Q.macroModel.greedyAction
  let PR := selectorClosedLoopMatrix R.macroModel sigmaR
  let hPQ : PQ ∈ Matrix.rowStochastic ℝ S :=
    selectorClosedLoopMatrix_rowStochastic
      Q.macroModel Q.macroModel.greedyAction
  let hPR : PR ∈ Matrix.rowStochastic ℝ S :=
    selectorClosedLoopMatrix_rowStochastic R.macroModel sigmaR
  have hconj : ∀ s t, PQ s t = PR (e s) (e t) := by
    simpa [PQ, PR, sigmaR] using
      selectorClosedLoop_conjugate_of_semanticRelabel
        Q R e hsem Q.macroModel.greedyAction
  have halphaPQ : dobrushinAlpha PQ hPQ < 1 := by
    simpa [PQ, hPQ] using halpha
  rcases (p_goa_02_via_mcf PQ hPQ halphaPQ).1 with
    ⟨mustarQ, hmustarQ, _⟩
  refine ⟨mustarQ, hmustarQ, ?_, ?_, ?_⟩
  · exact dobrushinAlpha_relabel_of_conjugate PQ PR hPQ hPR e hconj
  · intro mu n
    exact dobrushin_iterate_to_invariant_le_via_mcf
      PQ hPQ halphaPQ mu mustarQ hmustarQ n
  · intro mu n
    exact geometricMixing_relabel_of_conjugate
      PQ PR hPQ hPR e hconj halphaPQ mu mustarQ hmustarQ n

end ControlGauge

end


end UEOT.V3.Compression.MetricGaugeInvariance
