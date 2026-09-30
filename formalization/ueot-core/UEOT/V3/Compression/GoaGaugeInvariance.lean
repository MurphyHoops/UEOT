import UEOT.V3.Compression.GaugeSemanticTransfer
import UEOT.V3.Compression.ContractiveFixedPoint
import UEOT.V3.CoreOperationalAssembly

/-!
# Closed-loop and GOA gauge invariance

This module lifts exact control-semantic quotient gauge through a deterministic
optimal selector to the policy-induced closed-loop dynamics and its unique
invariant law.

The central structure is conjugacy: if quotient states are related by
`e : S ≃ S`, the corresponding closed-loop kernels satisfy

`P_Q s t = P_R (e s) (e t)`.

The same equivalence relabels simplex laws, intertwines one-step evolution, and
therefore transports invariant laws.  Under an explicit Dobrushin margin on
the source closed loop, M-CF supplies uniqueness, so the unique invariant GOA
is a quotient-gauge invariant object.
-/

namespace UEOT.V3.Compression.GoaGaugeInvariance

open Function
open UEOT.V3
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.FiniteDobrushin
open UEOT.V3.CoreOperationalAssembly
open UEOT.V3.Compression.GaugeSemanticTransfer
open UEOT.V3.Compression.ContractiveFixedPoint

universe uX uS uA

noncomputable section

variable {X : Type uX} [Fintype X] [Nonempty X]
variable {S : Type uS} [Fintype S] [Nonempty S]
variable {Act : Type uA} [Fintype Act] [Nonempty Act]

noncomputable local instance stateDecidableEq : DecidableEq S :=
  Classical.decEq S

/-- Transport a deterministic selector through one quotient-state
equivalence. -/
def transportSelector (e : S ≃ S) (sigma : S → Act) : S → Act :=
  fun s => sigma (e.symm s)

@[simp] theorem transportSelector_apply_e
    (e : S ≃ S) (sigma : S → Act) (s : S) :
    transportSelector e sigma (e s) = sigma s := by
  simp [transportSelector]

/-- Existing P-CORE policy matrix specialized to a deterministic selector. -/
def selectorClosedLoopMatrix
    (M : Model S (fun _ => Act)) (sigma : S → Act) : Matrix S S ℝ :=
  policyMatrix M (StationaryPolicy.ofSelector sigma)

theorem selectorClosedLoopMatrix_rowStochastic
    (M : Model S (fun _ => Act)) (sigma : S → Act) :
    selectorClosedLoopMatrix M sigma ∈ Matrix.rowStochastic ℝ S := by
  exact policyMatrix_rowStochastic M (StationaryPolicy.ofSelector sigma)

@[simp] theorem selectorClosedLoopMatrix_apply
    (M : Model S (fun _ => Act)) (sigma : S → Act) (s t : S) :
    selectorClosedLoopMatrix M sigma s t = M.transition s (sigma s) t := by
  classical
  simp [selectorClosedLoopMatrix, policyMatrix,
    Model.policyTransition, StationaryPolicy.ofSelector]

/-- Relabel a finite probability-simplex law along a quotient-state
equivalence. -/
def relabelSimplex (e : S ≃ S) (mu : stdSimplex ℝ S) : stdSimplex ℝ S := by
  refine ⟨fun s => mu (e.symm s), ?_, ?_⟩
  · intro s
    exact stdSimplex.zero_le mu (e.symm s)
  · calc
      (∑ s, mu (e.symm s)) = ∑ s, mu s := e.symm.sum_comp (fun s => mu s)
      _ = 1 := stdSimplex.sum_eq_one mu

@[simp] theorem relabelSimplex_apply_e
    (e : S ≃ S) (mu : stdSimplex ℝ S) (s : S) :
    relabelSimplex e mu (e s) = mu s := by
  change mu (e.symm (e s)) = mu s
  rw [e.symm_apply_apply]

@[simp] theorem relabelSimplex_symm_relabel
    (e : S ≃ S) (mu : stdSimplex ℝ S) :
    relabelSimplex e.symm (relabelSimplex e mu) = mu := by
  apply Subtype.ext
  funext s
  change relabelSimplex e mu (e s) = mu s
  exact relabelSimplex_apply_e e mu s

@[simp] theorem relabelSimplex_relabel_symm
    (e : S ≃ S) (mu : stdSimplex ℝ S) :
    relabelSimplex e (relabelSimplex e.symm mu) = mu := by
  simpa using relabelSimplex_symm_relabel (e := e.symm) mu

/-- A conjugacy of stochastic matrices intertwines their simplex evolution. -/
theorem step_relabel_of_conjugate
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (e : S ≃ S)
    (hconj : ∀ s t, P s t = Q (e s) (e t))
    (mu : stdSimplex ℝ S) :
    relabelSimplex e (step P hP mu) =
      step Q hQ (relabelSimplex e mu) := by
  apply Subtype.ext
  funext z
  rcases e.surjective z with ⟨t, rfl⟩
  change
    (step P hP mu).1 (e.symm (e t)) =
      (step Q hQ (relabelSimplex e mu)).1 (e t)
  rw [e.symm_apply_apply, step_apply, step_apply]
  have hsum := Fintype.sum_equiv e
    (fun s => mu s * P s t)
    (fun y => relabelSimplex e mu y * Q y (e t))
    (fun s => by simp [hconj s t])
  exact hsum

/-- Invariant laws transport forward through matrix conjugacy. -/
theorem invariant_relabel_of_conjugate
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (e : S ≃ S)
    (hconj : ∀ s t, P s t = Q (e s) (e t))
    (mu : stdSimplex ℝ S)
    (hmu : step P hP mu = mu) :
    step Q hQ (relabelSimplex e mu) = relabelSimplex e mu := by
  calc
    step Q hQ (relabelSimplex e mu) =
        relabelSimplex e (step P hP mu) :=
      (step_relabel_of_conjugate P Q hP hQ e hconj mu).symm
    _ = relabelSimplex e mu := by rw [hmu]

/-- Uniqueness of an invariant law is preserved by conjugacy. -/
theorem uniqueInvariant_relabel_of_conjugate
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (e : S ≃ S)
    (hconj : ∀ s t, P s t = Q (e s) (e t))
    (mustar : stdSimplex ℝ S)
    (hmustar : step P hP mustar = mustar)
    (hunique : ∀ mu, step P hP mu = mu → mu = mustar) :
    step Q hQ (relabelSimplex e mustar) = relabelSimplex e mustar ∧
      ∀ nu, step Q hQ nu = nu → nu = relabelSimplex e mustar := by
  have hconjRev : ∀ s t, Q s t = P (e.symm s) (e.symm t) := by
    intro s t
    have h := hconj (e.symm s) (e.symm t)
    simpa using h.symm
  constructor
  · exact invariant_relabel_of_conjugate
      P Q hP hQ e hconj mustar hmustar
  · intro nu hnu
    have hback :
        step P hP (relabelSimplex e.symm nu) =
          relabelSimplex e.symm nu :=
      invariant_relabel_of_conjugate
        Q P hQ hP e.symm hconjRev nu hnu
    have hbackEq : relabelSimplex e.symm nu = mustar :=
      hunique _ hback
    calc
      nu = relabelSimplex e (relabelSimplex e.symm nu) :=
        (relabelSimplex_relabel_symm e nu).symm
      _ = relabelSimplex e mustar := by rw [hbackEq]

/-- Semantic quotient relabeling conjugates deterministic closed loops when
the selector is transported along the same state equivalence. -/
theorem selectorClosedLoop_conjugate_of_semanticRelabel
    (Q R : ExactControlQuotient X S (fun _ => Act))
    (e : S ≃ S)
    (hsem : SemanticRelabel Q R e)
    (sigma : S → Act) :
    ∀ s t,
      selectorClosedLoopMatrix Q.macroModel sigma s t =
        selectorClosedLoopMatrix R.macroModel
          (transportSelector e sigma) (e s) (e t) := by
  rcases hsem with ⟨_, _, htransition, _, _, _⟩
  intro s t
  rw [selectorClosedLoopMatrix_apply, selectorClosedLoopMatrix_apply,
    transportSelector_apply_e]
  exact htransition s (sigma s) t

/-- A source canonical greedy selector transported through a semantic quotient
relabeling remains Bellman-optimal on every target state.  Literal equality
with the target's own canonical `greedyAction` is intentionally not claimed. -/
theorem transportedGreedy_optimal_of_semanticRelabel
    (Q R : ExactControlQuotient X S (fun _ => Act))
    (e : S ≃ S)
    (hsem : SemanticRelabel Q R e) :
    ∀ s,
      R.macroModel.qValue R.macroModel.optimalValue s
          (transportSelector e Q.macroModel.greedyAction s) =
        R.macroModel.optimalValue s := by
  rcases hsem with ⟨_, _, _, _, _, hgreedy⟩
  intro s
  rcases e.surjective s with ⟨x, rfl⟩
  simpa using hgreedy x

/-- Main GOA gauge theorem.

Assume two exact quotients are already related by one exact semantic relabeling.
Use the source quotient's canonical greedy selector and transport it to the
target quotient.  If the source greedy closed loop has Dobrushin coefficient
strictly below one, then:

* the transported target selector is Bellman-optimal;
* the two policy-induced closed-loop matrices are conjugate;
* the source closed loop has one unique invariant law by M-CF;
* the target closed loop has one unique invariant law, exactly the relabeling
  of the source law.
-/
theorem greedyUniqueGoa_gaugeInvariant
    (Q R : ExactControlQuotient X S (fun _ => Act))
    (e : S ≃ S)
    (hsem : SemanticRelabel Q R e)
    (halpha :
      dobrushinAlpha
          (selectorClosedLoopMatrix Q.macroModel Q.macroModel.greedyAction)
          (selectorClosedLoopMatrix_rowStochastic
            Q.macroModel Q.macroModel.greedyAction) < 1) :
    let sigmaR := transportSelector e Q.macroModel.greedyAction
    let PQ := selectorClosedLoopMatrix Q.macroModel Q.macroModel.greedyAction
    let PR := selectorClosedLoopMatrix R.macroModel sigmaR
    let hPQ := selectorClosedLoopMatrix_rowStochastic
      Q.macroModel Q.macroModel.greedyAction
    let hPR := selectorClosedLoopMatrix_rowStochastic R.macroModel sigmaR
    (∀ s,
      R.macroModel.qValue R.macroModel.optimalValue s (sigmaR s) =
        R.macroModel.optimalValue s) ∧
    (∀ s t, PQ s t = PR (e s) (e t)) ∧
    ∃ mustarQ mustarR : stdSimplex ℝ S,
      step PQ hPQ mustarQ = mustarQ ∧
      (∀ mu, step PQ hPQ mu = mu → mu = mustarQ) ∧
      mustarR = relabelSimplex e mustarQ ∧
      step PR hPR mustarR = mustarR ∧
      (∀ nu, step PR hPR nu = nu → nu = mustarR) := by
  dsimp only
  let sigmaR := transportSelector e Q.macroModel.greedyAction
  let PQ := selectorClosedLoopMatrix Q.macroModel Q.macroModel.greedyAction
  let PR := selectorClosedLoopMatrix R.macroModel sigmaR
  let hPQ : PQ ∈ Matrix.rowStochastic ℝ S :=
    selectorClosedLoopMatrix_rowStochastic
      Q.macroModel Q.macroModel.greedyAction
  let hPR : PR ∈ Matrix.rowStochastic ℝ S :=
    selectorClosedLoopMatrix_rowStochastic R.macroModel sigmaR
  have hopt : ∀ s,
      R.macroModel.qValue R.macroModel.optimalValue s (sigmaR s) =
        R.macroModel.optimalValue s := by
    simpa [sigmaR] using
      transportedGreedy_optimal_of_semanticRelabel Q R e hsem
  have hconj : ∀ s t, PQ s t = PR (e s) (e t) := by
    simpa [PQ, PR, sigmaR] using
      selectorClosedLoop_conjugate_of_semanticRelabel
        Q R e hsem Q.macroModel.greedyAction
  have hgoaQ :=
    (p_goa_02_via_mcf PQ hPQ (by simpa [PQ, hPQ] using halpha)).1
  rcases hgoaQ with ⟨mustarQ, hmustarQ, huniqueQ⟩
  have hgoaR := uniqueInvariant_relabel_of_conjugate
    PQ PR hPQ hPR e hconj mustarQ hmustarQ huniqueQ
  let mustarR := relabelSimplex e mustarQ
  refine ⟨hopt, hconj, mustarQ, mustarR,
    hmustarQ, huniqueQ, rfl, ?_, ?_⟩
  · exact hgoaR.1
  · exact hgoaR.2

/-- Direct representation-gauge-to-GOA wrapper.

The caller supplies only the source-level gauge facts — literal equality of the
micro model and equality of encoder fibres — plus the source greedy closed-loop
Dobrushin margin.  M-QD's quotient-gauge theorem constructs the unique semantic
state relabeling, after which `greedyUniqueGoa_gaugeInvariant` transports the
optimal closed loop and its unique invariant GOA.
-/
theorem exists_greedyUniqueGoa_gaugeInvariant_of_sameFibers
    (Q R : ExactControlQuotient X S (fun _ => Act))
    (hMicro : Q.micro = R.micro)
    (hsame : UEOT.V3.Compression.QuotientGauge.SameFibers Q.f R.f)
    (halpha :
      dobrushinAlpha
          (selectorClosedLoopMatrix Q.macroModel Q.macroModel.greedyAction)
          (selectorClosedLoopMatrix_rowStochastic
            Q.macroModel Q.macroModel.greedyAction) < 1) :
    ∃ e : S ≃ S,
      SemanticRelabel Q R e ∧
      (let sigmaR := transportSelector e Q.macroModel.greedyAction
       let PQ := selectorClosedLoopMatrix Q.macroModel Q.macroModel.greedyAction
       let PR := selectorClosedLoopMatrix R.macroModel sigmaR
       let hPQ := selectorClosedLoopMatrix_rowStochastic
         Q.macroModel Q.macroModel.greedyAction
       let hPR := selectorClosedLoopMatrix_rowStochastic R.macroModel sigmaR
       (∀ s,
         R.macroModel.qValue R.macroModel.optimalValue s (sigmaR s) =
           R.macroModel.optimalValue s) ∧
       (∀ s t, PQ s t = PR (e s) (e t)) ∧
       ∃ mustarQ mustarR : stdSimplex ℝ S,
         step PQ hPQ mustarQ = mustarQ ∧
         (∀ mu, step PQ hPQ mu = mu → mu = mustarQ) ∧
         mustarR = relabelSimplex e mustarQ ∧
         step PR hPR mustarR = mustarR ∧
         (∀ nu, step PR hPR nu = nu → nu = mustarR)) := by
  rcases existsUnique_semanticRelabel_of_sameFibers Q R hMicro hsame with
    ⟨e, hsem, _⟩
  refine ⟨e, hsem, ?_⟩
  exact greedyUniqueGoa_gaugeInvariant Q R e hsem halpha

end


end UEOT.V3.Compression.GoaGaugeInvariance
