import UEOT.V3.Compression.GoaGaugeInvariance

/-!
# Set-valued GOA gauge invariance

The unique-Dobrushin GOA lane is intentionally only one special case of
long-run structure.  A finite closed loop may have several recurrent classes
and hence many invariant laws.  In that regime the gauge-invariant object is
the entire invariant-law set, not one distinguished stationary law.

This module proves that exact kernel conjugacy transports that full set
bijectively under the quotient-state relabeling.  No contraction,
irreducibility, aperiodicity, uniqueness, or global-attraction hypothesis is
used.
-/

namespace UEOT.V3.Compression.InvariantSetGaugeInvariance

open UEOT.V3
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.GoaGaugeInvariance
open UEOT.V3.Compression.GaugeSemanticTransfer

universe uX uS uA

noncomputable section

variable {S : Type uS} [Fintype S] [Nonempty S]

noncomputable local instance stateDecidableEq : DecidableEq S :=
  Classical.decEq S

/-- The full invariant-law set of a finite stochastic kernel. -/
def invariantLawSet
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S) :
    Set (stdSimplex ℝ S) :=
  {mu | step P hP mu = mu}

@[simp] theorem mem_invariantLawSet
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (mu : stdSimplex ℝ S) :
    mu ∈ invariantLawSet P hP ↔ step P hP mu = mu := by
  rfl

/-- Under exact kernel conjugacy, invariance is equivalent before and after
state relabeling. -/
theorem relabel_mem_invariantLawSet_iff
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (e : S ≃ S)
    (hconj : ∀ s t, P s t = Q (e s) (e t))
    (mu : stdSimplex ℝ S) :
    relabelSimplex e mu ∈ invariantLawSet Q hQ ↔
      mu ∈ invariantLawSet P hP := by
  have hconjRev : ∀ s t, Q s t = P (e.symm s) (e.symm t) := by
    intro s t
    have h := hconj (e.symm s) (e.symm t)
    simpa using h.symm
  constructor
  · intro hmu
    have hback := invariant_relabel_of_conjugate
      Q P hQ hP e.symm hconjRev (relabelSimplex e mu) hmu
    simpa using hback
  · intro hmu
    exact invariant_relabel_of_conjugate
      P Q hP hQ e hconj mu hmu

/-- Exact conjugacy identifies the complete target invariant-law set with the
pushforward image of the source invariant-law set. -/
theorem invariantLawSet_relabel_eq
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (e : S ≃ S)
    (hconj : ∀ s t, P s t = Q (e s) (e t)) :
    invariantLawSet Q hQ = relabelSimplex e '' invariantLawSet P hP := by
  ext nu
  constructor
  · intro hnu
    let mu := relabelSimplex e.symm nu
    have hconjRev : ∀ s t, Q s t = P (e.symm s) (e.symm t) := by
      intro s t
      have h := hconj (e.symm s) (e.symm t)
      simpa using h.symm
    have hmu : mu ∈ invariantLawSet P hP := by
      exact invariant_relabel_of_conjugate Q P hQ hP e.symm hconjRev nu hnu
    refine ⟨mu, hmu, ?_⟩
    simp [mu]
  · rintro ⟨mu, hmu, rfl⟩
    exact (relabel_mem_invariantLawSet_iff P Q hP hQ e hconj mu).2 hmu

/-- Set-valued GOA of one deterministic closed loop.  This definition remains
meaningful when the chain has multiple recurrent classes and multiple invariant
laws. -/
def selectorInvariantGoaSet
    {Act : Type uA} [Fintype Act] [Nonempty Act]
    (M : Model S (fun _ => Act)) (sigma : S → Act) :
    Set (stdSimplex ℝ S) :=
  invariantLawSet
    (selectorClosedLoopMatrix M sigma)
    (selectorClosedLoopMatrix_rowStochastic M sigma)

/-- Exact semantic quotient gauge transports the **entire** deterministic
closed-loop GOA invariant set, without any Dobrushin or uniqueness assumption. -/
theorem selectorInvariantGoaSet_gaugeInvariant
    {X : Type uX} [Fintype X] [Nonempty X]
    {Act : Type uA} [Fintype Act] [Nonempty Act]
    (Q R : ExactControlQuotient X S (fun _ => Act))
    (e : S ≃ S)
    (hsem : SemanticRelabel Q R e)
    (sigma : S → Act) :
    selectorInvariantGoaSet R.macroModel (transportSelector e sigma) =
      relabelSimplex e '' selectorInvariantGoaSet Q.macroModel sigma := by
  let PQ := selectorClosedLoopMatrix Q.macroModel sigma
  let sigmaR := transportSelector e sigma
  let PR := selectorClosedLoopMatrix R.macroModel sigmaR
  let hPQ : PQ ∈ Matrix.rowStochastic ℝ S :=
    selectorClosedLoopMatrix_rowStochastic Q.macroModel sigma
  let hPR : PR ∈ Matrix.rowStochastic ℝ S :=
    selectorClosedLoopMatrix_rowStochastic R.macroModel sigmaR
  have hconj : ∀ s t, PQ s t = PR (e s) (e t) := by
    simpa [PQ, PR, sigmaR] using
      selectorClosedLoop_conjugate_of_semanticRelabel Q R e hsem sigma
  simpa [selectorInvariantGoaSet, PQ, PR, sigmaR, hPQ, hPR] using
    invariantLawSet_relabel_eq PQ PR hPQ hPR e hconj

/-- The exact greedy closed-loop GOA set is quotient-gauge invariant as a set,
even when it is not a singleton. -/
theorem greedyInvariantGoaSet_gaugeInvariant
    {X : Type uX} [Fintype X] [Nonempty X]
    {Act : Type uA} [Fintype Act] [Nonempty Act]
    (Q R : ExactControlQuotient X S (fun _ => Act))
    (e : S ≃ S)
    (hsem : SemanticRelabel Q R e) :
    selectorInvariantGoaSet R.macroModel
        (transportSelector e Q.macroModel.greedyAction) =
      relabelSimplex e ''
        selectorInvariantGoaSet Q.macroModel Q.macroModel.greedyAction := by
  exact selectorInvariantGoaSet_gaugeInvariant
    Q R e hsem Q.macroModel.greedyAction

end

end UEOT.V3.Compression.InvariantSetGaugeInvariance
