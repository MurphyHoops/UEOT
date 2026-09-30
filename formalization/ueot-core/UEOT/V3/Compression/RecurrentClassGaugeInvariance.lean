import UEOT.V3.Compression.CesaroOccupationGaugeInvariance

/-!
# Recurrent-class gauge invariance

The P-GOA-03 source theorem packages recurrent structure in a rich block
decomposition suited to quantitative perturbation.  Exact representation gauge
should first be separated from that perturbation machinery.

This module therefore works directly with one finite stochastic kernel.  It
formalizes positive-probability reachability, communication, closed carriers,
recurrent carriers, and carrier-supported invariant laws, then proves all of
them invariant under exact state relabeling.

No transient fundamental matrix, small perturbation bound, Dobrushin
contraction, irreducibility of the whole chain, or uniqueness of a class law is
assumed.
-/

namespace UEOT.V3.Compression.RecurrentClassGaugeInvariance

open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.GoaGaugeInvariance
open UEOT.V3.Compression.GaugeSemanticTransfer
open UEOT.V3.Compression.InvariantSetGaugeInvariance

universe uX uS uA

noncomputable section

variable {S : Type uS} [Fintype S] [DecidableEq S]

/-- Exact kernel conjugacy is preserved by every matrix power. -/
theorem pow_conjugate
    (P Q : Matrix S S ℝ)
    (e : S ≃ S)
    (hconj : ∀ s t, P s t = Q (e s) (e t)) :
    ∀ n s t, (P ^ n) s t = (Q ^ n) (e s) (e t) := by
  intro n
  induction n with
  | zero =>
      intro s t
      simp [Matrix.one_apply, e.injective.eq_iff]
  | succ n ih =>
      intro s t
      rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
      exact Fintype.sum_equiv e
        (fun u => (P ^ n) s u * P u t)
        (fun v => (Q ^ n) (e s) v * Q v (e t))
        (fun u => by simp [ih s u, hconj u t])

/-- Positive-probability finite-step reachability.  `n = 0` is allowed, making
the relation reflexive as in the standard communication relation. -/
def Reachable (P : Matrix S S ℝ) (x y : S) : Prop :=
  ∃ n : ℕ, 0 < (P ^ n) x y

/-- Mutual positive-probability reachability. -/
def Communicates (P : Matrix S S ℝ) (x y : S) : Prop :=
  Reachable P x y ∧ Reachable P y x

/-- A state carrier is closed if no positive one-step transition exits it. -/
def ClosedCarrier (P : Matrix S S ℝ) (A : Set S) : Prop :=
  ∀ ⦃x⦄, x ∈ A → ∀ y, 0 < P x y → y ∈ A

/-- A recurrent carrier is a nonempty, internally communicating, closed set.
Minimality/maximality is deliberately not baked in; exact gauge already
preserves this structural certificate, and canonical communicating classes can
be recovered by the usual equivalence-class construction. -/
def RecurrentCarrier (P : Matrix S S ℝ) (A : Set S) : Prop :=
  A.Nonempty ∧
    (∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ A → Communicates P x y) ∧
    ClosedCarrier P A

/-- Reachability is exactly preserved by state gauge. -/
theorem reachable_relabel_iff
    (P Q : Matrix S S ℝ)
    (e : S ≃ S)
    (hconj : ∀ s t, P s t = Q (e s) (e t))
    (x y : S) :
    Reachable Q (e x) (e y) ↔ Reachable P x y := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by simpa [pow_conjugate P Q e hconj n x y] using hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by simpa [← pow_conjugate P Q e hconj n x y] using hn⟩

/-- Communication is exactly preserved by state gauge. -/
theorem communicates_relabel_iff
    (P Q : Matrix S S ℝ)
    (e : S ≃ S)
    (hconj : ∀ s t, P s t = Q (e s) (e t))
    (x y : S) :
    Communicates Q (e x) (e y) ↔ Communicates P x y := by
  simp only [Communicates, reachable_relabel_iff P Q e hconj]

/-- Closed carriers transport exactly under state relabeling. -/
theorem closedCarrier_image_iff
    (P Q : Matrix S S ℝ)
    (e : S ≃ S)
    (hconj : ∀ s t, P s t = Q (e s) (e t))
    (A : Set S) :
    ClosedCarrier Q (e '' A) ↔ ClosedCarrier P A := by
  constructor
  · intro hclosed x hx y hxy
    have hx' : e x ∈ e '' A := ⟨x, hx, rfl⟩
    have hq : 0 < Q (e x) (e y) := by simpa [← hconj x y] using hxy
    rcases hclosed hx' (e y) hq with ⟨z, hz, hez⟩
    have : z = y := e.injective (by simpa using hez)
    simpa [this] using hz
  · intro hclosed _ hxImage y hy
    rcases hxImage with ⟨x, hx, rfl⟩
    rcases e.surjective y with ⟨z, rfl⟩
    have hp : 0 < P x z := by simpa [hconj x z] using hy
    exact ⟨z, hclosed hx z hp, rfl⟩

/-- Recurrent carriers are exact gauge objects. -/
theorem recurrentCarrier_image_iff
    (P Q : Matrix S S ℝ)
    (e : S ≃ S)
    (hconj : ∀ s t, P s t = Q (e s) (e t))
    (A : Set S) :
    RecurrentCarrier Q (e '' A) ↔ RecurrentCarrier P A := by
  constructor
  · rintro ⟨hne, hcomm, hclosed⟩
    refine ⟨?_, ?_, (closedCarrier_image_iff P Q e hconj A).1 hclosed⟩
    · rcases hne with ⟨y, x, hx, hxy⟩
      exact ⟨x, hx⟩
    · intro x hx y hy
      have hxyQ := hcomm ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
      exact (communicates_relabel_iff P Q e hconj x y).1 hxyQ
  · rintro ⟨hne, hcomm, hclosed⟩
    refine ⟨?_, ?_, (closedCarrier_image_iff P Q e hconj A).2 hclosed⟩
    · rcases hne with ⟨x, hx⟩
      exact ⟨e x, x, hx, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact (communicates_relabel_iff P Q e hconj x y).2 (hcomm hx hy)

/-- A law is physically carried by `A` if it vanishes outside `A`. -/
def SupportedOn (mu : stdSimplex ℝ S) (A : Set S) : Prop :=
  ∀ ⦃x⦄, x ∉ A → mu x = 0

/-- Support transport is exact under gauge. -/
theorem supportedOn_relabel_iff
    (e : S ≃ S) (mu : stdSimplex ℝ S) (A : Set S) :
    SupportedOn (relabelSimplex e mu) (e '' A) ↔ SupportedOn mu A := by
  constructor
  · intro hs x hx
    have hex : e x ∉ e '' A := by
      intro himage
      rcases himage with ⟨y, hy, hey⟩
      apply hx
      have : y = x := e.injective (by simpa using hey)
      simpa [this] using hy
    have hz := hs hex
    calc
      mu x = (relabelSimplex e mu) (e x) :=
        by change mu x = mu (e.symm (e x)); simp
      _ = 0 := hz
  · intro hs y hy
    rcases e.surjective y with ⟨x, rfl⟩
    have hx : x ∉ A := by
      intro hx
      exact hy ⟨x, hx, rfl⟩
    calc
      (relabelSimplex e mu) (e x) = mu x :=
        by change mu (e.symm (e x)) = mu x; simp
      _ = 0 := hs hx

/-- Invariant laws carried by one recurrent carrier. -/
def carrierInvariantLawSet
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (A : Set S) : Set (stdSimplex ℝ S) :=
  {mu | mu ∈ invariantLawSet P hP ∧ SupportedOn mu A}

variable [Nonempty S]

/-- Exact gauge transports the complete family of invariant laws supported on
one recurrent carrier. -/
theorem carrierInvariantLawSet_relabel_eq
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (e : S ≃ S)
    (hconj : ∀ s t, P s t = Q (e s) (e t))
    (A : Set S) :
    carrierInvariantLawSet Q hQ (e '' A) =
      relabelSimplex e '' carrierInvariantLawSet P hP A := by
  ext nu
  constructor
  · rintro ⟨hnuInv, hnuSupp⟩
    let mu := relabelSimplex e.symm nu
    have hconjRev : ∀ s t, Q s t = P (e.symm s) (e.symm t) := by
      intro s t
      have h := hconj (e.symm s) (e.symm t)
      simpa using h.symm
    have hmuInv : mu ∈ invariantLawSet P hP :=
      invariant_relabel_of_conjugate Q P hQ hP e.symm hconjRev nu hnuInv
    have hmuSupp : SupportedOn mu A := by
      have hrelabel : relabelSimplex e mu = nu := by
        simp [mu]
      apply (supportedOn_relabel_iff e mu A).1
      rw [hrelabel]
      exact hnuSupp
    refine ⟨mu, ⟨hmuInv, hmuSupp⟩, ?_⟩
    simp [mu]
  · rintro ⟨mu, ⟨hmuInv, hmuSupp⟩, rfl⟩
    exact ⟨
      (relabel_mem_invariantLawSet_iff P Q hP hQ e hconj mu).2 hmuInv,
      (supportedOn_relabel_iff e mu A).2 hmuSupp⟩

/-- Exact semantic quotient gauge preserves recurrent closed-loop carriers for
any transported deterministic selector. -/
theorem selectorRecurrentCarrier_gaugeInvariant
    {X : Type uX} [Fintype X] [Nonempty X]
    {Act : Type uA} [Fintype Act] [Nonempty Act]
    (Q R : ExactControlQuotient X S (fun _ => Act))
    (e : S ≃ S)
    (hsem : SemanticRelabel Q R e)
    (sigma : S → Act) (A : Set S) :
    RecurrentCarrier
        (selectorClosedLoopMatrix R.macroModel (transportSelector e sigma))
        (e '' A) ↔
      RecurrentCarrier
        (selectorClosedLoopMatrix Q.macroModel sigma) A := by
  apply recurrentCarrier_image_iff
  intro s t
  exact selectorClosedLoop_conjugate_of_semanticRelabel
    Q R e hsem sigma s t

end

end UEOT.V3.Compression.RecurrentClassGaugeInvariance
