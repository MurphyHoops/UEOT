import UEOT.V3.Compression.RecurrentSupportMargin

/-!
# Topology-changing GOA semantics

Recurrent topology may genuinely change when support edges are added or
deleted.  In that regime the frozen P-GOA-03 class labels are no longer the
right comparison object: a merged target carrier need not preserve either
source class stationary law, and a split target need not preserve the old class
mixture decomposition.

The first required semantic fact is therefore label-free existence: every
finite closed recurrent carrier supports at least one invariant law of the
ambient kernel itself.

The proof deliberately routes through the existing finite Cesaro/M-OI
machinery rather than constructing a separate restricted Markov chain:

* closedness keeps one-step mass inside the carrier;
* hence every finite orbit and Cesaro average stays inside;
* support is closed under coordinatewise limits;
* P-GOA-01 supplies a convergent Cesaro subsequence whose limit is invariant.

This produces a new carrier-level GOA object after topology change without
reusing stale source class labels or stationary laws.
-/

namespace UEOT.V3.Compression.TopologyChangingGoaSemantics

open Filter Topology
open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.FiniteCesaroInvariant
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.Compression.RecurrentClassGaugeInvariance
open UEOT.V3.Compression.RecurrentSupportMargin

universe uS

noncomputable section

variable {S : Type uS} [Fintype S] [Nonempty S]

noncomputable local instance stateDecidableEq : DecidableEq S :=
  Classical.decEq S

/-- A closed carrier is invariant under one Markov step at the level of law
support. -/
theorem step_supportedOn_of_closedCarrier
    (P : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (A : Set S)
    (hclosed : ClosedCarrier P A)
    (mu : stdSimplex ℝ S)
    (hmu : SupportedOn mu A) :
    SupportedOn (step P hP mu) A := by
  intro y hy
  change (step P hP mu).1 y = 0
  rw [step_apply]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : x ∈ A
  · have hPxy : P x y = 0 := by
      apply le_antisymm
      · apply le_of_not_gt
        intro hpos
        exact hy (hclosed hx y hpos)
      · exact hP.1 x y
    simp [hPxy]
  · have hmux : mu x = 0 := hmu hx
    change mu.1 x = 0 at hmux
    rw [hmux, zero_mul]

/-- Closed carriers contain every finite-time orbit law started inside them. -/
theorem orbit_supportedOn_of_closedCarrier
    (P : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (A : Set S)
    (hclosed : ClosedCarrier P A)
    (mu : stdSimplex ℝ S)
    (hmu : SupportedOn mu A) :
    ∀ n, SupportedOn (orbit P hP mu n) A := by
  intro n
  induction n with
  | zero =>
      intro y hy
      have h0 := congrFun (orbit_zero P hP mu) y
      calc
        (orbit P hP mu 0) y = mu y := h0
        _ = 0 := hmu hy
  | succ n ih =>
      have hstep : orbit P hP mu (n + 1) = step P hP (orbit P hP mu n) := by
        apply Subtype.ext
        exact orbit_succ P hP mu n
      rw [hstep]
      exact step_supportedOn_of_closedCarrier P hP A hclosed
        (orbit P hP mu n) ih

/-- Every finite Cesaro occupation law stays inside a closed carrier when the
initial law does. -/
theorem cesaroRow_supportedOn_of_closedCarrier
    (P : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (A : Set S)
    (hclosed : ClosedCarrier P A)
    (mu : stdSimplex ℝ S)
    (hmu : SupportedOn mu A)
    (n : ℕ) :
    SupportedOn (cesaroRow P hP mu n) A := by
  intro y hy
  have hcoe := congrFun (cesaroRow_coe P hP mu n) y
  rw [hcoe]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  have horbit : ∀ t, (orbit P hP mu t) y = 0 := by
    intro t
    exact orbit_supportedOn_of_closedCarrier P hP A hclosed mu hmu t hy
  simp [horbit]

/-- Support in a fixed carrier is closed under simplex convergence. -/
theorem supportedOn_of_tendsto
    (A : Set S)
    (f : ℕ → stdSimplex ℝ S)
    (nu : stdSimplex ℝ S)
    (hsupp : ∀ n, SupportedOn (f n) A)
    (hlim : Tendsto f atTop (𝓝 nu)) :
    SupportedOn nu A := by
  intro y hy
  have hcoe := tendsto_subtype_rng.mp hlim
  have hcoord : Tendsto (fun n => (f n) y) atTop (𝓝 (nu y)) :=
    (tendsto_pi_nhds.mp hcoe) y
  have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds
  have hcoordZero : Tendsto (fun n => (f n) y) atTop (𝓝 0) := by
    convert hzero using 1
    funext n
    exact hsupp n hy
  exact tendsto_nhds_unique hcoord hcoordZero

/-- A simplex vertex carried by any set containing its state. -/
theorem pureSimplex_supportedOn
    (A : Set S) (x0 : S) (hx0 : x0 ∈ A) :
    SupportedOn (pureSimplex x0) A := by
  intro y hy
  have hne : y ≠ x0 := by
    intro h
    apply hy
    simpa [h] using hx0
  change Function.update (fun _ : S => (0 : ℝ)) x0 1 y = 0
  rw [Function.update_of_ne hne]

/-- **Carrier-level GOA existence.** Every finite recurrent carrier supports at
least one invariant law of the ambient stochastic kernel.

This is intentionally independent of any frozen recurrent-class label or
fixed-partition decomposition.  It therefore remains meaningful after a
topology-changing merge has produced a new recurrent carrier. -/
theorem recurrentCarrier_carrierInvariantLawSet_nonempty
    (P : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (A : Set S)
    (hrec : RecurrentCarrier P A) :
    (carrierInvariantLawSet P hP A).Nonempty := by
  rcases hrec.1 with ⟨x0, hx0⟩
  let mu0 : stdSimplex ℝ S := pureSimplex x0
  have hmu0 : SupportedOn mu0 A := by
    simpa [mu0] using pureSimplex_supportedOn A x0 hx0
  rcases (p_goa_01 P hP mu0).1 with ⟨nu, phi, hphi, hlim⟩
  have hnuSupp : SupportedOn nu A := by
    apply supportedOn_of_tendsto A (cesaroRow P hP mu0 ∘ phi) nu
    · intro n
      exact cesaroRow_supportedOn_of_closedCarrier
        P hP A hrec.2.2 mu0 hmu0 (phi n)
    · exact hlim
  have hnuInvVec := (p_goa_01 P hP mu0).2 nu phi hphi hlim
  have hnuInv : nu ∈ invariantLawSet P hP := by
    apply Subtype.ext
    exact hnuInvVec
  exact ⟨nu, hnuInv, hnuSupp⟩

/-- **Merge semantics without stale class labels.**  If two source recurrent
carriers merge into one target recurrent carrier by the structural cross-
communication criterion, then the merged target carrier supports at least one
target invariant law.  No source class stationary law is assumed to remain
invariant after the topology change. -/
theorem mergedCarrier_carrierInvariantLawSet_nonempty_of_cross
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (hsupp : TransitionSupportLe P Q)
    (A B : Set S)
    (hrecA : RecurrentCarrier P A)
    (hrecB : RecurrentCarrier P B)
    {a b : S} (ha : a ∈ A) (hb : b ∈ B)
    (hcross : Communicates Q a b)
    (hclosed : ClosedCarrier Q (A ∪ B)) :
    (carrierInvariantLawSet Q hQ (A ∪ B)).Nonempty := by
  apply recurrentCarrier_carrierInvariantLawSet_nonempty Q hQ (A ∪ B)
  exact recurrentCarrier_union_of_cross_of_closed
    P Q hP hQ hsupp A B hrecA hrecB ha hb hcross hclosed

/-- Operational topology-changing GOA theorem: retained source support, one
new positive cross-edge each way, and target closure of the union not only
force a recurrent merge, but also generate a nonempty invariant-law family on
that new merged carrier. -/
theorem mergedCarrier_carrierInvariantLawSet_nonempty_of_two_edges
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (hsupp : TransitionSupportLe P Q)
    (A B : Set S)
    (hrecA : RecurrentCarrier P A)
    (hrecB : RecurrentCarrier P B)
    {a₁ a₂ b₁ b₂ : S}
    (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A)
    (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B)
    (hAB : 0 < Q a₁ b₁)
    (hBA : 0 < Q b₂ a₂)
    (hclosed : ClosedCarrier Q (A ∪ B)) :
    (carrierInvariantLawSet Q hQ (A ∪ B)).Nonempty := by
  apply recurrentCarrier_carrierInvariantLawSet_nonempty Q hQ (A ∪ B)
  exact recurrentCarrier_union_of_two_edges_of_closed
    P Q hP hQ hsupp A B hrecA hrecB
      ha₁ ha₂ hb₁ hb₂ hAB hBA hclosed

end

end UEOT.V3.Compression.TopologyChangingGoaSemantics
