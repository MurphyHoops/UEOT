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

/-- Set of all subsequential Cesaro occupation limits from one initial law.
This is an initial-condition-resolved long-run semantic object that does not
mention any recurrent-class labels. -/
def cesaroLimitSet
    (P : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (mu0 : stdSimplex ℝ S) : Set (stdSimplex ℝ S) :=
  {nu | ∃ phi : ℕ → ℕ,
    StrictMono phi ∧ Tendsto (cesaroRow P hP mu0 ∘ phi) atTop (𝓝 nu)}

/-- The probability-simplex face cut out by support in a state carrier.  This
depends only on the common state space and the carrier, not on a Markov kernel
or a recurrent-class label. -/
def supportFace (A : Set S) : Set (stdSimplex ℝ S) :=
  {mu | SupportedOn mu A}

/-- Support faces are monotone with carrier inclusion. -/
theorem supportFace_mono
    {A B : Set S} (hAB : A ⊆ B) :
    supportFace A ⊆ supportFace B := by
  intro mu hmu y hyB
  apply hmu
  intro hyA
  exact hyB (hAB hyA)

/-- Every carrier-supported invariant-law family lies inside the corresponding
support face, independently of the kernel's other recurrent structure. -/
theorem carrierInvariantLawSet_subset_supportFace
    (P : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (A : Set S) :
    carrierInvariantLawSet P hP A ⊆ supportFace A := by
  intro mu hmu
  exact hmu.2

/-- P-GOA-01 gives at least one Cesaro subsequential limit from every initial
law in the finite setting. -/
theorem cesaroLimitSet_nonempty
    (P : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (mu0 : stdSimplex ℝ S) :
    (cesaroLimitSet P hP mu0).Nonempty := by
  rcases (p_goa_01 P hP mu0).1 with ⟨nu, phi, hphi, hlim⟩
  exact ⟨nu, phi, hphi, hlim⟩

/-- Every Cesaro subsequential limit is an invariant law. -/
theorem cesaroLimitSet_subset_invariantLawSet
    (P : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (mu0 : stdSimplex ℝ S) :
    cesaroLimitSet P hP mu0 ⊆ invariantLawSet P hP := by
  intro nu hnu
  rcases hnu with ⟨phi, hphi, hlim⟩
  have hinv := (p_goa_01 P hP mu0).2 nu phi hphi hlim
  apply Subtype.ext
  exact hinv

/-- If the initial law is carried by a closed carrier, every realizable Cesaro
limit belongs to that carrier's invariant-law family. -/
theorem cesaroLimitSet_subset_carrierInvariantLawSet_of_closed
    (P : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (A : Set S)
    (hclosed : ClosedCarrier P A)
    (mu0 : stdSimplex ℝ S)
    (hmu0 : SupportedOn mu0 A) :
    cesaroLimitSet P hP mu0 ⊆ carrierInvariantLawSet P hP A := by
  intro nu hnu
  rcases hnu with ⟨phi, hphi, hlim⟩
  have hinvVec := (p_goa_01 P hP mu0).2 nu phi hphi hlim
  have hinv : nu ∈ invariantLawSet P hP := by
    apply Subtype.ext
    exact hinvVec
  have hsupp : SupportedOn nu A := by
    apply supportedOn_of_tendsto A (cesaroRow P hP mu0 ∘ phi) nu
    · intro n
      exact cesaroRow_supportedOn_of_closedCarrier
        P hP A hclosed mu0 hmu0 (phi n)
    · exact hlim
  exact ⟨hinv, hsupp⟩

/-- For a recurrent carrier and an initial state inside it, the Cesaro limit
set is nonempty and every one of its elements lies in the carrier-level GOA
family. -/
theorem recurrentCarrier_pure_cesaro_semantics
    (P : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (A : Set S)
    (hrec : RecurrentCarrier P A)
    (x0 : S) (hx0 : x0 ∈ A) :
    (cesaroLimitSet P hP (pureSimplex x0)).Nonempty ∧
      cesaroLimitSet P hP (pureSimplex x0) ⊆
        carrierInvariantLawSet P hP A := by
  exact ⟨
    cesaroLimitSet_nonempty P hP (pureSimplex x0),
    cesaroLimitSet_subset_carrierInvariantLawSet_of_closed
      P hP A hrec.2.2 (pureSimplex x0)
        (pureSimplex_supportedOn A x0 hx0)⟩

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

/-- Initial-condition-resolved merge semantics.  Once `A ∪ B` is a target
recurrent carrier, every Cesaro subsequential limit started from a law already
supported on that union belongs to the newly generated target GOA family. -/
theorem mergedCarrier_cesaroLimitSet_subset_of_cross
    (P Q : Matrix S S ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (hsupp : TransitionSupportLe P Q)
    (A B : Set S)
    (hrecA : RecurrentCarrier P A)
    (hrecB : RecurrentCarrier P B)
    {a b : S} (ha : a ∈ A) (hb : b ∈ B)
    (hcross : Communicates Q a b)
    (hclosed : ClosedCarrier Q (A ∪ B))
    (mu0 : stdSimplex ℝ S)
    (hmu0 : SupportedOn mu0 (A ∪ B)) :
    cesaroLimitSet Q hQ mu0 ⊆
      carrierInvariantLawSet Q hQ (A ∪ B) := by
  have hmerged : RecurrentCarrier Q (A ∪ B) :=
    recurrentCarrier_union_of_cross_of_closed
      P Q hP hQ hsupp A B hrecA hrecB ha hb hcross hclosed
  exact cesaroLimitSet_subset_carrierInvariantLawSet_of_closed
    Q hQ (A ∪ B) hmerged.2.2 mu0 hmu0

/-- Exact common-state-space semantic envelope for a recurrent merge.

The two source GOA families live in the smaller support faces `A` and `B`, hence
also in the union face.  The newly regenerated target GOA family is nonempty
and lives in the same union face.  No elementwise source/target stationary-law
matching is asserted. -/
theorem recurrentMerge_supportFace_envelope
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
    carrierInvariantLawSet P hP A ⊆ supportFace (A ∪ B) ∧
      carrierInvariantLawSet P hP B ⊆ supportFace (A ∪ B) ∧
      (carrierInvariantLawSet Q hQ (A ∪ B)).Nonempty ∧
      carrierInvariantLawSet Q hQ (A ∪ B) ⊆ supportFace (A ∪ B) := by
  have hA : A ⊆ A ∪ B := fun x hx => Or.inl hx
  have hB : B ⊆ A ∪ B := fun x hx => Or.inr hx
  refine ⟨?_, ?_, ?_, carrierInvariantLawSet_subset_supportFace Q hQ (A ∪ B)⟩
  · exact (carrierInvariantLawSet_subset_supportFace P hP A).trans
      (supportFace_mono hA)
  · exact (carrierInvariantLawSet_subset_supportFace P hP B).trans
      (supportFace_mono hB)
  · exact mergedCarrier_carrierInvariantLawSet_nonempty_of_cross
      P Q hP hQ hsupp A B hrecA hrecB ha hb hcross hclosed

/-- Exact support-face semantics for a recurrent split/refinement.  Any target
recurrent subcarrier `C` lying inside an old source carrier `A` regenerates a
nonempty target GOA family, and every law in that family remains inside the old
source support face.  This gives a common ambient semantic envelope even when
the old class label has split. -/
theorem recurrentSubcarrier_supportFace_envelope
    (Q : Matrix S S ℝ)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (A C : Set S)
    (hCA : C ⊆ A)
    (hrecC : RecurrentCarrier Q C) :
    (carrierInvariantLawSet Q hQ C).Nonempty ∧
      carrierInvariantLawSet Q hQ C ⊆ supportFace A := by
  refine ⟨recurrentCarrier_carrierInvariantLawSet_nonempty Q hQ C hrecC, ?_⟩
  exact (carrierInvariantLawSet_subset_supportFace Q hQ C).trans
    (supportFace_mono hCA)

/-- Two recurrent target subcarriers inside one old source carrier each
regenerate their own nonempty GOA family, while both families remain in the old
source support face.  This is the set-valued semantic counterpart of a split,
without requiring a brittle one-to-one class-label correspondence. -/
theorem recurrentSplit_supportFace_envelope
    (Q : Matrix S S ℝ)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (A C D : Set S)
    (hCA : C ⊆ A) (hDA : D ⊆ A)
    (hrecC : RecurrentCarrier Q C)
    (hrecD : RecurrentCarrier Q D) :
    (carrierInvariantLawSet Q hQ C).Nonempty ∧
      (carrierInvariantLawSet Q hQ D).Nonempty ∧
      carrierInvariantLawSet Q hQ C ⊆ supportFace A ∧
      carrierInvariantLawSet Q hQ D ⊆ supportFace A := by
  rcases recurrentSubcarrier_supportFace_envelope Q hQ A C hCA hrecC with
    ⟨hneC, hsubC⟩
  rcases recurrentSubcarrier_supportFace_envelope Q hQ A D hDA hrecD with
    ⟨hneD, hsubD⟩
  exact ⟨hneC, hneD, hsubC, hsubD⟩

end

noncomputable section

local instance twoStateDecidableEq : DecidableEq (Fin 2) :=
  Classical.decEq (Fin 2)

/-! ## A two-state merge bifurcation: arbitrarily small kernel error, fixed GOA jump -/

/-- Two disconnected absorbing states.  The singleton carriers `{0}` and `{1}`
are distinct recurrent carriers, and every simplex law is invariant. -/
def twoStateSourceKernel : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, 1]

/-- A symmetric support-opening perturbation.  For every `eps > 0`, the two
source recurrent singleton carriers communicate in both directions and merge
into one recurrent carrier. -/
def twoStateMergedKernel (eps : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 - eps, eps; eps, 1 - eps]

theorem twoStateSourceKernel_stochastic :
    twoStateSourceKernel ∈ Matrix.rowStochastic ℝ (Fin 2) := by
  rw [Matrix.mem_rowStochastic_iff_sum]
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [twoStateSourceKernel]
  · intro i
    fin_cases i <;> rw [Fin.sum_univ_two] <;> norm_num [twoStateSourceKernel]

theorem twoStateMergedKernel_stochastic
    (eps : ℝ) (he0 : 0 ≤ eps) (he1 : eps ≤ 1) :
    twoStateMergedKernel eps ∈ Matrix.rowStochastic ℝ (Fin 2) := by
  rw [Matrix.mem_rowStochastic_iff_sum]
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [twoStateMergedKernel] <;> linarith
  · intro i
    fin_cases i <;> rw [Fin.sum_univ_two] <;> simp [twoStateMergedKernel]

/-- The left absorbing source state is itself a recurrent carrier. -/
theorem twoStateSource_zero_recurrent :
    RecurrentCarrier twoStateSourceKernel ({0} : Set (Fin 2)) := by
  refine ⟨⟨0, by simp⟩, ?_, ?_⟩
  · intro x hx y hy
    simp only [Set.mem_singleton_iff] at hx hy
    subst x
    subst y
    exact ⟨⟨0, by simp [twoStateSourceKernel]⟩,
      ⟨0, by simp [twoStateSourceKernel]⟩⟩
  · intro x hx y hpos
    simp only [Set.mem_singleton_iff] at hx ⊢
    subst x
    fin_cases y
    · rfl
    · norm_num [twoStateSourceKernel] at hpos

/-- The right absorbing source state is itself a recurrent carrier. -/
theorem twoStateSource_one_recurrent :
    RecurrentCarrier twoStateSourceKernel ({1} : Set (Fin 2)) := by
  refine ⟨⟨1, by simp⟩, ?_, ?_⟩
  · intro x hx y hy
    simp only [Set.mem_singleton_iff] at hx hy
    subst x
    subst y
    exact ⟨⟨0, by simp [twoStateSourceKernel]⟩,
      ⟨0, by simp [twoStateSourceKernel]⟩⟩
  · intro x hx y hpos
    simp only [Set.mem_singleton_iff] at hx ⊢
    subst x
    fin_cases y
    · norm_num [twoStateSourceKernel] at hpos
    · rfl

/-- For `0 < eps < 1`, all source-positive support remains target-positive. -/
theorem twoStateSourceSupport_le_merged
    (eps : ℝ) (_heps : 0 < eps) (heps1 : eps < 1) :
    TransitionSupportLe twoStateSourceKernel (twoStateMergedKernel eps) := by
  intro x y hpos
  fin_cases x <;> fin_cases y
  · simpa [twoStateSourceKernel, twoStateMergedKernel] using sub_pos.mpr heps1
  · norm_num [twoStateSourceKernel] at hpos
  · norm_num [twoStateSourceKernel] at hpos
  · simpa [twoStateSourceKernel, twoStateMergedKernel] using sub_pos.mpr heps1

/-- The symmetric positive cross-edges turn the two source recurrent
singletons into one target recurrent union.  This theorem deliberately reuses
the generic two-edge recurrent-merge bridge proved in `RecurrentSupportMargin`.
-/
theorem twoStateMerged_union_recurrent
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1) :
    RecurrentCarrier (twoStateMergedKernel eps)
      (({0} : Set (Fin 2)) ∪ {1}) := by
  apply recurrentCarrier_union_of_two_edges_of_closed
    twoStateSourceKernel (twoStateMergedKernel eps)
    twoStateSourceKernel_stochastic
    (twoStateMergedKernel_stochastic eps heps.le heps1.le)
    (twoStateSourceSupport_le_merged eps heps heps1)
    ({0} : Set (Fin 2)) ({1} : Set (Fin 2))
    twoStateSource_zero_recurrent twoStateSource_one_recurrent
    (a₁ := 0) (a₂ := 0) (b₁ := 1) (b₂ := 1)
  · simp
  · simp
  · simp
  · simp
  · simpa [twoStateMergedKernel] using heps
  · simpa [twoStateMergedKernel] using heps
  · intro x hx y hpos
    fin_cases y <;> simp

/-- The source point mass at state `0` is invariant before the merge. -/
theorem twoStateSource_pureZero_invariant :
    pureSimplex (0 : Fin 2) ∈
      invariantLawSet twoStateSourceKernel twoStateSourceKernel_stochastic := by
  apply Subtype.ext
  funext y
  rw [step_apply, Fin.sum_univ_two]
  fin_cases y <;>
    norm_num [twoStateSourceKernel, pureSimplex, Pi.single]

/-- Once the symmetric cross-support is opened, every target invariant law has
exactly half of its mass on each state. -/
theorem twoStateMerged_invariant_coordinates
    (eps : ℝ) (heps : 0 < eps) (he1 : eps ≤ 1)
    (mu : stdSimplex ℝ (Fin 2))
    (hmu : mu ∈ invariantLawSet (twoStateMergedKernel eps)
      (twoStateMergedKernel_stochastic eps heps.le he1)) :
    mu (0 : Fin 2) = 1 / 2 ∧ mu (1 : Fin 2) = 1 / 2 := by
  have hvec :
      (step (twoStateMergedKernel eps)
        (twoStateMergedKernel_stochastic eps heps.le he1) mu).1 = mu.1 :=
    congrArg Subtype.val hmu
  have h0 := congrFun hvec (0 : Fin 2)
  rw [step_apply, Fin.sum_univ_two] at h0
  simp [twoStateMergedKernel] at h0
  change mu (0 : Fin 2) * (1 - eps) + mu (1 : Fin 2) * eps =
    mu (0 : Fin 2) at h0
  have hfac : (mu (1 : Fin 2) - mu (0 : Fin 2)) * eps = 0 := by
    calc
      (mu (1 : Fin 2) - mu (0 : Fin 2)) * eps =
          mu (0 : Fin 2) * (1 - eps) + mu (1 : Fin 2) * eps -
            mu (0 : Fin 2) := by ring
      _ = 0 := by rw [h0]; ring
  have heq : mu (1 : Fin 2) = mu (0 : Fin 2) := by
    have hz : mu (1 : Fin 2) - mu (0 : Fin 2) = 0 :=
      (mul_eq_zero.mp hfac).resolve_right (ne_of_gt heps)
    linarith
  have hsum := stdSimplex.sum_eq_one mu
  rw [Fin.sum_univ_two, heq] at hsum
  constructor <;> linarith

/-- The long-run semantic jump across this merge is not small: every target
invariant law is exactly TV-distance `1/2` from the source invariant point mass
at state `0`, for every `eps > 0`. -/
theorem twoStateMerged_invariant_tv_from_source_pureZero
    (eps : ℝ) (heps : 0 < eps) (he1 : eps ≤ 1)
    (mu : stdSimplex ℝ (Fin 2))
    (hmu : mu ∈ invariantLawSet (twoStateMergedKernel eps)
      (twoStateMergedKernel_stochastic eps heps.le he1)) :
    lawTV (pureSimplex (0 : Fin 2)) mu = 1 / 2 := by
  rcases twoStateMerged_invariant_coordinates eps heps he1 mu hmu with
    ⟨h0, h1⟩
  change mu.1 (0 : Fin 2) = 1 / 2 at h0
  change mu.1 (1 : Fin 2) = 1 / 2 at h1
  unfold lawTV UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.tvDist
  letI : MeasurableSpace (Fin 2) := ⊤
  rw [UEOT.V3.FiniteRecurrentDecompositionStability.pmf_tv_eq_half_sum_abs]
  simp_rw [simplexPMF_toReal]
  rw [Fin.sum_univ_two, h0, h1]
  norm_num [pureSimplex, Pi.single]

/-- The entrywise perturbation magnitude of the symmetric merge kernel is
exactly `eps` in every matrix entry. -/
theorem twoStateMergedKernel_entrywise_distance
    (eps : ℝ) (heps : 0 ≤ eps) :
    ∀ i j : Fin 2,
      |twoStateMergedKernel eps i j - twoStateSourceKernel i j| = eps := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [twoStateMergedKernel, twoStateSourceKernel, abs_of_nonneg heps]

/-- **Topology-bifurcation discontinuity theorem.**  For every requested
entrywise perturbation radius `delta > 0`, there exists a stochastic two-state
target kernel within that radius such that:

* the two source recurrent singleton carriers genuinely merge in the target;
* the source point mass `delta_0` is invariant before the merge; and
* every target invariant law stays at TV distance exactly `1/2` from that
  source invariant law.

Hence no unconditional stationary-law continuity estimate that vanishes only
with entrywise kernel error can hold across recurrent-topology bifurcations.
-/
theorem arbitrarily_small_recurrentMerge_fixed_stationary_jump
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ eps : ℝ,
      ∃ hQ : twoStateMergedKernel eps ∈ Matrix.rowStochastic ℝ (Fin 2),
        0 < eps ∧ eps < delta ∧ eps < 1 ∧
        (∀ i j : Fin 2,
          |twoStateMergedKernel eps i j - twoStateSourceKernel i j| < delta) ∧
        RecurrentCarrier twoStateSourceKernel ({0} : Set (Fin 2)) ∧
        RecurrentCarrier twoStateSourceKernel ({1} : Set (Fin 2)) ∧
        RecurrentCarrier (twoStateMergedKernel eps)
          (({0} : Set (Fin 2)) ∪ {1}) ∧
        pureSimplex (0 : Fin 2) ∈
          invariantLawSet twoStateSourceKernel twoStateSourceKernel_stochastic ∧
        (∀ mu : stdSimplex ℝ (Fin 2),
          mu ∈ invariantLawSet (twoStateMergedKernel eps) hQ →
          lawTV (pureSimplex (0 : Fin 2)) mu = 1 / 2) := by
  let eps : ℝ := min (delta / 2) (1 / 2)
  have heps : 0 < eps := by
    dsimp [eps]
    exact lt_min (by linarith) (by norm_num)
  have hepsDelta : eps < delta := by
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hepsOne : eps < 1 := by
    exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  let hQ := twoStateMergedKernel_stochastic eps heps.le hepsOne.le
  refine ⟨eps, hQ, heps, hepsDelta, hepsOne, ?_,
    twoStateSource_zero_recurrent, twoStateSource_one_recurrent,
    twoStateMerged_union_recurrent eps heps hepsOne,
    twoStateSource_pureZero_invariant, ?_⟩
  · intro i j
    rw [twoStateMergedKernel_entrywise_distance eps heps.le]
    exact hepsDelta
  · intro mu hmu
    exact twoStateMerged_invariant_tv_from_source_pureZero
      eps heps hepsOne.le mu hmu

end

end UEOT.V3.Compression.TopologyChangingGoaSemantics
