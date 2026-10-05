import UEOT.V3.Compression.AgencyGodGoaAssembly
import UEOT.V3.Compression.InvariantSetGaugeInvariance
import UEOT.V3.Compression.OccupationLimitInvariance
import UEOT.V3.FiniteRecurrentDecompositionStability
import UEOT.V3.QSDPerron

/-!
# P0.4 scratch — GOA constitution

GOA is not identified with one universal fixed point. The semantic layer below
keeps several existing long-run objects distinct and proves only canonical
bridges between them.
-/

namespace UEOT.V3.Compression.TheoryCompletion

noncomputable section

open Filter Topology Function
open scoped BigOperators
open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.FiniteCesaroInvariant
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.FiniteRecurrentDecompositionStability
open UEOT.V3.Compression.AgencyGodGoaAssembly
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.Compression.OccupationLimitInvariance
open UEOT.V3.QSDPerron

universe uX uS uA uT uR uC

noncomputable local instance goaStateDecidableEq (S : Type uS) : DecidableEq S :=
  Classical.decEq S

/-- Generic fixed-point semantics. It is one GOA specialization, not the
definition of every GOA. -/
def FixedPointGOA {X : Type uX} (advance : X → X) (x : X) : Prop :=
  advance x = x

/-- Invariant probability-law semantics for one finite stochastic kernel. -/
def InvariantLawGOA
    {S : Type uS} [Fintype S] [Nonempty S]
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (mu : stdSimplex ℝ S) : Prop :=
  mu ∈ invariantLawSet P hP

/-- Cesaro/occupation-limit semantics: nu is a subsequential limit of the
finite-chain Cesaro orbit from the declared initial law. -/
def CesaroLimitGOA
    {S : Type uS} [Fintype S] [Nonempty S]
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (mu0 nu : stdSimplex ℝ S) : Prop :=
  ∃ phi : ℕ → ℕ,
    StrictMono phi ∧
    Tendsto (cesaroRow P hP mu0 ∘ phi) atTop (𝓝 nu)

/-- Every finite Cesaro-limit GOA is an invariant-law GOA. This implication
uses the canonical occupation-limit theorem and does not claim uniqueness. -/
theorem cesaroLimitGOA_is_invariant
    {S : Type uS} [Fintype S] [Nonempty S]
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (mu0 nu : stdSimplex ℝ S)
    (h : CesaroLimitGOA P hP mu0 nu) :
    InvariantLawGOA P hP nu := by
  rcases h with ⟨phi, hphi, hlim⟩
  have hinv :=
    finite_invariant_of_cesaro_tendsto P hP mu0 nu phi hphi hlim
  change step P hP nu = nu
  apply Subtype.ext
  exact hinv

/-- Existing finite recurrent decompositions are a recurrent-structure GOA
specialization. This is a type alias only; no uniqueness or mixing is added. -/
abbrev RecurrentGOAStructure
    {T : Type uT} [Fintype T] [DecidableEq T]
    {R : Type uR} {C : Type uC}
    [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]
    (K : RecurrentPartition R C) :=
  FiniteRecurrentDecomposition (T := T) K

/-- A killed finite-kernel QSD semantic predicate. It records exactly a
substochastic nonnegative kernel, a normalized nonnegative law, positive
survival factor, and the left Perron/QSD relation. -/
def KilledQSDGOA
    {S : Type uS} [Fintype S]
    (Q : Matrix S S ℝ) (q : S → ℝ) (rho : ℝ) : Prop :=
  (∀ i j, 0 ≤ Q i j) ∧
  (∀ i, ∑ j : S, Q i j ≤ 1) ∧
  (∀ i, 0 ≤ q i) ∧
  (∑ i : S, q i = 1) ∧
  0 < rho ∧
  (∀ j, rowApply q Q j = rho * q j)

/-- The QSD predicate has the expected all-step conditional invariance. -/
theorem killedQSDGOA_all_steps
    {S : Type uS} [Fintype S]
    (Q : Matrix S S ℝ) (q : S → ℝ) (rho : ℝ)
    (h : KilledQSDGOA Q q rho) :
    ∀ n j, rowApply q (Q ^ n) j / rho ^ n = q j := by
  exact qsd_all_steps Q q rho h.2.2.2.2.1 h.2.2.2.2.2

/-- A killed QSD survival factor cannot exceed one. -/
theorem killedQSDGOA_rho_le_one
    {S : Type uS} [Fintype S]
    (Q : Matrix S S ℝ) (q : S → ℝ) (rho : ℝ)
    (h : KilledQSDGOA Q q rho) :
    rho ≤ 1 := by
  exact perron_root_le_one_of_substochastic
    Q q rho h.2.2.1 h.2.1 h.2.2.2.1 h.2.2.2.2.2

/-- Optimal long-run semantics for a finite control model, kept as the whole
invariant-law set of the Bellman-greedy closed loop. It remains meaningful
when that set has more than one element. -/
def GreedyInvariantGOASet
    {S : Type uS} [Fintype S] [Nonempty S]
    {A : S → Type uA} [∀ s, Fintype (A s)] [∀ s, Nonempty (A s)]
    (M : Model S A) : Set (stdSimplex ℝ S) :=
  invariantLawSet
    (greedyClosedLoopMatrix M)
    (greedyClosedLoopMatrix_rowStochastic M)

/-- Every finite Bellman-greedy closed loop has at least one invariant-law GOA.
No Dobrushin margin, irreducibility, uniqueness, or global mixing is assumed. -/
theorem greedyInvariantGOASet_nonempty
    {S : Type uS} [Fintype S] [Nonempty S]
    {A : S → Type uA} [∀ s, Fintype (A s)] [∀ s, Nonempty (A s)]
    (M : Model S A) :
    (GreedyInvariantGOASet M).Nonempty := by
  let P := greedyClosedLoopMatrix M
  let hP : P ∈ Matrix.rowStochastic ℝ S :=
    greedyClosedLoopMatrix_rowStochastic M
  let s0 : S := Classical.choice inferInstance
  let mu0 : stdSimplex ℝ S := pureSimplex s0
  rcases (p_goa_01_via_occupationLimit P hP mu0).1 with
    ⟨nu, phi, hphi, hlim⟩
  refine ⟨nu, ?_⟩
  have hgoa : InvariantLawGOA P hP nu :=
    cesaroLimitGOA_is_invariant P hP mu0 nu ⟨phi, hphi, hlim⟩
  simpa [GreedyInvariantGOASet, P, hP, InvariantLawGOA] using hgoa

end

end UEOT.V3.Compression.TheoryCompletion
