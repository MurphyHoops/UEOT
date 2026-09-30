import UEOT.V3.Compression.RecursiveSufficientState
import UEOT.V3.Compression.ContractiveFixedPoint
import UEOT.V3.Compression.OccupationLimitInvariance
import UEOT.V3.CoreOperationalAssembly
import UEOT.V3.FiniteDiscountedSelector

/-!
# End-to-end Agency -> GOD -> GOA assembly

This module is the decisive out-of-sample test requested by the second-order
compression program.  It composes existing interfaces rather than introducing
another proposed generator.

The chain is:

1. a history-level response is sufficient through one finite effective state;
2. M-QD-derived recursive closure gives the unique state update;
3. finite discounted control supplies the Bellman-optimal selector;
4. that selector induces the literal closed-loop Markov matrix used by P-CORE;
5. M-OI supplies existence of an invariant long-run law through Cesaro closure;
6. under an explicit Dobrushin margin, M-CF supplies uniqueness and geometric
   convergence to that law.

The Dobrushin hypothesis is a real stability assumption.  No GOA existence,
uniqueness, or mixing conclusion is assumed in advance.
-/

namespace UEOT.V3.Compression.AgencyGodGoaAssembly

open Filter Topology Function
open UEOT.V3
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.FiniteDobrushin
open UEOT.V3.CoreOperationalAssembly
open UEOT.V3.Compression.RecursiveSufficientState
open UEOT.V3.Compression.ContractiveFixedPoint
open UEOT.V3.Compression.OccupationLimitInvariance

universe uH uS uE uT uA

noncomputable local instance stateDecidableEq (S : Type uS) : DecidableEq S :=
  Classical.decEq S

/-- The stationary policy obtained from the canonical Bellman-greedy selector.
This is the exact policy whose induced matrix is interpreted as the controlled
closed-loop dynamics. -/
noncomputable def greedyStationaryPolicy
    {S : Type uS} [Fintype S]
    {A : S → Type uA} [∀ s, Fintype (A s)] [∀ s, Nonempty (A s)]
    (M : Model S A) : StationaryPolicy A :=
  StationaryPolicy.ofSelector M.greedyAction

/-- The literal closed-loop matrix induced by the Bellman-greedy selector. -/
noncomputable def greedyClosedLoopMatrix
    {S : Type uS} [Fintype S]
    {A : S → Type uA} [∀ s, Fintype (A s)] [∀ s, Nonempty (A s)]
    (M : Model S A) : Matrix S S ℝ :=
  policyMatrix M (greedyStationaryPolicy M)

theorem greedyClosedLoopMatrix_rowStochastic
    {S : Type uS} [Fintype S]
    {A : S → Type uA} [∀ s, Fintype (A s)] [∀ s, Nonempty (A s)]
    (M : Model S A) :
    greedyClosedLoopMatrix M ∈ Matrix.rowStochastic ℝ S := by
  classical
  exact policyMatrix_rowStochastic M (greedyStationaryPolicy M)

/-- End-to-end finite Agency -> GOD -> GOA assembly.

`C` is the effective state map from histories.  Surjectivity says the chosen
finite control state contains exactly reachable effective states; if an ambient
state space contains unreachable points, use `ReachableState C` instead.

The conclusion exposes all four stages without identifying them:

* a unique recursive update on the effective state;
* Bellman-greedy action optimality and domination of every causal policy;
* an invariant closed-loop law whose existence is obtained through M-OI;
* uniqueness and geometric mixing under the explicit Dobrushin margin.
-/
theorem agency_god_goa
    {H : Type uH} {S : Type uS} [Fintype S] [Nonempty S]
    {E : Type uE} {T : Type uT}
    (C : H → S) (hC : Surjective C)
    (R : H → E → T)
    (hcompat : InputFiberCompatible C R)
    {A : S → Type uA} [∀ s, Fintype (A s)] [∀ s, Nonempty (A s)]
    (M : Model S A)
    (halpha :
      dobrushinAlpha
        (greedyClosedLoopMatrix M)
        (greedyClosedLoopMatrix_rowStochastic M) < 1) :
    (∃! U : S → E → T, ∀ h e, U (C h) e = R h e) ∧
    (∀ s,
      M.qValue M.optimalValue s (M.greedyAction s) = M.optimalValue s) ∧
    ((∀ {t : ℕ} (s : S),
        CausalPolicy.infiniteValue
          (selectorPolicy M.greedyAction) M (t := t) s =
            M.optimalValue s) ∧
      (∀ (π : CausalPolicy S A) {t : ℕ} (h : π.Memory t),
        CausalPolicy.infiniteValue π M h ≤
          M.optimalValue (π.current h))) ∧
    ∃ mustar : stdSimplex ℝ S,
      step
          (greedyClosedLoopMatrix M)
          (greedyClosedLoopMatrix_rowStochastic M) mustar = mustar ∧
      (∀ mu : stdSimplex ℝ S,
        step
            (greedyClosedLoopMatrix M)
            (greedyClosedLoopMatrix_rowStochastic M) mu = mu →
          mu = mustar) ∧
      ∀ (mu : stdSimplex ℝ S) (n : ℕ),
        lawTV
            (((step
              (greedyClosedLoopMatrix M)
              (greedyClosedLoopMatrix_rowStochastic M))^[n]) mu)
            mustar ≤
          dobrushinAlpha
              (greedyClosedLoopMatrix M)
              (greedyClosedLoopMatrix_rowStochastic M) ^ n *
            lawTV mu mustar := by
  classical
  let P : Matrix S S ℝ := greedyClosedLoopMatrix M
  let hP : P ∈ Matrix.rowStochastic ℝ S := by
    simpa [P] using greedyClosedLoopMatrix_rowStochastic M
  have hupdate := existsUnique_ambientUpdate_of_surjective
    C hC R hcompat
  have hgod : ∀ s,
      M.qValue M.optimalValue s (M.greedyAction s) = M.optimalValue s :=
    M.greedyAction_spec
  have hcontrol := selector_optimal_against_all_causal
    M M.greedyAction hgod
  let s0 : S := Classical.choice inferInstance
  let mu0 : stdSimplex ℝ S := pureSimplex s0
  have hgoa01 := p_goa_01_via_occupationLimit P hP mu0
  rcases hgoa01.1 with ⟨mustar, phi, hphi, hlim⟩
  have hvec : Matrix.vecMul mustar.1 P = mustar.1 :=
    hgoa01.2 mustar phi hphi hlim
  have hmustar : step P hP mustar = mustar := by
    apply Subtype.ext
    exact hvec
  have hcontract :
      ContractiveFixedPoint.ContractiveWith
        (ContractiveFixedPoint.lawTVDistanceLike (S := S))
        (dobrushinAlpha P hP) (step P hP) := by
    apply ContractiveFixedPoint.dobrushin_contractiveWith P hP
    simpa [P, hP] using halpha
  refine ⟨hupdate, hgod, hcontrol, mustar, ?_, ?_, ?_⟩
  · simpa [P, hP] using hmustar
  · intro mu hmu
    have hmu' : step P hP mu = mu := by
      simpa [P, hP] using hmu
    exact hcontract.fixedPoint_unique hmu' hmustar
  · intro mu n
    have hmix := ContractiveFixedPoint.dobrushin_iterate_to_invariant_le_via_mcf
      P hP (by simpa [P, hP] using halpha) mu mustar hmustar n
    simpa [P, hP] using hmix

/-! ## History-derived control model -/

/-- History-level control data whose reward and next-state law are sufficient
through the same effective state map `C`.

The action type is uniform in this first end-to-end theorem.  This keeps the
history-level action interface honest: before quotienting, a state-dependent
action family would itself require a compatibility theorem.  The existing
finite-control layer remains fully state-dependent; this structure is only the
minimal bridge needed to prove the cross-layer assembly. -/
structure HistoryControlSpec
    (H : Type uH) (S : Type uS) [Fintype S]
    (Act : Type uA) [Fintype Act] [Nonempty Act]
    (C : H → S) where
  transition : H → Act → S → ℝ
  reward : H → Act → ℝ
  rewardBound : ℝ
  discount : ℝ
  transition_nonneg : ∀ h a y, 0 ≤ transition h a y
  transition_sum_one : ∀ h a, ∑ y, transition h a y = 1
  reward_abs_le : ∀ h a, |reward h a| ≤ rewardBound
  discount_pos : 0 < discount
  discount_lt_one : discount < 1
  sufficient :
    InputFiberCompatible C (fun h a => (reward h a, transition h a))

namespace HistoryControlSpec

variable {H : Type uH} {S : Type uS} [Fintype S]
variable {Act : Type uA} [Fintype Act] [Nonempty Act]
variable {C : H → S}

/-- The unique state-level reward/transition response induced by history-level
sufficiency. -/
noncomputable def stateResponse
    (D : HistoryControlSpec H S Act C) (hC : Surjective C) :
    S → Act → (ℝ × (S → ℝ)) :=
  Classical.choose <|
    existsUnique_ambientUpdate_of_surjective
      C hC (fun h a => (D.reward h a, D.transition h a)) D.sufficient

theorem stateResponse_spec
    (D : HistoryControlSpec H S Act C) (hC : Surjective C)
    (h : H) (a : Act) :
    D.stateResponse hC (C h) a = (D.reward h a, D.transition h a) := by
  exact (Classical.choose_spec <|
    existsUnique_ambientUpdate_of_surjective
      C hC (fun h a => (D.reward h a, D.transition h a)) D.sufficient).1 h a

/-- The finite controlled Markov model canonically realized by the sufficient
history representation.  All model laws are inherited from history-level data
through surjectivity and the unique quotient update. -/
noncomputable def toModel
    (D : HistoryControlSpec H S Act C) (hC : Surjective C) :
    Model S (fun _ => Act) where
  transition := fun s a y => (D.stateResponse hC s a).2 y
  reward := fun s a => (D.stateResponse hC s a).1
  rewardBound := D.rewardBound
  discount := D.discount
  transition_nonneg := by
    intro s a y
    rcases hC s with ⟨h, rfl⟩
    rw [D.stateResponse_spec hC h a]
    exact D.transition_nonneg h a y
  transition_sum_one := by
    intro s a
    rcases hC s with ⟨h, rfl⟩
    simp only [D.stateResponse_spec hC h a]
    exact D.transition_sum_one h a
  reward_abs_le := by
    intro s a
    rcases hC s with ⟨h, rfl⟩
    rw [D.stateResponse_spec hC h a]
    exact D.reward_abs_le h a
  discount_pos := D.discount_pos
  discount_lt_one := D.discount_lt_one

@[simp] theorem toModel_reward_on_history
    (D : HistoryControlSpec H S Act C) (hC : Surjective C)
    (h : H) (a : Act) :
    (D.toModel hC).reward (C h) a = D.reward h a := by
  simp [toModel, stateResponse_spec]

@[simp] theorem toModel_transition_on_history
    (D : HistoryControlSpec H S Act C) (hC : Surjective C)
    (h : H) (a : Act) (y : S) :
    (D.toModel hC).transition (C h) a y = D.transition h a y := by
  simp [toModel, stateResponse_spec]

end HistoryControlSpec

/-- Strong end-to-end assembly with an explicit identity guard from the
history process into the finite control model.

Unlike `agency_god_goa`, the control model here is not supplied independently.
It is *constructed* from the same history-level reward/transition response that
is recursively sufficient through `C`.  Thus the optimal selector and its
closed-loop GOA belong to the quotient dynamics of the original history data,
not merely to an unrelated model sharing the same state type. -/
theorem agency_god_goa_from_history
    {H : Type uH} {S : Type uS} [Fintype S] [Nonempty S]
    {Act : Type uA} [Fintype Act] [Nonempty Act]
    (C : H → S) (hC : Surjective C)
    (D : HistoryControlSpec H S Act C)
    (halpha :
      dobrushinAlpha
        (greedyClosedLoopMatrix (D.toModel hC))
        (greedyClosedLoopMatrix_rowStochastic (D.toModel hC)) < 1) :
    let M := D.toModel hC
    (∀ h a, M.reward (C h) a = D.reward h a) ∧
    (∀ h a y, M.transition (C h) a y = D.transition h a y) ∧
    (∃! U : S → Act → (ℝ × (S → ℝ)),
      ∀ h a, U (C h) a = (D.reward h a, D.transition h a)) ∧
    (∀ s,
      M.qValue M.optimalValue s (M.greedyAction s) = M.optimalValue s) ∧
    ((∀ {t : ℕ} (s : S),
        CausalPolicy.infiniteValue
          (selectorPolicy M.greedyAction) M (t := t) s =
            M.optimalValue s) ∧
      (∀ (π : CausalPolicy S (fun _ => Act)) {t : ℕ} (h : π.Memory t),
        CausalPolicy.infiniteValue π M h ≤
          M.optimalValue (π.current h))) ∧
    ∃ mustar : stdSimplex ℝ S,
      step
          (greedyClosedLoopMatrix M)
          (greedyClosedLoopMatrix_rowStochastic M) mustar = mustar ∧
      (∀ mu : stdSimplex ℝ S,
        step
            (greedyClosedLoopMatrix M)
            (greedyClosedLoopMatrix_rowStochastic M) mu = mu →
          mu = mustar) ∧
      ∀ (mu : stdSimplex ℝ S) (n : ℕ),
        lawTV
            (((step
              (greedyClosedLoopMatrix M)
              (greedyClosedLoopMatrix_rowStochastic M))^[n]) mu)
            mustar ≤
          dobrushinAlpha
              (greedyClosedLoopMatrix M)
              (greedyClosedLoopMatrix_rowStochastic M) ^ n *
            lawTV mu mustar := by
  dsimp only
  let M := D.toModel hC
  have hassembly := agency_god_goa
    C hC
    (fun h a => (D.reward h a, D.transition h a))
    D.sufficient M
    (by simpa [M] using halpha)
  refine ⟨?_, ?_, hassembly.1, hassembly.2.1,
    hassembly.2.2.1, hassembly.2.2.2⟩
  · intro h a
    exact D.toModel_reward_on_history hC h a
  · intro h a y
    exact D.toModel_transition_on_history hC h a y

end UEOT.V3.Compression.AgencyGodGoaAssembly
