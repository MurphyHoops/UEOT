import UEOT.V3.StatisticalDefect
import UEOT.V3.PredictiveClassRecovery
import UEOT.V3.Threshold
import UEOT.Core.Blocker
import UEOT.V3.Decision
import UEOT.V3.FiniteDiscountedApproxQuotientBounds
import UEOT.V3.FiniteDiscountedPolicyResolvent
import UEOT.V3.PathError
import UEOT.V3.OmegaIntegrityMargin
import UEOT.V3.TransportDefect
import UEOT.V3.DevelopmentTransport
import UEOT.V3.FiniteDobrushin
import UEOT.V3.FiniteRecurrentDecompositionStability
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-!
# P-CORE-01 — finite operational core assembly

The frozen Core 3 theorem is an assembly result, not a new existence axiom.
It combines already certified response recovery, exact carrier recovery,
discounted quotient control, same-policy finite-path error, optional long-run
and history-transport certificates, and the integrity-margin certificate on
one common high-probability event.

This module keeps two source-identity rules explicit:

* predictive classes and carrier defects are recovered from the same true and
  empirical response tables;
* the action certificate derives the `D` action-value error from the same
  approximate quotient used for the value/regret certificate, rather than
  assuming an unrelated action-value error bound.

The final probabilistic layer is indexed by a finite set of event keys.  A
shared event therefore occurs once in the index set and its failure budget is
not counted twice, matching the frozen source's explicit bookkeeping clause.
-/

namespace UEOT.V3.CoreOperationalAssembly

open MeasureTheory
open Filter Topology
open UEOT.V3.TotalVariation
open UEOT.V3.FiniteDiscountedControl
open scoped BigOperators Matrix.Norms.Operator

universe uΩ uK uV uH uI uR uY uX uM uA uT uRec uC uS uPA uObj

/-! ## Distinct-event probability bookkeeping -/

/-- The common good event for a finite family of distinct certification-event
keys.  Reused module requirements should point to the same key. -/
def commonGoodEvent {Ω : Type uΩ} {K : Type uK}
    (E : K → Set Ω) : Set Ω :=
  ⋂ k, E k

/-- Finite union bound in the exact real-probability form used by P-CORE-01.
No independence between certification events is assumed. -/
theorem commonGoodEvent_measureReal_lower
    {Ω : Type uΩ} [MeasurableSpace Ω]
    {K : Type uK} [Fintype K]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : K → Set Ω) (α : K → ℝ)
    (hE : ∀ k, MeasurableSet (E k))
    (hfail : ∀ k, μ.real (E k)ᶜ ≤ α k) :
    1 - ∑ k, α k ≤ μ.real (commonGoodEvent E) := by
  have hbad : μ.real (commonGoodEvent E)ᶜ ≤ ∑ k, α k := by
    rw [commonGoodEvent, Set.compl_iInter]
    exact (measureReal_iUnion_fintype_le (fun k => (E k)ᶜ)).trans
      (Finset.sum_le_sum fun k _ => hfail k)
  have hgood : MeasurableSet (commonGoodEvent E) :=
    MeasurableSet.iInter hE
  rw [measureReal_compl hgood] at hbad
  have huniv : μ.real Set.univ = 1 := by simp
  rw [huniv] at hbad
  linarith

/-- Literal three-budget form displayed in frozen §31.1.  The generic
`commonGoodEvent_measureReal_lower` above is the deduplicating form to use when
two modules reuse the same certification event. -/
theorem three_event_measureReal_lower
    {Ω : Type uΩ} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Eresp Ectl Eaux : Set Ω)
    (hrespMeas : MeasurableSet Eresp)
    (hctlMeas : MeasurableSet Ectl)
    (hauxMeas : MeasurableSet Eaux)
    (αresp αctl αaux : ℝ)
    (hrespFail : μ.real Erespᶜ ≤ αresp)
    (hctlFail : μ.real Ectlᶜ ≤ αctl)
    (hauxFail : μ.real Eauxᶜ ≤ αaux) :
    1 - αresp - αctl - αaux ≤ μ.real (Eresp ∩ Ectl ∩ Eaux) := by
  have hbad : μ.real (Eresp ∩ Ectl ∩ Eaux)ᶜ ≤ αresp + αctl + αaux := by
    rw [Set.compl_inter, Set.compl_inter]
    calc
      μ.real (Erespᶜ ∪ Ectlᶜ ∪ Eauxᶜ) ≤
          μ.real (Erespᶜ ∪ Ectlᶜ) + μ.real Eauxᶜ :=
        measureReal_union_le _ _
      _ ≤ (μ.real Erespᶜ + μ.real Ectlᶜ) + μ.real Eauxᶜ := by
        gcongr
        exact measureReal_union_le _ _
      _ ≤ (αresp + αctl) + αaux := by linarith
      _ = αresp + αctl + αaux := by ring
  have hgood : MeasurableSet (Eresp ∩ Ectl ∩ Eaux) :=
    (hrespMeas.inter hctlMeas).inter hauxMeas
  rw [measureReal_compl hgood] at hbad
  have huniv : μ.real Set.univ = 1 := by simp
  rw [huniv] at hbad
  linarith

/-! ## One response table -> predictive classes + exact carriers + blocker -/

/-- Exact minimal carrier family of the frozen response defect. -/
def exactCarrierFamily
    {V : Type uV} {H : Type uH} {I : Type uI}
    {R : Type uR} {Y : Type uY} [MeasurableSpace Y]
    (readout : Finset V → H → R)
    (p : H → I → Measure Y) : Set (Finset V) :=
  {S | Finite.Minimal
    (fun T => StatisticalDefect.responseDefect readout p T = 0) S}

/-- Empirical threshold carrier family used in P-STAT-04. -/
def estimatedCarrierFamily
    {V : Type uV} {H : Type uH} {I : Type uI}
    {R : Type uR} {Y : Type uY} [MeasurableSpace Y]
    (readout : Finset V → H → R)
    (pHat : H → I → Measure Y) (τ : ℝ) : Set (Finset V) :=
  {S | Finite.Minimal
    (fun T => StatisticalDefect.responseDefect readout pHat T ≤ τ) S}

/-- A response defect is nonnegative because every within-fibre TV distance is
nonnegative. -/
theorem responseDefect_nonneg
    {V : Type uV} {H : Type uH} {I : Type uI}
    {R : Type uR} {Y : Type uY} [MeasurableSpace Y]
    (readout : Finset V → H → R)
    (p : H → I → Measure Y)
    (hp : ∀ h i, IsProbabilityMeasure (p h i))
    (S : Finset V) :
    0 ≤ StatisticalDefect.responseDefect readout p S := by
  unfold StatisticalDefect.responseDefect
  apply Real.sSup_nonneg
  intro d hd
  rcases hd with ⟨h, h', i, _hfiber, rfl⟩
  letI : IsProbabilityMeasure (p h i) := hp h i
  letI : IsProbabilityMeasure (p h' i) := hp h' i
  exact tvDist_nonneg (p h i) (p h' i)

/-- Deterministic response-side assembly on the simultaneous response-error
event.  The same `readout`, `p`, `pHat` feed P-STAT-05, P-STAT-02 and
P-STAT-04, preventing a hidden change of source object. -/
theorem response_recovery_on_good_event
    {V : Type uV} [Fintype V] [DecidableEq V]
    {H : Type uH} [Fintype H] [Nonempty H]
    {I : Type uI} [Fintype I] [Nonempty I]
    {R : Type uR} {Y : Type uY} [MeasurableSpace Y]
    (readout : Finset V → H → R)
    (p pHat : H → I → Measure Y)
    (hp : ∀ h i, IsProbabilityMeasure (p h i))
    (hpHat : ∀ h i, IsProbabilityMeasure (pHat h i))
    (η γ Δ τ : ℝ)
    (hresp : ∀ h i, tvDist (p h i) (pHat h i) ≤ η)
    (hsep : ∀ h h',
      ¬PredictiveClassRecovery.trueEquivalent p h h' →
        γ ≤ PredictiveClassRecovery.protocolDistance p h h')
    (hpredGap : 2 * η < γ / 2)
    (hcarrierGap : ∀ S,
      0 < StatisticalDefect.responseDefect readout p S →
        Δ ≤ StatisticalDefect.responseDefect readout p S)
    (hlower : 2 * η < τ) (hupper : τ < Δ - 2 * η) :
    (∀ h h',
      PredictiveClassRecovery.protocolDistance pHat h h' ≤ γ / 2 ↔
        PredictiveClassRecovery.trueEquivalent p h h') ∧
    estimatedCarrierFamily readout pHat τ = exactCarrierFamily readout p ∧
    Blocker.blocker (estimatedCarrierFamily readout pHat τ) =
      Blocker.blocker (exactCarrierFamily readout p) := by
  have hpred :=
    PredictiveClassRecovery.p_stat_05
      p pHat hp hpHat η γ hresp hsep hpredGap
  have hdefect :=
    StatisticalDefect.p_stat_02 readout p pHat hp hpHat η hresp
  have hcarrier :
      estimatedCarrierFamily readout pHat τ = exactCarrierFamily readout p := by
    simpa [estimatedCarrierFamily, exactCarrierFamily] using
      (Threshold.exact_family
        (StatisticalDefect.responseDefect readout p)
        (StatisticalDefect.responseDefect readout pHat)
        Δ τ η
        (responseDefect_nonneg readout p hp)
        hdefect hcarrierGap hlower hupper)
  exact ⟨hpred, hcarrier, congrArg Blocker.blocker hcarrier⟩

/-! ## One quotient -> value/regret + action certification -/

/-- P-QUO-02 implies that the true optimal micro action value and the macro
optimal action value differ by at most the same global radius `D`.

The proof is the frozen identity `β D + δ = D`: changing the micro
continuation from `V*` to the pulled-back macro optimum costs `β D`, while the
one-step quotient comparison costs `δ`. -/
theorem optimal_qValue_macro_error_le_D
    {X : Type uX} [Fintype X]
    {M : Type uM} [Fintype M]
    {Abar : M → Type uA}
    [∀ m, Fintype (Abar m)] [∀ m, Nonempty (Abar m)]
    (Q : ApproxControlQuotient X M Abar)
    (x : X) (a : Abar (Q.f x)) :
    |Q.micro.qValue Q.micro.optimalValue x a -
      Q.macroModel.qValue Q.macroModel.optimalValue (Q.f x) a| ≤ Q.D := by
  have hmicro :=
    Q.micro.abs_qValue_sub_le Q.micro.optimalValue Q.w x a
  have hdist := Q.optimalValue_dist_w_le
  have hβ : 0 ≤ Q.micro.discount := Q.micro.discount_pos.le
  have hmicroD :
      |Q.micro.qValue Q.micro.optimalValue x a -
        Q.micro.qValue Q.w x a| ≤ Q.micro.discount * Q.D :=
    hmicro.trans (mul_le_mul_of_nonneg_left hdist hβ)
  have hmacro :=
    Q.abs_qValue_pullback_sub_le x a Q.macroModel.optimalValue
  have hmacroδ :
      |Q.micro.qValue Q.w x a -
        Q.macroModel.qValue Q.macroModel.optimalValue (Q.f x) a| ≤ Q.delta := by
    simpa [ApproxControlQuotient.w, ApproxControlQuotient.delta] using hmacro
  have htri :
      |Q.micro.qValue Q.micro.optimalValue x a -
        Q.macroModel.qValue Q.macroModel.optimalValue (Q.f x) a| ≤
        |Q.micro.qValue Q.micro.optimalValue x a - Q.micro.qValue Q.w x a| +
        |Q.micro.qValue Q.w x a -
          Q.macroModel.qValue Q.macroModel.optimalValue (Q.f x) a| := by
    have h := abs_add_le
      (Q.micro.qValue Q.micro.optimalValue x a - Q.micro.qValue Q.w x a)
      (Q.micro.qValue Q.w x a -
        Q.macroModel.qValue Q.macroModel.optimalValue (Q.f x) a)
    simpa [sub_add_sub_cancel] using h
  calc
    |Q.micro.qValue Q.micro.optimalValue x a -
        Q.macroModel.qValue Q.macroModel.optimalValue (Q.f x) a|
        ≤ |Q.micro.qValue Q.micro.optimalValue x a - Q.micro.qValue Q.w x a| +
          |Q.micro.qValue Q.w x a -
            Q.macroModel.qValue Q.macroModel.optimalValue (Q.f x) a| := htri
    _ ≤ Q.micro.discount * Q.D + Q.delta := add_le_add hmicroD hmacroδ
    _ = Q.D := by
      rw [Q.discount_eq]
      unfold ApproxControlQuotient.D
      have hne : 1 - Q.macroModel.discount ≠ 0 :=
        ne_of_gt (sub_pos.mpr Q.macroModel.discount_lt_one)
      field_simp [hne]
      ring

/-- Estimated macro greedy actions with a strict `2D` gap are genuine unique
micro optimal actions at the same represented state.  The error premise of
P-QUO-03 is derived above; it is not an extra assumption. -/
theorem macro_gap_certifies_micro_action
    {X : Type uX} [Fintype X]
    {M : Type uM} [Fintype M]
    {Abar : M → Type uA}
    [∀ m, Fintype (Abar m)] [∀ m, Nonempty (Abar m)]
    (Q : ApproxControlQuotient X M Abar)
    (x : X)
    (hgap : ∀ a, a ≠ Q.macroModel.greedyAction (Q.f x) →
      2 * Q.D <
        Q.macroModel.qValue Q.macroModel.optimalValue (Q.f x)
          (Q.macroModel.greedyAction (Q.f x)) -
        Q.macroModel.qValue Q.macroModel.optimalValue (Q.f x) a) :
    ∀ a, a ≠ Q.macroModel.greedyAction (Q.f x) →
      Q.micro.qValue Q.micro.optimalValue x a <
        Q.micro.qValue Q.micro.optimalValue x
          (Q.macroModel.greedyAction (Q.f x)) := by
  exact Decision.action_gap
    (fun a => Q.micro.qValue Q.micro.optimalValue x a)
    (fun a => Q.macroModel.qValue Q.macroModel.optimalValue (Q.f x) a)
    Q.D (Q.macroModel.greedyAction (Q.f x))
    (optimal_qValue_macro_error_le_D Q x) hgap

/-! ## The same stationary policy -> finite path and GOA kernels -/

/-- Exact PMF of a model's transition after applying one fixed stationary
randomized policy. -/
noncomputable def policyTransitionPMF
    {S : Type uX} [Fintype S]
    {A : S → Type uA} [∀ s, Fintype (A s)] [∀ s, Nonempty (A s)]
    (M : Model S A) (π : StationaryPolicy A) (x : S) : PMF S :=
  FiniteProbabilityRow.ofRealRow (M.policyTransition π x)
    (M.policyTransition_nonneg π x) (M.policyTransition_sum_one π x)

@[simp] theorem policyTransitionPMF_apply_toReal
    {S : Type uX} [Fintype S]
    {A : S → Type uA} [∀ s, Fintype (A s)] [∀ s, Nonempty (A s)]
    (M : Model S A) (π : StationaryPolicy A) (x y : S) :
    ((policyTransitionPMF M π x) y).toReal = M.policyTransition π x y := by
  simp [policyTransitionPMF, FiniteProbabilityRow.ofRealRow_apply_toReal]

/-- Last physical state represented by a recursive P-DYN-03 history. -/
def currentState {S : Type uX} :
    ∀ n, PathError.CausalHistory S S n → S
  | 0, x => x
  | _ + 1, h => h.2

/-- The next-record kernel generated by an actual model under one stationary
policy, written in the history-indexed interface used by P-DYN-03. -/
noncomputable def policyPathKernel
    {S : Type uX} [Fintype S]
    {A : S → Type uA} [∀ s, Fintype (A s)] [∀ s, Nonempty (A s)]
    (M : Model S A) (π : StationaryPolicy A) :
    ∀ n, PathError.CausalHistory S S n → PMF S :=
  fun n h => policyTransitionPMF M π (currentState n h)

/-- P-DYN-03 for two finite controlled models under exactly the same stationary
policy.  The path kernels are derived from each model's policy transition, so
unrelated free `K/L` kernels cannot be substituted. -/
theorem same_policy_path_error
    {S : Type uX} [Fintype S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    {A : S → Type uA} [∀ s, Fintype (A s)] [∀ s, Nonempty (A s)]
    (M Mhat : Model S A) (π : StationaryPolicy A)
    (p₀ : PMF S) (ε : ℕ → ℝ)
    (hε0 : ∀ n, 0 ≤ ε n) (hε1 : ∀ n, ε n ≤ 1)
    (hrow : ∀ n x,
      tvDist
        (policyTransitionPMF M π x).toMeasure
        (policyTransitionPMF Mhat π x).toMeasure ≤ ε n) :
    ∀ T,
      tvDist
          (PathError.causalLaw p₀ (policyPathKernel M π) T).toMeasure
          (PathError.causalLaw p₀ (policyPathKernel Mhat π) T).toMeasure
        ≤ 1 - (∏ i ∈ Finset.range T, (1 - ε i)) ∧
      1 - (∏ i ∈ Finset.range T, (1 - ε i))
        ≤ ∑ i ∈ Finset.range T, ε i := by
  apply PathError.p_dyn_03_finite_path_error
      p₀ (policyPathKernel M π) (policyPathKernel Mhat π) ε hε0 hε1
  intro n h
  exact hrow n (currentState n h)

/-- Policy-induced stochastic matrix used by the finite GOA theorems. -/
def policyMatrix
    {S : Type uX} [Fintype S]
    {A : S → Type uA} [∀ s, Fintype (A s)] [∀ s, Nonempty (A s)]
    (M : Model S A) (π : StationaryPolicy A) : Matrix S S ℝ :=
  fun x y => M.policyTransition π x y

/-- The policy-induced matrix is row stochastic, derived from the model and
policy rather than supplied as an independent kernel. -/
theorem policyMatrix_rowStochastic
    {S : Type uX} [Fintype S] [DecidableEq S]
    {A : S → Type uA} [∀ s, Fintype (A s)] [∀ s, Nonempty (A s)]
    (M : Model S A) (π : StationaryPolicy A) :
    policyMatrix M π ∈ Matrix.rowStochastic ℝ S := by
  classical
  rw [Matrix.mem_rowStochastic_iff_sum]
  constructor
  · intro i j
    exact M.policyTransition_nonneg π i j
  · intro i
    exact M.policyTransition_sum_one π i

/-- Dobrushin long-run stability for two controlled models under the exact same
stationary policy.  This realizes the source's optional mixing-based GOA port. -/
theorem same_policy_goa02
    {S : Type uX} [Fintype S] [DecidableEq S] [Nonempty S]
    {A : S → Type uA} [∀ s, Fintype (A s)] [∀ s, Nonempty (A s)]
    (M Mhat : Model S A) (π : StationaryPolicy A)
    (halpha :
      FiniteDobrushin.dobrushinAlpha
        (policyMatrix M π) (policyMatrix_rowStochastic M π) < 1)
    (mu muhat : stdSimplex ℝ S) (epsilon : ℝ)
    (hmu : FiniteDobrushin.step
      (policyMatrix M π) (policyMatrix_rowStochastic M π) mu = mu)
    (hmuhat : FiniteDobrushin.step
      (policyMatrix Mhat π) (policyMatrix_rowStochastic Mhat π) muhat = muhat)
    (hrow : ∀ x,
      FiniteDobrushin.crossRowTV
        (policyMatrix M π) (policyMatrix_rowStochastic M π)
        (policyMatrix Mhat π) (policyMatrix_rowStochastic Mhat π) x ≤ epsilon) :
    FiniteDobrushin.lawTV mu muhat ≤
      epsilon /
        (1 - FiniteDobrushin.dobrushinAlpha
          (policyMatrix M π) (policyMatrix_rowStochastic M π)) := by
  exact (FiniteDobrushin.p_goa_02
    (policyMatrix M π) (policyMatrix_rowStochastic M π) halpha).2
      (policyMatrix Mhat π) (policyMatrix_rowStochastic Mhat π)
      mu muhat epsilon hmu hmuhat hrow

/-- Recurrent-decomposition data whose actual stochastic kernel is exactly the
policy-induced matrix of the controlled model.  This equality is the identity
guard required by the frozen P-CORE-01 long-run clause. -/
structure PolicyRecurrentData
    {T : Type uT} [Fintype T] [DecidableEq T]
    {R : Type uRec} {C : Type uC}
    [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]
    (K : FiniteRecurrentDecompositionStability.RecurrentPartition R C)
    {A : FiniteRecurrentDecompositionStability.FullState T R → Type uA}
    [∀ x, Fintype (A x)] [∀ x, Nonempty (A x)]
    (M : Model (FiniteRecurrentDecompositionStability.FullState T R) A)
    (π : StationaryPolicy A) where
  decomp :
    FiniteRecurrentDecompositionStability.FiniteRecurrentDecomposition
      (T := T) K
  kernel_eq : decomp.P = policyMatrix M π

/-- P-GOA-03 for two controlled models under one shared stationary policy and
one literal recurrent partition.  Each decomposition is required to expose the
same policy-induced matrix as its full kernel. -/
theorem same_policy_goa03
    {T : Type uT} [Fintype T] [DecidableEq T]
    {R : Type uRec} {C : Type uC}
    [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]
    (K : FiniteRecurrentDecompositionStability.RecurrentPartition R C)
    {A : FiniteRecurrentDecompositionStability.FullState T R → Type uA}
    [∀ x, Fintype (A x)] [∀ x, Nonempty (A x)]
    (M Mhat : Model (FiniteRecurrentDecompositionStability.FullState T R) A)
    (π : StationaryPolicy A)
    (B : PolicyRecurrentData K M π)
    (Bhat : PolicyRecurrentData K Mhat π)
    (epsQ epsR : ℝ)
    (hQ : ‖Bhat.decomp.block.Q - B.decomp.block.Q‖ ≤ epsQ)
    (hR : ‖Bhat.decomp.block.R - B.decomp.block.R‖ ≤ epsR)
    (hsmall : ‖B.decomp.block.N‖ * epsQ < 1)
    (x0 : FiniteRecurrentDecompositionStability.FullState T R)
    (epsStat : C → ℝ)
    (hstat : ∀ j,
      FiniteDobrushin.lawTV
        (B.decomp.classLaw j) (Bhat.decomp.classLaw j) ≤ epsStat j) :
    let nu := FiniteRecurrentDecompositionStability.recurrentMixture
      (FiniteRecurrentDecompositionStability.initialClassWeights
        K B.decomp.block x0) B.decomp.classLaw
    let nuhat := FiniteRecurrentDecompositionStability.recurrentMixture
      (FiniteRecurrentDecompositionStability.initialClassWeights
        K Bhat.decomp.block x0) Bhat.decomp.classLaw
    ‖Bhat.decomp.block.H - B.decomp.block.H‖ ≤
        (‖B.decomp.block.N‖ ^ 2 * epsQ + ‖B.decomp.block.N‖ * epsR) /
          (1 - ‖B.decomp.block.N‖ * epsQ) ∧
      Tendsto
        (UEOT.V3.FiniteCesaroInvariant.cesaroRow
          B.decomp.P B.decomp.stochastic
          (FiniteRecurrentDecompositionStability.FiniteRecurrentDecomposition.pureFullLaw x0))
        Filter.atTop (𝓝 nu) ∧
      Tendsto
        (UEOT.V3.FiniteCesaroInvariant.cesaroRow
          Bhat.decomp.P Bhat.decomp.stochastic
          (FiniteRecurrentDecompositionStability.FiniteRecurrentDecomposition.pureFullLaw x0))
        Filter.atTop (𝓝 nuhat) ∧
      FiniteDobrushin.lawTV nu nuhat ≤
        (1 / 2 : ℝ) *
            ((‖B.decomp.block.N‖ ^ 2 * epsQ + ‖B.decomp.block.N‖ * epsR) /
              (1 - ‖B.decomp.block.N‖ * epsQ)) +
          ∑ j,
            (FiniteRecurrentDecompositionStability.initialClassWeights
              K Bhat.decomp.block x0).1 j * epsStat j := by
  exact FiniteRecurrentDecompositionStability.p_goa_03
    K B.decomp Bhat.decomp epsQ epsR hQ hR hsmall x0 epsStat hstat

/-! ## Certified history transport port -/

/-- Frozen P-ID-01 history/scale transport accumulation, exposed here as the
optional transport port of P-CORE-01.  The system's endpoint kernels and
coherent transports are the actual source objects; no independent final-error
premise is introduced. -/
theorem history_transport_certificate
    {M : ℕ → Type uX} [∀ n, MeasurableSpace (M n)]
    (S : TransportDefect.FrozenTransportSystem M)
    (ε : ℕ → ℝ) [Nonempty (M 0)]
    (hadj : S.AdjacentBound ε) (n : ℕ) :
    sSup (Set.range fun m : M 0 =>
      tvDist ((S.K 0 m).map (S.Γ 0 n))
        (S.K n (S.Γ 0 n m))) ≤
      ∑ i ∈ Finset.range n, ε i := by
  exact TransportDefect.FrozenTransportSystem.p_id_01 S ε hadj n

/-! ## Integrity-margin robustness -/

/-- If a representation perturbation is smaller than the true margin to a
fixed nonempty failure set, the perturbed representation cannot lie in that
failure set.  This is the direct P-OMG-02 consequence used by P-CORE-01. -/
theorem not_mem_failure_of_dist_lt_integrityMargin
    {X : Type uX} [PseudoMetricSpace X]
    (F : Set X) (hF : F.Nonempty) (T S : X)
    (hmargin : dist T S < OmegaIntegrityMargin.integrityMargin F T) :
    S ∉ F := by
  intro hSF
  have hlip := OmegaIntegrityMargin.p_omg_02 F hF T S
  have hzero : OmegaIntegrityMargin.integrityMargin F S = 0 := by
    unfold OmegaIntegrityMargin.integrityMargin
    exact Metric.infDist_zero_of_mem hSF
  rw [hzero, sub_zero] at hlip
  unfold OmegaIntegrityMargin.integrityMargin at hlip hmargin
  rw [abs_of_nonneg (Metric.infDist_nonneg : 0 ≤ Metric.infDist T F)] at hlip
  linarith

/-- Frozen §12.3/P-CORE orientation.  If the estimated representation has
margin strictly larger than a certified representation error `η`, then the
true representation still has positive distance from the same fixed failure
set. -/
theorem integrityMargin_pos_of_estimated_margin
    {X : Type uX} [PseudoMetricSpace X]
    (F : Set X) (hF : F.Nonempty)
    (T THat : X) (η : ℝ)
    (herr : dist T THat ≤ η)
    (hhat : η < OmegaIntegrityMargin.integrityMargin F THat) :
    0 < OmegaIntegrityMargin.integrityMargin F T := by
  have hlip := OmegaIntegrityMargin.p_omg_02 F hF T THat
  have hleft := (abs_le.mp hlip).1
  linarith

/-! ## Source-facing common-event assembly -/

/-- A realized sample inside all distinct certification events.  The inference
objects below are only required on this subtype; no theorem hypothesis is
silently strengthened to demand that estimation guarantees hold on failed
samples. -/
def GoodSample {Ω : Type uΩ} {K : Type uK}
    (E : K → Set Ω) :=
  {ω : Ω // ω ∈ commonGoodEvent E}

/-- Sample-dependent estimated quotient data with a definitionally fixed true
controlled process, candidate quotient map, and source error radii.  This is the
bridge that prevents the P-CORE probability space from changing the true world
or candidate `f` from sample to sample. -/
structure FixedSourceApproximation
    {X : Type uX} [Fintype X]
    {M : Type uM} [Fintype M]
    {Abar : M → Type uA}
    [∀ m, Fintype (Abar m)] [∀ m, Nonempty (Abar m)]
    (f : X → M)
    (micro : Model X (fun x => Abar (f x)))
    (εr εp : ℝ) where
  macroModel : Model M Abar
  discount_eq : micro.discount = macroModel.discount
  reward_approx : ∀ x (a : Abar (f x)),
    |micro.reward x a - macroModel.reward (f x) a| ≤ εr
  transition_tv_approx : ∀ x (a : Abar (f x)),
    FiniteProbabilityRow.tvDist
      (pushforwardTransitionPMF f micro x a)
      (macroModel.transitionPMF (f x) a) ≤ εp

/-- Forget the fixed-source wrapper only after the source identity has been
locked; all P-QUO-02 APIs can then be reused without duplicating their proofs. -/
def FixedSourceApproximation.toApproxControlQuotient
    {X : Type uX} [Fintype X]
    {M : Type uM} [Fintype M]
    {Abar : M → Type uA}
    [∀ m, Fintype (Abar m)] [∀ m, Nonempty (Abar m)]
    {f : X → M}
    {micro : Model X (fun x => Abar (f x))}
    {εr εp : ℝ}
    (Q : FixedSourceApproximation f micro εr εp)
    (hf : Function.Surjective f)
    (hεr : 0 ≤ εr) (hεp : 0 ≤ εp) :
    ApproxControlQuotient X M Abar where
  f := f
  surjective := hf
  micro := micro
  macroModel := Q.macroModel
  discount_eq := Q.discount_eq
  epsilonReward := εr
  epsilonTransition := εp
  epsilonReward_nonneg := hεr
  epsilonTransition_nonneg := hεp
  reward_approx := Q.reward_approx
  transition_tv_approx := Q.transition_tv_approx

/-- The exact P-QUO-02 value/regret conclusions for one realized approximate
control quotient. -/
def ControlCertificate
    {X : Type uX} [Fintype X]
    {M : Type uM} [Fintype M]
    {Abar : M → Type uA}
    [∀ m, Fintype (Abar m)] [∀ m, Nonempty (Abar m)]
    (Q : ApproxControlQuotient X M Abar) : Prop :=
  dist Q.micro.optimalValue
      (Q.pullback Q.macroModel.optimalValue) ≤ Q.D ∧
    ∀ {t : ℕ} (x : X),
      0 ≤ Q.micro.optimalValue x -
        CausalPolicy.infiniteValue
          (selectorPolicy (Q.liftSelector Q.macroModel.greedyAction))
          Q.micro (t := t) x ∧
      Q.micro.optimalValue x -
        CausalPolicy.infiniteValue
          (selectorPolicy (Q.liftSelector Q.macroModel.greedyAction))
          Q.micro (t := t) x ≤ 2 * Q.D

/-- The P-QUO-03 action-gap consequence, with its `D`-radius supplied by the
same quotient as `ControlCertificate`. -/
def ActionCertificate
    {X : Type uX} [Fintype X]
    {M : Type uM} [Fintype M]
    {Abar : M → Type uA}
    [∀ m, Fintype (Abar m)] [∀ m, Nonempty (Abar m)]
    (Q : ApproxControlQuotient X M Abar) : Prop :=
  ∀ x,
    (∀ a, a ≠ Q.macroModel.greedyAction (Q.f x) →
      2 * Q.D <
        Q.macroModel.qValue Q.macroModel.optimalValue (Q.f x)
          (Q.macroModel.greedyAction (Q.f x)) -
        Q.macroModel.qValue Q.macroModel.optimalValue (Q.f x) a) →
    ∀ a, a ≠ Q.macroModel.greedyAction (Q.f x) →
      Q.micro.qValue Q.micro.optimalValue x a <
        Q.micro.qValue Q.micro.optimalValue x
          (Q.macroModel.greedyAction (Q.f x))

/-- The stationary deterministic implementation policy certified by the same
approximate quotient: lift the macro greedy selector back to the micro state
space, then regard it as a stationary randomized policy concentrated at that
action. -/
noncomputable def quotientLiftedPolicy
    {X : Type uX} [Fintype X]
    {M : Type uM} [Fintype M]
    {Abar : M → Type uA}
    [∀ m, Fintype (Abar m)] [∀ m, Nonempty (Abar m)]
    (Q : ApproxControlQuotient X M Abar) :
    StationaryPolicy (fun x => Abar (Q.f x)) :=
  StationaryPolicy.ofSelector
    (Q.liftSelector Q.macroModel.greedyAction)

/-- The exact product-plus-additive P-DYN-03 path certificate for two models
under one stationary policy. -/
def PathCertificate
    {S : Type uS} [Fintype S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    {A : S → Type uPA} [∀ s, Fintype (A s)] [∀ s, Nonempty (A s)]
    (M Mhat : Model S A) (π : StationaryPolicy A)
    (p₀ : PMF S) (ε : ℕ → ℝ) : Prop :=
  ∀ T,
    tvDist
        (PathError.causalLaw p₀ (policyPathKernel M π) T).toMeasure
        (PathError.causalLaw p₀ (policyPathKernel Mhat π) T).toMeasure
      ≤ 1 - (∏ i ∈ Finset.range T, (1 - ε i)) ∧
    1 - (∏ i ∈ Finset.range T, (1 - ε i))
      ≤ ∑ i ∈ Finset.range T, ε i

/-- Optional P-GOA-02 port tied to exactly the same two controlled models and
the same implemented stationary policy as the finite-path certificate. -/
def MixingGOACertificate
    {S : Type uS} [Fintype S] [DecidableEq S] [Nonempty S]
    {A : S → Type uPA} [∀ s, Fintype (A s)] [∀ s, Nonempty (A s)]
    (M Mhat : Model S A) (π : StationaryPolicy A) : Prop :=
  ∀
    (halpha :
      FiniteDobrushin.dobrushinAlpha
        (policyMatrix M π) (policyMatrix_rowStochastic M π) < 1)
    (mu muhat : stdSimplex ℝ S) (epsilon : ℝ),
    FiniteDobrushin.step
        (policyMatrix M π) (policyMatrix_rowStochastic M π) mu = mu →
    FiniteDobrushin.step
        (policyMatrix Mhat π) (policyMatrix_rowStochastic Mhat π) muhat = muhat →
    (∀ x,
      FiniteDobrushin.crossRowTV
        (policyMatrix M π) (policyMatrix_rowStochastic M π)
        (policyMatrix Mhat π) (policyMatrix_rowStochastic Mhat π) x ≤ epsilon) →
    FiniteDobrushin.lawTV mu muhat ≤
      epsilon /
        (1 - FiniteDobrushin.dobrushinAlpha
          (policyMatrix M π) (policyMatrix_rowStochastic M π))

/-- Optional recurrent-structure P-GOA-03 port.  Because the frozen recurrent
decomposition theorem exposes its state as `T ⊕ R`, this port carries explicit
heterogeneous identity guards tying that decomposition back to the same true
model, estimated model, and implemented policy used by the finite control/path
certificate.  `PolicyRecurrentData` then additionally locks each decomposition
kernel to the corresponding policy-induced matrix. -/
def RecurrentGOACertificate
    {S : Type uS} [Fintype S]
    {A : S → Type uPA} [∀ s, Fintype (A s)] [∀ s, Nonempty (A s)]
    (M Mhat : Model S A) (π : StationaryPolicy A) : Prop :=
  ∀ {T : Type uS} [Fintype T] [DecidableEq T]
    {R : Type uS} {C : Type uS}
    [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]
    (K : FiniteRecurrentDecompositionStability.RecurrentPartition R C)
    {A' : FiniteRecurrentDecompositionStability.FullState T R → Type uPA}
    [∀ x, Fintype (A' x)] [∀ x, Nonempty (A' x)]
    (M' Mhat' : Model
      (FiniteRecurrentDecompositionStability.FullState T R) A')
    (π' : StationaryPolicy A')
    (_hM : HEq M' M) (_hMhat : HEq Mhat' Mhat) (_hπ : HEq π' π)
    (B : PolicyRecurrentData K M' π')
    (Bhat : PolicyRecurrentData K Mhat' π')
    (epsQ epsR : ℝ)
    (hQ : ‖Bhat.decomp.block.Q - B.decomp.block.Q‖ ≤ epsQ)
    (hR : ‖Bhat.decomp.block.R - B.decomp.block.R‖ ≤ epsR)
    (hsmall : ‖B.decomp.block.N‖ * epsQ < 1)
    (x0 : FiniteRecurrentDecompositionStability.FullState T R)
    (epsStat : C → ℝ)
    (hstat : ∀ j,
      FiniteDobrushin.lawTV
        (B.decomp.classLaw j) (Bhat.decomp.classLaw j) ≤ epsStat j),
    let nu := FiniteRecurrentDecompositionStability.recurrentMixture
      (FiniteRecurrentDecompositionStability.initialClassWeights
        K B.decomp.block x0) B.decomp.classLaw
    let nuhat := FiniteRecurrentDecompositionStability.recurrentMixture
      (FiniteRecurrentDecompositionStability.initialClassWeights
        K Bhat.decomp.block x0) Bhat.decomp.classLaw
    ‖Bhat.decomp.block.H - B.decomp.block.H‖ ≤
        (‖B.decomp.block.N‖ ^ 2 * epsQ + ‖B.decomp.block.N‖ * epsR) /
          (1 - ‖B.decomp.block.N‖ * epsQ) ∧
      Tendsto
        (UEOT.V3.FiniteCesaroInvariant.cesaroRow
          B.decomp.P B.decomp.stochastic
          (FiniteRecurrentDecompositionStability.FiniteRecurrentDecomposition.pureFullLaw x0))
        atTop (𝓝 nu) ∧
      Tendsto
        (UEOT.V3.FiniteCesaroInvariant.cesaroRow
          Bhat.decomp.P Bhat.decomp.stochastic
          (FiniteRecurrentDecompositionStability.FiniteRecurrentDecomposition.pureFullLaw x0))
        atTop (𝓝 nuhat) ∧
      FiniteDobrushin.lawTV nu nuhat ≤
        (1 / 2 : ℝ) *
            ((‖B.decomp.block.N‖ ^ 2 * epsQ + ‖B.decomp.block.N‖ * epsR) /
              (1 - ‖B.decomp.block.N‖ * epsQ)) +
          ∑ j,
            (FiniteRecurrentDecompositionStability.initialClassWeights
              K Bhat.decomp.block x0).1 j * epsStat j

/-- Pointwise certificate produced on every sample of the common good event. -/
structure CorePointwiseCertificate
    {V : Type uV} [Fintype V] [DecidableEq V]
    {H : Type uH} [Fintype H] [Nonempty H]
    {I : Type uI} [Fintype I] [Nonempty I]
    {R : Type uR} {Y : Type uY} [MeasurableSpace Y]
    (readout : Finset V → H → R)
    (p pHat : H → I → Measure Y)
    (γ τ : ℝ)
    {X : Type uX} [Fintype X] [DecidableEq X] [Nonempty X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    {M : Type uM} [Fintype M]
    {Abar : M → Type uA}
    [∀ m, Fintype (Abar m)] [∀ m, Nonempty (Abar m)]
    (Q : ApproxControlQuotient X M Abar)
    (microHat : Model X (fun x => Abar (Q.f x)))
    (p₀ : PMF X) (εPath : ℕ → ℝ)
    {Obj : Type uObj} [PseudoMetricSpace Obj]
    (failure : Set Obj) (object objectHat : Obj) : Prop where
  predictive_recovery :
    ∀ h h',
      PredictiveClassRecovery.protocolDistance pHat h h' ≤ γ / 2 ↔
        PredictiveClassRecovery.trueEquivalent p h h'
  carrier_recovery :
    estimatedCarrierFamily readout pHat τ = exactCarrierFamily readout p
  blocker_recovery :
    Blocker.blocker (estimatedCarrierFamily readout pHat τ) =
      Blocker.blocker (exactCarrierFamily readout p)
  control : ControlCertificate Q
  action : ActionCertificate Q
  path : PathCertificate Q.micro microHat (quotientLiftedPolicy Q) p₀ εPath
  mixing_goa : MixingGOACertificate Q.micro microHat (quotientLiftedPolicy Q)
  recurrent_goa :
    RecurrentGOACertificate Q.micro microHat (quotientLiftedPolicy Q)
  history_transport :
    ∀ {MH : ℕ → Type uH} [∀ n, MeasurableSpace (MH n)]
      (S : TransportDefect.FrozenTransportSystem MH)
      (ε : ℕ → ℝ) [Nonempty (MH 0)]
      (hadj : S.AdjacentBound ε) (n : ℕ),
      sSup (Set.range fun m : MH 0 =>
        tvDist ((S.K 0 m).map (S.Γ 0 n))
          (S.K n (S.Γ 0 n m))) ≤
        ∑ i ∈ Finset.range n, ε i
  integrity : 0 < OmegaIntegrityMargin.integrityMargin failure object

/-- **P-CORE-01, finite operational assembly.**

`K` indexes distinct certification events.  If one event is reused by several
modules, it is represented by one key and is therefore counted once in the
failure budget.  The theorem first gives the common-event probability lower
bound and then constructs all mandatory finite certificates on every realized
sample in that event.

The optional long-run and history-transport clauses occur inside each
`CorePointwiseCertificate` as conditional ports.  They therefore belong to the
same common-good-event conclusion while still requiring exactly their
source-declared additional assumptions. -/
theorem p_core_01
    {Ω : Type uΩ} [MeasurableSpace Ω]
    {K : Type uK} [Fintype K]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : K → Set Ω) (α : K → ℝ)
    (hE : ∀ k, MeasurableSet (E k))
    (hfail : ∀ k, μ.real (E k)ᶜ ≤ α k)
    {V : Type uV} [Fintype V] [DecidableEq V]
    {H : Type uH} [Fintype H] [Nonempty H]
    {I : Type uI} [Fintype I] [Nonempty I]
    {R : Type uR} {Y : Type uY} [MeasurableSpace Y]
    (readout : Finset V → H → R)
    (p : H → I → Measure Y)
    (hp : ∀ h i, IsProbabilityMeasure (p h i))
    (pHat : GoodSample E → H → I → Measure Y)
    (hpHat : ∀ ω h i, IsProbabilityMeasure (pHat ω h i))
    (η γ Δ τ : ℝ)
    (hresp : ∀ ω h i, tvDist (p h i) (pHat ω h i) ≤ η)
    (hsep : ∀ h h',
      ¬PredictiveClassRecovery.trueEquivalent p h h' →
        γ ≤ PredictiveClassRecovery.protocolDistance p h h')
    (hpredGap : 2 * η < γ / 2)
    (hcarrierGap : ∀ S,
      0 < StatisticalDefect.responseDefect readout p S →
        Δ ≤ StatisticalDefect.responseDefect readout p S)
    (hlower : 2 * η < τ) (hupper : τ < Δ - 2 * η)
    {X : Type uX} [Fintype X] [DecidableEq X] [Nonempty X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    {M : Type uM} [Fintype M]
    {Abar : M → Type uA}
    [∀ m, Fintype (Abar m)] [∀ m, Nonempty (Abar m)]
    (f : X → M) (hf : Function.Surjective f)
    (micro : Model X (fun x => Abar (f x)))
    (εr εp : ℝ) (hεr : 0 ≤ εr) (hεp : 0 ≤ εp)
    (QHat : GoodSample E → FixedSourceApproximation f micro εr εp)
    (microHat : GoodSample E → Model X (fun x => Abar (f x)))
    (p₀ : PMF X) (εPath : ℕ → ℝ)
    (hε0 : ∀ n, 0 ≤ εPath n) (hε1 : ∀ n, εPath n ≤ 1)
    (hpath : ∀ ω n x,
      let Q := (QHat ω).toApproxControlQuotient hf hεr hεp
      tvDist
        (policyTransitionPMF micro (quotientLiftedPolicy Q) x).toMeasure
        (policyTransitionPMF (microHat ω) (quotientLiftedPolicy Q) x).toMeasure
          ≤ εPath n)
    {Obj : Type uObj} [PseudoMetricSpace Obj]
    (failure : Set Obj) (hFailure : failure.Nonempty)
    (object : Obj) (objectHat : GoodSample E → Obj)
    (ηObj : ℝ)
    (hobject : ∀ ω, dist object (objectHat ω) ≤ ηObj)
    (hestimatedMargin : ∀ ω,
      ηObj < OmegaIntegrityMargin.integrityMargin failure (objectHat ω)) :
    1 - ∑ k, α k ≤ μ.real (commonGoodEvent E) ∧
      ∀ ω : GoodSample E,
        let Q := (QHat ω).toApproxControlQuotient hf hεr hεp
        CorePointwiseCertificate
          readout p (pHat ω) γ τ Q
          (microHat ω) p₀ εPath failure object (objectHat ω) := by
  constructor
  · exact commonGoodEvent_measureReal_lower μ E α hE hfail
  · intro ω
    dsimp only
    let Q := (QHat ω).toApproxControlQuotient hf hεr hεp
    have hresponse := response_recovery_on_good_event
      readout p (pHat ω) hp (hpHat ω) η γ Δ τ
      (hresp ω) hsep hpredGap hcarrierGap hlower hupper
    refine
      { predictive_recovery := hresponse.1
        carrier_recovery := hresponse.2.1
        blocker_recovery := hresponse.2.2
        control := ?_
        action := ?_
        path := ?_
        mixing_goa := ?_
        recurrent_goa := ?_
        history_transport := ?_
        integrity := ?_ }
    · exact Q.p_quo_02
    · intro x hgap
      exact macro_gap_certifies_micro_action Q x hgap
    · exact same_policy_path_error
        micro (microHat ω) (quotientLiftedPolicy Q)
        p₀ εPath hε0 hε1 (hpath ω)
    · intro halpha mu muhat epsilon hmu hmuhat hrow
      exact same_policy_goa02
        micro (microHat ω) (quotientLiftedPolicy Q)
        halpha mu muhat epsilon hmu hmuhat hrow
    · intro T _ _ R C _ _ _ _ K A' _ _ M' Mhat' π'
        _hM _hMhat _hπ B Bhat epsQ epsR hQ hR hsmall x0 epsStat hstat
      exact same_policy_goa03
        K M' Mhat' π' B Bhat epsQ epsR hQ hR hsmall x0 epsStat hstat
    · intro MH _ S ε _ hadj n
      exact history_transport_certificate S ε hadj n
    · exact integrityMargin_pos_of_estimated_margin
        failure hFailure object (objectHat ω) ηObj
        (hobject ω) (hestimatedMargin ω)

end UEOT.V3.CoreOperationalAssembly
