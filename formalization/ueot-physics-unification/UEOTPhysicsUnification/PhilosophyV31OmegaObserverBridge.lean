import UEOT.V3.PersistenceOmega
import UEOT.V3.ViabilityKernel
import UEOT.V3.Agency
import UEOT.V3.RepresentationCovariance
import UEOT.V3.Compression.QuotientDescent
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionRepresentation
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionNativeConsumer
import UEOTPhysicsUnification.OperationalHorizonMinimumScale
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# UEOT Philosophy v3.1 (`Ch. 1–30`) + Mathematics v4.2 (`1,051` Modules) ↔ Unified Physics Bridge
(`P-PHIL31-OMEGA-01`, `P-PHIL31-REALIZ-02`, `P-PHIL31-LAKATOS-03`)

Pure-kernel Lean 4 formalization bridging the **UEOT Philosophy Book v3.1** (*Objects, Evolution,
and Meaning*, Parts I–VI, Chapters 1–30, Appendices A–D) and **Mathematics Book v4.2** (`UEOT.V3`
and `TheoryCompletion.UnifiedClosure`) to **Unified Physics** (`PR #468` `RC01`–`RC12` / `AH01`–`AH12`
and `UEOTPhysicsUnification`):

1. **Physical Realization & Exclusivity of Organizational Integrity `Ω` (`P-PHIL31-OMEGA-01`,
   Philosophy v3.1 Ch. 4, 6–9, 14)**:
   - Passive Gibbs / state-independent variational equilibrium kernels have identically zero
     interventional self-repair differentiation (`passive_gibbs_zero_constitutive_repair_diff`) and
     collapse to an empty controlled viability kernel (`viabilityStep = ∅`) under any nonzero thermal
     damage probability (`passive_gibbs_viability_collapses_under_thermal_fault`).
   - By contrast, a prepaid regenerative organization achieves strictly positive interventional
     self-repair differentiation and a non-empty all-horizon controlled viability kernel (`ViabilityKernel`)
     if and only if its prepaid resource budget covers the positive repair tariff
     (`prepaid_regen_positive_repair_diff_iff_budget`, `prepaid_regen_viability_kernel_intact_iff_budget`).
   - Connects directly to Ch. 14's separation of stationary marginal occupancy (`7/8`) from cumulative
     uninterrupted survival (`15/64 > 1/8` two-step interruption) and `PersistenceOmega.p_per_01`,
     and directly consumes `RegisterDecisionRepresentation`, `RegisterJointDecisionNativeConsumer`,
     `RegisterJointDecisionSource`, and `RegisterDecisionRepresentationWitnesses`
     (`charged_iff_nonzero_fee`, `24(H+1)^4` node bound, `result_native_optimal`, and memory
     insufficiency of `(body, wallet, elapsed)` alone).
   - Proves the exact necessary-and-sufficient (`↔`) quantum-gravitational realization theorem
     (`ah01_nontrapped_clock_persistence_iff_above_planck_floor`,
     `autonomous_clock_pointer_omega_persistence_and_record_iff`): an autonomous quantum
     clock-controller-pointer (`RC01`–`RC09`, `AH01`–`AH08`) achieves non-trapped operational
     persistence and strictly positive relational record distinguishability (`d_TV > 2.69 × 10⁻³⁰` at
     unit benchmark) if and only if its sensor scale exceeds the `AH01` Planck-horizon floor
     `L > L_min * l_P` and its prepaid energy/coherence budget is strictly positive.

2. **Macroscopic Realization Without Causal Double-Counting, Representation Covariance, Rank-3
   `(s, b, bq)` Boundary & Phenomenal/Normative Non-Deduction (`P-PHIL31-REALIZ-02`, Ch. 12–13, 15–17, 21, 25)**:
   - Applies `QuotientDescent.existsUnique_descend` to prove unique coarse-grained RG/hydrodynamic/
     gravitational realization (`no_second_force_unique_quotient_realization`) and proves the
     additive causal-exclusion theorem (`double_counting_sum_equals_realized_iff_zero`): summing
     microscopic and macroscopic responses agrees with physical realization iff the response vanishes.
   - Directly links `RepresentationCovariance` (`p_fac_01_covariance_bundle`,
     `optimalExpectedValue_transport`), Ch. 13 `Π/Φ` additive gauge invariance, and Ch. 5/8/17
     lineage retention vs enlarged-permission (`dispatch2`) quotient breakdown.
   - Formalizes Ch. 12 / Mathematics v4.2 §23.4's exact `3 × 3` Jacobian determinant `det J = b > 0`
     for `(s, b, q) ↦ (s, b, b * q)` and proves via the Fréchet chain rule (`HasFDerivAt.comp`) plus
     constructive `ℝ³ → ℝ²` kernel elimination that **no differentiable 2D `Π/Φ` bottleneck** can
     locally factor `(s, b, bq)` whenever `b ≠ 0` (`ch12_no_differentiable_two_dim_piphi_bottleneck`).
   - Proves Ch. 21's model-theoretic non-deduction of phenomenal consciousness from functional
     transition/report laws alone and Ch. 25's non-deduction of republican non-domination /
     substantive capabilities from exponential growth rates (`Agency.extension_optimalValue_mono`).

3. **Formalized Ch. 28 Lakatosian Research Programme Contract & Non-Immunity (`P-PHIL31-LAKATOS-03`,
   Philosophy v3.1 Ch. 28–30)**:
   - Formalizes `(HardCore, ProtectiveBelt, RefutationWitness)`, proves that post-hoc domain excision
     is a degenerating shift with strictly shrunk scope (`ad_hoc_domain_excision_is_degenerating_shift`),
     constructs explicit protective-belt and uniform hard-core refutation witnesses for UEOT Physics
     (`ueot_lakatos_nonvacuous_and_non_immune`), and proves why finite non-refuted trials never erase
     positive failure risk, preserving `UNVERIFIED_EMPIRICAL` and `"physical_unification": "OPEN"`.
-/

namespace UEOTPhysicsUnification.PhilosophyV31OmegaObserverBridge

open Set Function Filter Topology MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators NNReal
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

/-! ## Section 1. Physical Realization & Exclusivity of Organizational Integrity `Ω`
(`P-PHIL31-OMEGA-01`: Philosophy v3.1 Ch. 4, 6–9, 14) -/

/-- Exact normalized `Bool` probability mass function with intact probability `p` (`p ≤ 1`) and
damage probability `1 - p`. -/
noncomputable def boolCoinPMF (p : ℝ≥0) (hp : p ≤ 1) : PMF Bool :=
  PMF.ofFintype
    (fun b : Bool => if b then (p : ENNReal) else ((1 - p : ℝ≥0) : ENNReal))
    (by
      rw [Fintype.sum_bool]
      simp only [ite_true, Bool.false_eq_true, ite_false]
      exact_mod_cast add_tsub_cancel_of_le hp)

@[simp] theorem boolCoinPMF_apply_true (p : ℝ≥0) (hp : p ≤ 1) :
    boolCoinPMF p hp true = (p : ENNReal) := by
  simp [boolCoinPMF]

@[simp] theorem boolCoinPMF_apply_false (p : ℝ≥0) (hp : p ≤ 1) :
    boolCoinPMF p hp false = ((1 - p : ℝ≥0) : ENNReal) := by
  simp [boolCoinPMF]

theorem false_mem_support_boolCoinPMF {p : ℝ≥0} (hp : p ≤ 1) (hlt : p < 1) :
    false ∈ (boolCoinPMF p hp).support := by
  rw [PMF.mem_support_iff, boolCoinPMF_apply_false]
  have hsub : (0 : ℝ≥0) < 1 - p := tsub_pos_of_lt hlt
  exact ENNReal.coe_ne_zero.mpr (ne_of_gt hsub)

/-- State-and-intervention-independent passive Gibbs / variational equilibrium kernel on `Bool`
(`true` = intact operating state, `false` = damaged state). -/
noncomputable def passiveGibbsKernel (A : Type*) (pEq : ℝ≥0) (hp : pEq ≤ 1) :
    Bool → A → PMF Bool :=
  fun _ _ => boolCoinPMF pEq hp

/-- **Passive Gibbs Zero Repair Differentiation (`Ch. 4`)**: Any passive equilibrium relaxation law
whose transition weights do not consume prepaid work to counter damage exhibits identically zero
constitutive repair differentiation across all interventions `a₁, a₂`. -/
theorem passive_gibbs_zero_constitutive_repair_diff
    {A : Type*} (pEq : ℝ≥0) (hp : pEq ≤ 1) (a₁ a₂ : A) :
    (passiveGibbsKernel A pEq hp false a₁ true).toReal -
      (passiveGibbsKernel A pEq hp false a₂ true).toReal = 0 := by
  simp [passiveGibbsKernel]

/-- **Passive Gibbs Controlled Viability Collapse (`Ch. 4` & `ViabilityKernel`)**: Whenever thermal
fluctuations assign strictly positive probability to the damaged state (`pEq < 1`), the intact domain
`{true}` has an empty controlled viability step under `passiveGibbsKernel`. -/
theorem passive_gibbs_viability_collapses_under_thermal_fault
    (A : Type*) [Fintype A] (pEq : ℝ≥0) (hp : pEq ≤ 1) (hfault : pEq < 1) :
    UEOT.V3.ViabilityKernel.viabilityStep (passiveGibbsKernel A pEq hp) ({true} : Set Bool) = ∅ := by
  ext x
  simp only [UEOT.V3.ViabilityKernel.viabilityStep, UEOT.V3.ViabilityKernel.StaysIn,
    mem_singleton_iff, mem_empty_iff_false, iff_false]
  rintro ⟨rfl, a, hsub⟩
  have hfalse : false ∈ (passiveGibbsKernel A pEq hp true a).support :=
    false_mem_support_boolCoinPMF hp hfault
  exact Bool.false_ne_true (mem_singleton_iff.mp (hsub hfalse))

/-- Prepaid regenerative transition kernel on `Bool` (`true` = intact, `false` = damaged) with
action `a : Bool` (`false` = unpaid idle, `true` = paid repair/maintenance), repair tariff `cRep`,
and prepaid wallet budget `B`. -/
noncomputable def prepaidRegenKernel
    (rIdle rRep : ℝ≥0) (hIdle : rIdle ≤ 1) (hRep : rRep ≤ 1) (cRep B : ℝ) :
    Bool → Bool → PMF Bool
  | false, a =>
      if a = true ∧ cRep ≤ B then boolCoinPMF rRep hRep
      else boolCoinPMF rIdle hIdle
  | true, a =>
      if a = true ∧ cRep ≤ B then PMF.pure true
      else boolCoinPMF rIdle hIdle

/-- **Constitutive Self-Repair Exclusivity (`Ch. 4, 6–7, 9`)**: Under positive repair efficacy
`rIdle < rRep` and positive tariff `0 < cRep`, interventional constitutive repair differentiation
from a damaged state is strictly positive **if and only if** the prepaid budget covers the tariff
(`cRep ≤ B`, which forces strictly positive budget `0 < B`). -/
theorem prepaid_regen_positive_repair_diff_iff_budget
    (rIdle rRep : ℝ≥0) (hIdle : rIdle ≤ 1) (hRep : rRep ≤ 1)
    {cRep B : ℝ} (hc : 0 < cRep) (hr : rIdle < rRep) :
    (0 < (prepaidRegenKernel rIdle rRep hIdle hRep cRep B false true true).toReal -
        (prepaidRegenKernel rIdle rRep hIdle hRep cRep B false false true).toReal) ↔
      (cRep ≤ B ∧ 0 < B) := by
  constructor
  · intro hpos
    by_cases hB : cRep ≤ B
    · exact ⟨hB, lt_of_lt_of_le hc hB⟩
    · simp [prepaidRegenKernel, hB] at hpos
  · rintro ⟨hB, _⟩
    simp only [prepaidRegenKernel, true_and, if_pos hB, Bool.false_eq_true, false_and, if_false,
      boolCoinPMF_apply_true, ENNReal.coe_toReal]
    exact sub_pos.mpr (NNReal.coe_lt_coe.mpr hr)

/-- **Controlled Viability Kernel Stabilization under Prepaid Budget (`Ch. 9` & `ViabilityKernel`)**:
With positive idle fault risk `rIdle < 1` and positive tariff `0 < cRep`, `{true}` is a fixed
controlled viability kernel (guaranteeing all-horizon probability-1 retention under a stationary
policy via `ViabilityKernel.stationaryStateLaw_staysIn`) **if and only if** `cRep ≤ B`. -/
theorem prepaid_regen_viability_kernel_intact_iff_budget
    (rIdle rRep : ℝ≥0) (hIdle : rIdle ≤ 1) (hRep : rRep ≤ 1)
    (hFault : rIdle < 1) {cRep B : ℝ} (_hc : 0 < cRep) :
    UEOT.V3.ViabilityKernel.viabilityStep
        (prepaidRegenKernel rIdle rRep hIdle hRep cRep B) ({true} : Set Bool) = {true} ↔
      cRep ≤ B := by
  constructor
  · intro hfix
    by_contra hnotB
    have hmem : true ∈ UEOT.V3.ViabilityKernel.viabilityStep
        (prepaidRegenKernel rIdle rRep hIdle hRep cRep B) ({true} : Set Bool) := by
      rw [hfix]; exact mem_singleton true
    rcases hmem with ⟨_, a, ha⟩
    have hfalse : false ∈ (prepaidRegenKernel rIdle rRep hIdle hRep cRep B true a).support := by
      simp only [prepaidRegenKernel, hnotB, and_false, if_false]
      exact false_mem_support_boolCoinPMF hIdle hFault
    exact Bool.false_ne_true (mem_singleton_iff.mp (ha hfalse))
  · intro hB
    ext x
    simp only [UEOT.V3.ViabilityKernel.viabilityStep, UEOT.V3.ViabilityKernel.StaysIn,
      mem_singleton_iff]
    constructor
    · exact fun hx => hx.1
    · rintro rfl
      refine ⟨rfl, true, ?_⟩
      simp [prepaidRegenKernel, hB]

/-- All-horizon probability-1 intact persistence extracted via `UEOT.V3.ViabilityKernel` whenever
`cRep ≤ B`. -/
theorem prepaid_regen_all_horizon_intact_persistence
    (rIdle rRep : ℝ≥0) (hIdle : rIdle ≤ 1) (hRep : rRep ≤ 1)
    {cRep B : ℝ} (hB : cRep ≤ B) (n : ℕ) :
    UEOT.V3.ViabilityKernel.StaysIn
      (UEOT.V3.ViabilityKernel.stationaryStateLaw
        (prepaidRegenKernel rIdle rRep hIdle hRep cRep B) (fun _ => true) (PMF.pure true) n)
      ({true} : Set Bool) := by
  apply UEOT.V3.ViabilityKernel.stationaryStateLaw_staysIn
  · simp [UEOT.V3.ViabilityKernel.StaysIn]
  · intro x hx
    rw [mem_singleton_iff.mp hx]
    simp [UEOT.V3.ViabilityKernel.StaysIn, prepaidRegenKernel, hB]

/-- **Philosophy v3.1 Ch. 14 Separation of Stationary Marginal vs Uninterrupted Path Viability**:
For any step interruption probability `p ∈ (0, 1)`, the two-step cumulative interruption probability
`1 - (1 - p)^2 = p * (2 - p)` strictly exceeds the constant single-time marginal interruption `p`;
at Ch. 14's exact parameter `p = 1/8`, stationary operating marginals remain `7/8` while two-step
cumulative interruption reaches `15/64 > 1/8`. -/
theorem ch14_stationary_marginal_vs_uninterrupted_survival_strict_gap
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    p < 1 - (1 - p) ^ 2 ∧
      (1 : ℝ) - (1 - 1 / 8) ^ 2 = 15 / 64 ∧ (1 / 8 : ℝ) < 15 / 64 := by
  refine ⟨by nlinarith, by norm_num, by norm_num⟩

/-- Direct continuous-time `ℝ≥0` semiflow persistence bridge to `UEOT.V3.PersistenceOmega.p_per_01`. -/
theorem ch14_persistence_omega_semiflow_bridge
    {X : Type*} [TopologicalSpace X] [T2Space X] [FirstCountableTopology X]
    (φ : Flow ℝ≥0 X) (x : X) {V : Set X}
    (hV : IsClosed V)
    (hstay : ∀ᶠ t in (atTop : Filter ℝ≥0), φ t x ∈ V)
    (hpre : IsCompact (closure (range fun t : ℝ≥0 => φ t x))) :
    (omegaLimit (atTop : Filter ℝ≥0) φ ({x} : Set X)).Nonempty ∧
      IsCompact (omegaLimit (atTop : Filter ℝ≥0) φ ({x} : Set X)) ∧
      omegaLimit (atTop : Filter ℝ≥0) φ ({x} : Set X) ⊆ V ∧
      ∀ s : ℝ≥0,
        φ s '' omegaLimit (atTop : Filter ℝ≥0) φ ({x} : Set X) =
          omegaLimit (atTop : Filter ℝ≥0) φ ({x} : Set X) :=
  UEOT.V3.PersistenceOmega.p_per_01 φ x hV hstay hpre

/-- Positive public write tariff (`0 < writeCost`) makes write-charge observation strictly equivalent
to nonzero resource expenditure (`RegisterJointDecisionSource.charged_iff_nonzero_fee`), ruling out
zero-cost Maxwell-demon mode probing. -/
theorem positive_tariff_excludes_zero_cost_mode_oracle
    {Theta : Type*} {n : ℕ} (i : Fin n)
    (m : RegisterMechanismPurpose.Mechanism)
    (w : RegisterJointDecisionSource.NativeWorld Theta n)
    (a : RegisterJointDecisionSource.Act) (z : RegisterJointDecisionSource.Noise)
    (hc : 0 < (m.writeCost : ℝ)) :
    (RegisterJointDecisionSource.observe m.goal
      (RegisterJointDecisionSource.projectWorld i w) a z).2 = true ↔
      RegisterJointDecisionSource.nativeFee
        (RegisterJointDecisionSource.nativeTransaction i m w a z) ≠ 0 :=
  RegisterJointDecisionSource.charged_iff_nonzero_fee i m w a z hc

/-- **Direct Native Bridge to Prepaid `Store`, `DecisionRepresentation` & Memory Sufficiency
(`Ch. 6–9`)**:
1. Any certified compact `DecisionRepresentation` controller has polynomial node count `≤ 24(H+1)^4`,
   achieves its exact value under literal `Store` execution from the damaged founder, and dominates
   every permitted full-history real-randomized competitor (`result_native_optimal`);
2. Present `(elapsed, paidCount, body)` alone is insufficient for optimal future prediction/control
   (`body_wallet_time_is_insufficient`: posteriors `1/4` vs `1/2`, next-birth laws `5/8` vs `1/2`). -/
theorem prepaid_store_and_decision_representation_omega_bridge
    {Theta : Type} [Fintype Theta]
    (P : RegisterJointDecisionConsumer.Family Theta)
    (prior : Theta → ℚ) (hn : ∀ t, 0 ≤ prior t) (ht : ∑ t, prior t = 1)
    (initial : RegisterJointDecisionConsumer.Wallet) (H : ℕ)
    (result : RegisterDecisionRepresentation.Result P prior hn ht initial H) :
    result.control.graph.size ≤ 24 * (H + 1) ^ 4 ∧
    ((∑ theta, (prior theta : ℝ) *
      RegisterDecisionRepresentationNative.nativeGraphJ P (0 : Fin 1)
        (RegisterDecisionRepresentationModel.model P prior hn ht initial)
        result.control.graph H (RegisterDecisionObserver.initialStat P.goal)
        (some result.control.root.val)
        (RegisterJointDecisionNativeConsumer.nativeInitial P theta)) =
      ((result.control.graph[result.control.root.val]).value : ℝ)) ∧
    (∀ (pi : FiniteJointDecisionSupportedPolicy.RawCausalPolicy
          (RegisterJointDecisionConsumer.model P))
        (h : pi.Memory)
        (_hi : pi.info h =
          (RegisterJointDecisionConsumer.initialBelief P prior hn ht, initial))
        (R : RegisterJointDecisionNativeConsumer.Realization P (0 : Fin 1) (pi.info h).1)
        (_ha : FiniteJointDecisionSupportedPolicy.SupportedAdmissible
          (RegisterJointDecisionConsumer.model P) pi H h),
      RegisterJointDecisionNativeConsumer.expectedRawNativeJ P (0 : Fin 1) pi H h R ≤
        ((result.control.graph[result.control.root.val]).value : ℝ)) ∧
    RegisterDecisionRepresentationWitnesses.lowPosterior
      RegisterDecisionRepresentationWitnesses.insufficientA = 1 / 4 ∧
    RegisterDecisionRepresentationWitnesses.lowPosterior
      RegisterDecisionRepresentationWitnesses.insufficientB = 1 / 2 ∧
    RegisterDecisionRepresentationWitnesses.conditionalNextBirth
      RegisterDecisionRepresentationWitnesses.insufficientA
      RegisterDecisionRepresentationWitnesses.childIdle = 5 / 8 ∧
    RegisterDecisionRepresentationWitnesses.conditionalNextBirth
      RegisterDecisionRepresentationWitnesses.insufficientB
      RegisterDecisionRepresentationWitnesses.childIdle = 1 / 2 := by
  have hmem := RegisterDecisionRepresentationWitnesses.body_wallet_time_is_insufficient
  refine ⟨RegisterDecisionRepresentation.result_node_bound P prior hn ht initial H result,
    RegisterDecisionRepresentation.result_native_value P prior hn ht initial H result,
    fun pi h hi R ha =>
      RegisterDecisionRepresentation.result_native_optimal P prior hn ht initial H result pi h hi R ha,
    hmem.2.2.2.2.1, hmem.2.2.2.2.2.1, hmem.2.2.2.2.2.2.1, hmem.2.2.2.2.2.2.2⟩

/-- CPTP binary readout stability: if a reference channel achieves binary gap `≥ dRef` and both
branch readout probabilities deviate from the reference by at most `delta`, the actual binary TV
distinguishability is at least `dRef - 2 * delta`. -/
theorem cptp_binary_gap_perturbation_lower_bound
    {pPlusRef pMinusRef pPlusAct pMinusAct dRef delta : ℝ}
    (href : dRef ≤ |pPlusRef - pMinusRef|)
    (hPlus : |pPlusAct - pPlusRef| ≤ delta)
    (hMinus : |pMinusAct - pMinusRef| ≤ delta) :
    dRef - 2 * delta ≤ |pPlusAct - pMinusAct| := by
  have hrew : pPlusRef - pMinusRef =
      (pPlusAct - pMinusAct) + (pPlusRef - pPlusAct) + (pMinusAct - pMinusRef) := by ring
  have h1 := abs_add_le (pPlusAct - pMinusAct + (pPlusRef - pPlusAct)) (pMinusAct - pMinusRef)
  have h2 := abs_add_le (pPlusAct - pMinusAct) (pPlusRef - pPlusAct)
  rw [← hrew] at h1
  have hPlus' : |pPlusRef - pPlusAct| ≤ delta := by rw [abs_sub_comm]; exact hPlus
  linarith

/-- Certified rational continuum binary record gaps (`RC02` `> 2.69 × 10⁻³⁰` and `RC09` local
autonomous pointer `> 4.5 × 10⁻²³ > 2.69 × 10⁻³⁰`). -/
theorem rc02_and_rc09_continuum_record_tv_certified :
    ((269 : ℝ) / 10 ^ 32 < (27346 : ℝ) / 10 ^ 34 - 2 * ((503 : ℝ) / 10 ^ 35)) ∧
      ((45 : ℝ) / 10 ^ 24 < (5049 : ℝ) / 10 ^ 26 - 2 * ((431 : ℝ) / 10 ^ 28)) ∧
      ((269 : ℝ) / 10 ^ 32 < (45 : ℝ) / 10 ^ 24) := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **Exact `iff` Characterization of Non-Trapped Operational Quantum Clock Persistence (`AH01`)**:
Given `L, E_min, hbar, c, G, lam_sys > 0`, define dimensionless horizon coefficient
`L_min := √(2 * E_min / lam_sys)` and Planck length `l_P := √(ℏ * G / c^3)`.
There exists a total apparatus energy budget `E_tot : ℝ` simultaneously satisfying the operational
quantum clock uncertainty/SNR floor `E_min * ℏ * c ≤ E_tot * L` and spherical hoop non-trapping
`2 * G * E_tot < lam_sys * c^4 * L` **if and only if** `L_min * l_P < L` — and every such `E_tot`
is strictly positive (`0 < E_tot`). -/
theorem ah01_nontrapped_clock_persistence_iff_above_planck_floor
    {L E_min hbar c G lam_sys : ℝ}
    (hL : 0 < L) (hEmin : 0 < E_min) (hhbar : 0 < hbar)
    (hc : 0 < c) (hG : 0 < G) (hlam : 0 < lam_sys) :
    let L_min := Real.sqrt (2 * E_min / lam_sys)
    let l_P := Real.sqrt (hbar * G / c ^ 3)
    (∃ E_tot : ℝ, E_min * hbar * c ≤ E_tot * L ∧ 2 * G * E_tot < lam_sys * c ^ 4 * L) ↔
      (L_min * l_P < L ∧
        ∀ E_tot : ℝ, E_min * hbar * c ≤ E_tot * L → 0 < E_tot) := by
  intro L_min l_P
  have ha_nonneg : 0 ≤ 2 * E_min / lam_sys := by positivity
  have hb_nonneg : 0 ≤ hbar * G / c ^ 3 := by positivity
  have hprod_sqrt : L_min * l_P = Real.sqrt ((2 * E_min / lam_sys) * (hbar * G / c ^ 3)) := by
    dsimp [L_min, l_P]
    rw [← Real.sqrt_mul ha_nonneg]
  have hpos_E : ∀ E_tot : ℝ, E_min * hbar * c ≤ E_tot * L → 0 < E_tot := by
    intro E_tot hclock
    have hprod_pos : 0 < E_tot * L := lt_of_lt_of_le (by positivity) hclock
    exact (mul_pos_iff_of_pos_right hL).mp hprod_pos
  constructor
  · rintro ⟨E_tot, hclock, hnotrap⟩
    refine ⟨?_, hpos_E⟩
    have hsq := (UEOTPhysicsUnification.OperationalHorizonMinimumScale.gravitational_horizon_excludes_pointlike_clock
      hL hEmin hhbar hc hG hlam hclock hnotrap).2
    rw [hprod_sqrt]
    exact Real.sqrt_lt' hL |>.mpr hsq
  · rintro ⟨hLgt, _⟩
    rw [hprod_sqrt] at hLgt
    have hsq : (2 * E_min / lam_sys) * (hbar * G / c ^ 3) < L ^ 2 := by
      have h1 := mul_lt_mul_of_nonneg_of_pos hLgt (le_of_lt hLgt) (Real.sqrt_nonneg _) hL
      rwa [Real.mul_self_sqrt (mul_nonneg ha_nonneg hb_nonneg), ← sq] at h1
    let E_low := E_min * hbar * c / L
    let E_high := lam_sys * c ^ 4 * L / (2 * G)
    have hlt_E : E_low < E_high := by
      dsimp [E_low, E_high]
      rw [div_lt_div_iff₀ hL (by positivity)]
      have hc_ne : c ≠ 0 := ne_of_gt hc
      have hlam_ne : lam_sys ≠ 0 := ne_of_gt hlam
      have hrew : (2 * E_min / lam_sys) * (hbar * G / c ^ 3) =
          (E_min * hbar * c * (2 * G)) / (lam_sys * c ^ 4) := by
        field_simp [hc_ne, hlam_ne]
      rw [hrew, div_lt_iff₀ (by positivity)] at hsq
      nlinarith
    refine ⟨(E_low + E_high) / 2, ?_, ?_⟩
    · have hle : E_low ≤ (E_low + E_high) / 2 := by linarith
      have := mul_le_mul_of_nonneg_right hle (le_of_lt hL)
      dsimp [E_low] at this
      rwa [div_mul_cancel₀ _ (ne_of_gt hL)] at this
    · have hlt : (E_low + E_high) / 2 < E_high := by linarith
      have := mul_lt_mul_of_pos_left hlt (by positivity : 0 < 2 * G)
      dsimp [E_high] at this
      have hG2_ne : 2 * G ≠ 0 := by positivity
      rwa [mul_div_cancel₀ _ hG2_ne] at this

/-- **Master Physical Realization & Exclusivity Theorem for Organizational Integrity `Ω`
(`P-PHIL31-OMEGA-01`)**:
For an autonomous quantum clock-controller-pointer with normalized prepaid coherence/record budget
`β_coh ≥ 0` scaling the certified `RC02` continuum channel (`d_ref0 = 27346 / 10^34`,
`delta0 = 503 / 10^35`), simultaneous non-trapped operational clock persistence AND strictly
positive relational record distinguishability (`0 < β_coh * (d_ref0 - 2 * delta0)`, exceeding
`2.69 × 10⁻³⁰` whenever `1 ≤ β_coh`) hold **if and only if** `L > L_min * l_P` AND `0 < β_coh`. -/
theorem autonomous_clock_pointer_omega_persistence_and_record_iff
    {L E_min hbar c G lam_sys β_coh : ℝ}
    (hL : 0 < L) (hEmin : 0 < E_min) (hhbar : 0 < hbar)
    (hc : 0 < c) (hG : 0 < G) (hlam : 0 < lam_sys) (_hβ : 0 ≤ β_coh) :
    let L_min := Real.sqrt (2 * E_min / lam_sys)
    let l_P := Real.sqrt (hbar * G / c ^ 3)
    let d_bench := (27346 : ℝ) / 10 ^ 34 - 2 * ((503 : ℝ) / 10 ^ 35)
    ((∃ E_tot : ℝ, E_min * hbar * c ≤ E_tot * L ∧ 2 * G * E_tot < lam_sys * c ^ 4 * L) ∧
      0 < β_coh * d_bench) ↔
      (L_min * l_P < L ∧ 0 < β_coh) := by
  intro L_min l_P d_bench
  have hd_pos : 0 < d_bench := by
    dsimp [d_bench]
    norm_num
  have hiff_L := ah01_nontrapped_clock_persistence_iff_above_planck_floor hL hEmin hhbar hc hG hlam
  constructor
  · rintro ⟨hE, hrec⟩
    refine ⟨(hiff_L.mp hE).1, ?_⟩
    exact (mul_pos_iff_of_pos_right hd_pos).mp hrec
  · rintro ⟨hLgt, hβpos⟩
    have hpos_E : ∀ E_tot : ℝ, E_min * hbar * c ≤ E_tot * L → 0 < E_tot := by
      intro E_tot hclock
      exact (mul_pos_iff_of_pos_right hL).mp (lt_of_lt_of_le (by positivity) hclock)
    exact ⟨hiff_L.mpr ⟨hLgt, hpos_E⟩, mul_pos hβpos hd_pos⟩

/-! ## Section 2. Macroscopic Realization Without Double-Counting, Representation Covariance,
Rank-3 `(s, b, bq)` Boundary & Phenomenal/Normative Non-Deduction
(`P-PHIL31-REALIZ-02`: Philosophy v3.1 Ch. 12–13, 15–17, 21, 25) -/

/-- **Unique Macroscopic Quotient Realization (`Ch. 16–17` & `QuotientDescent`)**:
Every surjective coarse-graining `q : X → M` (RG, hydrodynamic, or gravitational macro-map) whose
fibers preserve microscopic interventional responses `F_micro a : X → V` induces a **unique**
macroscopic response law `F_macro a : M → V` satisfying `F_macro a (q x) = F_micro a x`. -/
theorem no_second_force_unique_quotient_realization
    {A X M V : Type*} (q : X → M) (F_micro : A → X → V)
    (hq : Surjective q)
    (hcompat : ∀ a : A, UEOT.V3.Compression.QuotientDescent.FiberCompatible q (F_micro a)) :
    ∀ a : A, ∃! F_macro : M → V, F_macro ∘ q = F_micro a :=
  fun a => UEOT.V3.Compression.QuotientDescent.existsUnique_descend q (F_micro a) hq (hcompat a)

/-- **Causal-Exclusion / Double-Counting Obstruction (`Ch. 16`)**:
If `F_macro ∘ q = F_micro` realizes a microscopic response in a torsion-free additive module (such
as `ℝ` or `ℝⁿ`), adding `F_macro (q x)` *on top of* `F_micro x` as an independent "second force"
equals the actual physical response `F_micro x` **if and only if** `F_micro x = 0` (otherwise it
strictly double-counts `2 • F_micro x ≠ F_micro x`). -/
theorem double_counting_sum_equals_realized_iff_zero
    {X M V : Type*} [AddCommGroup V] [Module ℝ V]
    (q : X → M) (F_micro : X → V) (F_macro : M → V)
    (hreal : ∀ x : X, F_macro (q x) = F_micro x) (x : X) :
    (F_micro x + F_macro (q x) = F_micro x ↔ F_micro x = 0) ∧
      F_micro x + F_macro (q x) = (2 : ℝ) • F_micro x := by
  rw [hreal x]
  refine ⟨?_, (two_smul ℝ (F_micro x)).symm⟩
  constructor
  · intro h
    simpa using add_left_cancel (a := F_micro x) (b := F_micro x) (c := 0) (by simpa using h)
  · intro hz
    simp [hz]

/-- **Representation Covariance Preserves Dynamical Closure & Optimal Control Value (`Ch. 13, 17`)**:
Direct bridge to `UEOT.V3.RepresentationCovariance` establishing that bimeasurable microscopic
coordinate transformations preserve controlled strong lumpability, protocol-indexed predictive
sufficiency, and optimal expected control value. -/
theorem representation_covariance_preserves_closure_and_optimal_value
    {X X' M A E Pol Ω Ω' : Type*} {Y : E → Type*}
    [MeasurableSpace X] [MeasurableSpace X'] [MeasurableSpace M]
    [∀ e, MeasurableSpace (Y e)] [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : A → Kernel X X) (Pbar : A → Kernel M M)
    (Q : ∀ e, Kernel X (Y e)) (Qbar : ∀ e, Kernel M (Y e))
    (f : X → M) (hf : Measurable f) (T : X ≃ᵐ X')
    (law : Pol → Measure Ω) (law' : Pol → Measure Ω')
    (TΩ : Ω ≃ᵐ Ω') (reward : Ω → ℝ) (hlaw : ∀ π, law' π = (law π).map TΩ) :
    (((∀ a, UEOT.V3.DynamicsKernel.StrongLumpability (P a) (Pbar a) f hf) ↔
      ∀ a, UEOT.V3.DynamicsKernel.StrongLumpability
        (UEOT.V3.RepresentationCovariance.transportKernel (P a) T) (Pbar a)
        (UEOT.V3.RepresentationCovariance.transportReadout f T)
        (UEOT.V3.RepresentationCovariance.measurable_transportReadout f hf T)) ∧
    ((∀ e x, Q e x = Qbar e (f x)) ↔
      ∀ e x', UEOT.V3.RepresentationCovariance.transportResponse (Q e) T x' =
        Qbar e (UEOT.V3.RepresentationCovariance.transportReadout f T x'))) ∧
    UEOT.V3.RepresentationCovariance.optimalExpectedValue law' (reward ∘ TΩ.symm) =
      UEOT.V3.RepresentationCovariance.optimalExpectedValue law reward :=
  ⟨UEOT.V3.RepresentationCovariance.p_fac_01_covariance_bundle P Pbar Q Qbar f hf T,
    UEOT.V3.RepresentationCovariance.optimalExpectedValue_transport law law' TΩ reward hlaw⟩

/-- **Scale Quotient Retains Ontological Lineage & Breaks Under Enlarged Intervention Permission
(`Ch. 5, 8, 17` & `RegisterDecisionRepresentationWitnesses`)**:
Two histories (`mergeA`, `mergeB`) whose decision-sufficient control keys merge under `{root0, child1}`
nevertheless retain distinct allocated `Store` lineages at slots `2` and `3`, and enlarging dispatch
permissions to `address 2` strictly separates their birth laws (`0` vs `r` whenever `r ≠ 0`). -/
theorem scale_quotient_retains_lineage_and_breaks_under_enlarged_permission
    (tariff : ℝ≥0) (l0 l1 l2 : Bool) {r : ℚ} (hr : r ≠ 0) :
    let sa := (RegisterJointDecisionExecution.nativeExecute 0 ⟨true, tariff⟩
      RegisterDecisionRepresentationWitnesses.mergeTableA
      RegisterDecisionRepresentationWitnesses.nativeInitial
      ![(true, l0), (false, l1), (true, l2)]).finalWorld.store
    let sb := (RegisterJointDecisionExecution.nativeExecute 0 ⟨true, tariff⟩
      RegisterDecisionRepresentationWitnesses.mergeTableB
      RegisterDecisionRepresentationWitnesses.nativeInitial
      ![(true, l0), (true, l1), (false, l2)]).finalWorld.store
    RegisterPopulationHistorySource.lookup sa 2 = none ∧
    (RegisterPopulationHistorySource.lookup sb 2).map (fun p => p.identity) =
      some [(0, false), (1, l0), (2, l1)] ∧
    (∑ z : RegisterJointDecisionSource.Noise,
      RegisterJointDecisionSource.primitiveWeight (fun _ : Unit => r)
        RegisterDecisionRepresentationWitnesses.mergedWorldA z *
        if (RegisterJointDecisionSource.packedObserve true
          RegisterDecisionRepresentationWitnesses.mergedWorldA.store 2 none z.1).1 then 1 else 0) ≠
    (∑ z : RegisterJointDecisionSource.Noise,
      RegisterJointDecisionSource.primitiveWeight (fun _ : Unit => r)
        RegisterDecisionRepresentationWitnesses.mergedWorldB z *
        if (RegisterJointDecisionSource.packedObserve true
          RegisterDecisionRepresentationWitnesses.mergedWorldB.store 2 none z.1).1 then 1 else 0) := by
  have hrec := RegisterDecisionRepresentationWitnesses.native_merge_keeps_distinct_records tariff l0 l1 l2
  have hdisp := RegisterDecisionRepresentationWitnesses.dispatch2_birth_laws r
  refine ⟨hrec.1, hrec.2.2.1, ?_⟩
  rw [hdisp.1, hdisp.2]
  exact hr.symm

/-- **Philosophy v3.1 Ch. 13 `Π/Φ` Additive Gauge Invariance vs Anchoring**:
Shifting `(Π_val, Φ_val)` by `(+δ, -δ)` leaves every policy total score and `UEOT.V3.Agency.feasibleValue`
identically invariant across every feasible set `S`, proving that aggregate choice rankings alone
cannot uniquely decompose `Π` from `Φ` without independent channel anchors. -/
theorem ch13_pi_phi_additive_gauge_invariance
    {P : Type*} (piVal phiVal delta : P → ℝ) (S : Set P) :
    (fun p => (piVal p + delta p) + (phiVal p - delta p)) = (fun p => piVal p + phiVal p) ∧
      UEOT.V3.Agency.feasibleValue (fun p => (piVal p + delta p) + (phiVal p - delta p)) S =
        UEOT.V3.Agency.feasibleValue (fun p => piVal p + phiVal p) S := by
  have hfun : (fun p => (piVal p + delta p) + (phiVal p - delta p)) =
      (fun p => piVal p + phiVal p) := by
    funext p; ring
  exact ⟨hfun, by rw [hfun]⟩

/-- Philosophy v3.1 Ch. 12 / Mathematics v4.2 §23.4 three-observable care response map
`(s, b, q) ↦ (s, b, b * q)`. -/
def sbbqMap (p : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![p 0, p 1, p 1 * p 2]

/-- Exact `3 × 3` Jacobian matrix of `sbbqMap` at `(s, b, q)`. -/
def sbbqJacobianMatrix (b q : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 0, 1, 0; 0, q, b]

/-- **Exact Rank-3 Jacobian Determinant (`Ch. 12` / §23.4)**: `det J_{(s,b,q)} = b`, which is
strictly nonzero (`> 0`) across the entire open regenerative regime `b ∈ (0, 1)`. -/
theorem ch12_sbbq_jacobian_det_eq_b (b q : ℝ) :
    (sbbqJacobianMatrix b q).det = b := by
  simp [sbbqJacobianMatrix, Matrix.det_fin_three]

/-- Explicit inverse-type injectivity of `sbbqJacobianMatrix b q` whenever `b ≠ 0`. -/
theorem sbbqJacobian_toLin_injective {b q : ℝ} (hb : b ≠ 0) :
    Injective (Matrix.toLin' (sbbqJacobianMatrix b q)) := by
  intro u v huv
  have h0 : u 0 = v 0 := by
    have := congrFun huv 0
    simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      sbbqJacobianMatrix] using this
  have h1 : u 1 = v 1 := by
    have := congrFun huv 1
    simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      sbbqJacobianMatrix] using this
  have h2_eq : q * u 1 + b * u 2 = q * v 1 + b * v 2 := by
    have := congrFun huv 2
    simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      sbbqJacobianMatrix] using this
  have h2 : u 2 = v 2 := by
    rw [h1] at h2_eq
    exact mul_left_cancel₀ hb (by linarith)
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- Constructive `ℝ³ → ℝ²` nontrivial kernel lemma: every `ℝ`-linear map `(Fin 3 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)`
annihilates a nonzero vector `v ≠ 0`. -/
theorem linear_map_fin3_to_fin2_exists_nonzero_ker
    (L : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) :
    ∃ v : Fin 3 → ℝ, v ≠ 0 ∧ L v = 0 := by
  let e0 : Fin 3 → ℝ := ![1, 0, 0]
  let e1 : Fin 3 → ℝ := ![0, 1, 0]
  let e2 : Fin 3 → ℝ := ![0, 0, 1]
  have hexpand : ∀ x y z : ℝ, (![x, y, z] : Fin 3 → ℝ) = x • e0 + y • e1 + z • e2 := by
    intro x y z
    ext i
    fin_cases i <;> simp [e0, e1, e2]
  let a0 := L e0 0; let c0 := L e0 1
  let a1 := L e1 0; let c1 := L e1 1
  let a2 := L e2 0; let c2 := L e2 1
  by_cases he0 : a0 = 0 ∧ c0 = 0
  · refine ⟨e0, ?_, ?_⟩
    · intro h; have := congrFun h 0; norm_num [e0] at this
    · ext j; fin_cases j
      · exact he0.1
      · exact he0.2
  · let d01 := a0 * c1 - c0 * a1
    by_cases hd01 : d01 = 0
    · by_cases ha0 : a0 ≠ 0
      · refine ⟨![-a1, a0, 0], ?_, ?_⟩
        · intro h; have := congrFun h 1; simp [ha0] at this
        · rw [hexpand, map_add, map_add, map_smul, map_smul, map_smul]
          ext j; fin_cases j
          · change (-a1) * a0 + a0 * a1 + 0 * a2 = 0; ring
          · change (-a1) * c0 + a0 * c1 + 0 * c2 = 0
            dsimp [d01] at hd01; linarith
      · have ha0_zero : a0 = 0 := Classical.not_not.mp ha0
        have hc0 : c0 ≠ 0 := fun hc => he0 ⟨ha0_zero, hc⟩
        refine ⟨![-c1, c0, 0], ?_, ?_⟩
        · intro h; have := congrFun h 1; simp [hc0] at this
        · rw [hexpand, map_add, map_add, map_smul, map_smul, map_smul]
          ext j; fin_cases j
          · change (-c1) * a0 + c0 * a1 + 0 * a2 = 0
            dsimp [d01] at hd01; linarith
          · change (-c1) * c0 + c0 * c1 + 0 * c2 = 0; ring
    · refine ⟨![a1 * c2 - c1 * a2, c0 * a2 - a0 * c2, d01], ?_, ?_⟩
      · intro h; have := congrFun h 2; simp [hd01] at this
      · rw [hexpand, map_add, map_add, map_smul, map_smul, map_smul]
        ext j; fin_cases j
        · change (a1 * c2 - c1 * a2) * a0 + (c0 * a2 - a0 * c2) * a1 + (a0 * c1 - c0 * a1) * a2 = 0
          ring
        · change (a1 * c2 - c1 * a2) * c0 + (c0 * a2 - a0 * c2) * c1 + (a0 * c1 - c0 * a1) * c2 = 0
          ring

/-- Continuous Fréchet derivative of `sbbqMap` at `p = ![s, b, q]` equals `sbbqJacobianMatrix b q`. -/
theorem ch12_sbbq_hasFDerivAt (p : Fin 3 → ℝ) :
    HasFDerivAt sbbqMap
      ((Matrix.toLin' (sbbqJacobianMatrix (p 1) (p 2))).toContinuousLinearMap) p := by
  let J := (Matrix.toLin' (sbbqJacobianMatrix (p 1) (p 2))).toContinuousLinearMap
  let φ' : Fin 3 → (Fin 3 → ℝ) →L[ℝ] ℝ := fun i =>
    (ContinuousLinearMap.proj (R := ℝ) i).comp J
  have hpi : HasFDerivAt (fun x i => sbbqMap x i) (ContinuousLinearMap.pi φ') p := by
    rw [hasFDerivAt_pi]
    intro i
    have h0 : HasFDerivAt (fun x : Fin 3 → ℝ => x 0)
        (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 3)) p :=
      hasFDerivAt_apply (0 : Fin 3) p
    have h1 : HasFDerivAt (fun x : Fin 3 → ℝ => x 1)
        (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 3)) p :=
      hasFDerivAt_apply (1 : Fin 3) p
    have h2 : HasFDerivAt (fun x : Fin 3 → ℝ => x 2)
        (ContinuousLinearMap.proj (R := ℝ) (2 : Fin 3)) p :=
      hasFDerivAt_apply (2 : Fin 3) p
    fin_cases i
    · refine h0.congr_of_eventuallyEq (Eventually.of_forall fun x => rfl) |>.congr_fderiv ?_
      ext v
      simp [φ', J, Matrix.toLin'_apply, dotProduct, Fin.sum_univ_three, sbbqJacobianMatrix]
    · refine h1.congr_of_eventuallyEq (Eventually.of_forall fun x => rfl) |>.congr_fderiv ?_
      ext v
      simp [φ', J, Matrix.toLin'_apply, dotProduct, Fin.sum_univ_three, sbbqJacobianMatrix]
    · have hmul := h1.mul h2
      refine hmul.congr_of_eventuallyEq (Eventually.of_forall fun x => rfl) |>.congr_fderiv ?_
      ext v
      simp [φ', J, Matrix.toLin'_apply, dotProduct, Fin.sum_univ_three, sbbqJacobianMatrix]
      ring
  have hJ : ContinuousLinearMap.pi φ' = J := by
    ext v i
    rfl
  rwa [hJ] at hpi

/-- **Philosophy v3.1 Ch. 12 No-Smooth-2D-`Π/Φ`-Bottleneck Theorem**:
At any point `p₀ = (s, b, q)` with `b ≠ 0` (in particular across the open domain `b ∈ (0, 1)`),
there exist **no** maps `g : (Fin 3 → ℝ) → (Fin 2 → ℝ)` and `h : (Fin 2 → ℝ) → (Fin 3 → ℝ)`
differentiable at `p₀` and `g p₀` that factor `sbbqMap` on any neighborhood of `p₀` (`h ∘ g =ᶠ[𝓝 p₀] sbbqMap`). -/
theorem ch12_no_differentiable_two_dim_piphi_bottleneck
    (p₀ : Fin 3 → ℝ) (hb : p₀ 1 ≠ 0)
    (g : (Fin 3 → ℝ) → (Fin 2 → ℝ)) (h : (Fin 2 → ℝ) → (Fin 3 → ℝ))
    (hg : DifferentiableAt ℝ g p₀) (hh : DifferentiableAt ℝ h (g p₀)) :
    ¬ ((h ∘ g) =ᶠ[𝓝 p₀] sbbqMap) := by
  intro heq
  have hcomp_deriv : HasFDerivAt (h ∘ g) ((fderiv ℝ h (g p₀)).comp (fderiv ℝ g p₀)) p₀ :=
    hh.hasFDerivAt.comp p₀ hg.hasFDerivAt
  have hsbbq_deriv := ch12_sbbq_hasFDerivAt p₀
  have hcomp_deriv' : HasFDerivAt sbbqMap ((fderiv ℝ h (g p₀)).comp (fderiv ℝ g p₀)) p₀ :=
    hcomp_deriv.congr_of_eventuallyEq heq.symm
  have hlin_eq := hcomp_deriv'.unique hsbbq_deriv
  obtain ⟨v, hv_ne, hv_ker⟩ :=
    linear_map_fin3_to_fin2_exists_nonzero_ker (fderiv ℝ g p₀).toLinearMap
  have hv_ker' : fderiv ℝ g p₀ v = 0 := hv_ker
  have hJv_zero : Matrix.toLin' (sbbqJacobianMatrix (p₀ 1) (p₀ 2)) v = 0 := by
    have := DFunLike.congr_fun hlin_eq.symm v
    simpa [ContinuousLinearMap.comp_apply, hv_ker'] using this
  have hinj := sbbqJacobian_toLin_injective (q := p₀ 2) hb
  exact hv_ne (hinj (by simpa using hJv_zero))

/-- Finite-horizon trajectory and external behavioral report trace of a physical-functional machine. -/
def functionalReportTrace
    {X A Obs : Type*} (step : X → A → X) (report : X → Obs) :
    ∀ n : ℕ, X → (Fin n → A) → List Obs
  | 0, x, _ => [report x]
  | n + 1, x, as =>
      report x :: functionalReportTrace step report n (step x (as 0)) (fun i => as i.succ)

/-- Paired physical-functional machine plus phenomenal assignment (`Philosophy v3.1 Ch. 21`). -/
structure PsychophysicalWorld (X A Obs : Type*) where
  step : X → A → X
  report : X → Obs
  quale : X → Bool

/-- Complete physical-functional observable projection erasing phenomenal labels. -/
def PsychophysicalWorld.physProj {X A Obs : Type*}
    (W : PsychophysicalWorld X A Obs) : (X → A → X) × (X → Obs) :=
  (W.step, W.report)

/-- **Philosophy v3.1 Ch. 21 Symmetric Model-Theoretic Non-Deduction of Phenomenal Experience**:
For any physical-functional machine `(step, report)` on nonempty `X`:
1. There exist two worlds `W₀, W₁` with identical physical transitions `physProj W₀ = physProj W₁`
   and identical external behavioral report traces across every horizon `n` and action sequence `as`,
   yet opposite phenomenal assignments (`quale = false` vs `quale = true`);
2. Consequently, **no** purely physical-functional predicate `T_phys` satisfied by `(step, report)`
   can logically entail either universal phenomenal presence OR universal phenomenal absence across
   models (`Ch. 21`: physical functionalism neither deduces phenomenal feel nor proves its impossibility
   without an independent psychophysical bridge). -/
theorem ch21_phenomenal_non_deduction_from_functional_dynamics
    {X A Obs : Type*} [Nonempty X] (step : X → A → X) (report : X → Obs) :
    (∃ W₀ W₁ : PsychophysicalWorld X A Obs,
      W₀.physProj = (step, report) ∧
      W₁.physProj = (step, report) ∧
      W₀.quale ≠ W₁.quale ∧
      ∀ (n : ℕ) (x : X) (as : Fin n → A),
        functionalReportTrace W₀.step W₀.report n x as =
          functionalReportTrace W₁.step W₁.report n x as) ∧
    ∀ (T_phys : ((X → A → X) × (X → Obs)) → Prop),
      T_phys (step, report) →
        ¬ (∀ W : PsychophysicalWorld X A Obs, T_phys W.physProj → ∀ x : X, W.quale x = true) ∧
        ¬ (∀ W : PsychophysicalWorld X A Obs, T_phys W.physProj → ∀ x : X, W.quale x = false) := by
  let W₀ : PsychophysicalWorld X A Obs := ⟨step, report, fun _ => false⟩
  let W₁ : PsychophysicalWorld X A Obs := ⟨step, report, fun _ => true⟩
  let x₀ : X := Classical.arbitrary X
  refine ⟨⟨W₀, W₁, rfl, rfl, ?_, fun _ _ _ => rfl⟩, ?_⟩
  · intro h
    exact Bool.false_ne_true (congrFun h x₀)
  · intro T_phys hT
    refine ⟨fun hall => Bool.false_ne_true (hall W₀ hT x₀),
      fun hall => Bool.false_ne_true (hall W₁ hT x₀).symm⟩

/-- Explicit two-participant institutional/regenerative mechanism comparing aggregate growth against
each participant's substantive capability floor (`Philosophy v3.1 Ch. 25`). -/
structure TwoAgentSocialMechanism where
  cap : Fin 2 → ℝ
  growthFactor : ℝ

/-- Minimum capability across both interdependent participants (`Sen–Nussbaum / Scanlon` floor). -/
def TwoAgentSocialMechanism.minCapability (M : TwoAgentSocialMechanism) : ℝ :=
  min (M.cap 0) (M.cap 1)

/-- **Philosophy v3.1 Ch. 25 Normative Non-Reduction & `Agency` Capability Monotonicity**:
1. Explicit extractive vs cooperative two-agent mechanisms prove that strictly higher aggregate
   growth (`3/2 > 5/4 > 1`) reverses the substantive capability / non-domination ordering
   (`minCapability M_dom = 0 < 5/4 = minCapability M_coop`), blocking Hume/Street evolutionary
   deduction of moral legitimacy from growth rates alone;
2. Expanding feasible capabilities (`Extends D₁ D₂`) monotonically preserves or improves attainable
   agency value (`UEOT.V3.Agency.extension_optimalValue_mono`). -/
theorem ch25_normative_independence_and_capability_monotonicity
    {P : Type*} {D₁ D₂ : UEOT.V3.Agency.FeasibleDecision P}
    (hExt : UEOT.V3.Agency.Extends D₁ D₂) :
    (∃ M_dom M_coop : TwoAgentSocialMechanism,
      1 < M_coop.growthFactor ∧
      M_coop.growthFactor < M_dom.growthFactor ∧
      M_dom.minCapability = 0 ∧
      0 < M_coop.minCapability ∧
      M_dom.minCapability < M_coop.minCapability) ∧
    UEOT.V3.Agency.optimalValue D₁ ≤ UEOT.V3.Agency.optimalValue D₂ := by
  let M_dom : TwoAgentSocialMechanism := ⟨![3, 0], 3 / 2⟩
  let M_coop : TwoAgentSocialMechanism := ⟨![5 / 4, 5 / 4], 5 / 4⟩
  refine ⟨⟨M_dom, M_coop, by norm_num, by norm_num, ?_, ?_, ?_⟩,
    UEOT.V3.Agency.extension_optimalValue_mono hExt⟩
  · simp [TwoAgentSocialMechanism.minCapability, M_dom]
  · simp [TwoAgentSocialMechanism.minCapability, M_coop]
  · simp [TwoAgentSocialMechanism.minCapability, M_dom, M_coop]

/-! ## Section 3. Formalized Ch. 28 Lakatosian Research Programme Contract & Non-Immunity
(`P-PHIL31-LAKATOS-03`: Philosophy v3.1 Ch. 28–30) -/

/-- Epistemic status tags separating pure-kernel conditional proofs from unverified empirical
universality and open physical unification (`Philosophy v3.1 Ch. 28 & 30`). -/
inductive EpistemicStatus
  | provedConditional
  | calibratedModel
  | unverifiedEmpirical
  | openFrontier
  deriving DecidableEq, Repr

/-- Formal Lakatosian Research Programme `(domain, hardCore, protectiveBelt, admissibleParams)`. -/
structure LakatosProgramme (ObsData Param : Type*) where
  domain : Set ObsData
  hardCore : ObsData → Prop
  protectiveBelt : Param → ObsData → Prop
  admissibleParams : Set Param

/-- Joint empirical prediction of parameter `θ` on datum `d`. -/
def LakatosProgramme.Predicts {ObsData Param : Type*}
    (LP : LakatosProgramme ObsData Param) (θ : Param) (d : ObsData) : Prop :=
  LP.hardCore d ∧ LP.protectiveBelt θ d

/-- Protective-belt refutation witness within the pre-registered domain `LP.domain`. -/
def LakatosProgramme.BeltRefutationWitness {ObsData Param : Type*}
    (LP : LakatosProgramme ObsData Param) (θ : Param) (d : ObsData) : Prop :=
  d ∈ LP.domain ∧ ¬ LP.protectiveBelt θ d

/-- Uniform programme refutation witness falsifying `Predicts θ` across all `θ ∈ admissibleParams`
within the pre-registered domain `LP.domain`. -/
def LakatosProgramme.UniformRefutationWitness {ObsData Param : Type*}
    (LP : LakatosProgramme ObsData Param) (d : ObsData) : Prop :=
  d ∈ LP.domain ∧ ∀ θ ∈ LP.admissibleParams, ¬ LP.Predicts θ d

/-- Post-hoc domain excision that deletes refuting observations rather than revising mechanisms. -/
def adHocDomainShrink {ObsData Param : Type*}
    (LP : LakatosProgramme ObsData Param) (θ : Param) : LakatosProgramme ObsData Param :=
  { LP with domain := {d ∈ LP.domain | LP.Predicts θ d} }

/-- **Degenerating Domain-Shrink Theorem (`Ch. 28`)**: Post-hoc excision of refuting observations
trivially eliminates refutations on the shrunk domain, yet strictly shrinks empirical scope (`⊂`)
whenever any refutation witness exists and adds zero novel predictions outside the shrunk domain. -/
theorem ad_hoc_domain_excision_is_degenerating_shift
    {ObsData Param : Type*} (LP : LakatosProgramme ObsData Param) (θ : Param)
    {d_ref : ObsData} (hd : d_ref ∈ LP.domain) (href : ¬ LP.Predicts θ d_ref) :
    (∀ d ∈ (adHocDomainShrink LP θ).domain, (adHocDomainShrink LP θ).Predicts θ d) ∧
      (adHocDomainShrink LP θ).domain ⊂ LP.domain := by
  refine ⟨fun d hd' => hd'.2, ?_⟩
  rw [ssubset_iff_subset_not_subset]
  refine ⟨fun d hd' => hd'.1, ?_⟩
  intro hsub
  exact href (hsub hd).2

/-- Concrete four-observable empirical tuple `(rankObs, delta123, dphiGrav, wBMV)` for UEOT's
three-volume research programme (`Ch. 12` response rank, Angle 3 1-loop `Δ₁₂₃` desert defect,
`AH08` mesoscopic gravimetric phase `Δφ_grav`, and Angle 4 non-LOCC BMV witness `W_BMV`). -/
structure UEOTTestObs where
  rankObs : ℕ
  delta123 : ℝ
  dphiGrav : ℝ
  wBMV : ℝ

/-- Auxiliary protective-belt switches `(allowRank3, hasIntermediateThreshold)`. -/
structure UEOTBeltParam where
  allowRank3 : Bool
  hasIntermediateThreshold : Bool
  deriving DecidableEq

/-- Pre-registered Ch. 28 Lakatosian contract for UEOT's unified physics bridge. -/
def ueotLakatosContract : LakatosProgramme UEOTTestObs UEOTBeltParam where
  domain := {d | 1 ≤ d.rankObs ∧ 0 ≤ d.dphiGrav}
  hardCore := fun d => (31 / 100 : ℝ) < d.dphiGrav ∧ d.dphiGrav < (32 / 100 : ℝ) ∧ d.wBMV < 0
  protectiveBelt := fun θ d =>
    (if θ.allowRank3 then d.rankObs ≤ 3 else d.rankObs ≤ 2) ∧
      (if θ.hasIntermediateThreshold then True else d.delta123 = 0)
  admissibleParams := Set.univ

/-- **UEOT Lakatosian Non-Vacuity & Strict Non-Immunity Theorem (`P-PHIL31-LAKATOS-03`)**:
Within the fixed pre-registered domain `ueotLakatosContract.domain` (zero post-hoc domain shrinking):
1. **Non-Vacuity**: Explicit viable datum `(3, -37, 0.3164, -0.20)` satisfies `Predicts ⟨true, true⟩`;
2. **Belt Refutation 1**: The same datum strictly refutes naive 2D `Π/Φ` bottleneck `⟨false, true⟩`;
3. **Belt Refutation 2**: The same datum strictly refutes single-step desert unification `⟨true, false⟩`;
4. **Uniform Hard-Core Refutation**: Observing null gravimetric phase or separable LOCC statistics
   `(3, -37, 0, 1/10)` lies inside `domain` and uniformly refutes `Predicts θ` for **all** `θ`. -/
theorem ueot_lakatos_nonvacuous_and_non_immune :
    let d_viable : UEOTTestObs := ⟨3, -37, 3164 / 10000, -1 / 5⟩
    let d_null_locc : UEOTTestObs := ⟨3, -37, 0, 1 / 10⟩
    (d_viable ∈ ueotLakatosContract.domain ∧
      ueotLakatosContract.Predicts ⟨true, true⟩ d_viable) ∧
    ueotLakatosContract.BeltRefutationWitness ⟨false, true⟩ d_viable ∧
    ueotLakatosContract.BeltRefutationWitness ⟨true, false⟩ d_viable ∧
    ueotLakatosContract.UniformRefutationWitness d_null_locc := by
  intro d_viable d_null_locc
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨⟨by decide, by norm_num⟩, ⟨⟨by norm_num, by norm_num, by norm_num⟩, ?_⟩⟩
    simp [ueotLakatosContract, d_viable]
  · refine ⟨⟨by decide, by norm_num⟩, ?_⟩
    simp [ueotLakatosContract, d_viable]
  · refine ⟨⟨by decide, by norm_num⟩, ?_⟩
    simp [ueotLakatosContract, d_viable]
  · refine ⟨⟨by decide, by norm_num⟩, ?_⟩
    intro θ _ hpred
    have h0 : (31 / 100 : ℝ) < 0 := hpred.1.1
    linarith

/-- **Epistemic Honesty Under Finite Samples (`Ch. 8, 28, 30` & `M-40.5`)**:
For any nonzero latent failure probability `p_fail ∈ (0, 1)` and any finite test sample count `N`,
the probability `(1 - p_fail)^N` of observing zero failures across all `N` trials remains strictly
positive (`> 0`), proving why finite model/synthetic passes cannot promote `unverifiedEmpirical` or
`openFrontier` (`"physical_unification": "OPEN"`) to universal empirical confirmation. -/
theorem finite_zero_failures_preserve_unverified_open_honesty
    {p_fail : ℝ} (_hp0 : 0 < p_fail) (hp1 : p_fail < 1) (N : ℕ) :
    0 < (1 - p_fail) ^ N ∧
      EpistemicStatus.provedConditional ≠ EpistemicStatus.unverifiedEmpirical ∧
      EpistemicStatus.calibratedModel ≠ EpistemicStatus.openFrontier := by
  have h1m : 0 < 1 - p_fail := by linarith
  exact ⟨pow_pos h1m N, by decide, by decide⟩

end UEOTPhysicsUnification.PhilosophyV31OmegaObserverBridge
