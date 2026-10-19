import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FinitePMFProjection
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteHorizonPathAdapter
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CalibratedRiskRows

/-!
# The actual microscopic path projected under one observable-history policy

Approximate row agreement does not make the coarse process Markov.  The
actual coarse history kernel below is built from the microscopic path law
by finite conditional disintegration, and its causal law is proved equal
to the actual path pushforward before applying frozen P-DYN-03.

The calibrated representative endpoints use an explicit section of the chosen
partition and the actual source rows. Calibration coverage probabilities and
hidden microscopic failure events require separate application interfaces.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open MeasureTheory UEOT.V3.PathError UEOT.V3.TotalVariation
open scoped BigOperators Classical

noncomputable section

universe u

/-- Project the initial record and every appended record. -/
def riskHistoryMap
    {X Y Z W : Type u} (f : X → Y) (g : Z → W) :
    ∀ n, CausalHistory X Z n → CausalHistory Y W n
  | 0, h => f h
  | n + 1, h => (riskHistoryMap f g n h.1, g h.2)

/-- Actual conditional next-record law on the projected history. -/
def riskProjectedKernel
    {X Y Z W : Type u}
    (p₀ : PMF X) (K : ∀ n, CausalHistory X Z n → PMF Z)
    (f : X → Y) (g : Z → W)
    (L : ∀ n, CausalHistory Y W n → PMF W) :
    ∀ n, CausalHistory Y W n → PMF W :=
  fun n => riskConditionedRow (causalLaw p₀ K n)
    (riskHistoryMap f g n) (fun h => (K n h).map g) (L n)

/-- The history disintegration is the true microscopic pushforward, at every horizon. -/
theorem risk_causalLaw_map
    {X Y Z W : Type u}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype W]
    (p₀ : PMF X) (K : ∀ n, CausalHistory X Z n → PMF Z)
    (f : X → Y) (g : Z → W)
    (L : ∀ n, CausalHistory Y W n → PMF W) (n : ℕ) :
    (causalLaw p₀ K n).map (riskHistoryMap f g n) =
      causalLaw (p₀.map f) (riskProjectedKernel p₀ K f g L) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change
      (pmfExtend (causalLaw p₀ K n) (K n)).map
          (fun hz => (riskHistoryMap f g n hz.1, g hz.2)) =
        pmfExtend (causalLaw (p₀.map f) (riskProjectedKernel p₀ K f g L) n)
          (riskProjectedKernel p₀ K f g L n)
    calc
      (pmfExtend (causalLaw p₀ K n) (K n)).map
          (fun hz => (riskHistoryMap f g n hz.1, g hz.2)) =
        ((pmfExtend (causalLaw p₀ K n) (K n)).map
          (fun hz => (hz.1, g hz.2))).map
            (fun hz => (riskHistoryMap f g n hz.1, hz.2)) := by
              rw [PMF.map_comp]
              rfl
      _ = (pmfExtend (causalLaw p₀ K n) (fun h => (K n h).map g)).map
          (fun hz => (riskHistoryMap f g n hz.1, hz.2)) := by
            rw [risk_map_extend_right]
      _ = pmfExtend ((causalLaw p₀ K n).map (riskHistoryMap f g n))
          (riskConditionedRow (causalLaw p₀ K n) (riskHistoryMap f g n)
            (fun h => (K n h).map g) (L n)) :=
            risk_map_extend_eq _ _ _ _
      _ = _ := by
        rw [ih]
        rfl

/-- Uniform projected microscopic rows control every constructed coarse-history row,
including null histories, where the constructed row is exactly the reference. -/
theorem risk_projectedKernel_tv_le
    {X Y Z W : Type u}
    [Fintype X] [Fintype Z] [Fintype W]
    [MeasurableSpace W] [MeasurableSingletonClass W]
    (p₀ : PMF X) (K : ∀ n, CausalHistory X Z n → PMF Z)
    (f : X → Y) (g : Z → W)
    (L : ∀ n, CausalHistory Y W n → PMF W)
    (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hrow : ∀ h,
      tvDist ((K n h).map g).toMeasure
        (L n (riskHistoryMap f g n h)).toMeasure ≤ ε)
    (h : CausalHistory Y W n) :
    tvDist (riskProjectedKernel p₀ K f g L n h).toMeasure (L n h).toMeasure ≤ ε :=
  risk_conditionedRow_tv_le _ _ _ _ ε hε hrow h

/-- Finite P-DYN-03 bound for the actual microscopic projected path, with no
postulated Markov quotient and no assumptions after the chosen horizon. -/
theorem risk_projected_causalLaw_finite_error
    {X Y Z W : Type u}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype W]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [MeasurableSpace W] [MeasurableSingletonClass W]
    (p₀ : PMF X) (K : ∀ n, CausalHistory X Z n → PMF Z)
    (f : X → Y) (g : Z → W)
    (L : ∀ n, CausalHistory Y W n → PMF W)
    (ε : ℕ → ℝ) (T : ℕ)
    (hε0 : ∀ n, n < T → 0 ≤ ε n)
    (hε1 : ∀ n, n < T → ε n ≤ 1)
    (hrow : ∀ n, n < T → ∀ h,
      tvDist ((K n h).map g).toMeasure
        (L n (riskHistoryMap f g n h)).toMeasure ≤ ε n) :
    tvDist ((causalLaw p₀ K T).map (riskHistoryMap f g T)).toMeasure
        (causalLaw (p₀.map f) L T).toMeasure
        ≤ 1 - (∏ i ∈ Finset.range T, (1 - ε i)) ∧
      1 - (∏ i ∈ Finset.range T, (1 - ε i))
        ≤ ∑ i ∈ Finset.range T, ε i := by
  rw [risk_causalLaw_map p₀ K f g L T]
  exact finite_horizon_path_error (p₀.map f) (riskProjectedKernel p₀ K f g L) L
    ε T hε0 hε1 (by
      intro n hn h
      exact risk_projectedKernel_tv_le p₀ K f g L n (ε n) (hε0 n hn)
        (hrow n hn) h)

/-- Source event-supremum TV transfers a registered event risk, clipped at one. -/
theorem risk_event_transfer
    {S : Type u} [MeasurableSpace S]
    (p q : PMF S) (b : ℝ)
    (hTV : tvDist p.toMeasure q.toMeasure ≤ b)
    (F : Set S) (hF : MeasurableSet F) :
    p.toMeasure.real F ≤ min 1 (q.toMeasure.real F + b) := by
  apply le_min measureReal_le_one
  have hgap := (le_abs_self (p.toMeasure.real F - q.toMeasure.real F)).trans
    ((tvEvent_le p.toMeasure q.toMeasure F hF).trans hTV)
  linarith

/-- The current state in an action/state record history. -/
def riskLastState {X A : Type u} : ∀ n, CausalHistory X (A × X) n → X
  | 0, h => h
  | _ + 1, h => h.2.2

@[simp] theorem risk_last_project
    {X Y A : Type u} (q : X → Y) (n : ℕ)
    (h : CausalHistory X (A × X) n) :
    riskLastState n
        (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) n h) =
      q (riskLastState n h) := by
  cases n <;> rfl

/-- The microscopic controller is exactly the common observable-history policy. -/
def riskMicroControlKernel
    {X Y A : Type u} (q : X → Y) (P : ℕ → X → A → PMF X)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A) :
    ∀ n, CausalHistory X (A × X) n → PMF (A × X) :=
  fun n h => pmfExtend
    (π n (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) n h))
    (P n (riskLastState n h))

/-- The reference macro process uses the very same conditional action PMF. -/
def riskMacroControlKernel
    {Y A : Type u} (Q : ℕ → Y → A → PMF Y)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A) :
    ∀ n, CausalHistory Y (A × Y) n → PMF (A × Y) :=
  fun n h => pmfExtend (π n h) (Q n (riskLastState n h))

/-- Applying common randomized action weights preserves a uniform transition-row TV bound. -/
theorem risk_tv_extend_same_initial
    {A Y : Type u} [Fintype A] [Fintype Y]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (p : PMF A) (K L : A → PMF Y) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hrow : ∀ a, tvDist (K a).toMeasure (L a).toMeasure ≤ ε) :
    tvDist (pmfExtend p K).toMeasure (pmfExtend p L).toMeasure ≤ ε := by
  have hcommon := pmfCommonMass_extend_of_tv p p K L hε0 hε1 hrow
  rw [pmfCommonMass_self, one_mul] at hcommon
  rw [tvDist_eq_one_sub_pmfCommonMass]
  linarith

/-- The actual controlled next-record row satisfies the source error bound. -/
theorem risk_same_policy_row_tv
    {X Y A : Type u} [Fintype X] [Fintype Y] [Fintype A]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (q : X → Y) (P : ℕ → X → A → PMF X) (Q : ℕ → Y → A → PMF Y)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (n : ℕ) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hrow : ∀ x a,
      tvDist ((P n x a).map q).toMeasure (Q n (q x) a).toMeasure ≤ ε)
    (h : CausalHistory X (A × X) n) :
    tvDist
        ((riskMicroControlKernel q P π n h).map
          (fun ax : A × X => (ax.1, q ax.2))).toMeasure
        (riskMacroControlKernel Q π n
          (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) n h)).toMeasure ≤ ε := by
  dsimp only [riskMicroControlKernel, riskMacroControlKernel]
  rw [risk_map_extend_right, risk_last_project]
  exact risk_tv_extend_same_initial _ _ _ ε hε0 hε1
    (fun a => hrow (riskLastState n h) a)

/-- Main actual-source endpoint: the SAME macro-history policy, the SAME projected
initial law, and finite all-action row bounds yield the sharp projected path bound. -/
theorem same_policy_projected_path_error
    {X Y A : Type u} [Fintype X] [Fintype Y] [Fintype A]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p₀ : PMF X) (q : X → Y)
    (P : ℕ → X → A → PMF X) (Q : ℕ → Y → A → PMF Y)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (ε : ℕ → ℝ) (T : ℕ)
    (hε0 : ∀ n, n < T → 0 ≤ ε n)
    (hε1 : ∀ n, n < T → ε n ≤ 1)
    (hrow : ∀ n, n < T → ∀ x a,
      tvDist ((P n x a).map q).toMeasure (Q n (q x) a).toMeasure ≤ ε n) :
    tvDist
        ((causalLaw p₀ (riskMicroControlKernel q P π) T).map
          (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) T)).toMeasure
        (causalLaw (p₀.map q) (riskMacroControlKernel Q π) T).toMeasure
        ≤ 1 - (∏ i ∈ Finset.range T, (1 - ε i)) ∧
      1 - (∏ i ∈ Finset.range T, (1 - ε i))
        ≤ ∑ i ∈ Finset.range T, ε i := by
  exact risk_projected_causalLaw_finite_error p₀ (riskMicroControlKernel q P π)
    q (fun ax : A × X => (ax.1, q ax.2)) (riskMacroControlKernel Q π)
    ε T hε0 hε1 (by
      intro n hn h
      exact risk_same_policy_row_tv q P Q π n (ε n) (hε0 n hn) (hε1 n hn)
        (hrow n hn) h)

/-- Registered finite-horizon failure risk for the actual projected microscopic path. -/
theorem same_policy_projected_failure_risk
    {X Y A : Type u} [Fintype X] [Fintype Y] [Fintype A]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p₀ : PMF X) (q : X → Y)
    (P : ℕ → X → A → PMF X) (Q : ℕ → Y → A → PMF Y)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (ε : ℕ → ℝ) (T : ℕ)
    (hε0 : ∀ n, n < T → 0 ≤ ε n)
    (hε1 : ∀ n, n < T → ε n ≤ 1)
    (hrow : ∀ n, n < T → ∀ x a,
      tvDist ((P n x a).map q).toMeasure (Q n (q x) a).toMeasure ≤ ε n)
    (F : Set (CausalHistory Y (A × Y) T)) (hF : MeasurableSet F) :
    (((causalLaw p₀ (riskMicroControlKernel q P π) T).map
        (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) T)).toMeasure).real F
      ≤ min 1
        ((causalLaw (p₀.map q) (riskMacroControlKernel Q π) T).toMeasure.real F +
          (1 - (∏ i ∈ Finset.range T, (1 - ε i)))) := by
  exact risk_event_transfer _ _ _
    (same_policy_projected_path_error p₀ q P Q π ε T hε0 hε1 hrow).1 F hF

/-- The finite PMF half-L1 class-coordinate budget, capped at one. -/
def riskCoordinateBudget {Y : Type u} [Fintype Y]
    (Γ : ℕ → Y → ℝ) (n : ℕ) : ℝ :=
  min 1 ((1 / 2 : ℝ) * ∑ y, Γ n y)

/-- True chosen-quotient PMF coordinate errors feed the actual-source path theorem.
The class type is the caller's Y, not an implicitly substituted predictive quotient. -/
theorem same_policy_coordinate_path_error
    {X Y A : Type u} [Fintype X] [Fintype Y] [Fintype A]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p₀ : PMF X) (q : X → Y)
    (P : ℕ → X → A → PMF X) (Q : ℕ → Y → A → PMF Y)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (Γ : ℕ → Y → ℝ) (T : ℕ)
    (hΓ : ∀ n, n < T → ∀ y, 0 ≤ Γ n y)
    (hcoord : ∀ n, n < T → ∀ x a y,
      |(((P n x a).map q) y).toReal - (Q n (q x) a y).toReal| ≤ Γ n y) :
    tvDist
        ((causalLaw p₀ (riskMicroControlKernel q P π) T).map
          (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) T)).toMeasure
        (causalLaw (p₀.map q) (riskMacroControlKernel Q π) T).toMeasure
        ≤ 1 - (∏ i ∈ Finset.range T, (1 - riskCoordinateBudget Γ i)) ∧
      1 - (∏ i ∈ Finset.range T, (1 - riskCoordinateBudget Γ i))
        ≤ ∑ i ∈ Finset.range T, riskCoordinateBudget Γ i := by
  apply same_policy_projected_path_error p₀ q P Q π (riskCoordinateBudget Γ) T
  · intro n hn
    unfold riskCoordinateBudget
    exact le_min zero_le_one
      (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun y _ => hΓ n hn y)))
  · intro n _
    exact min_le_left _ _
  · intro n hn x a
    exact pmf_tv_le_clipped_coordinate_budget _ _ (Γ n) (hcoord n hn x a)

/-- Coordinate-calibrated finite failure risk of the actual microscopic pushforward. -/
theorem same_policy_coordinate_failure_risk
    {X Y A : Type u} [Fintype X] [Fintype Y] [Fintype A]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p₀ : PMF X) (q : X → Y)
    (P : ℕ → X → A → PMF X) (Q : ℕ → Y → A → PMF Y)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (Γ : ℕ → Y → ℝ) (T : ℕ)
    (hΓ : ∀ n, n < T → ∀ y, 0 ≤ Γ n y)
    (hcoord : ∀ n, n < T → ∀ x a y,
      |(((P n x a).map q) y).toReal - (Q n (q x) a y).toReal| ≤ Γ n y)
    (F : Set (CausalHistory Y (A × Y) T)) (hF : MeasurableSet F) :
    (((causalLaw p₀ (riskMicroControlKernel q P π) T).map
        (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) T)).toMeasure).real F
      ≤ min 1
        ((causalLaw (p₀.map q) (riskMacroControlKernel Q π) T).toMeasure.real F +
          (1 - (∏ i ∈ Finset.range T, (1 - riskCoordinateBudget Γ i)))) := by
  exact risk_event_transfer _ _ _
    (same_policy_coordinate_path_error p₀ q P Q π Γ T hΓ hcoord).1 F hF

open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
open UEOT.V3.Compression.RecursiveSufficientState

/-- The reference row is the projected true row at the specified representative. -/
def riskRepresentativeKernel {X Y A : Type u} (q : X → Y) (r : Y → X)
    (P : ℕ → X → A → PMF X) : ℕ → Y → A → PMF Y :=
  fun n y a => (P n (r y) a).map q

section CalibratedRepresentative

variable {X A R O I : Type u} [Fintype X] [Fintype A] [Fintype I]
variable [MeasurableSpace A] [MeasurableSingletonClass A]
variable (M : ℕ → UEOT.V3.FiniteStablePartition.Model X A R O) (S : Setoid X)
variable (r : ReachableState (setoidRepresentation S) → X)
variable (hr : ∀ y, toReachable (setoidRepresentation S) (r y) = y)
variable (p₀ : PMF X)
variable (π : ∀ n, CausalHistory (ReachableState (setoidRepresentation S))
  (A × ReachableState (setoidRepresentation S)) n → PMF A)
variable (test : ℕ → I → X → ℝ) (coeff : ℕ → X → I → ℝ)
variable (measured : ℕ → A → X → I → ℝ) (delta eta rho kappa : ℕ → ℝ) (T : ℕ)
variable (hspan : ∀ n, n < T →
  ApproxSpansPartitionIndicators S (test n) (coeff n) (delta n))
variable (hcal : ∀ n, n < T → ∀ a x i,
  |transitionTestExpectation (M n) (test n i) a x - measured n a x i| ≤ rho n)
variable (hmeasured : ∀ n, n < T → ∀ ⦃x y⦄, S.r x y → ∀ a i,
  |measured n a x i - measured n a y i| ≤ eta n)
variable (hdelta : ∀ n, n < T → 0 ≤ delta n)
variable (heta : ∀ n, n < T → 0 ≤ eta n)
variable (hrho : ∀ n, n < T → 0 ≤ rho n)
variable (hkappa : ∀ n, n < T → 0 ≤ kappa n)
variable (hcondition : ∀ n, n < T → ∀ z, ∑ i, |coeff n z i| ≤ kappa n)

local notation "qS" => (toReachable (setoidRepresentation S))
local notation "microP" => (fun n x a => finiteKernelRowPMF (modelAsFiniteKernel (M n)) x a)
local notation "macroQ" => (riskRepresentativeKernel qS r microP)
local notation "rowBudget" => (fun n => min 1 ((1 / 2 : ℝ) *
  ((Fintype.card (ReachableState (setoidRepresentation S)) : ℝ) *
    (2 * delta n + (eta n + 2 * rho n) * kappa n))))

include hr hspan hcal hmeasured hdelta heta hrho hkappa hcondition in
/-- Calibrated experiments and approximate indicators control the actual source
against the explicitly chosen representative model, under their common policy. -/
theorem calibrated_representative_path_error :
    letI : Fintype (ReachableState (setoidRepresentation S)) := Fintype.ofFinite _
    letI : MeasurableSpace (ReachableState (setoidRepresentation S)) := ⊤
    tvDist
      ((causalLaw p₀ (riskMicroControlKernel qS microP π) T).map
        (riskHistoryMap qS (fun ax : A × X => (ax.1, qS ax.2)) T)).toMeasure
      (causalLaw (p₀.map qS) (riskMacroControlKernel macroQ π) T).toMeasure
      ≤ 1 - (∏ i ∈ Finset.range T, (1 - rowBudget i)) ∧
    1 - (∏ i ∈ Finset.range T, (1 - rowBudget i))
      ≤ ∑ i ∈ Finset.range T, rowBudget i := by
  classical
  let _ : Fintype (ReachableState (setoidRepresentation S)) := Fintype.ofFinite _
  let _ : MeasurableSpace (ReachableState (setoidRepresentation S)) := ⊤
  apply same_policy_projected_path_error p₀ qS microP macroQ π rowBudget T
  · intro n hn
    have hd := hdelta n hn
    have he := heta n hn
    have hp := hrho n hn
    have hk := hkappa n hn
    apply le_min zero_le_one
    positivity
  · intro n _
    exact min_le_left _ _
  · intro n hn x a
    have hxy : S.r x (r (qS x)) :=
      Quotient.eq.mp ((congrArg Subtype.val (hr (qS x))).symm)
    exact calibrated_observable_partition_tv_budget (M n) S (test n) (coeff n)
      (measured n) (delta n) (eta n) (rho n) (kappa n) (hspan n hn)
      (hcal n hn) (hmeasured n hn) (heta n hn) (hrho n hn)
      (hcondition n hn) hxy a

include hr hspan hcal hmeasured hdelta heta hrho hkappa hcondition in
/-- The same calibrated representative construction transfers any registered
finite projected failure event. Calibration coverage probabilities are external. -/
theorem calibrated_representative_failure_risk
    (F : Set (CausalHistory (ReachableState (setoidRepresentation S))
      (A × ReachableState (setoidRepresentation S)) T)) :
    letI : Fintype (ReachableState (setoidRepresentation S)) := Fintype.ofFinite _
    letI : MeasurableSpace (ReachableState (setoidRepresentation S)) := ⊤
    MeasurableSet F →
    (((causalLaw p₀ (riskMicroControlKernel qS microP π) T).map
      (riskHistoryMap qS (fun ax : A × X => (ax.1, qS ax.2)) T)).toMeasure).real F
      ≤ min 1
        ((causalLaw (p₀.map qS) (riskMacroControlKernel macroQ π) T).toMeasure.real F +
          (1 - (∏ i ∈ Finset.range T, (1 - rowBudget i)))) := by
  classical
  let _ : Fintype (ReachableState (setoidRepresentation S)) := Fintype.ofFinite _
  let _ : MeasurableSpace (ReachableState (setoidRepresentation S)) := ⊤
  intro hF
  exact risk_event_transfer _ _ _
    (calibrated_representative_path_error M S r hr p₀ π test coeff measured
      delta eta rho kappa T hspan hcal hmeasured hdelta heta hrho hkappa hcondition).1 F hF

end CalibratedRepresentative

end

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
