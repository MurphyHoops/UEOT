import UEOTQM.ClassicalSector
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreNonvacuousAllTimesWitness

/-!
# A classical purification boundary on one actual finite Core process

The four-state kernel is the existing Core survivalMicroKernel. Complete
registered observation makes its ACTUAL terminal stable quotient injective.
The same constructed control quotient drives a genuine infinite trajectory;
its first quotient marginal is mixed in the declared full classical simplex.
The classical product interpretation has no pure extension of that marginal.

This instantiates the stated finite control/quotient/viability interfaces only.
It is not a model of all 106 Core propositions with every physical interpretation,
nor a proof that the whole UEOT can never reconstruct quantum theory.
-/

namespace UEOTQM.Classical

open scoped BigOperators _root_.Classical
open MeasureTheory
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

noncomputable section

universe u v w

variable {X : Type u} {Y : Type v} {A : Type w}
  [Fintype X] [Fintype Y]

/-- Core's actual real probability-row construction. -/
def toPMF (p : State X) : PMF X :=
  FiniteProbabilityRow.ofRealRow p.weight p.nonneg p.sum_one

@[simp] theorem toPMF_apply (p : State X) (x : X) :
    toPMF p x = ENNReal.ofReal (p.weight x) := rfl

@[simp] theorem toPMF_apply_toReal (p : State X) (x : X) :
    (toPMF p x).toReal = p.weight x := by
  simp [p.nonneg]

theorem toPMF_dirac (x : X) : toPMF (dirac x) = PMF.pure x := by
  classical
  ext y
  by_cases h : y = x <;> simp [toPMF_apply, PMF.pure_apply, h]

theorem toPMF_pushforward (f : X → Y) (p : State X) :
    toPMF (pushforward f p) = (toPMF p).map f := by
  classical
  ext y
  rw [PMF.map_apply, tsum_fintype]
  simp only [toPMF_apply, pushforward_weight]
  calc
    ENNReal.ofReal (∑ x, if f x = y then p.weight x else 0) =
        ∑ x, ENNReal.ofReal (if f x = y then p.weight x else 0) := by
      exact ENNReal.ofReal_sum_of_nonneg fun x _ => by
        split_ifs <;> simp_all [p.nonneg]
    _ = ∑ x, if y = f x then ENNReal.ofReal (p.weight x) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : f x = y
      · simp [h]
      · have hy : y ≠ f x := Ne.symm h
        simp [h, hy]

/-- The scalar state is literally the existing Core transition row. -/
def rowState (K : FiniteControlledStochasticKernel X A) (x : X) (a : A) : State X :=
  ⟨K.mass x a, K.nonneg x a, K.normalized x a⟩

@[simp] theorem rowState_weight (K : FiniteControlledStochasticKernel X A)
    (x : X) (a : A) (z : X) : (rowState K x a).weight z = K.mass x a z := rfl

/-- Finite stochastic action on the full declared classical simplex. -/
def stepState (K : FiniteControlledStochasticKernel X A) (p : State X) (a : A) :
    State X where
  weight z := ∑ x, p.weight x * K.mass x a z
  nonneg z := Finset.sum_nonneg fun x _ => mul_nonneg (p.nonneg x) (K.nonneg x a z)
  sum_one := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, K.normalized, mul_one, p.sum_one]

theorem stepState_dirac (K : FiniteControlledStochasticKernel X A) (x : X) (a : A) :
    stepState K (dirac x) a = rowState K x a := by
  classical
  apply state_ext
  intro z
  simp [stepState, rowState_weight, dirac_weight]

/-- The full finite stochastic action agrees with the actual PMF bind of
the same real rows, for every input classical state. -/
theorem toPMF_stepState (K : FiniteControlledStochasticKernel X A)
    (p : State X) (a : A) :
    toPMF (stepState K p a) = (toPMF p).bind (fun x => toPMF (rowState K x a)) := by
  ext z
  rw [PMF.bind_apply, tsum_fintype]
  simp only [toPMF_apply, stepState, rowState_weight]
  rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => mul_nonneg (p.nonneg x) (K.nonneg x a z))]
  apply Finset.sum_congr rfl
  intro x _
  exact ENNReal.ofReal_mul (p.nonneg x)

end

end UEOTQM.Classical

namespace UEOTQM.CorePurificationBoundary

open scoped BigOperators _root_.Classical
open MeasureTheory
open UEOTQM.Classical
open UEOT.V3.FiniteStablePartition
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.ViabilityKernel
open UEOT.V3.ViabilityTrajectory
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
open UEOT.V3.Compression.RecursiveSufficientState

noncomputable section

abbrev Micro := Bool × Bool

def fullyObservedSurvivalModel :
    UEOT.V3.FiniteStablePartition.Model Micro Bool ℝ
      (Micro × Bool × Unit × Unit × Bool) :=
  modelWithRegisteredOrganization survivalMicroKernel
    (fun x => x) (fun x => x.1)
    (fun _ => ()) (fun _ => ()) (fun x => x.1) (fun _ _ => 0)

theorem terminal_eq_iff (x y : Micro) :
    (terminalSetoid fullyObservedSurvivalModel).r x y ↔ x = y := by
  constructor
  · intro h
    exact (registered_organizational_attributes_preserved survivalMicroKernel
      (fun x : Micro => x) (fun x => x.1)
      (fun _ => ()) (fun _ => ()) (fun x => x.1) (fun _ _ => 0) h).1
  · rintro rfl
    exact (terminalSetoid fullyObservedSurvivalModel).refl x

abbrev Terminal := ReachableState
  (setoidRepresentation (terminalSetoid fullyObservedSurvivalModel))

instance terminalFintype : Fintype Terminal := Fintype.ofFinite _
instance terminalMeasurableSpace : MeasurableSpace Terminal := ⊤

def terminalControl : ExactControlQuotient Micro Terminal (fun _ => Bool) :=
  organizationalTerminalControl fullyObservedSurvivalModel 0 (1/2)
    (by intro x a; norm_num [fullyObservedSurvivalModel, modelWithRegisteredOrganization])
    (by norm_num) (by norm_num)

def terminalGood (c : Terminal) : Prop :=
  (quotientOutput fullyObservedSurvivalModel
    (terminalSetoid fullyObservedSurvivalModel)
    (terminal_refines_initial fullyObservedSurvivalModel) c.1).1.1 = true

theorem terminalControl_source (x : Micro) (a : Bool) (z : Micro) :
    terminalControl.micro.transition x a z = survivalMicroKernel.mass x a z := rfl

theorem terminalControl_reward (x : Micro) (a : Bool) :
    terminalControl.micro.reward x a = 0 := by
  change quotientReward fullyObservedSurvivalModel
    (terminalSetoid fullyObservedSurvivalModel)
    (terminal_refines_initial fullyObservedSurvivalModel) a ⟦x⟧ = 0
  rw [quotientReward_mk]
  rfl

theorem terminalControl_optimalValue (x : Micro) :
    terminalControl.micro.optimalValue x =
      terminalControl.macroModel.optimalValue (terminalControl.f x) :=
  terminalControl.optimalValue_apply x

theorem terminalControl_injective : Function.Injective terminalControl.f := by
  intro x y h
  have hq := congrArg Subtype.val h
  change (⟦x⟧ : Quotient (terminalSetoid fullyObservedSurvivalModel)) = ⟦y⟧ at hq
  exact (terminal_eq_iff x y).mp (Quotient.exact hq)

theorem terminalGood_source (x : Micro) : terminalGood (terminalControl.f x) ↔ x.1 = true := by
  change (quotientOutput fullyObservedSurvivalModel
    (terminalSetoid fullyObservedSurvivalModel)
    (terminal_refines_initial fullyObservedSurvivalModel) ⟦x⟧).1.1 = true ↔ _
  rw [quotientOutput_mk]
  rfl

theorem viable_all_horizons (n : ℕ) (b : Bool) :
    microViable terminalControl terminalGood n (true,b) := by
  induction n generalizing b with
  | zero => exact (terminalGood_source (true,b)).2 rfl
  | succ n ih =>
      refine ⟨(terminalGood_source (true,b)).2 rfl, true, ?_⟩
      intro ⟨c,d⟩ hz
      cases c with
      | false => simp [terminalControl_source, survivalMicroKernel]
      | true => exact False.elim (hz (ih d))

theorem initial_support_viable (n : ℕ) :
    StaysIn (PMF.pure (true,false)) {x | microViable terminalControl terminalGood n x} := by
  intro x hx
  have hx' : x = (true,false) := by simpa [PMF.mem_support_iff] using hx
  subst x
  exact viable_all_horizons n false

def firstRow : Classical.State Micro := rowState survivalMicroKernel (true,false) true

theorem firstRow_halfMix :
    firstRow = halfMix (dirac (true,false)) (dirac (true,true)) := by
  apply state_ext
  rintro ⟨x,y⟩
  cases x <;> cases y <;>
    norm_num [firstRow, rowState_weight, survivalMicroKernel, halfMix_weight, dirac_weight]

def firstQuotientState : Classical.State Terminal :=
  pushforward terminalControl.f firstRow

theorem quotient_support_distinct : terminalControl.f (true,false) ≠ terminalControl.f (true,true) := by
  intro h
  have hh := terminalControl_injective h
  cases hh

theorem firstQuotientState_halfMix : firstQuotientState =
    halfMix (dirac (terminalControl.f (true,false))) (dirac (terminalControl.f (true,true))) := by
  rw [firstQuotientState, firstRow_halfMix, pushforward_halfMix,
    pushforward_dirac, pushforward_dirac]

theorem firstQuotientState_not_pure : ¬ IsPure firstQuotientState := by
  rw [firstQuotientState_halfMix]
  exact halfMix_not_pure quotient_support_distinct

theorem firstQuotientState_no_pure_extension (B : Type*) [Fintype B] :
    ¬ ∃ p : Classical.State (Terminal × B), IsPure p ∧ marginalLeft p = firstQuotientState := by
  rw [firstQuotientState_halfMix]
  exact no_pure_extension_halfMix quotient_support_distinct

def sourcePMF (x : Micro) (a : Bool) : PMF Micro := terminalControl.micro.transitionPMF x a

/-- An explicit safe policy; zero reward does not select it uniquely by value. -/
def piStar : Micro → Bool := fun _ => true

def actualPathLaw : Measure (ℕ → Micro) :=
  stationaryTrajMeasure sourcePMF piStar (PMF.pure (true,false))

theorem sourcePMF_toReal (x : Micro) (a : Bool) (z : Micro) :
    (sourcePMF x a z).toReal = survivalMicroKernel.mass x a z := by
  rw [sourcePMF, UEOT.V3.FiniteDiscountedControl.Model.transitionPMF_apply_toReal]
  rfl

theorem sourcePMF_firstRow : sourcePMF (true,false) true = toPMF firstRow := rfl

theorem sourcePMF_rowState (x : Micro) (a : Bool) :
    sourcePMF x a = toPMF (rowState survivalMicroKernel x a) := rfl

theorem piStar_preserves : ∀ x : Micro, x.1 = true →
    StaysIn (sourcePMF x (piStar x)) {z | z.1 = true} := by
  intro x _hx z hz
  change z.1 = true
  by_contra hbad
  have hzero : sourcePMF x (piStar x) z = 0 := by
    change ENNReal.ofReal (survivalMicroKernel.mass x true z) = 0
    simp [survivalMicroKernel, hbad]
  exact ((PMF.mem_support_iff _ _).mp hz) hzero

theorem actualPath_all_times_safe : actualPathLaw {ω | ∀ n : ℕ, (ω n).1 = true} = 1 := by
  have hinit : StaysIn (PMF.pure (true,false)) {z : Micro | z.1 = true} := by
    intro x hx
    have h : x = (true,false) := by simpa [PMF.mem_support_iff] using hx
    subst x
    rfl
  apply all_times_safe_of_coordinate_one sourcePMF piStar (PMF.pure (true,false))
    {z : Micro | z.1 = true}
  intro n
  have hm := stationaryStateLaw_staysIn sourcePMF piStar
    {z : Micro | z.1 = true} (PMF.pure (true,false)) hinit piStar_preserves n
  have heq := (staysIn_iff_toMeasure_eq_one _
    (Set.toFinite {z : Micro | z.1 = true}).measurableSet).mp hm
  have hcoord := stationaryTrajMeasure_coordinate sourcePMF piStar (PMF.pure (true,false)) n
  have h := congrArg (fun μ : Measure Micro => μ {z | z.1 = true}) hcoord
  rw [heq, Measure.map_apply (measurable_pi_apply n)
    (Set.toFinite {z : Micro | z.1 = true}).measurableSet] at h
  exact h

theorem actualPath_first_quotient_marginal :
    actualPathLaw.map (fun ω => terminalControl.f (ω 1)) =
      (toPMF firstQuotientState).toMeasure := by
  have hf : Measurable terminalControl.f := Measurable.of_discrete
  calc
    actualPathLaw.map (fun ω => terminalControl.f (ω 1)) =
        (actualPathLaw.map (fun ω => ω 1)).map terminalControl.f := by
      exact (Measure.map_map hf (measurable_pi_apply 1)).symm
    _ = (sourcePMF (true,false) true).toMeasure.map terminalControl.f := by
      rw [actualPathLaw, stationaryTrajMeasure_coordinate]
      simp [stationaryStateLaw, piStar, PMF.pure_bind]
    _ = (toPMF firstQuotientState).toMeasure := by
      rw [PMF.toMeasure_map terminalControl.f _ hf, sourcePMF_firstRow,
        ← toPMF_pushforward]
      rfl

theorem false_action_destructive :
    terminalControl.micro.transition (true,false) false (false,false) = 1/2 := by
  simp [terminalControl_source, survivalMicroKernel]

/-- Precisely the finite H1--H6 slice adopted for this model. It records
the actual stochastic process, registered readout, algorithmic stable quotient,
constructed exact control, nonempty viability and genuine safe trajectory.
It does not stand for the complete UEOT Core or for empirical realizability. -/
def FiniteCoreSlice : Prop :=
  (∀ x a z, 0 ≤ survivalMicroKernel.mass x a z) ∧
  (∀ x a, ∑ z, survivalMicroKernel.mass x a z = 1) ∧
  (∀ x a z, fullyObservedSurvivalModel.transition a x z = survivalMicroKernel.mass x a z) ∧
  (∀ x, fullyObservedSurvivalModel.output x = (x, x.1, (), (), x.1)) ∧
  Stable fullyObservedSurvivalModel (terminalSetoid fullyObservedSurvivalModel) ∧
  (∀ x y, (terminalSetoid fullyObservedSurvivalModel).r x y ↔ x = y) ∧
  (∀ x a z, terminalControl.micro.transition x a z = survivalMicroKernel.mass x a z) ∧
  (∀ x a, terminalControl.micro.reward x a = 0) ∧
  (∀ x, terminalControl.micro.optimalValue x =
    terminalControl.macroModel.optimalValue (terminalControl.f x)) ∧
  (∀ x, terminalGood (terminalControl.f x) ↔ x.1 = true) ∧
  (∀ n b, microViable terminalControl terminalGood n (true,b)) ∧
  (∀ n, StaysIn (PMF.pure (true,false))
    {x | microViable terminalControl terminalGood n x}) ∧
  (∀ x a, sourcePMF x a = toPMF (rowState survivalMicroKernel x a)) ∧
  actualPathLaw {ω | ∀ n : ℕ, (ω n).1 = true} = 1

theorem finiteCoreSlice_holds : FiniteCoreSlice :=
  ⟨survivalMicroKernel.nonneg, survivalMicroKernel.normalized,
    (fun _ _ _ => rfl), (fun _ => rfl), terminal_stable fullyObservedSurvivalModel,
    terminal_eq_iff, terminalControl_source, terminalControl_reward,
    terminalControl_optimalValue, terminalGood_source, viable_all_horizons,
    initial_support_viable, sourcePMF_rowState, actualPath_all_times_safe⟩

/-- One same-source separation certificate. The ancillary type is arbitrary
finite, including empty types. The classical interpretation is the full State
simplex, Effect interval, Cartesian composite and convex-extreme IsPure above;
none of those interpretation choices is asserted to be selected by Core. -/
theorem classical_purification_separation (B : Type*) [Fintype B] :
    FiniteCoreSlice ∧
    actualPathLaw.map (fun ω => terminalControl.f (ω 1)) =
      (toPMF firstQuotientState).toMeasure ∧
    ¬ ∃ p : Classical.State (Terminal × B), IsPure p ∧
      marginalLeft p = firstQuotientState :=
  ⟨finiteCoreSlice_holds, actualPath_first_quotient_marginal,
    firstQuotientState_no_pure_extension B⟩

/- The actual restricted-readout Core model merges the two supported points.
This deletion control validates why the full observation above matters. -/
abbrev RestrictedTerminal := ReachableState
  (setoidRepresentation (terminalSetoid registeredSurvivalModel))

instance restrictedTerminalFintype : Fintype RestrictedTerminal := Fintype.ofFinite _

def restrictedFirstQuotientState : Classical.State RestrictedTerminal :=
  pushforward registeredSurvivalTerminalControl.f firstRow

theorem restricted_support_merge :
    registeredSurvivalTerminalControl.f (true,false) =
      registeredSurvivalTerminalControl.f (true,true) := by
  apply Subtype.ext
  change (⟦(true,false)⟧ : Quotient (terminalSetoid registeredSurvivalModel)) = ⟦(true,true)⟧
  exact Quotient.sound registered_survival_two_hidden_states_merge

theorem restrictedFirstQuotientState_dirac : restrictedFirstQuotientState =
    dirac (registeredSurvivalTerminalControl.f (true,false)) := by
  rw [restrictedFirstQuotientState, firstRow_halfMix, pushforward_halfMix,
    pushforward_dirac, pushforward_dirac, ← restricted_support_merge]
  apply state_ext
  intro x
  simp

theorem restrictedFirstQuotientState_pure : IsPure restrictedFirstQuotientState := by
  rw [restrictedFirstQuotientState_dirac]
  exact dirac_isPure _

end

end UEOTQM.CorePurificationBoundary
