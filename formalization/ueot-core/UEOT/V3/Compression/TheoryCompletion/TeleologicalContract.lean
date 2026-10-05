import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import UEOT.V3.FiniteDiscountedOccupancy

/-!
# P1.1 — Admissible futures

Purpose is first scoped to a declared set of admissible futures.  This stage
introduces only the typed domain `Γ_Ω`; preference, scalar representation and
expected-value structure are deliberately deferred.
-/

namespace UEOT.V3.Compression.TheoryCompletion

open Set

universe uF

/-- The admissible-future set `Γ_Ω` for one declared object/context. -/
abbrev AdmissibleFutures (Future : Type uF) := Set Future

/-- A future together with evidence that it lies in the admissible set. -/
abbrev AdmissibleFuture
    {Future : Type uF} (Γ : AdmissibleFutures Future) :=
  {future : Future // future ∈ Γ}

@[simp] theorem admissibleFuture_mem
    {Future : Type uF} {Γ : AdmissibleFutures Future}
    (x : AdmissibleFuture Γ) : (x : Future) ∈ Γ :=
  x.property

/-- A nonempty admissible domain has at least one typed admissible future. -/
theorem exists_admissibleFuture
    {Future : Type uF} {Γ : AdmissibleFutures Future}
    (hΓ : Γ.Nonempty) : Nonempty (AdmissibleFuture Γ) := by
  rcases hΓ with ⟨x, hx⟩
  exact ⟨⟨x, hx⟩⟩

/-- Weak teleological preference on the typed admissible-future domain. -/
abbrev PreferenceRelation
    {Future : Type uF} (Γ : AdmissibleFutures Future) :=
  AdmissibleFuture Γ → AdmissibleFuture Γ → Prop

/-- Minimal preorder discipline for teleological preference. -/
def IsPreferencePreorder
    {Future : Type uF} {Γ : AdmissibleFutures Future}
    (prefers : PreferenceRelation Γ) : Prop :=
  (∀ x, prefers x x) ∧
    ∀ ⦃x y z⦄, prefers x y → prefers y z → prefers x z

/-- Minimal general teleological contract.

The contract declares which futures are admissible and how they are weakly
ordered. It contains no scalar objective, no totality/completeness assumption,
no uniqueness statement and no Π/Φ decomposition. -/
structure TeleologicalContract (Future : Type uF) where
  admissible : AdmissibleFutures Future
  admissible_nonempty : admissible.Nonempty
  prefers : PreferenceRelation admissible
  preference_preorder : IsPreferencePreorder prefers

namespace TeleologicalContract

variable {Future : Type uF} (C : TeleologicalContract Future)

theorem prefers_refl (x : AdmissibleFuture C.admissible) :
    C.prefers x x :=
  C.preference_preorder.1 x

theorem prefers_trans
    {x y z : AdmissibleFuture C.admissible}
    (hxy : C.prefers x y) (hyz : C.prefers y z) :
    C.prefers x z :=
  C.preference_preorder.2 hxy hyz

/-- Indifference induced by mutual weak preference. -/
def Indifferent
    (x y : AdmissibleFuture C.admissible) : Prop :=
  C.prefers x y ∧ C.prefers y x

theorem indifferent_refl (x : AdmissibleFuture C.admissible) :
    C.Indifferent x x :=
  ⟨C.prefers_refl x, C.prefers_refl x⟩

theorem indifferent_symm
    {x y : AdmissibleFuture C.admissible}
    (h : C.Indifferent x y) :
    C.Indifferent y x :=
  ⟨h.2, h.1⟩

theorem indifferent_trans
    {x y z : AdmissibleFuture C.admissible}
    (hxy : C.Indifferent x y) (hyz : C.Indifferent y z) :
    C.Indifferent x z :=
  ⟨C.prefers_trans hxy.1 hyz.1, C.prefers_trans hyz.2 hxy.2⟩

end TeleologicalContract

/-- Optional totality/completeness assumption used by finite ordinal
representation.  It is not part of the general teleological contract. -/
def IsTotalPreference
    {Future : Type uF} {Γ : AdmissibleFutures Future}
    (prefers : PreferenceRelation Γ) : Prop :=
  ∀ x y, prefers x y ∨ prefers y x

/-- Strict preference induced by weak preference. -/
def StrictPreference
    {Future : Type uF} {Γ : AdmissibleFutures Future}
    (prefers : PreferenceRelation Γ)
    (x y : AdmissibleFuture Γ) : Prop :=
  prefers x y ∧ ¬ prefers y x

/-- Strict lower contour inside a finite admissible-future domain. -/
noncomputable def strictPreferenceLowerContour
    {Future : Type uF} {Γ : AdmissibleFutures Future}
    [Fintype (AdmissibleFuture Γ)]
    (prefers : PreferenceRelation Γ)
    (x : AdmissibleFuture Γ) : Finset (AdmissibleFuture Γ) := by
  classical
  exact Finset.univ.filter (fun z => StrictPreference prefers z x)

@[simp] theorem mem_strictPreferenceLowerContour
    {Future : Type uF} {Γ : AdmissibleFutures Future}
    [Fintype (AdmissibleFuture Γ)]
    (prefers : PreferenceRelation Γ)
    (z x : AdmissibleFuture Γ) :
    z ∈ strictPreferenceLowerContour prefers x ↔
      StrictPreference prefers z x := by
  classical
  simp [strictPreferenceLowerContour]

/-- Canonical finite ordinal rank. -/
noncomputable def finiteContractOrdinalUtility
    {Future : Type uF} {Γ : AdmissibleFutures Future}
    [Fintype (AdmissibleFuture Γ)]
    (prefers : PreferenceRelation Γ)
    (x : AdmissibleFuture Γ) : ℝ :=
  (strictPreferenceLowerContour prefers x).card

theorem strictPreferenceLowerContour_mono
    {Future : Type uF} {Γ : AdmissibleFutures Future}
    [Fintype (AdmissibleFuture Γ)]
    (prefers : PreferenceRelation Γ)
    (hpre : IsPreferencePreorder prefers)
    {x y : AdmissibleFuture Γ} (hxy : prefers x y) :
    strictPreferenceLowerContour prefers x ⊆
      strictPreferenceLowerContour prefers y := by
  classical
  intro z hz
  rw [mem_strictPreferenceLowerContour] at hz ⊢
  refine ⟨hpre.2 hz.1 hxy, ?_⟩
  intro hyz
  exact hz.2 (hpre.2 hxy hyz)

theorem strictPreferenceLowerContour_ssubset
    {Future : Type uF} {Γ : AdmissibleFutures Future}
    [Fintype (AdmissibleFuture Γ)]
    (prefers : PreferenceRelation Γ)
    (hpre : IsPreferencePreorder prefers)
    {x y : AdmissibleFuture Γ}
    (hxy : StrictPreference prefers x y) :
    strictPreferenceLowerContour prefers x ⊂
      strictPreferenceLowerContour prefers y := by
  classical
  refine ⟨strictPreferenceLowerContour_mono prefers hpre hxy.1, ?_⟩
  intro hrev
  have hxMem : x ∈ strictPreferenceLowerContour prefers y := by
    rw [mem_strictPreferenceLowerContour]
    exact hxy
  have hxNotMem : x ∉ strictPreferenceLowerContour prefers x := by
    rw [mem_strictPreferenceLowerContour]
    intro hxx
    exact hxx.2 (hpre.1 x)
  exact hxNotMem (hrev hxMem)

/-- Finite ordinal representation theorem for a total teleological preorder.
No cardinal interpretation or positive-affine uniqueness is asserted. -/
theorem finiteContractOrdinalUtility_represents
    {Future : Type uF} {Γ : AdmissibleFutures Future}
    [Fintype (AdmissibleFuture Γ)]
    (prefers : PreferenceRelation Γ)
    (hpre : IsPreferencePreorder prefers)
    (htotal : IsTotalPreference prefers)
    (x y : AdmissibleFuture Γ) :
    finiteContractOrdinalUtility prefers x ≤
      finiteContractOrdinalUtility prefers y ↔ prefers x y := by
  classical
  constructor
  · intro hu
    by_contra hxy
    have hyx : prefers y x := (htotal x y).resolve_left hxy
    have hyltx : StrictPreference prefers y x := ⟨hyx, hxy⟩
    have hcard :
        (strictPreferenceLowerContour prefers y).card <
          (strictPreferenceLowerContour prefers x).card :=
      Finset.card_lt_card
        (strictPreferenceLowerContour_ssubset prefers hpre hyltx)
    have hlt' :
        ((strictPreferenceLowerContour prefers y).card : ℝ) <
          ((strictPreferenceLowerContour prefers x).card : ℝ) := by
      exact_mod_cast hcard
    have hlt :
        finiteContractOrdinalUtility prefers y <
          finiteContractOrdinalUtility prefers x := by
      simpa [finiteContractOrdinalUtility] using hlt'
    exact (not_lt_of_ge hu) hlt
  · intro hxy
    have hcard :
        (strictPreferenceLowerContour prefers x).card ≤
          (strictPreferenceLowerContour prefers y).card :=
      Finset.card_le_card
        (strictPreferenceLowerContour_mono prefers hpre hxy)
    have hle' :
        ((strictPreferenceLowerContour prefers x).card : ℝ) ≤
          ((strictPreferenceLowerContour prefers y).card : ℝ) := by
      exact_mod_cast hcard
    simpa [finiteContractOrdinalUtility] using hle'

set_option linter.style.haveILetI false in
/-- A finite admissible domain with total preference has a real-valued ordinal
representation of exactly the contract's weak preference relation. -/
theorem TeleologicalContract.exists_finite_ordinal_representation
    {Future : Type uF} (C : TeleologicalContract Future)
    (hfinite : C.admissible.Finite)
    (htotal : IsTotalPreference C.prefers) :
    ∃ u : AdmissibleFuture C.admissible → ℝ,
      ∀ x y, u x ≤ u y ↔ C.prefers x y := by
  classical
  letI : Fintype (AdmissibleFuture C.admissible) := hfinite.fintype
  refine ⟨finiteContractOrdinalUtility C.prefers, ?_⟩
  intro x y
  exact finiteContractOrdinalUtility_represents
    C.prefers C.preference_preorder htotal x y

open UEOT.V3.FiniteDiscountedControl

/-- Finite expected utility under one explicit probability row.

This is a stronger cardinal construction than P1.3's ordinal rank. -/
def finiteExpectedUtility
    {Outcome : Type*} [Fintype Outcome]
    (p : ProbabilityRow Outcome) (u : Outcome → ℝ) : ℝ :=
  p.expect u

/-- Explicit extra representation obligation for expected-value purpose
semantics. P1.3 does not prove that such a lottery map or cardinal outcome
utility exists. -/
def ExpectedUtilityRepresents
    {Future : Type uF} (C : TeleologicalContract Future)
    {Outcome : Type*} [Fintype Outcome]
    (lottery : AdmissibleFuture C.admissible → ProbabilityRow Outcome)
    (outcomeUtility : Outcome → ℝ) : Prop :=
  ∀ x y,
    finiteExpectedUtility (lottery x) outcomeUtility ≤
        finiteExpectedUtility (lottery y) outcomeUtility ↔
      C.prefers x y

/-! ### P1.4 ordinal-versus-expected-value boundary -/

private def middleLotteryProb : Fin 3 → ℝ :=
  ![0, 1, 0]

private noncomputable def endpointLotteryProb : Fin 3 → ℝ :=
  ![(1 / 2 : ℝ), 0, (1 / 2 : ℝ)]

private noncomputable def middleLottery : ProbabilityRow (Fin 3) where
  prob := middleLotteryProb
  prob_nonneg := by
    intro i
    fin_cases i <;> norm_num [middleLotteryProb]
  prob_sum_one := by
    norm_num [middleLotteryProb, Fin.sum_univ_succ]

private noncomputable def endpointLottery : ProbabilityRow (Fin 3) where
  prob := endpointLotteryProb
  prob_nonneg := by
    intro i
    fin_cases i <;> norm_num [endpointLotteryProb]
  prob_sum_one := by
    norm_num [endpointLotteryProb, Fin.sum_univ_succ]

private def ordinalBoundaryUtility : Fin 3 → ℝ :=
  ![0, 1, 2]

private def nonlinearBoundaryUtility : Fin 3 → ℝ :=
  ![0, 1, 4]

/-- The two outcome utilities induce exactly the same ordinal ordering. -/
theorem ordinalBoundaryUtilities_same_order (i j : Fin 3) :
    ordinalBoundaryUtility i ≤ ordinalBoundaryUtility j ↔
      nonlinearBoundaryUtility i ≤ nonlinearBoundaryUtility j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [ordinalBoundaryUtility, nonlinearBoundaryUtility]

private theorem middleLottery_expect_ordinal :
    middleLottery.expect ordinalBoundaryUtility = 1 := by
  norm_num [ProbabilityRow.expect, middleLottery, middleLotteryProb,
    ordinalBoundaryUtility, Fin.sum_univ_succ]

private theorem endpointLottery_expect_ordinal :
    endpointLottery.expect ordinalBoundaryUtility = 1 := by
  norm_num [ProbabilityRow.expect, endpointLottery, endpointLotteryProb,
    ordinalBoundaryUtility, Fin.sum_univ_succ]

private theorem middleLottery_expect_nonlinear :
    middleLottery.expect nonlinearBoundaryUtility = 1 := by
  norm_num [ProbabilityRow.expect, middleLottery, middleLotteryProb,
    nonlinearBoundaryUtility, Fin.sum_univ_succ]

private theorem endpointLottery_expect_nonlinear :
    endpointLottery.expect nonlinearBoundaryUtility = 2 := by
  norm_num [ProbabilityRow.expect, endpointLottery, endpointLotteryProb,
    nonlinearBoundaryUtility, Fin.sum_univ_succ]

/-- P1.4 boundary. Ordinal equivalence of outcome utilities does not determine
expected-value ordering over lotteries.

The middle outcome and a fifty-fifty endpoint lottery are tied by one ordinal
representative, while an increasing nonlinear representative strictly prefers
the endpoint lottery. Expected-value semantics therefore needs additional
cardinal/mixture structure beyond P1.3. -/
theorem ordinal_equivalence_does_not_determine_expected_value :
    middleLottery.expect ordinalBoundaryUtility =
        endpointLottery.expect ordinalBoundaryUtility ∧
      middleLottery.expect nonlinearBoundaryUtility <
        endpointLottery.expect nonlinearBoundaryUtility := by
  rw [middleLottery_expect_ordinal, endpointLottery_expect_ordinal,
    middleLottery_expect_nonlinear, endpointLottery_expect_nonlinear]
  norm_num

end UEOT.V3.Compression.TheoryCompletion
