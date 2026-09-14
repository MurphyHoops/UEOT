import Mathlib

/-!
# P-REF-03 — free information has nonnegative decision value

The signal is represented by an arbitrary sub-σ-algebra `mY` of the ambient
sample space. Only the action set is finite. Thus no discreteness assumption is
imposed on the signal space.

For each action `a`, the payoff `u a` is integrable. The informed decision can
choose the pointwise best conditional expected payoff after observing `mY`;
the uninformed decision chooses one fixed action. Because ignoring information
is always allowed, the informed value is at least the uninformed value.
-/

namespace UEOT.V3.FreeInformationValue

open MeasureTheory
open scoped BigOperators

universe uΩ uA

variable {Ω : Type uΩ} {A : Type uA}
variable [mΩ : MeasurableSpace Ω] [Fintype A] [Nonempty A]

/-- A finite pointwise supremum of integrable real-valued functions is
integrable. -/
theorem integrable_finset_sup'
    {μ : Measure Ω} {s : Finset A} (hs : s.Nonempty)
    (f : A → Ω → ℝ)
    (hf : ∀ a ∈ s, Integrable (f a) μ) :
    Integrable (s.sup' hs f) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert a s ha ih =>
      by_cases hsn : s.Nonempty
      · rw [Finset.sup'_insert hsn]
        exact (hf a (Finset.mem_insert_self a s)).sup
          (ih hsn (fun b hb => hf b (Finset.mem_insert_of_mem hb)))
      · have hse : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsn
        subst s
        simpa using hf a (Finset.mem_singleton_self a)

/-- **P-REF-03.** Free, ignorable information has weakly nonnegative decision
value. `mY` is an arbitrary sub-σ-algebra of the ambient measurable space, so
no finiteness or discreteness assumption is imposed on the signal. -/
theorem p_ref_03
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (mY : MeasurableSpace Ω) (hmY : mY ≤ mΩ)
    (u : A → Ω → ℝ)
    (hu : ∀ a, Integrable (u a) μ) :
    Finset.univ.sup' Finset.univ_nonempty (fun a => ∫ ω, u a ω ∂μ) ≤
      ∫ ω, Finset.univ.sup' Finset.univ_nonempty
        (fun a => MeasureTheory.condExp (m₀ := mΩ) mY μ (u a) ω) ∂μ := by
  classical
  let ce : A → Ω → ℝ := fun a =>
    MeasureTheory.condExp (m₀ := mΩ) mY μ (u a)
  have hCeInt : ∀ a, Integrable (ce a) μ := by
    intro a
    dsimp [ce]
    exact MeasureTheory.integrable_condExp
      (m₀ := mΩ) (m := mY) (μ := μ) (f := u a)
  have hInt : Integrable
      (Finset.univ.sup' Finset.univ_nonempty ce) μ :=
    integrable_finset_sup'
      (mΩ := mΩ) (μ := μ) (s := Finset.univ)
      Finset.univ_nonempty ce
      (fun a _ => hCeInt a)
  have hCeIntegral : ∀ a, ∫ ω, ce a ω ∂μ = ∫ ω, u a ω ∂μ := by
    intro a
    dsimp [ce]
    exact MeasureTheory.integral_condExp
      (m₀ := mΩ) (m := mY) (μ := μ) (f := u a) hmY
  have hMain :
      Finset.univ.sup' Finset.univ_nonempty
          (fun a => ∫ ω, u a ω ∂μ) ≤
        ∫ ω, Finset.univ.sup' Finset.univ_nonempty ce ω ∂μ := by
    apply Finset.sup'_le
    intro a ha
    calc
      ∫ ω, u a ω ∂μ = ∫ ω, ce a ω ∂μ := (hCeIntegral a).symm
      _ ≤ ∫ ω, Finset.univ.sup' Finset.univ_nonempty ce ω ∂μ := by
        have hPoint : ce a ≤ Finset.univ.sup' Finset.univ_nonempty ce := by
          intro ω
          simpa only [Finset.sup'_apply] using
            (Finset.le_sup' (s := Finset.univ)
              (f := fun b => ce b ω) (Finset.mem_univ a))
        exact integral_mono (hCeInt a) hInt hPoint
  simpa [ce] using hMain

end UEOT.V3.FreeInformationValue
