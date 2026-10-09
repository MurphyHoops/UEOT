import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OrganizationalViabilityMaximality
import UEOT.V3.FiniteDiscountedApproxQuotient
import UEOT.V3.ViabilityStrategy
import Mathlib.Tactic

/-!
# Unified mathematical core: reconcile V4 finite real-kernel viability with
# the FROZEN P-PER-03 genuine PMF viability kernel and causal strategy semantics

A repeated viability algorithm is not a new theory. The existing V4 real
recursion and P-PER PMF recursion are IDENTICAL at every finite horizon,
on exactly the same transition table, after the canonical certified Real->PMF
conversion from P-QUO-02. This means the canonical V4 result inherits
P-PER's history-dependent strategy-winning semantics rather than merely
the existence of one arbitrary finite-horizon feedback.

The distinction between registered observable safety and historical/physical
autopoiesis is retained.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.ViabilityKernel
open UEOT.V3.ViabilityStrategy

universe uX uY uA

/-- One real finite transition row places zero mass outside the region
exactly when the canonical PMF is almost-surely contained in the region.
The proof reuses P-QUO-02's normalized row conversion. -/
theorem frozen_pmf_staysIn_iff_real_zero_outside
    {Y : Type uY} {A : Type uA}
    [Fintype Y] [Fintype A] [Nonempty A]
    (M : UEOT.V3.FiniteDiscountedControl.Model Y (fun _ => A))
    (good : Y → Prop) (c : Y) (a : A) :
    StaysIn (M.transitionPMF c a) {d | good d} ↔
    ∀ d : Y, ¬ good d → M.transition c a d = 0 := by
  constructor
  · intro h d hd
    have hn : d ∉ (M.transitionPMF c a).support := by
      intro hs
      exact hd (h hs)
    have hp : M.transitionPMF c a d = 0 := by
      by_contra hz
      exact hn ((PMF.mem_support_iff _ _).2 hz)
    calc
      M.transition c a d = (M.transitionPMF c a d).toReal :=
        (M.transitionPMF_apply_toReal c a d).symm
      _ = 0 := by rw [hp]; simp
  · intro h d hd
    by_contra hnot
    have hd' : ¬ good d := hnot
    have hzreal : (M.transitionPMF c a d).toReal = 0 := by
      rw [M.transitionPMF_apply_toReal]
      exact h d hd'
    have hz : M.transitionPMF c a d = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff _).mp hzreal with hz | hz
      · exact hz
      · exact False.elim ((PMF.apply_ne_top (M.transitionPMF c a) d) hz)
    exact ((PMF.mem_support_iff _ _).1 hd) hz

/-- Existing P-PER-03 is precisely the same viability recursion as UMC V4.
No separate transition model, probability axiom, or viable controller is
assumed in either direction. -/
theorem macro_viability_iff_frozen_pmf_iteration
    {X : Type uX} {Y : Type uY} {A : Type uA}
    [Fintype X] [Fintype Y] [Fintype A] [Nonempty A]
    (Q : ExactControlQuotient X Y (fun _ => A))
    (safe : Y → Prop) :
    ∀ (n : ℕ) (c : Y),
      macroViable Q safe n c ↔
        c ∈ viabilityIter
          (fun y a => Q.macroModel.transitionPMF y a)
          {y | safe y} n := by
  intro n
  induction n with
  | zero =>
      intro c
      rfl
  | succ n ih =>
      intro c
      change (safe c ∧ ∃ a : A,
        ∀ d : Y, ¬ macroViable Q safe n d →
          Q.macroModel.transition c a d = 0) ↔
        c ∈ viabilityIter
          (fun y a => Q.macroModel.transitionPMF y a)
          {y | safe y} (n+1)
      rw [viabilityIter_succ]
      change (safe c ∧ ∃ a : A,
        ∀ d : Y, ¬ macroViable Q safe n d →
          Q.macroModel.transition c a d = 0) ↔
        (c ∈ viabilityIter
          (fun y a => Q.macroModel.transitionPMF y a)
          {y | safe y} n ∧
        ∃ a : A, StaysIn (Q.macroModel.transitionPMF c a)
          (viabilityIter (fun y a =>
            Q.macroModel.transitionPMF y a) {y | safe y} n))
      constructor
      · rintro ⟨hsafe, a, hact⟩
        have hcur : macroViable Q safe (n+1) c := ⟨hsafe, a, hact⟩
        refine ⟨(ih c).mp (macro_viable_succ_subset Q safe n c hcur), a, ?_⟩
        apply (frozen_pmf_staysIn_iff_real_zero_outside
          Q.macroModel
          (fun d => d ∈ viabilityIter
            (fun y b => Q.macroModel.transitionPMF y b) {y | safe y} n)
          c a).2
        intro d hd
        exact hact d (fun hv => hd ((ih d).mp hv))
      · rintro ⟨hprev,a,hact⟩
        have hvprev : macroViable Q safe n c := (ih c).mpr hprev
        have hsafe : safe c := by
          cases n with
          | zero => exact hvprev
          | succ k => exact hvprev.1
        refine ⟨hsafe,a,?_⟩
        have hh := (frozen_pmf_staysIn_iff_real_zero_outside
          Q.macroModel
          (fun d => d ∈ viabilityIter
            (fun y b => Q.macroModel.transitionPMF y b) {y | safe y} n)
          c a).1 hact
        intro d hd
        exact hh d (fun hmem => hd ((ih d).mpr hmem))

/-- The genuinely strongest behavioral semantics already existed in P-PER-03:
the UMC synthesized viability state is equivalent to the existence of an
arbitrary finite-history-dependent sure-safe strategy on the SAME macro PMF.
V4 micro exact-preimage transports that certified winning set back downstairs.

This is a substantive frozen-Core reconciliation, NOT a new copy of the
winning-set proof. -/
theorem micro_viability_equals_frozen_history_strategy_winning_set
    {X : Type uX} {Y : Type uY} {A : Type uA}
    [Fintype X] [Fintype Y] [Fintype A] [Nonempty A]
    (Q : ExactControlQuotient X Y (fun _ => A))
    (safe : Y → Prop) :
    ∃ n : ℕ,
      ∀ x : X,
        microViable Q safe n x ↔
          Q.f x ∈ winningSet
            (fun y a => Q.macroModel.transitionPMF y a)
            {y | safe y} := by
  obtain ⟨n, hfix, heq⟩ :=
    exists_stabilized_eq_winningSet
      (fun y a => Q.macroModel.transitionPMF y a)
      {y | safe y}
  refine ⟨n, fun x => ?_⟩
  rw [micro_viability_iff_macro_viability,
    macro_viability_iff_frozen_pmf_iteration]
  exact heq ▸ Iff.rfl

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
