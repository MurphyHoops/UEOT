import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreSourceAllTimesAssembly
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OrganizationalSufficiencyWitness
import Mathlib.Tactic

/-!
# Nonvacuous single-source infinite-path witness

An existing 4-state stochastic physical model is put through the ACTUAL
P-ALG terminal-partition -> SISC -> P-QUO -> P-PER pipeline. The viability
set contains a concrete microstate at EVERY horizon and therefore supports
a real nonempty initial PMF. We reuse the whole path theorem to certify
probability-one protection over countably infinitely many steps.

This witness contains no physical matter synthesis or lineage mechanism.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open UEOT.V3.FiniteStablePartition
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.ViabilityKernel
open UEOT.V3.ViabilityTrajectory
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
open UEOT.V3.Compression.RecursiveSufficientState

noncomputable def registeredSurvivalTerminalControl :
    let S := terminalSetoid registeredSurvivalModel
    let q := setoidRepresentation S
    letI : Fintype (ReachableState q) := Fintype.ofFinite _
    ExactControlQuotient (Bool × Bool) (ReachableState q) (fun _ => Bool) := by
  exact organizationalTerminalControl registeredSurvivalModel 0 (1/2)
    (by
      intro x a
      norm_num [registeredSurvivalModel, modelWithRegisteredOrganization])
    (by norm_num) (by norm_num)

def registeredSurvivalTerminalGood :
    let S := terminalSetoid registeredSurvivalModel
    let q := setoidRepresentation S
    ReachableState q → Prop :=
  fun c => (quotientOutput registeredSurvivalModel
    (terminalSetoid registeredSurvivalModel)
    (terminal_refines_initial registeredSurvivalModel) c.1).1 = true

/-- On the exact P-ALG terminal quotient, every microstate with safe
visible bit is viable for every finite horizon. -/
theorem registered_survival_viable_all_horizons :
    letI : Fintype (ReachableState
      (setoidRepresentation (terminalSetoid registeredSurvivalModel))) :=
      Fintype.ofFinite _
    ∀ n : ℕ, ∀ h : Bool,
      microViable registeredSurvivalTerminalControl
        registeredSurvivalTerminalGood n (true,h) := by
  classical
  letI : Fintype (ReachableState
    (setoidRepresentation (terminalSetoid registeredSurvivalModel))) :=
      Fintype.ofFinite _
  intro n
  induction n with
  | zero =>
      intro h
      change registeredSurvivalTerminalGood
        (registeredSurvivalTerminalControl.f (true,h))
      change (quotientOutput registeredSurvivalModel
        (terminalSetoid registeredSurvivalModel)
        (terminal_refines_initial registeredSurvivalModel)
        ⟦(true,h)⟧).1 = true
      rw [quotientOutput_mk]
      rfl
  | succ n ih =>
      intro h
      change registeredSurvivalTerminalGood
        (registeredSurvivalTerminalControl.f (true,h)) ∧
          ∃ a : Bool, ∀ z : Bool × Bool,
            ¬ microViable registeredSurvivalTerminalControl
              registeredSurvivalTerminalGood n z →
              registeredSurvivalTerminalControl.micro.transition
                (true,h) a z = 0
      constructor
      · change (quotientOutput registeredSurvivalModel
          (terminalSetoid registeredSurvivalModel)
          (terminal_refines_initial registeredSurvivalModel)
          ⟦(true,h)⟧).1 = true
        rw [quotientOutput_mk]
        rfl
      · refine ⟨true, ?_⟩
        intro ⟨b,h'⟩ hz
        cases b with
        | false =>
          change registeredSurvivalModel.transition true (true,h)
            (false,h') = 0
          simp [registeredSurvivalModel,
            modelWithRegisteredOrganization, survivalMicroKernel]
        | true =>
          exact False.elim (hz (ih h'))

/-- The complete same-source pipeline has a REAL initial viable PMF.
A policy produces a genuine non-vacuous infinite stochastic trajectory
whose registered safety is preserved at every discrete time with
probability one. -/
theorem registered_survival_nonempty_infinite_law :
    letI : Fintype (ReachableState
      (setoidRepresentation (terminalSetoid registeredSurvivalModel))) :=
      Fintype.ofFinite _
    ∃ pi : Bool × Bool → Bool,
      let Q := registeredSurvivalTerminalControl
      stationaryTrajMeasure
        (fun x a => Q.micro.transitionPMF x a) pi
        (PMF.pure (true,false))
        {ω | ∀ t : ℕ, (ω t).1 = true} = 1 := by
  classical
  letI : Fintype (ReachableState
    (setoidRepresentation (terminalSetoid registeredSurvivalModel))) :=
      Fintype.ofFinite _
  let Q := registeredSurvivalTerminalControl
  let good := registeredSurvivalTerminalGood
  obtain ⟨n, hn, hpath⟩ :=
    exists_source_micro_all_times_viable_path_law Q good
  have hμ : StaysIn (PMF.pure (true,false))
      {x | macroViable Q good n (Q.f x)} := by
    intro x hx
    have hx' : x = (true,false) := by
      simpa [PMF.mem_support_iff] using hx
    subst x
    exact (micro_viability_iff_macro_viability Q good n
      (true,false)).mp (registered_survival_viable_all_horizons n false)
  obtain ⟨pi,hpi⟩ := hpath (PMF.pure (true,false)) hμ
  refine ⟨pi, ?_⟩
  let mu := stationaryTrajMeasure
    (fun x a => Q.micro.transitionPMF x a) pi (PMF.pure (true,false))
  have hsub :
      {ω : ℕ → Bool × Bool | ∀ t, macroViable Q good n (Q.f (ω t))} ⊆
      {ω : ℕ → Bool × Bool | ∀ t, (ω t).1 = true} := by
    intro ω hω t
    have hsafe : good (Q.f (ω t)) := by
      cases n with
      | zero => exact hω t
      | succ k => exact (hω t).1
    change (quotientOutput registeredSurvivalModel
        (terminalSetoid registeredSurvivalModel)
        (terminal_refines_initial registeredSurvivalModel) ⟦ω t⟧).1 = true
      at hsafe
    rw [quotientOutput_mk] at hsafe
    simpa [registeredSurvivalModel, modelWithRegisteredOrganization]
      using hsafe
  have hle : mu {ω : ℕ → Bool × Bool | ∀ t, (ω t).1 = true} ≤ 1 := by
    calc
      _ ≤ mu Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
      _ = 1 := by simp
  have htarget : mu {ω : ℕ → Bool × Bool | ∀ t, (ω t).1 = true} = 1 :=
    le_antisymm hle (by
      calc
        1 = mu {ω : ℕ → Bool × Bool | ∀ t,
          macroViable Q good n (Q.f (ω t))} := hpi.symm
        _ ≤ mu {ω : ℕ → Bool × Bool | ∀ t, (ω t).1 = true} :=
          MeasureTheory.measure_mono hsub)
  simpa only [mu, Q] using htarget

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
