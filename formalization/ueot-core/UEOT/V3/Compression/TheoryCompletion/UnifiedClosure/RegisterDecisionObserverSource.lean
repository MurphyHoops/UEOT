import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionObserver
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionExecution

/-!
# Source derivation of the receipt-only observer

The Store projection below is used only on the world side of the proof. The
executable observer never calls it. Every transition theorem is derived from
the existing packed primitive and its already proved original Store bridge.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionObserverSource

open scoped BigOperators
open RegisterJointDecisionSource RegisterJointDecisionExecution
open RegisterDecisionObserver
open RegisterMechanismPurpose (Mechanism)
open FiniteJointDecisionSolver (Table)

def Rooted {Theta : Type*} (w : World Theta) : Prop :=
  ∃ bit tail, w.store = some bit :: tail

/-- A world-side projection. `fresh` distinguishes the original length-one
population from a later permanently empty child1 slot. -/
def projectLocal {Theta : Type*} (goal : Bool) (w : World Theta) : Local :=
  ⟨(packedLookup w.store 0).getD (!goal), packedLookup w.store 1,
    w.stopped, decide (w.store.length = 1)⟩

theorem selected_project {Theta : Type*} (goal : Bool) (w : World Theta)
    (j : Bool) (hw : Rooted w) :
    selected (projectLocal goal w) j = packedLookup w.store (address j) := by
  rcases hw with ⟨bit, tail, hs⟩
  cases j <;> simp [selected, projectLocal, address, packedLookup, hs]

theorem postBit_reconstructed (goal bit : Bool) (a : RegisterRepairSource.Action) (mode : Bool) :
    bitOfBirth goal (childBit goal bit a mode).isSome = postBit goal bit a mode := by
  cases goal <;> cases bit <;> cases a with
  | none => cases mode <;> rfl
  | some value => cases value <;> cases mode <;> rfl

theorem newborn_reconstructed (goal bit : Bool) (a : RegisterRepairSource.Action) (mode : Bool) :
    (if (childBit goal bit a mode).isSome then some goal else none) = childBit goal bit a mode := by
  cases goal <;> cases bit <;> cases a with
  | none => cases mode <;> rfl
  | some value => cases value <;> cases mode <;> rfl

/-- The two-mode local receipt is exactly the observation of the original
packed primitive; the hidden birth label cannot affect it. -/
theorem observe_project {Theta : Type*} (goal : Bool) (w : World Theta)
    (a : Act) (z : Noise) (hw : Rooted w) :
    observe goal w a z = receipt goal (projectLocal goal w) a z.1 := by
  rcases z with ⟨mode, label⟩
  change packedObserve goal w.store (address (effective w.stopped a).1)
      (effective w.stopped a).2 mode =
    if mode then
      match selected (projectLocal goal w) (effective w.stopped a).1 with
      | none => (false, false)
      | some bit => ((effective w.stopped a).2.getD bit == goal,
          (effective w.stopped a).2.isSome)
    else (false, false)
  rw [selected_project goal w _ hw]
  cases hs : packedLookup w.store (address (effective w.stopped a).1) with
  | none => cases mode <;> simp [packedObserve, hs]
  | some bit =>
      cases mode with
      | false => simp [packedObserve, childBit, hs]
      | true =>
          by_cases hg : (effective w.stopped a).2.getD bit = goal <;>
            simp [packedObserve, childBit, hs, hg]

theorem rooted_step {Theta : Type*} (goal : Bool) (w : World Theta)
    (a : Act) (z : Noise) (hw : Rooted w) : Rooted (step goal w a z) := by
  rcases w with ⟨theta, store, stopped⟩
  rcases hw with ⟨bit, tail, rfl⟩
  rcases z with ⟨mode, label⟩
  cases hreq : effective stopped a with
  | mk j action =>
      cases tail with
      | nil =>
          cases j <;> simp [Rooted, step, hreq, packedNext, packedLookup, address]
      | cons child tail =>
          cases j <;> cases child <;>
            simp [Rooted, step, hreq, packedNext, packedLookup, address]

/-- Each actual selected parent's new bit is reconstructed from birth. The
first actual append decides child1; all later tail appends are irrelevant to
the existing 0/1 menu but are still kept in the world. -/
theorem update_project {Theta : Type*} (goal : Bool) (w : World Theta)
    (a : Act) (z : Noise) (hw : Rooted w) :
    projectLocal goal (step goal w a z) =
      update goal (projectLocal goal w) a (observe goal w a z) := by
  rcases w with ⟨theta, store, stopped⟩
  rcases hw with ⟨bit, tail, rfl⟩
  rcases z with ⟨mode, label⟩
  cases hreq : effective stopped a with
  | mk j action =>
      cases tail with
      | nil =>
          cases j <;>
            simp [projectLocal, step, update, observe, hreq, packedNext,
              packedObserve, packedLookup, address, postBit_reconstructed, newborn_reconstructed]
      | cons child tail =>
          cases j <;> cases child <;>
            simp [projectLocal, step, update, observe, hreq, packedNext,
              packedObserve, packedLookup, address, postBit_reconstructed, newborn_reconstructed]

@[simp] theorem initial_project {Theta : Type*} (goal : Bool) (theta : Theta) :
    projectLocal goal (World.mk theta [some (!goal)] false) = init goal := rfl

theorem initial_rooted {Theta : Type*} (goal : Bool) (theta : Theta) :
    Rooted (World.mk theta [some (!goal)] false) := ⟨!goal, [], rfl⟩

/-- Source expectation for any receipt function. This integrates mode and the
fair hidden label; uninformative zeros have unit likelihood. -/
theorem likelihood_expectation (r : ℚ) (goal : Bool) (q : Local) (a : Act) (f : Obs → ℚ) :
    (∑ o : Obs, likelihood r goal q a o * f o) =
      r * f (normalReceipt goal q a) + (1-r) * f (false, false) := by
  simp [likelihood, add_mul, ite_mul, Finset.sum_add_distrib]

theorem primitive_likelihood {Theta : Type*} (r : Theta → ℚ) (goal : Bool)
    (w : World Theta) (a : Act) (o : Obs) (hw : Rooted w) :
    (∑ z : Noise, if observe goal w a z = o then primitiveWeight r w z else 0) =
      likelihood (r w.theta) goal (projectLocal goal w) a o := by
  simp_rw [observe_project goal w a _ hw]
  by_cases hn : normalReceipt goal (projectLocal goal w) a = o <;>
    by_cases hz : (false, false) = o <;>
      simp [primitiveWeight, receipt, likelihood, Fintype.sum_prod_type,
        Fintype.sum_bool, hn, hz] <;> ring

/-- Joint receipt/next-local-state law, not merely a scalar expected reward.
Any fee and birth test is included because both are functions of the receipt. -/
theorem primitive_joint {Theta : Type*} (r : Theta → ℚ) (goal : Bool)
    (w : World Theta) (a : Act) (test : Obs → Local → ℚ) (hw : Rooted w) :
    (∑ z : Noise, primitiveWeight r w z *
      test (observe goal w a z) (projectLocal goal (step goal w a z))) =
    ∑ o : Obs, likelihood (r w.theta) goal (projectLocal goal w) a o *
      test o (update goal (projectLocal goal w) a o) := by
  simp_rw [update_project goal w a _ hw, observe_project goal w a _ hw]
  rw [likelihood_expectation]
  simp [primitiveWeight, receipt, Fintype.sum_prod_type, Fintype.sum_bool]
  ring

def projectNative {Theta : Type*} {n : ℕ} (goal : Bool) (i : Fin n)
    (w : NativeWorld Theta n) : Local := projectLocal goal (projectWorld i w)

theorem native_observe {Theta : Type*} {n : ℕ} (i : Fin n) (m : Mechanism)
    (w : NativeWorld Theta n) (a : Act) (z : Noise)
    (ha : Aligned m.goal w.store) (hr : Rooted (projectWorld i w)) :
    nativeObs (nativeTransaction i m w a z) = receipt m.goal (projectNative m.goal i w) a z.1 := by
  rw [nativeObservation_project i m w a z ha, observe_project m.goal (projectWorld i w) a z hr]
  rfl

theorem native_update {Theta : Type*} {n : ℕ} (i : Fin n) (m : Mechanism)
    (w : NativeWorld Theta n) (a : Act) (z : Noise)
    (ha : Aligned m.goal w.store) (hr : Rooted (projectWorld i w)) :
    projectNative m.goal i (nativeStep i m w a z) =
      update m.goal (projectNative m.goal i w) a (nativeObs (nativeTransaction i m w a z)) := by
  unfold projectNative
  rw [nativeStep_project i m w a z ha, update_project m.goal (projectWorld i w) a z hr,
    nativeObservation_project i m w a z ha]

theorem native_rooted_step {Theta : Type*} {n : ℕ} (i : Fin n) (m : Mechanism)
    (w : NativeWorld Theta n) (a : Act) (z : Noise)
    (ha : Aligned m.goal w.store) (hr : Rooted (projectWorld i w)) :
    Rooted (projectWorld i (nativeStep i m w a z)) := by
  rw [nativeStep_project i m w a z ha]
  exact rooted_step m.goal (projectWorld i w) a z hr

/-- For every actual table and noise path, folding only its own requests and
receipts reconstructs the local state of the complete executed world. -/
theorem packed_summary {Theta : Type*} (goal : Bool) :
    ∀ {H : ℕ} (table : Table Act Obs H) (w : World Theta) (noise : Fin H → Noise)
      (st : Stat), Rooted w → st.q = projectLocal goal w →
      (summarizeFrom goal st (packedExecute goal table w noise).history).q =
        projectLocal goal (packedExecute goal table w noise).finalWorld := by
  intro H
  induction H with
  | zero => intro table w noise st hw hq; cases table; exact hq
  | succ H ih =>
      intro table w noise st hw hq
      cases table with
      | node a children =>
          let o := observe goal w a (noise 0)
          change (summarizeFrom goal (updateStat goal st a o)
              (packedExecute goal (children o) (step goal w a (noise 0))
                (fun j => noise j.succ)).history).q = _
          apply ih (children o) (step goal w a (noise 0)) (fun j => noise j.succ)
            (updateStat goal st a o) (rooted_step goal w a (noise 0) hw)
          change update goal st.q a o = _
          rw [hq]
          exact (update_project goal w a (noise 0) hw).symm

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionObserverSource
