import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SafeOptimalControlFromViability
import UEOT.V3.FiniteDiscountedGreedy
import Mathlib.Tactic

/-!
# Safe constrained control along arbitrary history-dependent randomized paths

Reuse P-CTL-01's causal-policy memory/action interface and the previous
source-derived subtype of exactly viable actions. Unlike earlier stationary
policy viability proofs, this applies to every positive-probability realized
action from any causal history, including randomized and time-dependent rules.
No new Bellman or PMF support theorem is proved.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.ViabilityKernel

universe uX uA uH

variable {X : Type uX} {A : Type uA}
variable [Fintype X] [Fintype A] [Nonempty A]

/-- An admissible action chosen by ANY causal history has source support
inside the registered fixed viable region whenever the current state is in it.
The transition is the original source transition, not a fabricated safe law. -/
theorem viable_action_positive_source_successor
    (M : Model X (fun _ => A)) (K : Set X)
    (x y : X) (a : viableSourceAction M K x)
    (hx : x ∈ K) (hpositive : 0 < M.transition x a.1 y) :
    y ∈ K := by
  have hne : M.transitionPMF x a.1 y ≠ 0 := by
    intro hz
    have hzero : M.transition x a.1 y = 0 := by
      rw [← M.transitionPMF_apply_toReal, hz]
      simp
    exact (ne_of_gt hpositive) hzero
  exact a.property hx ((PMF.mem_support_iff _ _).2 hne)

/-- A positive-support causal trajectory from a registered initial memory.
Every action is drawn from the source-derived viable subtype. Memory types
may include arbitrary complete histories; the proof does not use stationarity.
A strictly positive policy probability is part of the realized-path record. -/
inductive ViableCausalReachable
    (M : Model X (fun _ => A)) (K : Set X)
    (π : CausalPolicy X (viableSourceAction M K))
    (h0 : π.Memory 0) :
    ∀ {t : ℕ}, π.Memory t → Prop where
  | start : ViableCausalReachable M K π h0 h0
  | advance {t : ℕ} {h : π.Memory t}
      (hprev : ViableCausalReachable M K π h0 h)
      (a : viableSourceAction M K (π.current h)) (y : X)
      (ha : 0 < π.actionProb h a)
      (hy : 0 < M.transition (π.current h) a.1 y) :
      ViableCausalReachable M K π h0 (π.advance h a y)

/-- Every positive-probability finite realized history of an arbitrary
nonstationary randomized causal policy using derived safe actions remains
inside K, starting from a single genuinely viable microstate. -/
theorem all_positive_causal_histories_preserve_viability
    (M : Model X (fun _ => A)) (K : Set X)
    (π : CausalPolicy X (viableSourceAction M K))
    (h0 : π.Memory 0) (hstart : π.current h0 ∈ K) :
    ∀ {t : ℕ} (h : π.Memory t),
      ViableCausalReachable M K π h0 h → π.current h ∈ K := by
  intro t h hreach
  induction hreach with
  | start =>
      exact hstart
  | advance hprev a y ha hy ih =>
      rw [π.current_advance]
      exact viable_action_positive_source_successor
        M K _ y a ih hy

/-- The full frozen P-CTL causal theorem applies to the exact original
rewards/transitions restricted to actions that cannot leak from K.
The same policy also has the source-level finite-path invariant above.
Both properties are proved without a separately postulated policy selector. -/
theorem safe_causal_history_optimality_and_path_invariance
    (M : Model X (fun _ => A)) (K : Set X)
    (hfix : viabilityStep (fun x a => M.transitionPMF x a) K = K)
    (π : CausalPolicy X (viableSourceAction M K))
    (h0 : π.Memory 0) (hstart : π.current h0 ∈ K) :
    letI : ∀ x, Nonempty (viableSourceAction M K x) :=
      fun x => exists_viable_source_action M K hfix x
    let R := viableRestrictedModel M K hfix
    (∀ {t : ℕ} (h : π.Memory t),
      ViableCausalReachable M K π h0 h → π.current h ∈ K) ∧
    (∀ {t : ℕ} (h : π.Memory t),
      CausalPolicy.infiniteValue π R h ≤ R.optimalValue (π.current h)) := by
  letI : ∀ x, Nonempty (viableSourceAction M K x) :=
    fun x => exists_viable_source_action M K hfix x
  dsimp only
  exact ⟨all_positive_causal_histories_preserve_viability M K π h0 hstart,
    fun h => CausalPolicy.infiniteValue_le_optimal π
      (viableRestrictedModel M K hfix) h⟩

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
