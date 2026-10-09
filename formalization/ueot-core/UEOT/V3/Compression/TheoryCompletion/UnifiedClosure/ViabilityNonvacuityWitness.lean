import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ViabilityKernelIntertwining
import Mathlib.Tactic

/-!
# UMC: nonvacuous controlled viability and negative action

A single four-state micro world has two actions, stochastic hidden-bit
successors (each probability 1/2), and an exact two-state visible control
quotient. Action true maintains the nonempty registered safety region,
whereas action false leaves it. This is a toy mechanism, not autopoiesis.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
open UEOT.V3.FiniteDiscountedControl

noncomputable def survivalMicroKernel :
    FiniteControlledStochasticKernel (Bool × Bool) Bool where
  mass := fun _ a z => if z.1 = a then (1/2 : ℝ) else 0
  nonneg := by
    intro x a z
    split_ifs <;> norm_num
  normalized := by
    intro x a
    cases a <;> norm_num [Fintype.sum_prod_type]

theorem survivalKernel_nonDirac :
    survivalMicroKernel.mass (false,false) true (true,false) = 1/2 ∧
    survivalMicroKernel.mass (false,false) true (true,true) = 1/2 ∧
    survivalMicroKernel.mass (false,false) false (true,false) = 0 := by
  norm_num [survivalMicroKernel]

theorem survivalRead_strongLumpable :
    StrongLumpability survivalMicroKernel (fun x : Bool × Bool => x.1) := by
  intro x y heq a c
  rfl

/-- Source and macro are independently inspectable, but both transitions
are proved identical under the actual visible pushforward. -/
noncomputable def survivalExactControl :
    ExactControlQuotient (Bool × Bool) Bool (fun _ => Bool) := by
  classical
  refine {
    f := fun x => x.1
    surjective := ?_
    micro := {
      transition := survivalMicroKernel.mass
      reward := fun _ _ => 0
      rewardBound := 0
      discount := 1/2
      transition_nonneg := survivalMicroKernel.nonneg
      transition_sum_one := survivalMicroKernel.normalized
      reward_abs_le := by intros; norm_num
      discount_pos := by norm_num
      discount_lt_one := by norm_num
    }
    macroModel := {
      transition := fun _ a d => if d = a then 1 else 0
      reward := fun _ _ => 0
      rewardBound := 0
      discount := 1/2
      transition_nonneg := by intros; split_ifs <;> norm_num
      transition_sum_one := by
        intro c a
        cases a <;> norm_num [Fintype.sum_bool]
      reward_abs_le := by intros; norm_num
      discount_pos := by norm_num
      discount_lt_one := by norm_num
    }
    discount_eq := rfl
    reward_closed := by intros; rfl
    transition_closed := ?_
  }
  · intro b
    exact ⟨(b,false),rfl⟩
  · intro ⟨b,h⟩ a d
    cases a <;> cases d <;>
      norm_num [fiberMass, survivalMicroKernel, Fintype.sum_prod_type]

def survivalSafe : Bool → Prop := fun c => c = true

/-- The same micro-kernel allows genuinely random hidden outcomes. -/
theorem survivalMicro_hidden_random :
    survivalExactControl.micro.transition (true,false) true (true,false) =
      (1/2 : ℝ) ∧
    survivalExactControl.micro.transition (true,false) true (true,true) =
      (1/2 : ℝ) := by
  norm_num [survivalExactControl, survivalMicroKernel]

/-- Nonempty maximal viability: true remains feasible at all horizons,
and the preserving action is true, chosen from the source dynamics. -/
theorem survival_true_nonempty_all_horizons (n : ℕ) :
    macroViable survivalExactControl survivalSafe n true := by
  induction n with
  | zero => rfl
  | succ n ih =>
      refine ⟨rfl, true, ?_⟩
      intro d hd
      cases d
      · norm_num [survivalExactControl]
      · exact False.elim (hd ih)

/-- The other action destroys the registered survival condition. -/
theorem survival_false_action_is_destructive :
    survivalExactControl.micro.transition
      (true,false) false (false,false) = 1/2 := by
  norm_num [survivalExactControl, survivalMicroKernel]

/-- The hidden bit is physically distinct; only two observable classes
survive the quotient despite four underlying states. -/
theorem survival_micro_alias :
    survivalExactControl.f (true,false) =
    survivalExactControl.f (true,true) := rfl

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
