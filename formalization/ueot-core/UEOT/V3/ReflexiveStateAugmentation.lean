import UEOT.V3.FiniteHistoryMeasurable
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# P-REF-01 foundation — causal reflexive history kernel

The reflexive state is `Z = X × S`.  A causal randomized policy at time `n`
is a Markov kernel from the complete finite history
`H_n = (Z_0,A_0,...,A_{n-1},Z_n)` to the next action.  Given the source
controlled kernel `K : Kernel (Z × A) Z`, this module samples the action, then
the next reflexive state, then appends both to the complete history.

No deterministic-policy, Markov-policy, finite-memory or finite-state weakening
is made here.
-/

namespace UEOT.V3.ReflexiveStateAugmentation

open MeasureTheory ProbabilityTheory
open UEOT.V3.FiniteHistory
open UEOT.V3.FiniteHistoryMeasurable
open scoped ProbabilityTheory

universe uX uS uA uZ

abbrev ReflexiveState (X : Type uX) (S : Type uS) := X × S

variable {Z : Type uZ} {A : Type uA}
variable [MeasurableSpace Z] [MeasurableSpace A]

/-- Current reflexive state in a fixed-time complete history. -/
def currentFiber (n : ℕ) (h : HistoryFiber Z A n) : Z :=
  h.1 (Fin.last n)

theorem measurable_currentFiber (n : ℕ) :
    Measurable (currentFiber (Z := Z) (A := A) n) := by
  unfold currentFiber HistoryFiber
  exact (measurable_pi_apply (Fin.last n)).comp measurable_fst

/-- Pull the source controlled kernel back to complete histories and the
selected action.  Its history dependence is exactly through the current `Z`. -/
noncomputable def controlledNext
    (n : ℕ) (K : Kernel (Z × A) Z) :
    Kernel (HistoryFiber Z A n × A) Z :=
  K.comap
    (fun p => (currentFiber n p.1, p.2))
    (((measurable_currentFiber (Z := Z) (A := A) n).comp measurable_fst).prodMk
      measurable_snd)

instance isMarkovKernel_controlledNext
    (n : ℕ) (K : Kernel (Z × A) Z) [IsMarkovKernel K] :
    IsMarkovKernel (controlledNext n K) := by
  unfold controlledNext
  infer_instance

/-- One arbitrary causal-policy step on the complete finite history: sample
`a ~ pi_n(h)`, then `z' ~ K(current(h),a)`, then append `(a,z')`. -/
noncomputable def fixedPolicyAugmented
    (n : ℕ)
    (pi : Kernel (HistoryFiber Z A n) A)
    (K : Kernel (Z × A) Z) :
    Kernel (HistoryFiber Z A n) (Carrier Z A) :=
  (((Kernel.id ×ₖ pi) ⊗ₖ
      (controlledNext n K).comap Prod.snd measurable_snd).map
    (fun p : (HistoryFiber Z A n × A) × Z =>
      Carrier.advance (⟨n, p.1.1⟩ : Carrier Z A) p.1.2 p.2))

instance isMarkovKernel_fixedPolicyAugmented
    (n : ℕ)
    (pi : Kernel (HistoryFiber Z A n) A)
    (K : Kernel (Z × A) Z)
    [IsMarkovKernel pi] [IsMarkovKernel K] :
    IsMarkovKernel (fixedPolicyAugmented n pi K) := by
  unfold fixedPolicyAugmented
  exact Kernel.IsMarkovKernel.map _ (measurable_advance_fixed n)

/-- Arbitrary history-dependent randomized causal policy. -/
abbrev CausalPolicy (Z : Type uZ) (A : Type uA)
    [MeasurableSpace Z] [MeasurableSpace A] :=
  ∀ n : ℕ, Kernel (HistoryFiber Z A n) A

/-- One homogeneous Markov kernel on the time-tagged complete-history carrier.
The time tag and the entire history are internal to the state. -/
noncomputable def historyKernel
    (K : Kernel (Z × A) Z)
    (pi : CausalPolicy Z A) :
    Kernel (Carrier Z A) (Carrier Z A) where
  toFun h := fixedPolicyAugmented h.1 (pi h.1) K h.2
  measurable' :=
    measurable_of_forall_historyFiber
      (fun h : Carrier Z A => fixedPolicyAugmented h.1 (pi h.1) K h.2)
      (fun n => Kernel.measurable (fixedPolicyAugmented n (pi n) K))

instance isMarkovKernel_historyKernel
    (K : Kernel (Z × A) Z)
    (pi : CausalPolicy Z A)
    [IsMarkovKernel K]
    [∀ n, IsMarkovKernel (pi n)] :
    IsMarkovKernel (historyKernel K pi) := by
  constructor
  rintro ⟨n, h⟩
  change IsProbabilityMeasure (fixedPolicyAugmented n (pi n) K h)
  infer_instance

end UEOT.V3.ReflexiveStateAugmentation
