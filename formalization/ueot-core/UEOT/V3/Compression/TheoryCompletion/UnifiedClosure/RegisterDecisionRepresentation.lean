import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionCountHistory
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionRepresentationPayment
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionRepresentationBounds
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionRepresentationWitnesses
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionDAGGenerator

/-!
# Registered decision-representation closure: public return and consumption

The result is the actual checked graph and root, with the executable bound
check on every stored row. `returned` starts a fresh memo for these public
inputs. Its result executes by node index on the original finite population.
No theorem assumes a policy-value, optimality or funding conclusion as data.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionRepresentation

open scoped BigOperators
open RegisterJointDecisionSource RegisterJointDecisionConsumer
open RegisterJointDecisionNativeConsumer RegisterDecisionObserver
open RegisterDecisionRepresentationModel RegisterDecisionRepresentationNative
open RegisterDecisionRepresentationPayment RegisterDecisionRepresentationBounds
open FiniteJointDecisionSolver FiniteJointDecisionSupportedPolicy
open FiniteJointDecisionDAG FiniteJointDecisionDAGGenerator

variable {Theta : Type} [Fintype Theta]

structure Result (P : Family Theta) (prior : Theta → ℚ)
    (hn : ∀ t, 0 ≤ prior t) (ht : ∑ t, prior t = 1) (initial : Wallet) (H : ℕ) where
  control : Certified (RegisterDecisionRepresentationModel.model P prior hn ht initial)
    H (initialStat P.goal)
  bounds : boundCheck H control.graph = true

/-- Accept exactly this candidate array after the all-action check, root
binding and source-specific count/time check. Failure is explicit. -/
def accept (P : Family Theta) (prior : Theta → ℚ)
    (hn : ∀ t, 0 ≤ prior t) (ht : ∑ t, prior t = 1) (initial : Wallet) (H : ℕ)
    (candidate : Candidate Stat Act Obs) : Option (Result P prior hn ht initial H) := do
  let control ← certify (RegisterDecisionRepresentationModel.model P prior hn ht initial)
    H (initialStat P.goal) candidate
  if hb : boundCheck H control.graph = true then
    some ⟨control, hb⟩
  else none

/-- The fresh-memo, shared-state actual return entry. Public inputs stay
closed over by this call; no key from another problem is reused. -/
def returned (P : Family Theta) (prior : Theta → ℚ)
    (hn : ∀ t, 0 ≤ prior t) (ht : ∑ t, prior t = 1) (initial : Wallet) (H : ℕ) :
    Option (Result P prior hn ht initial H) :=
  accept P prior hn ht initial H
    (generate (RegisterDecisionRepresentationModel.model P prior hn ht initial)
      [(false,false),(false,true),(true,false),(true,true)] H (initialStat P.goal))

theorem result_node_bound (P : Family Theta) (prior : Theta → ℚ)
    (hn : ∀ t, 0 ≤ prior t) (ht : ∑ t, prior t = 1) (initial : Wallet) (H : ℕ)
    (result : Result P prior hn ht initial H) :
    result.control.graph.size ≤ 24*(H+1)^4 :=
  actual_graph_node_bound H result.control.graph result.control.good.1 result.bounds

/-- THIS accepted output has its reported exact value under literal native
execution, starting from the actual damaged founder and once-drawn theta. -/
theorem result_native_value (P : Family Theta) (prior : Theta → ℚ)
    (hn : ∀ t, 0 ≤ prior t) (ht : ∑ t, prior t = 1) (initial : Wallet) (H : ℕ)
    (result : Result P prior hn ht initial H) :
    (∑ theta, (prior theta : ℝ) *
      nativeGraphJ P (0 : Fin 1) (RegisterDecisionRepresentationModel.model P prior hn ht initial)
        result.control.graph H (initialStat P.goal) (some result.control.root.val)
        (nativeInitial P theta)) =
      ((result.control.graph[result.control.root.val]).value : ℝ) :=
  initial_checked_native_value P prior hn ht initial result.control.graph result.control.good
    H result.control.root result.control.remaining result.control.initial_state

/-- All permitted real full-history competitors remain below this returned
graph, with the same source, initial wallet, complete fees and finite clock. -/
theorem result_native_optimal (P : Family Theta) (prior : Theta → ℚ)
    (hn : ∀ t, 0 ≤ prior t) (ht : ∑ t, prior t = 1) (initial : Wallet) (H : ℕ)
    (result : Result P prior hn ht initial H)
    (pi : RawCausalPolicy (RegisterJointDecisionConsumer.model P)) (h : pi.Memory)
    (hi : pi.info h = (initialBelief P prior hn ht, initial))
    (R : Realization P (0 : Fin 1) (pi.info h).1)
    (ha : SupportedAdmissible (RegisterJointDecisionConsumer.model P) pi H h) :
    expectedRawNativeJ P (0 : Fin 1) pi H h R ≤
      ((result.control.graph[result.control.root.val]).value : ℝ) := by
  have hr : Rel P prior initial (pi.info h)
      (result.control.graph[result.control.root.val]).state := by
    rw [hi, result.control.initial_state]
    exact initial_relation P prior hn ht initial
  have hb := checked_native_optimal P (0 : Fin 1) prior hn ht initial
    result.control.graph result.control.good H result.control.root result.control.remaining pi h R hr ha
  rw [checked_native_value P (0 : Fin 1) prior hn ht initial result.control.graph
    result.control.good H result.control.root result.control.remaining (pi.info h) R hr] at hb
  exact hb

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionRepresentation
