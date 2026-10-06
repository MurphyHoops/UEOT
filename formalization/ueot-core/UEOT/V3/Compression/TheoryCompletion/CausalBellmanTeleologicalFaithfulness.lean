import UEOT.V3.Compression.TheoryCompletion.BellmanTeleologicalFaithfulness
import UEOT.V3.FiniteDiscountedSelector

/-!
# P2 audit hardening — causal-policy teleological faithfulness

The original BellmanTeleologicalFaithfulness certificate is intentionally
stationary-policy level. The frozen finite discounted control theorem is
stronger: a Bellman-optimal stationary selector dominates every causal,
history-dependent randomized policy.

Because a causal policy carries an arbitrary memory type in its own universe,
the honest Lean interface is policy-polymorphic rather than one structure that
pretends to quantify over every memory universe at once.
-/

namespace UEOT.V3.Compression.TheoryCompletion

open UEOT.V3.FiniteDiscountedControl

namespace ParentTeleologicalControlRealization

universe uP uX uA uF uHπ uHρ

variable
    {Parent : Type uP} {X : Type uX} {A : Type uA}
    {Future : Type uF}

/-- Pairwise causal-policy teleological faithfulness at a common current state.

This is deliberately not phrased against the Bellman-greedy policy.  It says
that whenever two arbitrary causal, history-dependent randomized policies are
currently at the same physical state, their infinite discounted value order is
exactly the declared contract order of their interpreted admissible futures.

The two policy memories live in independent universes.  Thus the certificate
does not impose a shared-memory, finite-memory, Markov, or same-universe
restriction, and it does not assume the greedy conclusion that will later be
derived from P-CTL-01. -/
def CausalPolicyPairTeleologicalFaithfulness
    [Fintype X] [Nonempty X] [Fintype A] [Nonempty A]
    (dynamics : Parent → X → A → PMF X)
    (R : ParentTeleologicalControlRealization Parent X A Future)
    (π : CausalPolicy.{uX, uA, uHπ} X (fun _ : X => A))
    (rho : CausalPolicy.{uX, uA, uHρ} X (fun _ : X => A))
    (πFuture :
      ∀ {t : ℕ}, π.Memory t →
        AdmissibleFuture R.contract.admissible)
    (rhoFuture :
      ∀ {t : ℕ}, rho.Memory t →
        AdmissibleFuture R.contract.admissible) : Prop :=
  ∀ {tπ tρ : ℕ} (hπ : π.Memory tπ) (hρ : rho.Memory tρ),
    π.current hπ = rho.current hρ →
      (CausalPolicy.infiniteValue π (R.toControlModel dynamics) hπ ≤
          CausalPolicy.infiniteValue rho (R.toControlModel dynamics) hρ ↔
      R.contract.prefers
        (πFuture hπ)
        (rhoFuture hρ))

/-- Specializing pairwise causal faithfulness to the canonical greedy selector,
P-CTL-01 upgrades Bellman optimality to contract maximality against an arbitrary
history-dependent randomized policy.

The conclusion is derived rather than built into the faithfulness predicate. -/
theorem greedyCausalPolicy_contract_maximal
    [Fintype X] [Nonempty X] [Fintype A] [Nonempty A]
    (dynamics : Parent → X → A → PMF X)
    (R : ParentTeleologicalControlRealization Parent X A Future)
    (π : CausalPolicy.{uX, uA, uHπ} X (fun _ : X => A))
    (πFuture :
      ∀ {t : ℕ}, π.Memory t →
        AdmissibleFuture R.contract.admissible)
    (greedyFuture :
      X → AdmissibleFuture R.contract.admissible)
    (F : CausalPolicyPairTeleologicalFaithfulness
      dynamics R π
        (selectorPolicy (R.toControlModel dynamics).greedyAction)
        πFuture (fun x => greedyFuture x))
    {t : ℕ} (h : π.Memory t) :
    R.contract.prefers
      (πFuture h)
      (greedyFuture (π.current h)) := by
  let M := R.toControlModel dynamics
  have hctl :=
    selector_optimal_against_all_causal
      M M.greedyAction M.greedyAction_spec
  have hπ :
      CausalPolicy.infiniteValue π M h ≤
        M.optimalValue (π.current h) :=
    hctl.2 π h
  have hgreedy :
      CausalPolicy.infiniteValue
          (selectorPolicy M.greedyAction) M
          (t := t) (π.current h) =
        M.optimalValue (π.current h) :=
    hctl.1 (t := t) (π.current h)
  apply
    (F h (π.current h)
      (by simp)).1
  simpa [M] using hπ.trans_eq hgreedy.symm

end ParentTeleologicalControlRealization

end UEOT.V3.Compression.TheoryCompletion
