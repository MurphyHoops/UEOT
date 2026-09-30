# Topology-Changing GOA Semantics Audit

Status: **LOCAL LEAN PASS / CARRIER-LEVEL GOA REGENERATION FORMALIZED / UNCOUNTED**

Module:

`UEOT/V3/Compression/TopologyChangingGoaSemantics.lean`

## 1. Why a new semantic layer is needed

The recurrent-topology lane established three distinct regimes:

- support-stable recurrent structure;
- support-addition merge;
- support-deletion split.

Frozen P-GOA-03 is intentionally a fixed-partition perturbation theorem.  Once
the recurrent topology genuinely changes, its old class labels no longer give
the right semantic correspondence.  In particular, after two recurrent
carriers merge, neither old class stationary law is generally invariant for the
new target kernel.

Therefore topology-changing GOA semantics must regenerate long-run objects from
the **target carrier itself**, rather than transport stale source class labels.

## 2. Closed carriers preserve law support

`step_supportedOn_of_closedCarrier` proves that if a law is supported on a
closed carrier `A`, then one stochastic step remains supported on `A`.

The proof is ambient: no restricted kernel is constructed.  For a target state
outside `A`, every contribution to the finite `vecMul` sum vanishes because
either

- the source state is outside `A`, so the law gives it zero mass; or
- the source state is inside `A`, so closedness forces the transition to the
  outside target state to be zero.

This yields `orbit_supportedOn_of_closedCarrier`: every finite-time orbit law
started in `A` remains in `A`.

## 3. Cesaro occupation also stays inside the carrier

`cesaroRow_supportedOn_of_closedCarrier` proves that every finite Cesaro
occupation law generated from a carrier-supported initial law is itself
supported on that carrier.

`supportedOn_of_tendsto` then proves that support in a fixed carrier is closed
under convergence in the finite probability simplex.  Coordinatewise zero mass
outside `A` survives in the limit.

Thus any convergent Cesaro subsequence started inside a closed carrier has its
limit inside the same carrier.

## 4. Every finite recurrent carrier has its own GOA family

`recurrentCarrier_carrierInvariantLawSet_nonempty` is the central theorem.

Given a finite stochastic kernel `P` and a recurrent carrier `A`:

1. choose any `x0 ∈ A`;
2. start from the pure law at `x0`;
3. closedness keeps every orbit/Cesaro law inside `A`;
4. frozen P-GOA-01 supplies a convergent Cesaro subsequence;
5. the limit remains supported on `A`;
6. P-GOA-01 proves that limit is invariant.

Therefore

\[
\boxed{
\operatorname{RecurrentCarrier}(P,A)
\Longrightarrow
\mathcal I_P(A)\neq\varnothing,
}
\]

where `I_P(A)` is the complete family of invariant laws supported on `A`.

This result is independent of any frozen recurrent-class label or
`FiniteRecurrentDecomposition` bookkeeping.

## 5. Merge creates new target GOA semantics

The previous topology lane proved that two source recurrent carriers `A` and
`B` can merge into a target recurrent carrier `A ∪ B` when old support is
retained, target cross-communication is created, and the union is target
closed.

`mergedCarrier_carrierInvariantLawSet_nonempty_of_cross` composes that merge
theorem with carrier-level GOA existence and proves

\[
\boxed{
\mathcal I_Q(A\cup B)\neq\varnothing.
}
\]

The theorem makes no claim that either source stationary law remains target
stationary.

`mergedCarrier_carrierInvariantLawSet_nonempty_of_two_edges` gives the fully
operational version: retained source support, one new positive edge in each
cross direction, and target closure of the union imply a nonempty target GOA
family on the merged carrier.

## 6. Initial-condition-resolved Cesaro limit semantics

The module now defines

`cesaroLimitSet P hP mu0`, the set of all limits of strictly increasing Cesaro
subsequences generated from one initial law `mu0`:

\[
\mathcal C_P(\mu_0)
=
\{\nu:\exists\phi\text{ strictly increasing},\;
C_{\phi(n)}(\mu_0)\to\nu\}.
\]

This object lives directly on the common state-space probability simplex and
does not depend on a recurrent partition.

`cesaroLimitSet_nonempty` is an exact P-GOA-01 corollary:

\[
\boxed{\mathcal C_P(\mu_0)\neq\varnothing.}
\]

`cesaroLimitSet_subset_invariantLawSet` proves every realizable Cesaro limit is
an invariant law:

\[
\boxed{
\mathcal C_P(\mu_0)\subseteq\mathcal I_P.
}
\]

If the initial law is supported on a closed carrier `A`,
`cesaroLimitSet_subset_carrierInvariantLawSet_of_closed` strengthens this to

\[
\boxed{
\mathcal C_P(\mu_0)\subseteq\mathcal I_P(A).
}
\]

Thus the carrier-level invariant-law family is not only an abstract existence
set: it contains every actual Cesaro subsequential long-run law generated from
initial data inside that carrier.

`recurrentCarrier_pure_cesaro_semantics` packages the result for a pure initial
state inside a recurrent carrier: the Cesaro limit set is nonempty and is a
subset of the carrier GOA family.

Finally `mergedCarrier_cesaroLimitSet_subset_of_cross` applies the same
initial-condition-resolved statement after a genuine recurrent merge.  For any
initial law already supported on `A ∪ B`, every target Cesaro subsequential
limit lies in the newly generated merged target GOA family.

## 7. Relation to M-OI and the compression architecture

This lane is not a new generator.  Its semantic existence result is generated
by combining:

- recurrent-carrier structure from the topology bridge network;
- support closure under the ambient Markov dynamics;
- the existing Cesaro/M-OI mechanism embodied by P-GOA-01.

So the new result is another example of the post-compression architecture
producing a theorem absent from the original 106 P-ID list without changing the
four-generator counted core.

## 8. Why this is stronger than label transport

Exact gauge transport handles two descriptions of the **same** recurrent
structure.  Topology change is different: the recurrent objects themselves may
merge or split.

The correct distinction is now formal:

\[
\text{exact gauge}
\Rightarrow
\text{transport the same GOA family},
\]

while

\[
\text{topology change}
\Rightarrow
\text{regenerate GOA semantics on the new carrier}.
\]

This prevents representation equivalence from being confused with genuine
dynamical reorganization.

## 9. Boundaries retained

- The current theorem proves **existence**, not uniqueness, of a target
  carrier-supported invariant law.
- It does not yet quantify the distance between pre-change and post-change
  invariant-law families.
- It does not claim continuity of stationary laws through a merge/split
  bifurcation.
- It now localizes every Cesaro subsequential limit to the correct target
  carrier family, but does not yet quantify how initial mass redistributes
  across newly merged or split recurrent carriers.
- No frozen theorem, counted generator, P-ID disposition, or ledger count is
  changed.

## 10. Next pressure test

The common-state-space Cesaro-limit object is now formalized.  The next useful
step is an exact **support-face relation** across topology change.  Rather than
matching old and new class labels, compare directly:

- carrier-supported invariant-law sets;
- supports/faces of the probability simplex;
- Cesaro limits generated from the same initial law.

The first safe theorem should characterize how a topology merge changes the
allowed support face: old carrier-supported invariant laws lived separately on
`A` or `B`, while both the new merged invariant family and its realizable
Cesaro limits live on `A ∪ B`.  Quantitative TV/Hausdorff-style stability should
only be attempted after this exact set-valued relation is formalized.
