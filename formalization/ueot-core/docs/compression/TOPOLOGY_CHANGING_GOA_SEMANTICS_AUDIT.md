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

## 9. Lower/Hausdorff-type discontinuity witness at a recurrent merge

The exact support-face envelope does **not** imply quantitative stationary-law
continuity across a topology bifurcation.  The module now contains an explicit
two-state counterexample.

Define the source kernel

\[
P=\begin{pmatrix}1&0\\0&1\end{pmatrix}
\]

and, for `0 < eps < 1`, the symmetric support-opening target kernel

\[
Q_\varepsilon=
\begin{pmatrix}
1-\varepsilon&\varepsilon\\
\varepsilon&1-\varepsilon
\end{pmatrix}.
\]

The machine-checked chain is:

- `{0}` and `{1}` are distinct source recurrent carriers;
- all source-positive support remains target-positive;
- the two new cross-edges are positive;
- the generic two-edge merge theorem therefore proves `{0} ∪ {1}` is one
  target recurrent carrier;
- `delta_0` is invariant for the source kernel;
- every invariant law of `Q_eps` has coordinates exactly `(1/2,1/2)`;
- finite-PMF TV then gives

\[
\boxed{
D_{TV}(\delta_0,\mu_\varepsilon)=\tfrac12
}
\]

for **every** target invariant law `mu_eps` and every `eps > 0`.

Moreover `twoStateMergedKernel_entrywise_distance` proves every matrix entry
changes by exactly `eps`.  Consequently
`arbitrarily_small_recurrentMerge_fixed_stationary_jump` proves:

\[
\boxed{
\forall\delta>0,\;\exists\varepsilon<\delta
\text{ with entrywise kernel error }<\delta,
\quad D_{TV}=\tfrac12.
}
\]

This is a genuine recurrent-topology merge, not a mere relabeling or a
one-sided transientization example.

The scientific consequence must be stated directionally.  The theorem proves
that **kernel closeness alone cannot force every prescribed source stationary
law to be approximated by target invariant laws with a radius vanishing with
kernel error**.  The witness `delta_0` remains TV-distance `1/2` from every
target invariant law, even as the kernel perturbation tends to zero.  This
rules out lower/Hausdorff-type continuity claims, or any perturbation theorem
that must approximate each source invariant law across the merge.

It does **not** show that all stationary-law continuity notions fail.  In this
same example the uniform law `(1/2,1/2)` is invariant for the identity source
kernel and for every stochastic symmetric target kernel above, so a continuous
stationary selection exists.  Nor does the counterexample refute the usual
upper-semicontinuity direction for finite-state invariant-law sets.

Therefore any positive theorem intended to track an arbitrary prescribed
source stationary law through such a bifurcation must add assumptions that
exclude this mechanism, such as support/topology lock, a uniform ergodicity
margin, or another certificate strong enough to preserve the relevant branch
of stationary semantics.

## 10. Boundaries retained

- The current theorem proves **existence**, not uniqueness, of a target
  carrier-supported invariant law.
- It does not claim full continuity of the invariant-law correspondence through
  a merge/split bifurcation.  The two-state theorem specifically disproves the
  lower/Hausdorff-type direction needed to approximate every prescribed source
  invariant law; it does not disprove existence of a continuous stationary
  selection or upper-semicontinuity of the invariant-law set.
- It does not yet characterize the strongest additional assumptions under
  which a positive set-distance theorem can be recovered.
- It now localizes every Cesaro subsequential limit to the correct target
  carrier family, but does not yet quantify how initial mass redistributes
  across newly merged or split recurrent carriers.
- No frozen theorem, counted generator, P-ID disposition, or ledger count is
  changed.

## 11. Current exact topology-changing semantic stack

The common-state-space Cesaro-limit object and exact **support-face relation**
are now both formalized.

`supportFace A` is the set of all probability laws supported on `A`.  It depends
only on the common state space and carrier, not on the kernel or a recurrent
class label.

`supportFace_mono` proves carrier inclusion induces probability-face inclusion,
and `carrierInvariantLawSet_subset_supportFace` places every carrier GOA family
inside its corresponding face.

For merge, `recurrentMerge_supportFace_envelope` proves all three semantic
objects live in one common ambient envelope:

- source `I_P(A)` lies in the union face `F(A ∪ B)`;
- source `I_P(B)` lies in the same union face;
- target `I_Q(A ∪ B)` is nonempty and also lies in that union face.

This is an exact common-state-space relation, not a claim that source and target
stationary laws are equal or close.

For split/refinement, `recurrentSubcarrier_supportFace_envelope` proves any
target recurrent subcarrier `C ⊆ A` regenerates a nonempty target GOA family
inside the old source face `F(A)`.  `recurrentSplit_supportFace_envelope`
packages two such target subcarriers simultaneously: both new GOA families are
nonempty and both remain inside the old source support face.

So topology-changing semantics now has two exact, label-free layers:

\[
\boxed{
\text{carrier topology}
\to
\text{support-face envelope}
\to
\text{carrier invariant-law family}
\supseteq
\text{realizable Cesaro-limit set}.
}
\]

The quantitative pressure test is now answered negatively for the
**prescribed-source-law / lower-Hausdorff direction** in the unrestricted
topology-changing regime.  The next research question is therefore narrower:

> What is the weakest explicit certificate that rules out the two-state
> bifurcation mechanism and restores quantitative GOA continuity?

The strongest already-formalized positive regime is support/topology lock from
`RecurrentSupportMargin`: under a positive source support gap plus the relevant
zero-support guard, recurrent structure is fixed.  A useful next theorem should
connect that structural lock to a set-valued stationary-law or Cesaro-limit
distance bound, rather than trying to prove continuity through an actual
merge/split event.
