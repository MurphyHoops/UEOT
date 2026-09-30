# Recurrent Support Margin / Class-Structure Lock Audit

Status: **LOCAL LEAN PASS / RECURRENT SUPPORT LOCK FORMALIZED / UNCOUNTED**

Module:

`UEOT/V3/Compression/RecurrentSupportMargin.lean`

## 1. Why metric smallness alone is insufficient

For recurrent decomposition, a zero transition is qualitatively different from
a tiny positive transition.  An arbitrarily small perturbation can turn

\[
P(x,y)=0
\]

into

\[
Q(x,y)=\varepsilon>0,
\]

creating a new directed edge and potentially merging communicating/recurrent
classes.  Therefore no theorem should infer class-structure stability from TV
or matrix-norm smallness alone.

This lane records that boundary formally instead of hiding it inside
P-GOA-03.

## 2. Positive transition gap

`HasTransitionGap P gamma` means every entry satisfies

\[
P(x,y)=0
\quad\text{or}\quad
P(x,y)\ge\gamma.
\]

Assume both kernels `P` and `Q` have the same positive margin `gamma > 0` and
the entrywise perturbation obeys

\[
|Q(x,y)-P(x,y)|<\gamma
\]

for every pair of states.

`transitionSupportEq_of_gap` proves

\[
\boxed{
P(x,y)>0\iff Q(x,y)>0.
}
\]

Thus a positive edge cannot disappear and a zero edge cannot become a new
positive edge while both kernels respect the gap.

## 3. One-step support equality propagates to every finite time

`pow_pos_iff_of_transitionSupportEq` proves for every `n`:

\[
\boxed{
(P^n)(x,y)>0
\iff
(Q^n)(x,y)>0.
}
\]

The proof uses only:

- nonnegativity from row stochasticity;
- the finite matrix-product expansion;
- positivity of a finite sum iff at least one nonnegative summand is positive;
- induction on path length.

Therefore equality of one-step support is enough to lock every finite
positive-probability path.

## 4. Reachability and communication lock

The module then derives:

- `reachable_iff_of_transitionSupportEq`;
- `communicates_iff_of_transitionSupportEq`.

Hence the communication graph is identical.  No spectral, mixing, or
stationary-law hypothesis is needed.

## 5. Recurrent carriers lock

Closure depends only on one-step positive support, while internal
communication depends only on finite-step reachability.  Combining both yields

`recurrentCarrier_iff_of_transitionSupportEq`, and then the explicit margin
corollary

`recurrentCarrier_iff_of_gap`:

\[
\boxed{
A\text{ recurrent for }P
\iff
A\text{ recurrent for }Q.
}
\]

This is the missing structural bridge behind the fixed-partition premise of
P-GOA-03.

## 6. Support lock plus exact state gauge

`recurrentCarrier_image_iff_of_gap_gauge` composes the support-margin theorem
with exact kernel conjugacy.  If `Qaligned` is close to `P` under the gap
condition and the physical target kernel is an exact relabeling of `Qaligned`,
then

\[
\boxed{
e(A)\text{ recurrent for }P_{target}
\iff
A\text{ recurrent for }P.
}
\]

This directly separates:

1. **support-stable perturbation** in one aligned coordinate system;
2. **pure representation gauge** into physical target coordinates.

## 7. Operational one-sided sparse-support lock

The symmetric gap theorem is sufficient but stronger than necessary for many
structured sparse models.  The module now also defines

`PreservesZeroSupport P Q`, meaning

\[
P(x,y)=0 \Longrightarrow Q(x,y)=0.
\]

Assume only:

- the **source** has positive-edge gap `gamma > 0`;
- source-zero edges remain exactly zero in the aligned target;
- every entry changes by strictly less than `gamma`.

Then `transitionSupportEq_of_sourceGap_zeroGuard` proves the same exact support
identity

\[
P(x,y)>0\iff Q(x,y)>0,
\]

without any independent target-gap certificate.  Source-positive edges cannot
fall to zero because doing so would require a perturbation of at least
`gamma`; source-zero edges cannot appear because the zero guard forbids them.

The corresponding theorems

- `recurrentCarrier_iff_of_sourceGap_zeroGuard`;
- `recurrentCarrier_image_iff_of_sourceGap_zeroGuard_gauge`

give recurrent-carrier lock directly in aligned coordinates and after an exact
state gauge.

This is the more operational sufficient condition for sparse Markov models:
the structural zero pattern is known by construction, while only the nonzero
transition weights are perturbed.

## 8. Relation to P-GOA-03

The chain is now:

\[
\boxed{
\text{transition support margin}
\to
\text{class-structure lock}
\to
\text{gauge-aligned recurrent decomposition}
\to
\text{P-GOA-03 quantitative mixture bound}
\to
\text{exact gauge transport}.
}
\]

This removes one major conceptual ambiguity in the previous approximate
recurrent theorem: the shared partition is not automatically guaranteed by
small norm error, but it *is* guaranteed under an explicit support-separation
margin.

## 9. Boundaries retained

- The original two-sided gap theorem is strong; the one-sided sparse-support
  theorem removes the target-gap certificate but still assumes exact
  preservation of source-zero edges.
- It does not yet construct the full target `FiniteRecurrentDecomposition`
  record or its transient fundamental matrix from support lock.
- It does not treat class splitting/merging at the boundary where positive
  transition probabilities approach zero.
- No counted generator, frozen P-ID, or ledger state changes.

## 10. Support-changing bifurcation diagnostic

The one-sided sparse-support closure is complete, and the support-changing
boundary is now diagnostic rather than rhetorical.

`recurrentCarrier_change_implies_new_positive_edge` proves that under a source
positive-edge gap and sub-gap entrywise perturbation,

\[
\neg\bigl(
A\text{ recurrent for }Q
\iff
A\text{ recurrent for }P
\bigr)
\]

forces a finite witness

\[
\boxed{
\exists x,y:\quad P(x,y)=0\ \land\ Q(x,y)>0.
}
\]

So, in this regime, recurrent-carrier change cannot be caused by weakening an
existing positive edge alone: every source-positive edge remains positive.
The obstruction is creation of new support.

`recurrentCarrier_gauge_change_implies_new_positive_edge` adds an arbitrary
exact state gauge between an aligned target and the physical target.  If the
physical recurrent carrier changes, the witness still occurs in the aligned
dynamics.  Exact relabeling itself therefore cannot be the bifurcation cause.

## 11. Post-bifurcation no-splitting structure

The module now separates **support addition** from full support equality via

`TransitionSupportLe P Q`:

\[
P(x,y)>0 \Longrightarrow Q(x,y)>0.
\]

`transitionSupportLe_of_sourceGap` proves that a source positive-edge gap plus
entrywise perturbation strictly below that gap already implies this inclusion.
Unlike the earlier zero-guard theorem, new target-positive edges are allowed.

The inclusion is then propagated through every finite matrix power:

\[
(P^n)(x,y)>0 \Longrightarrow (Q^n)(x,y)>0,
\]

and therefore through reachability and communication:

\[
\boxed{
\operatorname{Communicates}_P(x,y)
\Longrightarrow
\operatorname{Communicates}_Q(x,y).
}
\]

This gives the finite-state **no-splitting theorem** for the sub-gap regime:
an existing source communication class cannot fragment merely because its old
positive edges have been weakened.  New support can only preserve or merge
source communication classes.

For recurrent carriers, `recurrentCarrier_of_source_of_targetClosed` proves
that a source recurrent carrier remains recurrent whenever it remains closed
in the target, since internal communication has already been preserved.

Consequently `sourceRecurrent_loss_implies_new_exit_edge` sharpens the earlier
generic bifurcation witness.  If `A` is recurrent for `P` but not recurrent for
`Q`, then there are states `x,y` with

\[
\boxed{
x\in A,\quad y\notin A,\quad P(x,y)=0,\quad Q(x,y)>0.
}
\]

So loss of a source recurrent carrier is specifically a **loss of closedness**
through a newly created outgoing edge.  Internal communication does not fail in
this regime.

## 12. Refined bifurcation taxonomy

The formalized picture is now asymmetric in a scientifically useful way:

1. with a source positive-edge margin and sub-gap perturbation, **splitting is
   excluded** because every old positive path survives;
2. **merging / absorption into a larger communicating region** can occur only
   through newly created support edges;
3. genuine splitting requires leaving this regime, e.g. allowing old positive
   edges to vanish as the source margin collapses or the perturbation reaches
   the margin scale.

This distinction is stronger than the earlier statement that “support can
change.”  It identifies which direction of recurrent-topology change is
possible under the current perturbation hypotheses.

## 13. Recurrent merge structure

The merge side of the bifurcation is now formalized constructively.

First, `reachable_trans_of_rowStochastic` and
`communicates_trans_of_rowStochastic` make finite positive-probability path
concatenation explicit.  This supplies the graph-theoretic composition rule
needed to reason across source carriers after new target support is added.

For two source recurrent carriers `A` and `B`, assume old positive support is
retained.  `union_internalCommunicates_of_cross` proves that if some
`a ∈ A` and `b ∈ B` communicate in the target, then **every** pair of states in
`A ∪ B` communicates in the target.  Internal source communication survives,
and the single cross-communication certificate connects the two blocks.

Adding only target closedness of the union yields

`recurrentCarrier_union_of_cross_of_closed`:

\[
\boxed{
\operatorname{Communicates}_Q(a,b)
\land
\operatorname{ClosedCarrier}_Q(A\cup B)
\Longrightarrow
\operatorname{RecurrentCarrier}_Q(A\cup B).
}
\]

The module also supplies an operational sufficient condition.
`communicates_cross_of_two_edges` shows that it is enough to have

- one target-positive edge from `A` to `B`;
- one target-positive edge from `B` to `A`;
- retained source support inside both carriers.

The endpoints of the two new edges need not coincide, because preserved
internal communication connects them inside their respective source carriers.

Consequently `recurrentCarrier_union_of_two_edges_of_closed` proves that two
oppositely directed cross-edges plus target closure of `A ∪ B` are sufficient
for a genuine recurrent merge.

This gives a precise post-bifurcation mechanism:

\[
\boxed{
\text{new bidirectional cross support}
\to
\text{cross communication}
\to
\text{union communication}
\xrightarrow{\text{union closed}}
\text{merged recurrent carrier}.
}
\]

## 14. Remaining split regime

The split side is now isolated by a separate support-deletion diagnostic.

`communication_split_implies_deleted_positive_edge` proves that if

\[
\operatorname{Communicates}_P(x,y)
\quad\text{but}\quad
\neg\operatorname{Communicates}_Q(x,y),
\]

then some old source-positive edge has been deleted completely:

\[
\boxed{
\exists u,v:\quad P(u,v)>0\ \land\ Q(u,v)=0.
}
\]

This is the exact converse obstruction to the earlier support-inclusion
no-splitting theorem: if no source-positive edge is deleted, all source
communication survives.

With a source positive-edge gap `gamma`, the deleted-edge witness immediately
becomes quantitative.  `communication_split_implies_gap_crossing` proves

\[
\boxed{
\exists u,v:\quad
\gamma\le |Q(u,v)-P(u,v)|.
}
\]

Thus genuine class splitting is a **margin-threshold crossing**.  It is not a
strict sub-gap phenomenon.

For carrier-level statements the module defines

`RecurrentCarrierSplit P Q A`

to mean that two states inside the same source carrier communicated under `P`
but no longer communicate under `Q`.  The corresponding theorems

- `recurrentCarrierSplit_implies_deleted_positive_edge`;
- `recurrentCarrierSplit_implies_gap_crossing`

lift the same support-deletion and threshold witnesses to carrier splits.

This notion deliberately distinguishes **split** from the earlier event where a
source recurrent carrier stops being recurrent because a new outgoing edge
destroys closedness.  In the current taxonomy:

1. new support can open or merge recurrent regions;
2. deleted old support can split an existing communication class;
3. under a source gap, split requires perturbation at least at the gap scale;
4. exact gauge does neither—it only relabels the same structure.

## 15. Topology-changing GOA boundary

The finite recurrent topology layer is now separated into stable, merge, and
split regimes with explicit machine-checked witnesses.  The next research
question is no longer graph topology itself but **GOA semantics across a
changing recurrent partition**.

In particular, when source classes merge or split, the old componentwise
`classLaw` indexing and fixed mixture weights from P-GOA-03 are no longer the
right comparison coordinates.  A topology-changing theorem needs a common
observable/state space and should compare the induced invariant-law family or
long-run Cesaro law directly, rather than pretending that old and new class
labels still match.

This should be developed as a separate theorem family.  Fixed-partition
P-GOA-03 remains valid and useful inside the support-stable chamber; it should
not be weakened to silently cover a recurrent-topology bifurcation.
