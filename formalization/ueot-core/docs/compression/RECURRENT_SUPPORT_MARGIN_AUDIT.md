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

## 11. Next pressure test

The remaining research boundary is the **post-bifurcation regime**: classify
how new support edges merge recurrent components, how loss of a positive-edge
margin can permit class splitting, and how GOA should be compared across
genuinely different recurrent decompositions.

That regime should stay separate from fixed-partition P-GOA-03 rather than
being hidden inside its small-perturbation radius.
