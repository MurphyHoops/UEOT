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

## 7. Relation to P-GOA-03

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

## 8. Boundaries retained

- The two-sided gap assumption is strong.  It rules out arbitrarily small new
  positive edges by construction.
- This file does not derive a target transition gap from source data alone.
- It does not yet construct the full target `FiniteRecurrentDecomposition`
  record or its transient fundamental matrix from support lock.
- It does not treat class splitting/merging at the boundary where positive
  transition probabilities approach zero.
- No counted generator, frozen P-ID, or ledger state changes.

## 9. Next pressure test

The next useful closure is a **source-margin plus zero-support guard** variant:
replace the symmetric target-gap certificate with a more operational condition
that source-zero edges remain exactly zero while source-positive edges stay
positive under a one-sided margin.  That condition is closer to structured
model perturbations where sparsity is known by construction.

After that, the remaining hard boundary is genuine support-changing
bifurcation: class split/merge should be treated as a different regime rather
than forced into fixed-partition P-GOA-03.
