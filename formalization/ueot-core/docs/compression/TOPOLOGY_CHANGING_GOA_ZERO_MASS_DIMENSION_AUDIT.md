# Topology-Changing GOA Zero-Mass Dimension Audit

Status: **LOCAL CANDIDATE / TRACK S / UNCOUNTED**

Module:

`UEOT/V3/Compression/TopologyChangingGoaZeroMassDimension.lean`

## 1. Purpose

The merged sharp singular-value theorem uses the final valid singular-value
index of the zero-total-mass signed-law subspace.  Internally that requires

\[
0<\operatorname{finrank}\{v:\sum_xv_x=0\}.
\]

This checkpoint converts that implementation-level condition into the natural
finite-state statement `1 < card S`.

## 2. The total-mass functional is nonzero

`euclideanSum` sends a Euclidean signed law to the sum of its coordinates.

`euclideanSum_ne_zero` evaluates it on the all-ones vector.  For a finite
nonempty state space the result cannot vanish, so the linear functional is
nonzero.

## 3. Exact zero-mass dimension

The zero-mass space is defined as the kernel of `euclideanSum`.

Mathlib's dual-space theorem

`Module.Dual.finrank_ker_add_one_of_ne_zero`

therefore gives, exactly,

\[
\boxed{
\dim\{v:\sum_xv_x=0\}+1=|S|.
}
\]

This is formalized as `finrank_zeroSumEuclidean_add_one`.

The immediate corollary `zeroSum_finrank_pos_iff_card_one_lt` is

\[
\boxed{
0<\dim\{v:\sum_xv_x=0\}
\iff
1<|S|.
}
\]

Thus the earlier sharp theorem's nonzero-domain condition is neither a hidden
spectral assumption nor an extra dynamical hypothesis: it simply excludes the
one-state trivial system where no final valid singular-value index exists.

## 4. User-facing sharp spectral theorem

`restrictedMinSingularValue_pos_of_card_one_lt` replaces the internal positive-
finrank premise by `1 < Fintype.card S` and proves the restricted minimum
singular value is strictly positive under residual injectivity.

`sharp_stationary_tracking_of_card_one_lt` then gives the full semantic result:

for a source stationary law `muStar`, a target kernel with uniform row-TV defect
`epsilon`, at least two states, and injective zero-mass residual restriction,
there exists a target invariant law `muhat` with

\[
\boxed{
D_{TV}(\mu_*,\hat\mu)
\le
\frac{\sqrt{|S|}\,\varepsilon}
     {\sigma_{\min}^{0}(P)}.
}
\]

Here `sigma_min^0(P)` is the actual final valid indexed singular value of the
zero-mass residual operator already formalized in the preceding checkpoint.

## 5. Architectural significance

This closes an API gap rather than adding a new mathematical primitive.  The
Track-S operator route is now stated entirely in ordinary finite-state terms:

\[
\boxed{
|S|\ge2
+\text{zero-mass residual injective}
+\text{kernel perturbation }\varepsilon
\Longrightarrow
\text{explicit near-GOA radius}.
}
\]

The internal Euclidean subspace dimension is fully discharged by a standard
finite-dimensional identity.

## 6. Boundaries retained

- The one-state case is excluded only because the final valid singular-value
  index does not exist; its dynamics are trivial rather than unstable.
- The denominator is the sharp Euclidean residual singular value, while the
  final TV numerator still uses the generic `sqrt(card S)` norm conversion.
- No claim is made that the displayed TV prefactor is globally optimal.
- No generator promotion, frozen P-ID change, ledger mutation, or Track-H
  theorem change occurs.

## 7. Next Track-S question

With the indexing and dimension boundary now eliminated from the public API,
the remaining quantitative looseness is the Euclidean-to-TV norm conversion.
A future Track-S checkpoint may examine direct `L1`/TV residual geometry or
kernel-specific norm-equivalence constants, but that is separate from the
completed singular-value certificate.
