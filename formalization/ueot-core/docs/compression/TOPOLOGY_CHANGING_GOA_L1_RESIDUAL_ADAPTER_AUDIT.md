# Topology-Changing GOA Direct L1 Residual Adapter Audit

Status: **LOCAL CANDIDATE / TRACK S / UNCOUNTED**

Module:

`UEOT/V3/Compression/TopologyChangingGoaL1ResidualAdapter.lean`

## 1. Purpose

The merged Track-S spectral route realizes the zero-total-mass residual
operator

\[
R_P(v)=vP-v
\]

in Euclidean `L2` geometry.  It now supplies an explicit smallest-singular-value
certificate and therefore the quantitative TV bound

\[
D_{TV}(\mu_*,\hat\mu)
\le
\frac{\sqrt{|S|}\,\varepsilon}{\sigma^0_{\min}(P)}.
\]

The existing semantic layer also has a direct `L1` interface:
`ZeroSumL1Isolation P kappa`, which yields the exact TV residual inverse with
constant `1/kappa` and stationary tracking radius `epsilon/kappa`.

This checkpoint proves that the qualitative operator-isolation condition is the
same in the finite-dimensional `L1` and `L2` realizations, and that restricted
injectivity therefore guarantees existence of some positive direct-L1
minimum-gain certificate.

## 2. L1 realization

The module defines:

- `l1Sum`: the coordinate total-mass functional on `WithLp 1 (S -> R)`;
- `zeroSumL1Space`: its kernel;
- `residualL1Linear P`: the coordinate residual `vP-v` in `L1` geometry;
- `zeroSumResidualL1Linear P`: the residual restricted to the zero-mass `L1`
  subspace.

The coordinate bridge theorems prove that these definitions are literal
realizations of the already merged `signedL1` and `signedResidual` interfaces,
not a new dynamical operator.

## 3. Norm-independent qualitative isolation

The key finite-dimensional result is

`l1_restricted_injective_iff_l2_restricted_injective`:

\[
\boxed{
R_P|_{\sum v=0}\text{ injective in }L^1
\iff
R_P|_{\sum v=0}\text{ injective in }L^2.
}
\]

The proof does not use stochasticity.  Both sides are the same coordinate
linear map with the same zero-mass kernel; only the normed-space realization
changes.

This identifies a clean structural boundary:

> injectivity / spectral isolation is algebraic and norm-independent here;
> quantitative robustness constants depend on the chosen norm geometry.

## 4. Direct L1 minimum-gain existence

Mathlib's finite-dimensional `LinearMap.injective_iff_antilipschitz` applied to
the `L1` realization gives

`l1_restricted_injective_iff_exists_l1Isolation`:

\[
\boxed{
R_P|_{L^1_0}\text{ injective}
\iff
\exists\kappa_1>0:\
\kappa_1\|v\|_1\le\|R_Pv\|_1
\quad(\sum v=0).
}
\]

Combining this with the `L2`/`L1` injectivity equivalence gives

`restricted_injective_iff_exists_l1Isolation`:

\[
\boxed{
R_P|_{\sum v=0}\text{ injective}
\iff
\exists\kappa_1>0\;\text{direct L1 isolation}.
}
\]

And composing with the already merged singular-spectrum characterization gives

`all_singularValues_pos_iff_exists_l1Isolation`:

\[
\boxed{
\forall i<d,\;\sigma_i(R_P)>0
\iff
\exists\kappa_1>0\;\text{direct L1 isolation}.
}
\]

Thus positive Euclidean singular spectrum and existence of a positive exact-TV
minimum gain are the same qualitative finite-dimensional isolation condition.

## 5. End-to-end TV consequence

`exists_l1_stationary_tracking_of_l2_restricted_injective` proves:

if the source residual restriction is injective, then there exists some
`kappa > 0` and a target invariant law `muhat` satisfying

\[
\boxed{
D_{TV}(\mu_*,\hat\mu)\le\varepsilon/\kappa.
}
\]

`exists_l1_stationary_tracking_of_all_singularValues_pos` exposes the same
result directly from the positive-singular-spectrum hypothesis.

This route uses the existing exact `L1` semantic theorem; it does not pass
through the generic `L1 <= sqrt(card S) L2` conversion.

## 6. Relation to the merged sharp singular-value theorem

The two routes answer different quantitative questions:

1. **Euclidean spectral route**
   - explicit, canonical and directly computable denominator
     `sigma_min^0(P)`;
   - public TV bound includes the generic dimension factor
     `sqrt(card S)`.

2. **Direct L1 route in this checkpoint**
   - exact TV geometry, with no explicit dimension-conversion factor;
   - but the positive `kappa_1` produced here is only existential.

Therefore this checkpoint does **not** prove that the direct-L1 numerical bound
is uniformly better than the explicit singular-value bound.  It proves that a
positive direct-TV minimum gain necessarily exists whenever the same residual
operator is spectrally isolated.

## 7. Boundaries retained

- No closed-form or canonical value for the optimal `L1` minimum gain is
  identified here.
- No theorem states `kappa_1 = sigma_min`, nor that one numerical certificate
  dominates the other for every kernel.
- No new stochastic assumption is introduced in the norm-independence or
  existence equivalences.
- The stationary-tracking corollaries reuse the existing row-stochastic source
  and target interfaces exactly where the semantic theorem requires them.
- No frozen source theorem, P-ID disposition, counted mapping, generator count,
  ledger row, or Track-H theorem changes.

## 8. Next quantitative checkpoint

The natural follow-up is to define a canonical kernel-specific direct-L1 conorm

\[
\kappa_1^*(P)
=
\inf_{\sum v=0,\;\|v\|_1=1}\|R_Pv\|_1,
\]

prove positivity exactly under restricted injectivity, and show it itself is a
`ZeroSumL1Isolation` certificate.  A useful comparison target is then

\[
\kappa_1^*(P)
\ge
\frac{\sigma^0_{\min}(P)}{\sqrt{|S|}},
\]

which would formally show the canonical direct-TV certificate is never worse
than the generic Euclidean conversion route while leaving room for strict
kernel-specific improvement.
