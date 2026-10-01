# Topology-Changing GOA Spectral Isolation Audit

Status: **LOCAL LEAN PASS / OPERATOR-ISOLATION BRIDGE / UNCOUNTED**

Module:

`UEOT/V3/Compression/TopologyChangingGoaSpectralIsolation.lean`

## 1. Research question

The residual-inverse lane reduced stationary-branch robustness to the estimate

\[
D_{TV}(\mu_*,\nu)
\le
C\,D_{TV}(P\nu,\nu).
\]

The next question is where such a constant `C` can come from without assuming
contraction.  The natural finite-state answer is operator isolation of the
fixed-point equation on the zero-mass signed subspace.

This module machine-checks that bridge.

## 2. Signed residual operator

For a finite signed vector `v : S -> R`, define

\[
R_P v := vP-v.
\]

The code calls this `signedResidual P v`.

This is the negative of `(I-T_P)v`.  Since all isolation statements use norms,
the sign is irrelevant.

For two probability laws `nu` and stationary `muStar`, the difference

\[
v=\nu-\mu_*
\]

has zero total mass, and stationarity gives exactly

\[
R_Pv=P\nu-\nu.
\]

The module proves this identity in
`signedResidual_of_stationary_difference`.

## 3. TV geometry and Euclidean geometry are separated

The module defines

\[
\|v\|_1=\sum_x |v_x|
\]

and

\[
\|v\|_2=\sqrt{\sum_xv_x^2}.
\]

`signedL2_eq_euclidean_norm` proves that the second expression is exactly the
Mathlib norm on `EuclideanSpace R S`.  Thus the `L2` certificate is genuinely a
Euclidean minimum-gain / lower-singular-bound statement, not merely suggestive
notation.

The finite-dimensional norm bridges are also machine checked:

\[
\boxed{\|v\|_1\le\sqrt{|S|}\,\|v\|_2}
\]

and

\[
\boxed{\|v\|_2\le\|v\|_1}.
\]

## 4. Exact `L1` isolation

`ZeroSumL1Isolation P kappa` assumes

\[
\kappa\|v\|_1\le\|R_Pv\|_1
\]

for every zero-mass signed vector `v`, with `kappa > 0`.

Finite-law TV is exactly one half of coordinate `L1`, so
`residualInverse_of_l1Isolation` proves

\[
\boxed{
D_{TV}(\mu_*,\nu)
\le
\frac1\kappa D_{TV}(P\nu,\nu).
}
\]

There is no dimension factor here because the isolation hypothesis is already
expressed in the same `L1` geometry as total variation.

Composing with the merged residual-tracking theorem gives
`l1Isolation_stationary_tracking`:

\[
\boxed{
D_{TV}(\mu_*,\hat\mu)
\le
\frac{\varepsilon}{\kappa}.
}
\]

This is the exact version of the proposed `1/kappa` formula.

## 5. Standard Euclidean lower singular bound

`ZeroSumL2LowerSingularBound P kappa` assumes

\[
\kappa\|v\|_2\le\|R_Pv\|_2
\]

for every zero-mass signed vector `v`.

This is precisely the minimum-gain inequality associated with a positive lower
singular value of the residual operator restricted to the zero-mass subspace.

The TV estimate requires norm conversion.  Using the two finite-dimensional
inequalities above, `residualInverse_of_l2LowerSingularBound` proves

\[
\boxed{
D_{TV}(\mu_*,\nu)
\le
\frac{\sqrt{|S|}}{\kappa}
D_{TV}(P\nu,\nu).
}
\]

and `l2LowerSingularBound_stationary_tracking` gives

\[
\boxed{
D_{TV}(\mu_*,\hat\mu)
\le
\frac{\sqrt{|S|}\,\varepsilon}{\kappa}.
}
\]

## 6. Why the proposed Euclidean `1/kappa` bound needed correction

If `kappa` is a standard `L2` singular lower bound, the direct TV formula

\[
D_{TV}(\mu_*,\nu)
\le
\frac1\kappa D_{TV}(P\nu,\nu)
\]

does not follow in general from norm comparison alone.  The conversion from
`L2` control of `nu-muStar` to `L1`/TV introduces a finite-dimensional factor.

The safe general factor proved here is `sqrt(card S)`.

This factor is not claimed optimal for a given kernel or a particular
zero-mass subspace geometry.  It is the uniform dimension-safe bridge.

If one assumes an `L1` / TV minimum-gain constant instead, the exact
`1/kappa` statement is recovered, as proved in Section 4.

## 7. Updated Track S hierarchy

The machine-checked branch-stability route is now

\[
\text{global Dobrushin}
\Rightarrow
\text{one-step anchored}
\Rightarrow
\text{multi-step anchored}
\Rightarrow
\text{residual inverse}
\Rightarrow
\text{GOA branch tracking},
\]

with a new derivation into the residual-inverse node:

\[
\boxed{
\text{zero-sum operator isolation}
\Rightarrow
\text{residual inverse}
\Rightarrow
\text{GOA branch tracking}.
}
\]

This is the first post-final Track S bridge that connects semantic stationary-
branch robustness directly to finite-dimensional operator geometry rather than
to a contraction hypothesis.

## 8. What is and is not formalized here

Formalized now:

- the signed residual operator on law differences;
- exact zero-mass typing;
- exact `L1` minimum-gain -> `1/kappa` residual inverse;
- Euclidean norm identification;
- Euclidean lower-singular-bound -> `sqrt(card S)/kappa` residual inverse;
- both corresponding target stationary-tracking theorems.

Not yet formalized in this checkpoint:

- construction of the zero-mass Euclidean subspace as an explicit Mathlib
  inner-product subspace;
- construction of the restricted `(I-T_P)` endomorphism on that subspace;
- extraction of `kappa` from an actual indexed value of
  `LinearMap.singularValues`;
- an optimal TV/Euclidean norm-equivalence constant for a specific subspace or
  kernel.

The second item set is intentionally deferred to a separate adapter checkpoint
so that this PR does not hide a substantial spectral-library theorem inside a
semantic bridge.

## 9. Boundaries retained

- Operator isolation is a sufficient source-side certificate, not claimed
  necessary or weakest.
- A positive lower singular bound is not identified with global mixing or
  Dobrushin contraction; periodic chains can have isolated fixed points without
  strict contraction.
- The target kernel still need not preserve the source recurrent partition.
- The target invariant law need not be unique.
- No frozen source theorem, counted generator, P-ID disposition, or ledger count
  changes.

## 10. Next checkpoint

The next narrow goal is an actual Mathlib singular-value adapter:

1. define the zero-mass Euclidean subspace;
2. prove the residual operator preserves it;
3. restrict `I-T_P` to that finite-dimensional inner-product space;
4. relate a positive smallest singular value of the restricted operator to
   `ZeroSumL2LowerSingularBound`;
5. feed that certificate into the already proved GOA tracking chain.

That checkpoint should remain separate from any claim that the spectral
certificate is necessary, minimal, or optimal.
