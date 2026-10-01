# Topology-Changing GOA Canonical L1 Strict-Improvement Audit

Status: **LOCAL CANDIDATE / TRACK S / UNCOUNTED**

Module:

`UEOT/V3/Compression/TopologyChangingGoaL1StrictImprovement.lean`

## 1. Question

The merged canonical direct-L1 conorm theorem proves, under the shared
restricted-isolation hypotheses,

\[
\frac{\varepsilon}{\kappa_1^*(P)}
\le
\frac{\sqrt{|S|}\,\varepsilon}{\sigma_{\min}^0(P)}.
\]

That theorem establishes non-worseness but does not show whether the inequality
can be strict for a concrete kernel.

This checkpoint gives an explicit strict-improvement family.

## 2. Completely mixing matrix

Define the finite matrix

\[
U_{ij}=\frac1{|S|}.
\]

For every zero-mass signed vector `v`, Lean proves

\[
vU=0
\]

and therefore

\[
\boxed{R_U(v)=vU-v=-v.}
\]

This is a purely algebraic statement; no asymptotic argument is used.

## 3. Exact canonical L1 conorm

Because the residual is `-v` on the zero-mass subspace, `kappa=1` is a valid
`ZeroSumL1Isolation` constant.

For `|S|>1`, the merged canonical-conorm API provides a nonempty zero-mass L1
unit sphere and identifies `kappa_1^*(U)` as the greatest admissible L1
isolation constant.  The candidate module proves both directions and obtains

\[
\boxed{\kappa_1^*(U)=1.}
\]

The proof does not assume a particular minimizing vector.

## 4. Spectral denominator upper bound

On the same nontrivial state space, the zero-mass Euclidean residual is again
`-I`.  Rather than claiming a full singular-spectrum formula, the checkpoint
uses a normalized nonzero zero-mass vector plus the merged smallest-singular
value lower-gain theorem to prove the sufficient comparison

\[
\boxed{\sigma_{\min}^0(U)\le1.}
\]

Restricted injectivity gives `sigma_min^0(U)>0`.

The theorem intentionally proves only what is needed for the strict radius
comparison; it does not claim that all singular values have been explicitly
computed here.

## 5. Strict certificate improvement

For every nontrivial finite state space (`1 < card S`) and every `epsilon > 0`,
Lean proves

\[
\boxed{
\frac{\varepsilon}{\kappa_1^*(U)}
<
\frac{\sqrt{|S|}\,\varepsilon}{\sigma_{\min}^0(U)}.
}
\]

Since `kappa_1^*(U)=1`, the canonical direct-L1 radius is exactly `epsilon`.
The spectral-TV radius is strictly larger because

\[
0<\sigma_{\min}^0(U)\le1<\sqrt{|S|}.
\]

This is the first explicit machine-checked kernel family in Track S where the
canonical direct-TV certificate is proved strictly stronger than the generic
Euclidean spectral-to-TV certificate.

## 6. Interpretation

The result explains why the canonical L1 route is not merely a repackaging of
the singular-value route.

- Euclidean singular values control the residual in L2 and then pay a generic
  norm-conversion cost to reach TV.
- The canonical L1 conorm measures the residual directly in the semantic TV
  geometry.
- For the completely mixing family, that direct geometry removes a real
  dimension-dependent certificate loss.

## 7. Boundaries retained

- The theorem compares **certified upper bounds**; it does not claim either
  bound is attained by an actual perturbed kernel.
- It proves strict improvement for the explicit completely mixing family, not
  for every stochastic kernel.
- The matrix is algebraically the usual uniform-row mixing kernel, but this
  checkpoint does not require stochasticity to prove the residual/conorm
  comparison itself.
- No claim of a new generator, primitive, or counted theorem mapping is made.
- No frozen P-ID, ledger row, generator count, or Track-H theorem changes.

## 8. Next pressure test

A useful follow-up is to identify broader structural conditions under which

\[
\kappa_1^*(P)>
\sigma_{\min}^0(P)/\sqrt{|S|}
\]

holds, or to compute `kappa_1^*(P)` for additional finite benchmark kernels.
That would distinguish accidental strictness from a reusable kernel-geometry
criterion.
