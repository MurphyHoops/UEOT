# Topology-Changing GOA Constant-Row / Reset-Family Audit

Status: **LOCAL CANDIDATE / TRACK S / UNCOUNTED**

Module:

`UEOT/V3/Compression/TopologyChangingGoaL1ResetFamily.lean`

## 1. Scientific question

The merged strict-improvement checkpoint #213 proves that the canonical direct-L1
certificate is strictly stronger than the generic spectral-to-TV certificate
for the completely mixing uniform-row matrix.

The next question is whether that strictness is an isolated symmetry accident,
or follows from a reusable kernel structure.

This checkpoint proves the latter for the entire constant-row family.

## 2. Constant-row matrix

For an arbitrary row vector `q : S -> R`, define

\[
P_{ij}=q_j.
\]

No probability assumption is needed for the algebraic theorem. If `q` is
nonnegative and normalized, this is the usual one-step reset stochastic kernel.

For every zero-total-mass signed vector `v`, Lean proves

\[
(vP)_j
=
\sum_i v_i q_j
=
q_j\sum_i v_i
=0,
\]

hence

\[
\boxed{R_P(v)=vP-v=-v.}
\]

So the residual restriction on the zero-mass subspace is exactly `-I`,
independently of the particular common row `q`.

## 3. Exact canonical direct-L1 conorm

From `R_P=-I` on zero-mass vectors, `kappa=1` is an exact
`ZeroSumL1Isolation` certificate.

For every nontrivial finite state space (`1 < card S`), the merged canonical
conorm API then gives

\[
\boxed{\kappa_1^*(P)=1.}
\]

The proof uses the greatest-admissible-certificate characterization; it does not
assume that the defining unit-sphere infimum is attained by a named minimizer.

## 4. Euclidean spectral side

The same residual identity makes the zero-mass residual restriction injective.
Using a normalized nonzero zero-mass vector and the merged smallest-singular-value
lower-gain theorem, Lean proves the sufficient bound

\[
\boxed{0<\sigma_{\min}^0(P)\le1.}
\]

The checkpoint deliberately does not compute the full singular spectrum; the
upper bound is all that is needed for strict certificate comparison.

## 5. Strict certificate improvement for the whole family

For every `q : S -> R`, every nontrivial finite state space, and every
`epsilon > 0`, Lean proves

\[
\boxed{
\frac{\varepsilon}{\kappa_1^*(P)}
<
\frac{\sqrt{|S|}\,\varepsilon}{\sigma_{\min}^0(P)}.
}
\]

Since `kappa_1^*(P)=1`, the direct-L1 radius is exactly `epsilon`. The generic
spectral-to-TV certificate is strictly larger because

\[
0<\sigma_{\min}^0(P)\le1<\sqrt{|S|}.
\]

Thus #213's strict improvement is not peculiar to the uniform distribution: it
holds for the entire constant-row / one-step-reset structural family.

## 6. Interpretation

This isolates a reusable kernel-geometry criterion:

> If all rows coincide, the dynamics erase every zero-mass signed perturbation
> in one step. In the semantic L1/TV geometry the residual gain is exactly one,
> while a generic Euclidean-to-TV conversion still pays a dimension factor.

This makes the reason for the strict improvement structural rather than
benchmark-specific.

## 7. Boundaries retained

- For arbitrary `q`, the theorem is algebraic and does **not** assert row
  stochasticity. The stochastic reset interpretation applies only when `q` is
  a valid probability row.
- The strict inequality compares certified upper bounds; it does not claim that
  either bound is attained by an actual perturbed system.
- No claim is made that every kernel with strong mixing has conorm exactly one.
- No full singular-spectrum formula is claimed.
- No new generator, primitive, frozen P-ID mapping, ledger row, or Track-H
  theorem is introduced.

## 8. Next pressure test

The next meaningful extension is no longer another constant-row example. It is
to identify a broader computable condition on the zero-mass residual image or
matrix geometry that gives a strict lower bound on `kappa_1^*(P)` above
`sigma_min^0(P)/sqrt(card S)` without requiring exact one-step reset structure.
