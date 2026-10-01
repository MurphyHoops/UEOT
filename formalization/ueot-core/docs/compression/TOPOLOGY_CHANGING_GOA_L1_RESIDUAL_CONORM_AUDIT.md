# Topology-Changing GOA Canonical L1 Residual Conorm Audit

Status: **PREPARED LOCAL CANDIDATE / TRACK S / UNCOUNTED**

Candidate module:

`UEOT/V3/Compression/TopologyChangingGoaL1ResidualConorm.lean`

## 1. Purpose

The merged direct-L1 adapter proves that zero-mass residual injectivity is
norm-independent between finite-dimensional L2 and L1 realizations and hence
implies existence of some positive `ZeroSumL1Isolation P kappa` witness.

Existence alone is not yet a canonical quantitative certificate. This
checkpoint defines the kernel-specific L1 residual conorm

\[
\kappa_1^*(P)
:=
\inf_{\substack{v\in L^1_0\\ \|v\|_1=1}}
\|R_Pv\|_1,
\qquad R_P(v)=vP-v,
\]

and proves that it is the greatest admissible direct-L1 isolation constant.

## 2. Nontrivial-state boundary

For the finite zero-mass L1 subspace the candidate proves

\[
\dim L^1_0 + 1 = |S|,
\]

hence

\[
\dim L^1_0>0 \iff |S|>1.
\]

The hypothesis `1 < Fintype.card S` in the canonical optimality theorems is
mathematically necessary. When `|S|=1`, the zero-mass subspace is trivial and
every positive constant satisfies the lower-gain inequality vacuously, so
there is no greatest finite positive isolation constant to select.

## 3. Canonical conorm and lower-gain theorem

The candidate defines:

- `l1UnitGainSet P`: residual norms on the zero-mass L1 unit sphere;
- `l1ResidualConorm P := sInf (l1UnitGainSet P)`.

It proves the homogeneous lower-gain inequality

\[
\kappa_1^*(P)\,\|v\|_1\le \|R_Pv\|_1
\]

for every zero-mass vector, with no stochasticity assumption.

## 4. Positivity exactly characterizes isolation

For `|S|>1`:

\[
\boxed{
\kappa_1^*(P)>0
\iff
R_P|_{\sum v=0}\text{ is injective}
}
\]

and equivalently

\[
\boxed{
\kappa_1^*(P)>0
\iff
\text{all indexed singular values of the zero-mass Euclidean residual are positive}.
}
\]

Thus the direct-L1 and Euclidean spectral routes encode the same qualitative
operator isolation condition, while exposing different quantitative geometry.

## 5. Optimality among direct-L1 certificates

Under `|S|>1` and restricted injectivity the candidate proves

`l1ResidualConorm_isGreatest_isolation`:

\[
\boxed{
\kappa_1^*(P)
=
\max\{\kappa:\operatorname{ZeroSumL1Isolation}(P,\kappa)\}.
}
\]

No claim that a specific unit vector attains the defining infimum is required.
Optimality is stated as greatest admissible lower-gain constant.

Consequently, for every nonnegative perturbation envelope `epsilon` and every
other valid isolation witness `kappa`, the canonical radius is no worse:

\[
\frac{\varepsilon}{\kappa_1^*(P)}
\le
\frac{\varepsilon}{\kappa}.
\]

## 6. Comparison with the merged sharp spectral route

For `|S|>1` and restricted injectivity:

\[
\boxed{
\frac{\sigma_{\min}^0(P)}{\sqrt{|S|}}
\le
\kappa_1^*(P).
}
\]

Therefore for `epsilon >= 0`:

\[
\boxed{
\frac{\varepsilon}{\kappa_1^*(P)}
\le
\frac{\sqrt{|S|}\,\varepsilon}{\sigma_{\min}^0(P)}.
}
\]

This gives a rigorous relationship between the two quantitative routes:

- the singular-value route is explicit and Euclidean;
- the canonical L1 route is the optimal direct-TV lower-gain certificate;
- the canonical L1 radius is never worse than the generic Euclidean-to-TV
  conversion bound under the shared isolation assumptions;
- strict improvement is possible in principle but is **not** claimed uniformly
  without a kernel-specific strict inequality theorem or example.

## 7. End-to-end stationary tracking

Using the existing semantic theorem only at the final layer, the candidate
proves existence of a target invariant law `muhat` with

\[
D_{TV}(\mu_*,\hat\mu)
\le
\varepsilon/\kappa_1^*(P).
\]

The conorm construction, positivity equivalence, optimality, and spectral
comparison themselves do not require row-stochasticity.

## 8. Governance boundaries

- Track S only.
- Post-FINAL / uncounted.
- No frozen P-ID change.
- No ledger/count/generator change.
- No Track-H theorem mutation.
- No claim of a fifth primitive or counted generator.
- No claim that the L1 infimum is attained by a specific vector.
- No uniform strict-improvement claim over the spectral route.
