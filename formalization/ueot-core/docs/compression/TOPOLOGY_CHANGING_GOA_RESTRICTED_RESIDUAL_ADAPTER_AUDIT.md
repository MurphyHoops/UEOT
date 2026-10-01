# Topology-Changing GOA Restricted Residual Adapter Audit

Status: **LOCAL LEAN CANDIDATE / TRACK S / UNCOUNTED**

Module:

`UEOT/V3/Compression/TopologyChangingGoaRestrictedResidualAdapter.lean`

## 1. Purpose

S1 established the semantic bridge

\[
\text{zero-mass Euclidean lower gain}
\Longrightarrow
\text{residual inverse}
\Longrightarrow
\text{GOA stationary-branch tracking}.
\]

This checkpoint explains when such a positive Euclidean lower gain exists in
pure finite-dimensional operator terms.

For the signed-law residual

\[
R_P(v)=vP-v,
\]

probability-law differences lie in the zero-total-mass subspace.  The module
constructs that subspace inside Mathlib's `EuclideanSpace` and restricts the
residual operator to it.

## 2. Zero-mass Euclidean residual operator

The module defines:

- `euclideanSum` — the total-mass linear functional;
- `zeroSumEuclidean` — its kernel;
- `residualEuclideanLinear P` — the Euclidean realization of `v ↦ vP-v`;
- `zeroSumResidualLinear P` — the residual operator with zero-mass domain.

The theorem `zeroSum_mem_iff` proves that Euclidean subspace membership is
literally the coordinate condition

\[
\sum_x v_x=0.
\]

`residualEuclideanLinear_ofLp` machine-checks compatibility with the S1
coordinate residual `signedResidual`.

## 3. Restricted injectivity gives a positive lower gain

The core theorem

`exists_l2LowerSingularBound_of_restricted_injective`

assumes only

\[
\ker(R_P|_{\sum v=0})=\{0\}.
\]

Mathlib's finite-dimensional theorem
`LinearMap.injective_iff_antilipschitz` then supplies an antilipschitz constant.
Taking its reciprocal produces some

\[
\kappa>0
\]

such that

\[
\boxed{
\kappa\|v\|_2\le\|R_Pv\|_2
\qquad(\sum_xv_x=0).
}
\]

Thus the S1 `ZeroSumL2LowerSingularBound` hypothesis is not an isolated
assumption: it follows from a clean structural injectivity certificate in
finite dimension.

## 4. End-to-end GOA consequence

`exists_stationary_tracking_of_restricted_injective` composes the new operator
certificate with S1.

Given:

- source stochastic kernel `P`;
- selected source stationary law `muStar`;
- target stochastic kernel `Q`;
- uniform source/target row-TV defect `epsilon`;
- injectivity of the zero-mass restricted residual operator;

there exists some `kappa > 0` and some target invariant law `muhat` with

\[
\boxed{
D_{TV}(\mu_*,\hat\mu)
\le
\frac{\sqrt{|S|}\,\varepsilon}{\kappa}.
}
\]

The theorem intentionally asserts existence of a valid quantitative constant;
it does not claim this `kappa` is optimal.

## 5. Exact singular-value characterization of injectivity

The module then uses Mathlib's

`LinearMap.injective_iff_forall_lt_finrank_singularValues_pos`

directly.

`restricted_injective_iff_all_singularValues_pos` proves

\[
\boxed{
R_P|_{\sum v=0}\text{ injective}
\iff
\sigma_i(R_P|_{\sum v=0})>0
\text{ for every }i<\operatorname{finrank}.
}
\]

This is a genuine indexed singular-value statement, not only an informal
spectral interpretation.

`exists_stationary_tracking_of_all_singularValues_pos` then converts positivity
of all relevant singular values directly into existence of a quantitative GOA
tracking tube.

## 6. Scientific interpretation

The Track S chain now reads

\[
\boxed{
\text{positive singular spectrum on zero-mass directions}
\Longleftrightarrow
\text{restricted residual injectivity}
\Longrightarrow
\exists\kappa>0\text{ lower gain}
\Longrightarrow
\text{residual inverse}
\Longrightarrow
\text{GOA branch robustness}.
}
\]

This makes the earlier semantic robustness statement depend on a precise
operator-geometric property: there is no nonzero zero-mass signed perturbation
that is invisible to the fixed-point residual.

Periodic dynamics are not excluded merely for failing contraction.  The
certificate concerns isolation of the stationary equation, not one-step or
multi-step mixing.

## 7. Boundaries retained

- Restricted injectivity is sufficient for this route; it is not claimed to be
  the weakest possible semantic robustness condition.
- The produced `kappa` comes from finite-dimensional antilipschitz existence and
  is not claimed optimal.
- Although all relevant singular values are proved positive exactly when the
  restriction is injective, this checkpoint does **not** yet prove that the
  optimal lower-gain constant equals the final indexed singular value.
- The existing S1 distinction remains: a standard Euclidean lower gain feeds TV
  with the safe `sqrt(card S)` norm-conversion factor.
- No counted generator, frozen P-ID disposition, ledger row, or Track H theorem
  changes.

## 8. Next narrow checkpoint

The next optional linear-algebra adapter may identify the sharp Euclidean lower
gain with the smallest indexed singular value of `zeroSumResidualLinear`, using
Mathlib's spectral theorem / orthonormal eigenbasis for `T* T`.

That result should be kept separate because it is a reusable general linear-
algebra statement.  It is not required for the present existence-and-robustness
bridge, which is already complete.
