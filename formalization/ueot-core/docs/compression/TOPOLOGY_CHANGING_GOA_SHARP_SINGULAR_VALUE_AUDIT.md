# Topology-Changing GOA Sharp Singular-Value Audit

Status: **LOCAL CANDIDATE / TRACK S / UNCOUNTED**

Module:

`UEOT/V3/Compression/TopologyChangingGoaSharpSingularValue.lean`

## 1. Purpose

The preceding Track-S checkpoints established that, for the zero-mass signed-law
residual operator,

\[
\text{injective}
\iff
\text{all valid indexed singular values are positive}
\iff
\exists\kappa>0\text{ Euclidean lower gain}.
\]

That result was quantitative only existentially: finite-dimensionality
guaranteed some usable `kappa`, but did not identify it with a canonical
spectral quantity.

This checkpoint closes that gap.

## 2. General smallest-singular-value theorem

For any real finite-dimensional linear map

\[
T:E\to F
\]

with nonzero domain, `smallest_singularValue_mul_norm_le` proves

\[
\boxed{
\sigma_{n-1}(T)\,\|x\|
\le
\|Tx\|,
\qquad n=\dim E>0.
}
\]

Mathlib orders `LinearMap.singularValues` monotonically downward, so index
`n-1` is the final valid / smallest singular value.

The proof is machine checked from the spectral theorem:

1. diagonalize `T* T` in its orthonormal eigenbasis;
2. use Parseval to write `‖x‖²` as the sum of squared basis coefficients;
3. use antitonicity of the eigenvalues to lower-bound every diagonal term by
   the final eigenvalue;
4. identify that eigenvalue with `σ_{n-1}(T)²` through
   `LinearMap.sq_singularValues_fin`;
5. use `⟪x,T*Tx⟫ = ‖Tx‖²` and nonnegativity to take the square-root inequality.

No compactness, asymptotic mixing, or Markov-specific argument is used in this
general theorem.

## 3. Zero-dimensional boundary

The theorem explicitly assumes

\[
0<\dim E.
\]

This is necessary for the indexing statement itself: if the domain has finrank
zero there is no final valid singular-value index.  The corresponding residual
problem is vacuous on the zero vector space, but it should not be encoded by a
fabricated `σ_min` index.

For the GOA application this becomes the explicit hypothesis

\[
0<\dim\{v:\sum_xv_x=0\}.
\]

## 4. Explicit residual spectral certificate

Define

\[
\sigma_{\min}^{0}(P)
=
\sigma_{d-1}
\bigl(R_P|_{\sum v=0}\bigr),
\]

where `d` is the zero-mass subspace finrank and

\[
R_P(v)=vP-v.
\]

The Lean definition is `restrictedMinSingularValue P`.

Under positive zero-mass finrank and restricted injectivity,
`restrictedMinSingularValue_pos` proves

\[
\boxed{\sigma_{\min}^{0}(P)>0.}
\]

`sharp_l2LowerSingularBound_of_restricted_injective` then proves the exact
Euclidean lower-gain certificate

\[
\boxed{
\sigma_{\min}^{0}(P)\,\|v\|_2
\le
\|R_Pv\|_2
\qquad(\sum_xv_x=0).
}
\]

This replaces the previous existential `kappa` by a canonical indexed spectral
quantity.

## 5. Explicit GOA robustness radius

Composing the sharp lower-gain theorem with the already merged S1 semantic
bridge gives `sharp_stationary_tracking_of_restricted_injective`:

if `muStar` is source-stationary, the zero-mass residual restriction is
injective with positive-dimensional domain, and the target kernel has uniform
row-TV defect at most `epsilon`, then there exists a target invariant law
`muhat` satisfying

\[
\boxed{
D_{TV}(\mu_*,\hat\mu)
\le
\frac{\sqrt{|S|}\,\varepsilon}
     {\sigma_{\min}^{0}(P)}.
}
\]

The denominator is now directly computable from the restricted residual
operator's singular spectrum.

## 6. What became stronger

Before this checkpoint, Track S had proved only

\[
\text{spectral isolation}
\Rightarrow
\exists\kappa>0
\Rightarrow
\text{GOA robustness}.
\]

The present result upgrades that to

\[
\boxed{
\text{spectral isolation}
\Rightarrow
\kappa=\sigma_{\min}^{0}(P)
\Rightarrow
\text{explicit GOA robustness radius}.
}
\]

This is the precise operator-geometric version of the original proposed
`spectral isolation -> residual inverse -> GOA branch stability` idea.

## 7. Boundaries retained

- The zero-mass domain must have positive finrank for the final singular-value
  index to exist.
- The theorem gives the sharp Euclidean singular-value lower-gain constant, but
  the final TV bound still uses the uniform finite-dimensional conversion
  `‖v‖₁ <= sqrt(card S) ‖v‖₂`.
- Therefore the **Euclidean** denominator is canonical/sharp at this layer, but
  the displayed TV prefactor is not claimed globally optimal.
- Restricted residual injectivity remains an operator-isolation route to the
  selected stationary branch; no claim is made that every possible semantic
  residual inverse must arise from Euclidean spectral geometry.
- No frozen source theorem, counted generator, P-ID disposition, ledger count,
  or Track-H theorem changes.

## 8. Next pressure test

The most meaningful next Track-S question is no longer whether a spectral
constant exists.  It is whether the `sqrt(card S)` conversion can be improved
using the actual geometry of the zero-mass subspace or by working directly in
`L1`/TV operator geometry.

That should be treated as a separate norm-geometry checkpoint.  The current
module already closes the Euclidean singular-value certificate exactly.
