# Topology-Changing GOA Zero-Mass Norm Sharpness Audit

Status: **LOCAL CANDIDATE / TRACK S / UNCOUNTED**

Module:

`UEOT/V3/Compression/TopologyChangingGoaZeroMassNormSharpness.lean`

## 1. Question

The sharp singular-value GOA robustness theorem has the form

\[
D_{TV}(\mu_*,\hat\mu)
\le
\frac{\sqrt{|S|}\,\varepsilon}{\sigma_{\min}^{0}(P)}.
\]

The denominator is now the actual smallest valid singular value of the
zero-mass residual operator.  The remaining generic factor comes from

\[
\|v\|_1\le\sqrt{|S|}\,\|v\|_2.
\]

This checkpoint asks whether the zero-total-mass constraint alone allows that
`sqrt(card S)` factor to be uniformly improved.

## 2. Balanced zero-mass witness

For every `m > 0`, take the state space

\[
S=\operatorname{Fin}(m)\sqcup\operatorname{Fin}(m)
\]

and define a signed vector equal to `+1` on the left half and `-1` on the right
half.

The module proves:

\[
\sum_x v_x=0,
\qquad
\|v\|_1=2m,
\qquad
\|v\|_2^2=2m.
\]

Hence

\[
\boxed{
\|v\|_1=\sqrt{|S|}\,\|v\|_2.
}
\]

The theorem is `balancedSign_saturates_l1_l2`.

## 3. Exact optimality result

`sqrt_card_isLeast_zeroMass_l1_l2_constant` proves more than saturation of a
single inequality.  It identifies the least uniform constant on this entire
zero-mass vector space:

\[
\boxed{
\sqrt{|S|}
=
\min\left\{
C:\forall v,\ \sum_xv_x=0
\Rightarrow
\|v\|_1\le C\|v\|_2
\right\}.
}
\]

This holds for every positive even state cardinality represented by
`Fin m ⊕ Fin m`.

## 4. Consequence for Track S

The `sqrt(card S)` term in the generic Euclidean-to-TV route is therefore not
merely an artifact of a loose Cauchy--Schwarz proof.  On an infinite family of
zero-mass state spaces it is exactly the optimal state-count-only constant.

Thus there is no honest theorem of the form

\[
\|v\|_1\le c(|S|)\|v\|_2
\]

valid for all zero-mass vectors with

\[
c(2m)<\sqrt{2m}
\]

for every positive `m`.

This closes the proposed generic norm-factor optimization route on even state
sizes.

## 5. What may still improve

Further GOA robustness improvements remain possible only by adding information
not used in this checkpoint, for example:

- kernel-specific geometry of the residual image;
- support restrictions on admissible signed-law perturbations;
- a direct `L1`/TV minimum-gain certificate for the residual operator;
- structural sparsity or symmetry that reduces the actually reachable
  zero-mass directions.

Those are legitimate stronger-data routes.  They should not be conflated with
an impossible universal improvement from zero-mass alone.

## 6. Boundaries retained

- The exact optimality theorem is established on all positive even-cardinality
  model spaces `Fin m ⊕ Fin m`; it does not claim the same closed-form constant
  is optimal for every odd cardinality.
- This is a norm-geometry boundary theorem, not a new UEOT generator.
- It does not alter the sharp Euclidean singular-value theorem itself.
- No frozen source theorem, P-ID disposition, counted mapping, generator count,
  ledger row, or Track-H theorem changes.

## 7. Next Track-S direction

The next meaningful quantitative target is kernel-specific rather than purely
dimension-specific: formalize a direct `L1`/TV residual minimum gain or a
restricted-support norm constant, then compare it against the Euclidean
spectral certificate on concrete finite kernels.
