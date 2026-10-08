# SISC C5 — Common-2D Strict Spectral Rejection

Status: **LOCAL LEAN-CHECKED CONDITIONAL REJECTION**.
Scientific C5 port remains OPEN; no independently measured physical Pi/Phi.

## Same-Jacobian bridge

`SISCJoint2DRejection.lean` proves the missing *terminal* composition.
`third_singular_zero_of_rank_le_two` converts arbitrary finite-matrix rank ≤2
into an exact zero third Euclidean singular value (zero-index 2), with the
matrix rank and operator using the **same** represented linear map.

`reject_exact_common_twoD_from_same_jacobian` consumes:

1. one fixed budget point `B`, single vertically stacked response array `m`;
2. the **same** stacked Jacobian `J = stackedJacobian m B` used in the Core
   rank and singular-value theorems;
3. a genuinely certified operator 2-norm error bound
   `‖Jhat - J‖ ≤ eta`;
4. the prespecified strict rejection event `eta < sigma_3(Jhat)`.

It concludes that no single common differentiable 2D latent `z` (in the
declared budget coordinates) can factor all measured responses `m` through
environment-dependent `g` with the Core's differentiability conditions.
No `SameObject` or Pi/Phi mechanism-identification implication is invoked.

## Exact zero versus practical tolerance

`reject_practical_twoD` handles the **different** predeclared null
`sigma_3(J) ≤ tau0`. It rightly requires
`sigma_3(Jhat) > tau0 + eta`. A legacy exact-null reject (`sigmaHat > eta`)
does NOT suffice to reject this practical null when `tau0 > 0`.

For example, `(sigmaHat,eta,tau0)=(0.12,0.10,0.15)` rejects the exact-zero
null, but does not reject the practical-tolerance null. A reject of one
must never be represented as rejection of the other.

## Remaining evidence obligations

- Independently specified physical resource/information measurements and
  their units/gauges; repeatable interventions and rank estimation protocol.
- Predeclared normalization, same budget, finite-difference bandwidth,
  dependence/drift calibration, multiplicity and global alpha budget.
- Held-out 2-drive, noncommon 2D and true 3-drive controls with power curves;
  a low-rank result is compatibility, not mechanism identification.
- Independent review of the exact-machine-gate and any real-domain data.

The new proof and boundaries do not mutate frozen P-DDH-04/P-DDH-05,
the four compression generators, or the Core 106/106 counted coverage.
