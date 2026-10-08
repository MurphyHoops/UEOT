# SISC path-stability upgrade — two different error regimes

Status: **LOCAL LEAN-CHECKED CONDITIONAL STABILITY**. Identity and actual
long-run persistence remain unestablished.

The new `SISCPathStability.lean` establishes that the mechanistic formation
budget is **exactly**

`tau_n = tau_0 + n * (deltaWorld + deltaParent)`.

In contrast, when the realized transport has a separately calibrated strict
Lipschitz contraction factor `0 ≤ M < 1` and its local binding defect is
nonnegative `deltaBind`, the n-step realized tracking error obeys

`D_n ≤ deltaBind / (1 - M)` for **every finite n**.

`contracted_finite_mechanism_realization_bound` combines the latter with the
SI-3→SI-4 formed-history bridge. Both the formed-path witness and uniform
realized bound are part of the conclusion.

## Interpretation and scientific boundary

Even excellent long-run realized tracking can coexist with linearly growing
formation tolerance. If `deltaWorld + deltaParent > 0`, eventually the
registered parent response error margin may cease to discriminate clones or
competing candidates despite uniform realized metric error. Stable
*representation* is not automatically stable *identity*.

This is not a theorem that every physical transport contracts, that a
universal `M < 1` exists, that forming objects remain viable, or that a
stationary GOA exists. The strict contraction and nonnegative defect are
independent application-side measurements to be estimated/falsified.

For publishable applications, preregister both the finite-horizon formation
margin and the realized transport tolerance; an apparently stable numerical
response alone must not silently override a failed formation/identity gate.
