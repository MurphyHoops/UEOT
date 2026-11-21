# S. A conditional, noncommuting error budget for the next completed action

This theorem states a quantitative NEXT-GATE condition. It does not
assert that the new counterterms have already met it.

## S1. Assumptions that must be derived, not assumed away

Suppose the completed action and a controlled reduction actually
produce the SAME selected critical spectral branch on one common
physical Hilbert space, with bounded self-adjoint norm-continuous
T0(u)=E_c+f(u)K and T1=T0+delta T. Require both spectra and the
connecting interpolation to lie in the certified E_c+[0,1e8] slab.
The shared preparation here is on the REDUCED physical slice.
If R1 differs from R0, the corresponding raw initial kernels
R_j^-1 rho R_j^-1 differ; this is not automatic preservation of
one unreduced bare initial density. A fixed-bare comparison would
need its additional normalization/transport estimate.
Also retain the SAME normal preparation isometry W and terminal
effect 0<=F<=I. No commutation of T0 and delta T is assumed.

MIXED_ACTION has NOT established these reduction/common-space
hypotheses. Compressing a correction as Pi deltaT Pi is a changed
operator, not proof that the actual correction preserves the band.
Closure of the actual reduced space, or a separate leakage bound,
must be established first. A different phase space or constraint ordering must
first be handled on its own terms. C1 regularity is additionally
needed when expanding the raw normal-form connection.

## S2. Operator square roots, rather than a scalar derivative shortcut

For each u let
d_j=[B²-4a_c(T_j-D)]^(1/2),
kappa_j=[(-B-d_j)/(2a_c)]^(1/2).
If d_j>=d_min I and kappa_min I<=kappa_j<=kappa_max I,
the Sylvester equation and its convergent positive-operator
integral solution give

 ||d1-d0||<=2a_c ||delta T||/d_min,
 ||kappa1-kappa0||<=||delta T||/(2kappa_min d_min).

The cubic telescoping identity then yields

 ||h1-h0||<=L(u)||delta T||,
 L(u)=[2|B|+12c kappa_max²]/[2kappa_min d_min].         (S1)

This does not misuse the scalar h_E derivative as a general
operator-Lipschitz theorem. Both bounded self-adjoint families
have their actual time-ordered unitaries, and Duhamel gives

 delta_U=||U1-U0||<=integral_J L(u)||delta T(u)||du.       (S2)

No trial trajectory or mean-energy replacement occurs.

## S3. What this controls operationally

For E_j=W*U_j*F U_jW, pure-state trace distance, followed by
normal-state/reference extension, gives

 ||E1-E0||<=delta_U,
 ||E1-P_high||<=epsilon_0+delta_U.                     (S3)

For the complete two-record classical channel the corresponding
diamond-norm bound is at most 2delta_U.
If preparation or terminal effects change, their errors must be
added separately.

A noncommuting delta T may destroy source-code QND and total-K
conservation. Equation (S3) does NOT transport the old geometry
threshold, stress map or coherent-state disturbance theorem.
The full admitted K hull has spectrum through the threshold;
the empty interval of the PREPARED input classes is not a global
spectral gap to which a projection theorem can silently be applied.

The certificate bounds B_budget=integral_J L(u)du on 200 exact
cells and reports sup||delta T|| sufficient for extra record errors
.01 and .05. It explicitly checks that these budgets remain far
inside the larger admitted energy slab. These are MODEL conformal
energy units and conditional sufficient bounds; they do not
measure actual loop corrections or determine finite EFT coefficients.

The next completed theory must prove this kind of budget, or
replace it with a sharper valid estimate, before inheriting the
present apparatus calibration.
