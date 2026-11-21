# The fixed-test obstruction survives every allowed ordering sequence

## O1. Scope and rescaled comparison

The preceding results used a fixed eta>=-1/4. This page permits ANY
cutoff-dependent sequence eta_K>=-1/4 (constant in u at each K), with the SAME Friedrichs
principal realizations and finite-K existence class already established
in ALL_SIGN_EVOLUTION. The original AE/action coefficients, measure,
bulk identification and endpoint transport remain fixed. Other
boundary realizations, measures or counterterms are not covered.

Set

    M_K=K+max(eta_K,0), epsilon_tilde,K=log K/M_K,
    lambda_K=K/M_K in (0,1].

Then eta_K/M_K=1-lambda_K+O(K^-1), uniformly over the permitted
negative tail because eta_K>=-1/4. Every subsequence has a further
subsequence with lambda_K->lambda in [0,1].

Use a fixed reference ordering eta_0=0. The exact adiabatic expression is

    A_ad,etaK=A_ad,eta0+(eta_K-eta_0)kappa^-3.

The added ordering term is a scalar in the high source sector. It
contributes to the vacuum phase but EXACTLY drops out of
Q A_ad,etaK(phi tensor vacuum).

## O2. A uniform-in-ordering full-generator estimate

Use the same global finite-K frame and fixed regular C5 input.
In the comparison phase replace d_K by

    b_K(kappa)=G_K/kappa+(eta_K-eta_0)kappa^-3.

Its C^4 norm on the fixed support is O(M_K). On a window
0<=u-u_0<=S log K/M_K, the phase derivatives through order four
remain uniformly bounded. The profile time derivative has H^4 norm
O(M_K/log K).

The corrector is still

    eta_corr,K=-alpha_K F_K^-1 Q A_ad,eta0 v_0,K.

It has H^2 kappa norm O((log K)^-1/2), independent of eta_K, and
time derivative norm O(M_K/(log K)^(3/2)). The complete operator
acting on it is bounded by

    ||A_ad,etaK eta_corr,K||
       <=C(K+|eta_K|+1)/sqrt(log K)
       <=C' M_K/sqrt(log K).

Multiplication by alpha_K and integration over log K/M_K gives the
same O((log K)^-1/2) residual. The unchanged low/scalar L_K cost is
O(log K/M_K). The bare vacuum profile term uses A_eta0; the new
ordering scalar is already in the phase and is not counted twice.

Only actual unitarity at each finite K and compact/Schwartz snapshot
membership are used in Duhamel. No uniform-in-eta energy-space bound
or common full-field operator domain is assumed. Thus on any
lambda_K->lambda subsequence the complete uniform-reset limit is

    U_K(u_0+epsilon_tilde,K s,u_0)->F_s^lambda,
    F_s^lambda=exp[i s a_lambda(kappa)],
    a_lambda=lambda/(2kappa)+2(1-lambda)/kappa^3.

The prepared error is bounded by
C_S/sqrt(log K)+C_S|lambda_K-lambda|+C_S log K/M_K.
The dense-span and adjoint arguments are unchanged. One may also use
the full-sequence moving comparison F_s^{lambda_K}; compactness of
the (s,lambda) orbit controls its adjoints.

## O3. No allowed ordering tuning restores the fixed-test gate

For every lambda in [0,1],

    a_lambda>0,
    a_lambda'=-lambda/(2kappa^2)-6(1-lambda)/kappa^4<0.

Thus every nontrivial F_s^lambda has null phase level sets, no
eigenvalue-one vectors and no nonzero positive trace-class invariant
operator. The direct shift/dense-range proof of INTERIOR_COLLAPSE
applies on each lambda-convergent subsequence. It forces
B_K(h)->0 strongly and T_K X->0 for fixed original-clock tests there.

If the full sequence failed this convergence for some fixed test,
a subsequence would have a norm gap bounded below. Extracting a
lambda-convergent further subsequence gives a contradiction.
Therefore the full sequence obeys

    T_K X ->0

for EVERY allowed eta_K sequence. Its state-independent and all
normal-prepared fixed-test kernels have zero limit. The same
subsequence argument excludes trace-normal L^1 histories and
positive fixed-time averaged normal limits.

This closes ordering retuning as a repair within the declared family.
It does not prove an ordering-independent theorem over all quantum
gravity constructions. The mathematical singularity at eta=-1/4
is handled by the previously selected closed Friedrichs form, not
by splitting divergent kinetic/potential integrals.

The executable checks verify the phase coefficient, parameter
regimes and strict derivative sign. The all-ordering domain and
propagation result is the analytic argument O1-O3 tied to the
actual finite-K existence theorem.
