# Frozen snapshot resolvents, spectral laws and escaping first moments

## S1. Same selected snapshot, a stronger bounded spectral result

Fix u_i and the actual original self-adjoint finite-K snapshot
H_bulk,K(u_i) selected in ALL_SIGN_EVOLUTION A6. Set

    A_K=epsilon_K H_bulk,K(u_i), epsilon_K=log K/K,
    H_fast=-1/(2kappa), D(H_fast)=D(kappa^-1).

Freezing the coefficients in INITIAL_LAYER gives a genuine autonomous
group theorem

    exp(-is A_K)->exp(-is H_fast)=F_s

uniformly strongly on compact s windows. The proof uses the same
complete generator, source gap correction, original scalar terms,
half-line realization and dense limiting C5 family. It is not a new
choice of self-adjoint extension.

There is also a useful prepared rate for all s>=0. On a fixed compact
comparison support let

    h_K(kappa)=epsilon_K alpha_K(u_i)G_K(kappa)/kappa.

Its C^4 norm is uniformly bounded, and
||h_K+1/(2kappa)||_{C^4}=O(1/log K). Use phi_K(s)=exp(-is h_K)g and
eta_K=-alpha_K F_K^-1 Q A_ad,K(phi_K zeta tensor vacuum).
Direct differentiation gives

    ||phi_K(s)||_{H^4}+||partial_s phi_K(s)||_{H^4}
       <=C(1+s)^4,
    sum_{r<=2}||partial_kappa^r eta_K||+||partial_s eta_K||
       <=C(1+s)^4/sqrt(log K).

All constants are fixed profile/support/low-input constants. The exact
rescaled residual is

    i partial_s eta_K
      -epsilon_K L_K(v_0,K+eta_K)
      -epsilon_K alpha_K (A_eta phi_K)zeta tensor vacuum
      -epsilon_K alpha_K A_ad,K eta_K.

Since epsilon_K alpha_K=O(1/K), its norm is bounded by
C(1+s)^4/sqrt(log K). Duhamel, both endpoint corrections and the
phase replacement yield, for the actual C5 Psi_K,

    ||[exp(-is A_K)-F_s]Psi_K||
       <=C(1+s)^5/sqrt(log K), s>=0.                 (S.1)

This bound can exceed two at large s; it remains a valid bound.
The comparison vectors are in the accepted snapshot domain at every
finite s. Exact unitarity is sufficient; no confinement or global
energy-growth assumption on the exact orbit is made. This polynomial
all-s estimate is for the FROZEN autonomous snapshot, not for the
time-dependent original evolution on arbitrarily long windows.

## S2. Strong resolvent convergence and a prepared bound

For any self-adjoint A, the spectral theorem/Bochner integral gives

    (A-i)^-1=i integral_0^infinity e^-s exp(-isA)ds.

The sign is fixed by the scalar identity i/(1+i a)=1/(a-i).
Every input vector is allowed; the resulting vector lies in D(A).
Uniform strong group convergence on compact intervals and the
exponential tail show

    (A_K-i)^-1 -> (H_fast-i)^-1 strongly.

Thus A_K converges in strong resolvent sense to H_fast. Equation (S.1)
and integral_0^infinity e^-s(1+s)^5 ds=326 further give

    ||[(A_K-i)^-1-(H_fast-i)^-1]Psi_K||
       <=326 C/sqrt(log K).

For the fixed C5 limit vector add 2||Psi_K-Psi_infinity||=O(K^-1/2).
For Im z=b>0 replace 326 by
sum_{j=0}^5 binomial(5,j)j!/b^(j+1); the lower half-plane uses the reverse
group. These are analytic profile-dependent rates, not operator-norm
convergence or a practical numerical cutoff threshold.

## S3. Actual C9 spectral probability laws

Let rho_9,K be the actual C9 preparation, with the once-selected finite
initial mean Tr rho_9,K H_bulk,K(u_i)=E_* and fixed geometry density
n(kappa)=|g(kappa)|^2 supported in [a,b]. Its trace-normal limit is the
C5 rho_infinity. Define the spectral probability
mu_K(B)=Tr rho_9,K E_{A_K}(B). Strong resolvent convergence, finite-rank
approximation and rho_9,K->rho_infinity show convergence on C_0 spectral
tests. The limit has mass one, so tightness extends this to weak
probability convergence and all bounded continuous spectral tests:

    mu_K => mu_infinity,
    mu_infinity = pushforward of n(kappa)d kappa by -1/(2kappa).

Its support is contained in [-1/(2a),-1/(2b)].
This is an actual bounded spectral law of the complete snapshot,
not a spectrum of a projected Gaussian Hamiltonian.

## S4. The repaired mean does not pass to this normal limit

Despite the above convergence,

    integral E d mu_K =epsilon_K E_* ->0,
    integral E d mu_infinity =-I_1/2<0,
    I_1=integral n(kappa)/kappa d kappa.

The first moments are not uniformly integrable. More precisely, for
every fixed R>1/(2a), let clip_R(E)=max(-R,min(E,R)).
Its expectation converges to -I_1/2, while the full mean tends to zero.
Therefore

    integral [E-clip_R(E)] d mu_K -> I_1/2,
    liminf integral_{E>R}(E-R) d mu_K >=I_1/2,
    liminf integral_{|E|>R}|E| d mu_K >=I_1/2.

These are real escaping positive-tail moment bounds for this
preparation, even though the tail probability tends to zero.
The rare odd branch has probability ~1/(2log K) and a rescaled branch
energy separation of order log K, which explains the finite missing
mean without replacing the full spectral proof by branch means.

The predecessor C11 bound also gives

    liminf Var_{rho_9,K}(A_K)/log K >= I_1^2/2.

This is a mixed-state variance bound from the actual sector separation.
It is NOT a lower bound on quantum Fisher information. No stress
second moment, full constraint residual, uniform domain budget,
target geometry curvature or autonomous apparatus is recovered from
bounded spectral convergence.

## S5. Original pure C5: an exact second-moment excess

For the fixed regular pure C5 input, the exact high-vacuum/two/four
particle decomposition gives

    <A_K> -> -I_1/2,
    ||A_K Psi_K||^2 -> 3 I_2/4,
    Var(A_K) -> (3 I_2-I_1^2)/4,
    I_2=integral n(kappa)/kappa^2 d kappa.

The vacuum part tends to -Psi/(2kappa); the two-particle norm vanishes.
The four-particle raw norm is
integral n/kappa^2 [8(sum|c_j|^2)^2+16sum|c_j|^4].
Since sum|c_j|^2=K/8+O(1), sum|c_j|^4=O(1) and
epsilon_K alpha_K K->-2, its rescaled squared norm tends to I_2/2.
Only Psi_K in D(H_K) is required: the second spectral moment means
||H_K Psi_K||^2, not an asserted action of H_K^2.

The limiting spectral law has second moment I_2/4 and variance
(I_2-I_1^2)/4. Exactly I_2/2 is missing from the second-moment limit.
For every R>1/(2a), bounded spectral convergence of min(E^2,R^2)
and vanishing tail probability give

    integral_{|E|>R} E^2 d mu_C5,K -> I_2/2.

These C5 second moments are uniformly bounded, which DOES make its
first moments uniformly integrable. The failure is at the squared
moment; C9 has the different, stronger first-moment escape in S4.

For the PURE frozen family, the elementary pure-state identity
F_Q=4(||psi'||^2-|<psi,psi'>|^2)=4 Var(A_K)
gives F_Q,K->3I_2-I_1^2. The limiting pure layer family instead has
QFI I_2-I_1^2. Their excess is 2I_2. This also describes the initial
rescaled derivative of the actual nonautonomous pure family, not its
QFI at all later times or that of the mixed C9 state.

## S6. Verification scope

The paired script verifies the Laplace sign, the exact polynomial
integral, the scaling of the accepted variance bound, and an explicit
scalar rare-tail model illustrating (not replacing) the analytic
actual-model proof. No predecessor scientific executable or ODE runs.
