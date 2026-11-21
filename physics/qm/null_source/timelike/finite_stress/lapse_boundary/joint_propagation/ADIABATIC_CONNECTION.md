# Exact high-mode connection and the inverse-gap correction

## A1. Original complete generator and one declared comparison support

All formulas use the fixed bulk embedding of
[NEXT_PROPAGATOR_TEST](../joint_feedback/NEXT_PROPAGATOR_TEST.md).
Keep the original potential U_0, AE subtraction coefficients, ordering
eta>=-1/4, and selected Friedrichs realization. In the exact W frame,

    Hbar_K(u) = alpha_K A_eta + kappa^-1 H_0,K + D_K
                +d_0,K/kappa+d_1,K kappa+d_3,K kappa^3,
    A_eta = P_kappa kappa^-1 P_kappa +(eta-3/4)kappa^-3,
    alpha_K=(2 g_K)^-1, g_K=G(u)-Harmonic(K)/4,
    G(u)=(19+15 ell_0+30u)/120.

Thus alpha_K=-2/log K+O((log K)^-2) uniformly on each fixed compact clock
patch, and the exact u derivative is alpha_K'=-alpha_K^2/2. All source
zero modes and low modes remain in the generator. There are 2 k^2 real
oscillators per shell; omega_k=sqrt(k^2-1) for k>=2.

Fix a compact support I=[a,b] in (0,infinity), a slightly larger compact
I_ext, a smooth compact profile g, a fixed low-mode Schwartz vector zeta,
and one integer J with J^2>1+b_ext^2. These are fixed before K tends to
infinity. Put Omega_k=sqrt(k^2-1-kappa^2) on I. Choose a smooth bounded
function varrho equal to kappa near I and 0<=varrho<=b_ext, and use
Omega_tilde,k=sqrt(k^2-1-varrho^2)>0 outside I.

The finite-K product T_K of the actual chirp exp(-i kappa Q_high),
the real squeezes with frequencies Omega_tilde,k, and the Berry scalar
phase Theta_K is a global unitary. Choose Theta_K' as the sum over real
modes of 1/(4 Omega_tilde,j). The explicit formulas below are needed
only on I. The exact evolution is T_K* Ubar_K T_K globally.
Comparison vectors remain supported in I; the exact orbit is not
assumed to do so. Neither W_K nor T_K is required to have a separate
global limit.

## A2. Exact connection and all excitation sectors

On I, in the fixed oscillator basis, with primes now kappa derivatives,

    T_K* P_kappa T_K=P_kappa+Gamma_K,
    Gamma_K=sum_j [c_j a_j^dagger^2+conj(c_j) a_j^2+d_j n_j],
    c_j=-1/(4 Omega_j)-i kappa/(4 Omega_j^2),
    d_j=-1/(2 Omega_j).

The Berry choice sets the vacuum mean to zero. Directly,

    G_K=||Gamma_K vacuum||^2
       =2 sum_j |c_j|^2
       =(1/4) sum_{k=J}^K k^2(k^2-1)/(k^2-1-kappa^2)^2
       =K/4+O(1).

The remainder and its needed kappa derivatives are uniformly bounded
on I. In particular derivatives 1 through 4 of G_K are O(1), while all
derivatives 0 through 4 of d_K=G_K/kappa are O(K).

Write F_K=sum_j (Omega_j/kappa)n_j, P_0=|vacuum><vacuum| on high
modes and Q=1-P_0. On the comparison support the COMPLETE transformed
generator is exactly

    H_ad,K=F_K+L_K(u)+alpha_K A_ad,K,
    A_ad,K=(P_kappa+Gamma_K) kappa^-1 (P_kappa+Gamma_K)
            +(eta-3/4)kappa^-3.

L_K contains kappa^-1 H_0,low+D_low and the convergent scalar remainder
from the original d_0,d_1,d_3. The subtraction is exactly C2 of
[CORRELATED_GAUSSIAN](../joint_feedback/CORRELATED_GAUSSIAN.md):
the high ground shell term is k^2 sqrt(k^2-beta), beta=1+kappa^2,
and the subtracted polynomial is
k^3-beta k/2-beta^2/(8k). The leftover is O(k^-3), with each fixed
kappa derivative locally summable. No counterterm is added here.
L_K is bounded on the declared fixed low Schwartz input with its
required moment budget; it is not a bounded operator on the whole
low-mode Hilbert space.

For v=phi(kappa) zeta tensor vacuum, put Cdagger=sum_j c_j a_j^dagger^2.
Expanding the actual differential expression gives

    P_0 A_ad,K v = [A_eta phi +(G_K/kappa)phi] zeta tensor vacuum,
    Q A_ad,K v = zeta tensor [
        sum_j r_j(phi) a_j^dagger^2 vacuum
        + kappa^-1 phi (Cdagger)^2 vacuum],
    r_j(phi)=-2i kappa^-1 c_j phi'
             -i(kappa^-1 c_j)'phi+2 kappa^-1 d_j c_j phi.

Both the two-particle and four-particle sectors are kept.

## A3. Exact inverse-gap norms and uniform estimates

The two sectors are orthogonal. Their exact norms after the excitation
inverse are

    ||F_K^-1 sum_j r_j a_j^dagger^2 vacuum||^2
        =sum_j kappa^2 |r_j|^2/(2 Omega_j^2),

    ||F_K^-1 kappa^-1 (Cdagger)^2 vacuum||^2
        =(3/2) sum_j |c_j|^4/Omega_j^2
          +4 sum_{j<l}|c_j c_l|^2/(Omega_j+Omega_l)^2.

The diagonal coefficient follows from (a^dagger)^4 vacuum=sqrt(24)|4>;
the cross coefficient follows from
2 a_j^dagger^2 a_l^dagger^2 vacuum=4|2_j,2_l>.
These are finite-mode identities, before taking any limit.

Let q=1-(1+b_ext^2)/J^2>0. Then Omega_k>=sqrt(q)k,
|c_j|<=1/(4qk), |d_j|<=1/(2sqrt(q)k),
partial_kappa c_j=O(k^-2) and partial_kappa^2 c_j=O(k^-3).
For each fixed particle budget n, bosonic pair creation/annihilation
bounds therefore give

    ||Gamma_K restricted to N<=n|| <= C_n sqrt(K),
    ||partial_kappa Gamma_K||+||partial_kappa^2 Gamma_K|| <= C_n.

For example pair creation is at most
sqrt[(n+1)(n+2)] ||c||_2, annihilation at most
sqrt[n(n-1)] ||c||_2, and the number part at most n sup_j|d_j|.
The square-sum of c is O(K), while the derivative square-sums converge.

For each two/four-particle excitation, kappa derivatives of its inverse
gap through order two are bounded by a fixed constant times that
inverse gap on I. This follows by differentiating
kappa/(sum_j n_j Omega_j), using Omega_j>=sqrt(q) k_j and kappa>=a.
There is no inverse on the vacuum.

After shell multiplicities, the two-particle inverse norm is controlled
by sum k^-2. The four-particle cross norm is controlled by

    sum_{k,l=J}^K (k+l)^-2 <= 1+log(2K),

up to a fixed constant; the diagonal is summable. The same estimates
hold after two kappa derivatives of the coefficients and gaps. A safe
sufficient profile bound is consequently

    sum_{r=0}^2 ||partial_kappa^r [
         F_K^-1 Q A_ad,K(phi zeta tensor vacuum)]||
        <= C sqrt(1+log K) ||phi||_{H^4(I)} ||zeta||.

The constant is independent of K for the fixed support, J, and low
input. It is not declared uniform in J, the support, or the low moments.

## A4. Verification boundary

The paired script independently expands a finite Fock dictionary to
check all particle sectors and gap factors, verifies the differential
connection and shell identity symbolically, and checks the shell
bounds with an outward interval example. The full asymptotic bound
uses the displayed analytic sums and domain argument; it is not an
infinite-field numerical integration or a machine formal proof.
