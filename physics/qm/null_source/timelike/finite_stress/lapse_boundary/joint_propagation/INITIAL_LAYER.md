# Complete propagation in a shrinking initial layer

## P1. Statement and unchanged input

Let epsilon_K=log(K)/K, and let F_s be multiplication by
exp[is/(2 kappa)] in the fixed bulk Hilbert space of the predecessor
N1 test. The complete original finite-K propagators, embedded with
identity on the unused tail, obey

    sup_{0<=s<=S} ||[Ucal_K(u_i+epsilon_K s,u_i)-F_s] psi|| -> 0

for every fixed vector psi and every finite S. The adjoints converge
uniformly strongly as well, and the two-time propagators tend uniformly
strongly to F_{s-r} for s,r in [0,S]. This is a genuine propagation
result, proved below using the entire generator. It is a shrinking
original-clock window, not a fixed positive original-u interval.

The original AE coefficients, U_0, ordering, half-line realization,
source evolution, bulk reference and endpoint phases are retained.
Use the exact connection, excitation gaps and fixed support hypotheses
of [ADIABATIC_CONNECTION](ADIABATIC_CONNECTION.md). No field mode
is projected out of the exact evolution.

## P2. A corrected comparison trajectory

Write ell=log K, d_K=G_K/kappa and

    v_0,K(u)=phi_K(u,kappa) zeta tensor vacuum,
    phi_K=exp[-i d_K integral_{u_i}^u alpha_K(v)dv] g(kappa),
    eta_K(u)=-alpha_K(u) F_K^-1 Q A_ad,K v_0,K(u),
    w_K=v_0,K+eta_K.

Thus i partial_u v_0,K=alpha_K d_K v_0,K. On
0<=u-u_i<=S ell/K, the integral of alpha is O(1/K); derivatives through
order four of d_K are O(K). The phase therefore has uniformly bounded
kappa derivatives through order four. In particular

    ||phi_K||_{H^4}<=C_S,
    ||partial_u phi_K||_{H^4}<=C_S K/ell.

The second bound follows from the exact equation
partial_u phi=-i alpha_K d_K phi and its kappa derivatives. It does
not differentiate an unspecified asymptotic error.

The inverse-gap estimate proves

    sum_{r=0}^2 ||partial_kappa^r eta_K||<=C_S/sqrt(ell),
    ||partial_u eta_K||<=C_S K/ell^(3/2).

Indeed partial_u eta has the two terms with alpha_K' and partial_u phi;
alpha_K'=-alpha_K^2/2 contributes only O(ell^-3/2).
The correction has at most four high particles and the original
compact kappa support. The finite-sector Gamma bounds give

    ||A_ad,K eta_K||<=C_S K/sqrt(ell).

Expanding this operator yields eta'', Gamma eta', Gamma' eta,
and Gamma^2 eta. The latter costs O(K); its output may contain eight
particles, which are included in the estimate.

Because F_K eta_K=-alpha_K Q A_ad,K v_0,K, the EXACT residual is

    (i partial_u-H_ad,K)w_K
       =i partial_u eta_K-L_K(v_0,K+eta_K)
        -alpha_K (A_eta phi_K) zeta tensor vacuum
        -alpha_K A_ad,K eta_K.

The d_K vacuum term has already canceled i partial_u v_0,K. Including it
again as -alpha_K P_0 A_ad,K v_0,K would be an error.
The complete two/four-particle off-diagonal source is canceled by
F_K eta_K, not discarded.

All low terms and original scalar coefficients remain in L_K.
For fixed regular low zeta,

    ||L_K v_0,K||<=C_S,  ||L_K eta_K||<=C_S/sqrt(ell),
    ||alpha_K A_eta phi_K||<=C_S/ell.

Consequently the residual integrated over the whole shrinking window
is at most C_S[ell/K+ell^-1/2]. Both endpoint corrections have norm
at most C_S/sqrt(ell).

## P3. Duhamel for the actual accepted propagator

For each finite K, T_K w_K is compact-smooth in kappa and Schwartz in
the finite source coordinates. It belongs to the accepted snapshot
domain, with the actual formal generator action. It is continuous in
the finite-K invariant energy space Q and C^1 in the slice Hilbert
space; its residual is Hilbert-valued and integrable.

The accepted ALL_SIGN_EVOLUTION theorem supplies the complete weak
unitary evolution in Q/Q*. Pair the trial with a backward exact
trajectory from a dense Q vector. The Q/Q* product rule, justified
by time mollification, gives the Duhamel identity, hence

    ||U_ad,K(u,u_i)w_K(u_i)-w_K(u)|| <= integral ||residual_K|| du.

Density extends this Hilbert-norm estimate to the complete evolution.
It does not require a compactly supported exact orbit, a common
full-field operator domain, or an assertion that the compact/Schwartz
tests are an operator core. Snapshot membership and the weak evolution
already proved in the predecessor suffice.

Adding both eta endpoints compares with the actual intended initial
v_0,K(u_i)=g zeta tensor vacuum. Uniformly on the comparison support,

    d_K integral_{u_i}^{u_i+s ell/K} alpha_K(v)dv
       =-s/(2 kappa)+O(ell^-1).

Here alpha_K' is O(ell^-2), so freezing it over this interval costs
O(K^-2) before multiplication by d_K. The phase commutes with the
controlled W_K and T_K. For the actual C5 bulk vector Psi_K,

    sup_{s in [0,S]} ||Ucal_K(u_i+s ell/K,u_i)Psi_K-F_s Psi_K||
       <=C_S[ell^-1/2+ell/K].                         (P.1)

The constants are finite and can be bounded from fixed profile
seminorms, support parameters and low moments. More precisely, with
the support, J, S and the regular low input fixed, the entire trial,
correction and residual construction is linear in g, and (P.1) has
right side C_{I,J,S,zeta} ||g||_{H^4}[ell^-1/2+ell/K]. The constant
C_{I,J,S,zeta} is independent of the profile within that fixed support.
This explicit uniform dependence justifies the varying smooth phase
profiles used in DEPHASING_CONTROL and GAUSSIAN_CONTROL. No practically usable
numerical cutoff threshold is asserted. For a fixed regular low
mixture, the same proof uses its Hilbert-Schmidt purification and
finite H_0,low/D_low norm budget.

## P4. Density, adjoints and two-time evolution

For every fixed J, g and zeta, the C5 input converges to

    Psi_infinity^{J,g,zeta}(kappa)
       =g(kappa) e^{i Xi_infinity^J(kappa)}
        W_low^J(kappa)zeta tensor phi_{kappa,[J,infinity)}.

Its tail norm error is O(K^-1/2). The limiting vectors have dense linear
span in the fixed bulk Hilbert space. To prove this, start from a
compact smooth geometry packet times a finite-prefix Schwartz source
vector with the remaining modes in the omega vacuum. Such vectors
span a dense set. Choose J above the prefix and support threshold.
Uniformly on that support, the conditional real tail differs from
the omega vacuum by O(J^-1/2). Invert the fixed fiberwise unitary
e^{i Xi_infinity^J} W_low^J on the desired low amplitude, and approximate
the resulting L^2(I;H_low) amplitude by a finite sum
sum_i g_i(kappa) zeta_i, with smooth compact g_i and Schwartz zeta_i.
The controlled map and normalized tail attachment are isometries.

First choose J and this finite approximation for the desired accuracy;
hold them fixed while K tends to infinity. No uniform-in-J estimate
is used. Equation (P.1), the C5 tail and the bound ||Ucal_K||=||F_s||=1
give uniform strong convergence on this dense set and hence on every
fixed Hilbert vector.

The F_s family is strongly continuous by dominated convergence.
The orbit {F_s* psi:0<=s<=S} is compact. A finite-net argument and

    (Ucal_K* - F_s*)psi = Ucal_K* (F_s-Ucal_K)F_s*psi

give uniform strong convergence of the adjoints. Exact composition
then gives the two-time limit F_{s-r}, including the reverse direction.
This does not require F_s to preserve the global old energy domain.

## P5. Direct failure of the original uniform initial window

For s>0, F_s has no eigenvector with eigenvalue one: the kappa level
set of exp[is/(2 kappa)]=1 is countable and has measure zero.
Therefore ||(F_s-I)psi||>0 for every nonzero fixed psi.

An explicit Cauchy comparison is K=N^2 versus L=N, at the same
original elapsed time t_N=s epsilon_{N^2}. The L-rescaled elapsed
time is exactly t_N/epsilon_N=2s/N. Thus

    Ucal_{N^2}(u_i+t_N,u_i)psi -> F_s psi,
    Ucal_N(u_i+t_N,u_i)psi -> psi.

Their norm gap has a strictly positive limit for every nonzero psi.
The predecessor's uniform strongly continuous ordinary-u initial
window is rejected in this fixed representation. This conclusion is
stronger than a divergent initial derivative.

For normal density matrices, the complete result and noninvariance
are established in [RESCALED_KERNEL](RESCALED_KERNEL.md). The fixed
bounded coherence witness in [BOUNDED_WITNESS](BOUNDED_WITNESS.md)
shows that the obstruction is observable at the density level and is
not merely an irrelevant global phase.

No conclusion is asserted here about a fixed positive original-u
time, a selected interior noncompact readout, all weaker topologies, or
a different action/reference/quantization. Multiplication observables
B(kappa) commute with F_s and cannot by themselves detect this layer.

## P6. Subsequent interior closure

INTERIOR_COLLAPSE uniformly resets this complete estimate throughout a
fixed clock chart. Its shift/dense-range proof then rejects the nonzero
fixed-original-time N3 tested kernel, including interior tests.
ORDERING_SWEEP extends that specific obstruction to every permitted
cutoff-dependent ordering, constant in u at each K, in the same
Friedrichs family. These stronger results use complete propagation,
not the initial derivative alone.
