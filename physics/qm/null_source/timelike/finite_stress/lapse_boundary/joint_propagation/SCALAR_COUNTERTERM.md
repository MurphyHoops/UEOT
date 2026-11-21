# Leading scalar changes: classification, a concrete candidate, and its action cost

## C1. A conditional classification, not an adopted subtraction

Consider explicitly a DIFFERENT generator H_ad,K+V_ct,K(u,kappa).
Assume it has an actual finite-K unitary propagator in the same
comparison Hilbert space, and that V_ct,K is a real scalar with

    v_K(s,kappa)=epsilon_K V_ct,K(u_i+epsilon_K s,kappa)
       ->v(kappa)

uniformly for s in [0,S] in C^4(I), for every compact I in (0,infinity).
Here epsilon_K=log K/K and v is real C^4_loc. Local coefficient
convergence alone is not a self-adjointness theorem; existence is a
premise unless separately supplied for the explicit candidate.

Use the original gap correction with the phase

    phi_K=exp{-i integral[alpha_K d_K+V_ct,K]du} g.

The C^4 bound keeps its profile budget bounded. The complete residual
gains -V_ct,K eta_K, whose integrated norm is O((log K)^-1/2).
The same density argument as INITIAL_LAYER gives

    U_K^ct(u_i+epsilon_K s,u_i)
       ->F_s^v=exp{-is[v(kappa)-1/(2kappa)]}

uniformly strongly, with uniform strong adjoints, on compact rescaled
windows. On each fixed regular input the error is at most
C_S/sqrt(log K)+S delta_K+O(log K/K), where
delta_K=sup_s||v_K(s)-v||_{C^4(I)} tends to zero.

For the leading layer to leave every compact coherent density
unchanged, w=v-1/(2kappa) must be constant. If not, a profile supported
where w has different values has a strict phase-overlap loss at some
small s. Conversely a constant w is only a global phase at equal time.
Thus the necessary scalar form is

    v(kappa)=1/(2kappa)+c.

The original phase-fixed unitary gate requires c=0; a nonzero c also
changes a two-time kernel by exp[-ic(s-t)]. Removing that phase requires
an explicit clock/constraint energy-reference convention. This
classification closes only the FIRST layer. It proves no fixed-u
continuum or renormalization permission. The frozen original model
has V_ct=0 and is not changed anywhere in this cohort.

## C2. An explicit reference-vacuum scalar candidate

For the fixed omega vacuum of the nonzero source modes k=2,...,K,
let Q_osc,K=sum q_j^2/2 and

    nu_K=Var_omega(Q_osc,K)
        =sum_{k=2}^K k^2/[4(k^2-1)]
        =K/4-1/16-1/(8K)-1/[8(K+1)].

The two normal zero modes are retained in the original generator;
they are not assigned a nonexistent oscillator vacuum in this formula.
Consider the changed potential

    V_ct,K^nu(u,kappa)=-alpha_K(u)nu_K/kappa.

It depends on the fixed reference vacuum and K, not on the chosen
profile or a prepared expectation. It is a smooth change of the d_0(u)
coefficient on each fixed g_K!=0 clock patch. The finite-K existence
class of ALL_SIGN_EVOLUTION still applies: the derivative principal
part and the half-line realization are unchanged, and the extra
kappa^-1 coefficient is covered by the same energy comparison.
No old theorem executable is rerun.

Since epsilon_K V_ct,K^nu->1/(2kappa) in local C^4, this candidate
has rescaled full propagator limit I. Its SCALED frozen snapshot
epsilon_K H_K^nu(u_i) has strong resolvent limit zero. This is a controlled result for a changed model;
it is not acceptance of a new physical counterterm.

Scalar subtraction is not the complete finite-K Wick expansion.
With delta Q=Q_osc,K-<Q_osc,K>_omega,

    (delta Q)^2
       =:Q_osc,K^2:_omega
        +sum_j [1/(2omega_j)]:q_j^2:_omega+nu_K.

The linear operator contraction remains. This identity follows from
q_j^4=:q_j^4:+6 v_j:q_j^2:+3v_j^2,
q_i^2 q_j^2 normal ordering for i!=j, and v_j=1/(2omega_j).
Calling only the scalar removal 'the full Wick renormalization'
would omit an actual operator term.

## C3. The candidate cannot be absorbed by the frozen action parameters

The original action and coefficient formulas give

    g_K(u)=g_K(0)+u/4,
    d_0=V_0 A^4 U_0 e^{4u}-(3V_0 A^2/2)e^{2u}
         -u/8-c_an-C_rad,K.

The derivative principal coefficient is 1/(2g_K). A change that is
ONLY the proposed scalar potential must therefore keep g_K fixed.
Changing ell_0/g_K changes the principal part and the linked d_1,d_3
terms; it is not this scalar-only repair.

Even if constant U_0 and constant radiation/anomaly offsets were
allowed to vary, with geometry and the other coefficients fixed,
their d_0 shift has form A e^{4u}+B. The required shift is

    f_K(u)=-nu_K/[2g_K(u)].

The former obeys f''-4f'=0, whereas the latter gives

    f_K''-4f_K'
       =-nu_K[1+8g_K]/(16g_K^3),

which is not identically zero on any open clock interval.
Thus matching at a single slice cannot be promoted to absorption
on a common history. More generally a fixed finite combination of the
existing exponential/polynomial coefficients cannot equal the
nonzero reciprocal affine function on an open interval, by analytic
continuation and its pole. This is a fixed-family exclusion, not a
classification of every possible extended action.

## C4. The new lapse action and its mandatory rows

An exact homogeneous action producing this changed potential is

    delta S_K=integral d eta N r_K(u),
    r_K(u)=alpha_K(u)nu_K=nu_K/[2g_K(u)].

Its canonical constraint shift is delta C_K=-r_K, so dividing by
kappa produces precisely V_ct,K^nu. It has NONZERO interior rows

    delta Gamma_N=r_K,
    delta Gamma_u=N r_K',
    r_K'=-nu_K/(8g_K^2), r_K''=nu_K/(16g_K^3).

The mixed contact is delta Gamma_N/delta u=r_K'; the u-u contact
is N r_K''. These must be included on both CTP branches. A genuine
total derivative has zero interior Euler--Lagrange rows, so this
candidate is not the old endpoint canonical rewrite.

The extra action is consistent with its own homogeneous time Ward
identity: u' delta Gamma_u-N(delta Gamma_N)'=0, where the prime in
this identity denotes the original eta derivative. It must not be rejected
by falsely claiming that it violates that identity. It changes the
original AE/action density and pressure rows. The four-dimensional
local covariant origin of this new u-dependent potential is not given.

## C5. A remaining second moment after canceling the first layer

For the changed nu candidate and a fixed regular pure C5 input,
the exact vacuum/two/four-particle decomposition gives

    Var_{Psi_K}[epsilon_K H_K^nu(u_i)] -> I_2/2>0,
    I_2=integral |g(kappa)|^2/kappa^2 d kappa,

although its bounded spectral law tends to delta_0 and its mean
tends to zero. The vacuum part is O(1) before multiplication by
epsilon_K because G_K-nu_K=O(1); the two-particle rescaled part
vanishes. The four-particle norm is exactly

    ||kappa^-1 g(Cdagger)^2 vacuum||^2
      =integral |g|^2/kappa^2 [
          8(sum_j |c_j|^2)^2+16 sum_j |c_j|^4]d kappa.

Since sum|c_j|^2=K/8+O(1), sum|c_j|^4=O(1), and
epsilon_K alpha_K K->-2, its rescaled norm squared tends to I_2/2.
Only membership in D(H_K) is needed: the spectral second moment is
||H_K Psi_K||^2, not an asserted application of H_K^2 to the vector.
This candidate cancels the first layer but does not close the
second-moment gate. A kappa-dependent potential is not a constant
energy shift, so its variance must be recalculated, as above.

## C6. Static virtual correction: useful but not a next-time theorem

In this section G(u)=C(u)/120=(19+15 ell_0+30u)/120
=g_K(u)+Harmonic(K)/4. This scalar coefficient is distinct from
the kappa-dependent vacuum metric G_K(kappa).

Let R_4=kappa^-1(Cdagger)^2 vacuum. The exact inverse-gap form is

    <R_4,F_K^-1 R_4>
      =kappa^-1[6 sum_j |c_j|^4/Omega_j
          +8 sum_{j<l}|c_j c_l|^2/(Omega_j+Omega_l)].

Put S_k=2k^2|c_k|^2=1/8+O(k^-2). Reorganizing this expression gives
(4/kappa)sum_{k,l}S_k S_l/(Omega_k+Omega_l) plus a summable diagonal.
Replacing S_k S_l by 1/64 costs O(log K), replacing the frequencies
by k,l costs O(1), and

    sum_{k,l=J}^K 1/(k+l)=2K log 2+O(log K).

Consequently, for fixed phi,

    <Q A_ad(phi vacuum),F_K^-1 Q A_ad(phi vacuum)>
       =(K log2/8)integral |phi|^2/kappa +O(log K)||phi||_{H^1}^2.

The two-particle form contributes only O(log K). The formal
second-order energy term -alpha_K^2 times this expression has leading
-K log2/(2 log^2 K) times the same integral. This is an exact static
form asymptotic and a formal second-order diagnostic, NOT a proved
second time-layer propagation or a ground energy of the full
indefinite generator. A leading-only subtraction K/(2kappa log K)
also leaves the vacuum next coefficient
K[gamma_Euler-4G(u_i)]/(2kappa log^2 K); the virtual term is not the
whole next coefficient in that case.

## C7. Literature check and next admissibility question

Hollands--Wald, Local Wick Polynomials and Time Ordered Products
(gr-qc/0103074, Theorem 5.1), restrict local covariant Wick ambiguities
under their assumptions to finite polynomial curvature/mass data and
constants. Their introduction distinguishes reference-state normal
ordering from local covariance. Their later stress-conservation work
(gr-qc/0404074) treats action Ward conditions for perturbative scalar
theory on curved backgrounds. Those results do not directly classify
this global Q_K^2, harmonic cutoff and quantum geometry constraint.
They neither authorize r_K nor exclude all extended theories.

Primary sources inspected:
https://arxiv.org/abs/gr-qc/0103074
https://arxiv.org/abs/gr-qc/0404074

The concrete next question is whether a common full action,
renormalization and physical-domain construction can justify an
operator-level modification with its complete lapse/u/contact rows.
The current candidate remains a mathematically analyzed change,
not an adopted repair or physical unification.

## C8. Exact versus leading cancellation; endpoint transport

The exact reciprocal shift in C3 is not absorbable in the stated
constant-parameter family on a whole window. This is not an exclusion
of every leading scalar cancellation. For example the different
constant-in-u shift delta d_0,K=K/(2log K) already cancels the first
layer. It changes the frozen cutoff radiation/anomaly prescription and
leaves the next coefficients in C6. Its existing potential shape does
not make its new coefficient part of the accepted original model.

Nor can scalar-only subtraction be called a free endpoint phase.
For V=exp[i theta_K(u)/kappa],

    V*P_u V=P_u+theta_K'/kappa,
    V*P_kappa V=P_kappa-theta_K/kappa^2.

The full canonical transform includes the induced momentum connection,
cross terms and its quadratic term. In the lapse action,

    d[theta(u)/kappa]/d eta
       =N theta'(u)-N theta(u)chi/kappa^2.

The scalar lapse term is a boundary rewrite only together with that
mandatory linear-chi term and the transported states/observables.
The scalar-only nu comparison changes the constraint itself.
