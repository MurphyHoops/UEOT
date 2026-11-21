# Gaussian preparation: actual transfer, exact resources and retained memory

## G1. A finite normal preparation, selected once

Fix the original C5 compact profile g, n=|g|^2, support I=[a,b]
inside (0,infinity), the original bulk encoding and a shared normal
low/source/reference input. Define

    w(kappa)=1/(2kappa), F_lambda=exp(i lambda w),
    gamma_sigma(lambda)=exp[-lambda^2/(2sigma^2)]/(sqrt(2pi)sigma),
    E_sigma(rho)=integral gamma_sigma(lambda)F_lambda rho F_lambda* d lambda,
    I_j=integral n(kappa)kappa^-j d kappa.

For finite sigma>0 this is a normal completely positive trace-preserving
channel on trace-class inputs. It preserves the source marginal and
kappa law, changes geometry coherences and the complete joint state,
and is fixed at the initial slice. It is a changed preparation followed
by the unchanged complete original Hamiltonian, not a local autonomous
apparatus construction.

## G2. Reduced phase distinction and effective Fisher information

Translation of the Gaussian gives

    F_s E_sigma(rho)F_s*
       =integral gamma_sigma(lambda-s)F_lambda rho F_lambda* d lambda.

Trace contraction from the classical mixing density implies

    D_tr(E_sigma(rho),F_s E_sigma(rho)F_s*)
       <=erf[|s|/(2sqrt(2)sigma)]
       <=|s|/(sqrt(2pi)sigma),                         (G.1)
    F_Q(E_sigma(rho),w)<=1/sigma^2.                    (G.2)

D_tr is half the trace norm; a shared reference is allowed.
Here is a direct proof of the QFI bound. Put rho_lambda=F_lambda rho
F_lambda*, p_s=gamma_sigma(lambda-s), score=(lambda-s)/sigma^2.
For bounded self-adjoint L let m_lambda=Tr rho_lambda L and
v_lambda=Tr rho_lambda L^2>=m_lambda^2. Then

    2Tr rho_s' L-Tr rho_s L^2
       =integral p_s(2 score m_lambda-v_lambda)
       <=integral p_s score^2=1/sigma^2.

Completing the square in L^2(rho_s), with bounded approximants,
gives the SLD variational formula; its supremum proves (G.2).
This concerns the reduced state. A parameter-dependent relabeling of
an ACTUALLY retained memory is not permitted in this proof.

These are effective-s statements for w, NOT QFI bounds for the
original snapshot (log K/K)H_K or the actual mixed C9 derivative.
RARE_FISHER shows why bounded-history convergence does not control
that derivative information.

## G3. Exact form, current and retuning costs

Keep the original source connection in D_K, the covariant geometry
derivative, and define the complete positive form

    q_D(rho)=Tr rho D_K kappa^-1 D_K.

The identity D_K F_lambda=F_lambda(D_K+lambda w') and zero Gaussian
mean cancel every linear cross term. Since w'=-1/(2kappa^2),

    q_D(E_sigma rho)-q_D(rho)=sigma^2 I_5/4.           (G.3)

The ordering potential expectation is unchanged; the full initial
Hamiltonian mean changes by alpha_K sigma^2 I_5/4, with its ORIGINAL
sign. This is not a positive total-energy cost.

Use the self-adjoint compact-flow current whose coefficient equals
kappa^-1 on a neighborhood of I, conjugated by the original fiber
unitary. Its phase shift is -lambda/(2kappa^3). Consequently

    initial current mean is unchanged,
    Var(current;E_sigma rho)-Var(current;rho)
       =sigma^2 I_6/4.                               (G.4)

The compact vector field has a complete flow; no self-adjoint bare
half-line momentum is assumed. The inputs and derivatives remain
supported in I and their moments are finite.

For actual C9 all components have the same n, so the Gaussian adds
the same mean shift to each and leaves the gap Delta E unchanged.
The single initial selection

    p_sigma=p-alpha_K sigma^2 I_5/(4 Delta E)         (G.5)

restores E_*. The original r,b current adjustment remains valid.
For sigma^2=o(K), p_sigma~1/(2log K), hence is legal on a cofinal
range. The channel preserves its own input source marginal, but this
probability retuning changes the OLD C9 source marginal. The full
old state is not preserved.

## G4. Actual complete evolution with an explicit diagonal sequence

INITIAL_LAYER gives error(g)<=C||g||_{H^4}[(log K)^-1/2+log K/K],
with support, low input, J and S fixed. On I,

    ||exp(i lambda w)g||_{H^4}<=C_g(1+|lambda|)^4.

Averaging vector errors gives a complete classical-record estimate
O((1+sigma^4)/sqrt(log K)). For a coherent memory the Gaussian eighth
moment and the root-mean-square vector error give the same order.
This uses the ACTUAL complete propagator and its source correction.

Choose sigma_K=(log K)^(1/10) once. Uniformly on compact s windows,
the actual evolution error and reduced phase displacement are both
O((log K)^-1/10). The actual C9 comparison adds
O(p_sigma+r)=O((log K)^-1).
Form/current-variance increments are O((log K)^1/5), the unretuned
mean shift is O((log K)^-4/5), and
p_sigma-p=O(1/[K(log K)^4/5]).
No practical cutoff or physical duration in seconds is asserted.

## G5. Normal at finite cutoff; no normal limiting state

In the cyclic variable x=w, put

    f_0(x)=sqrt(2)kappa(x)g(kappa(x)),
    p_x(x)=2kappa(x)^2 n(kappa(x)), M=||p_x||_infinity<infinity.

The C5 fiber encoding is an isometry independent of lambda,s.
On its cyclic space the state is K_sigma tensor tau, where

    K_sigma(x,y)=f_0(x)conj(f_0(y))exp[-sigma^2(x-y)^2/2].

Multiplication by f_0 and Gaussian convolution give the norm bound;
direct integration of its squared kernel gives purity:

    ||K_sigma||<=sqrt(2pi)M/sigma,
    Tr K_sigma^2<=sqrt(pi)M/sigma.                    (G.6)

A mixed shared tau multiplies these bounds by ||tau||<=1 and
Tr tau^2<=1, respectively. Each C9 component has the same p_x, so
convexity preserves the norm bound for C9.

Every compact expectation tends to zero when sigma_K tends to infinity,
while each finite-K density has trace one. Thus no trace-norm
subsequence converges to a normal trace-one state. Original-time
prepared two-time kernels have operator norm <=sqrt(2pi)M/sigma_K,
irrespective of their unitary propagation; fixed tested pairings vanish.
This preparation fails the nonzero normal fixed-test kernel gate.

For the unretuned C5 state, its profile-range projection has probability
one initially and at most ||K_sigma|| afterward. Hence

    D_tr(E_sigma rho_C5,rho_C5)>=1-sqrt(2pi)M/sigma ->1.

For C9 add its explicitly small comparisons by the triangle inequality;
do not treat this as preservation of the old bare state.
For pure C5, the von Neumann entropy obeys

    S(E_sigma rho_C5)>=-log Tr K_sigma^2
       >=log sigma-log(sqrt(pi)M).

This is a reduced quantum entropy lower bound, not continuous
differential entropy or a complete apparatus entropy.

## G6. A normal coherent memory retains the distinction

The map into L^2(R,d lambda) tensor H,

    (W_sigma psi)(lambda)=sqrt(gamma_sigma(lambda))F_lambda psi,

is an isometry. W_sigma rho W_sigma* is genuinely positive trace class,
of trace one; tracing the memory gives E_sigma(rho). Moreover

    W_sigma F_s=(I_memory tensor F_s)W_sigma.

Thus retaining the coherent memory preserves exactly the original
phase-family trace distance and QFI. For the fixed C5 profile with a
shared low/reference factor this QFI is 4 Var_n(w)>0.

The fixed decomposable projection
E(lambda)=F_lambda P_M F_lambda*, using BOUNDED_WITNESS P_M, preserves
its base initial/evolved expectations independently of sigma.
G4 and the positive base gap yield a positive full-record gap under
the actual evolution. No rare successful record was removed.

A continuous classical record, if used, is instead the normal field
lambda->gamma_sigma(lambda)F_lambda rho F_lambda* in
L^1(R;trace-class(H)). It is NOT a trace-class delta-diagonal operator
on B(L^2(R) tensor H).

Normality holds at each finite sigma. The coherent vectors themselves
converge weakly to zero as sigma grows: truncate a test vector to a
bounded lambda interval, use sqrt(gamma_sigma)=O(sigma^-1/2) there,
then control its L^2 tail. There is no asserted normal infinite-noise
memory limit. A normal isometry is not a local autonomous apparatus or
an already included gravitational total source.

## G7. Effective information versus a declared positive-form resource

For any regular normal state supported in I, choose a smooth compact
vector field v equal to one near I, and its self-adjoint current J_v
conjugated by the original fiber unitary. On the support J_v=D_K:

    d/ds <J_v>_{F_s rho F_s*}|_0=-I_2/2.

SLD Cauchy--Schwarz for bounded spectral truncations, followed by the
finite-second-moment limit, gives

    F_Q(rho,w)Var_rho(J_v)>=I_2^2/4,
    Var_rho(J_v)<=b q_D(rho),
    F_Q(rho,w)q_D(rho)>=I_2^2/(4b)>0.                 (G.7)

This is a positive-form budget, not a total-energy or detector bound.

For the Gaussian C5 cyclic family, use a self-adjoint compact-flow
derivative J_x equal to P_x on the support of f_0. Lift it by the cyclic
isometry and extend by zero on the orthogonal complement. Then

    Var_{K_sigma}(J_x)=Var_{f_0}(P_x)+sigma^2,
    d/ds <J_x>_{exp(isx)K_sigma exp(-isx)}=1.

Consequently,

    1/[sigma^2+Var_{f_0}(P_x)]
       <=F_Q(K_sigma,x)<=1/sigma^2,
    sigma^2 F_Q(K_sigma,x)->1.                        (G.8)

The fixed smooth profile has finite Var(P_x); a shared fixed tau does
not change the result. At FIXED K and fixed input, G3/G8 give inverse
growth of effective information with the added form budget.
In the joint K,sigma_K limit the original C5 q_D already has an
order-K UV contribution. The added sigma_K^2 is not the whole resource.
Neither G7 nor G8 supplies an upper bound on actual C9/original-H QFI.

## G8. Closed comparison and open physical gate

Finite normal preparation, actual evolution, exact retuning and
fluctuation costs, retained normal memory, and failure of the nonzero
fixed-test kernel are specified. Reduced hiding is attainable by
changing the state; the complete record retains the distinction.

A local autonomous preparation/probe with its controller, source,
contact rows and total stress from one retained-lapse action remains
to be constructed. No common gravitational apparatus solution or
physical unification is claimed.
