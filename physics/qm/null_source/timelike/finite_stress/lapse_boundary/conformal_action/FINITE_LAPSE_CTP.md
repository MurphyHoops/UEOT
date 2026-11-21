# T. A finite-initial two-lapse influence from the actual canonical action

## T1. Same initial state, explicit cutoff prescription

This is a stationary Einstein-cylinder conformal-field comparison.
It is not the actual nonlinear u-clock geometry of PROJECTED_NOISE,
nor a joint quantum-gravitational solution.

Take N(t,x)=1+epsilon Y3(x) on a finite interval [0,T],
Y3=(4cos²chi-1)/sqrt(V), Delta Y3=-8Y3, V=2pi².
Perform the FULL canonical Legendre transformation FIRST:

 H[N]=(1/2) integral [N pi²+N|grad q|²+(N-Delta N/3)q²].

Then truncate the canonical q,pi to all k<=K modes on both branches.
This phase-space regulator is declared once. Truncating only the
configuration action first would instead produce the kinetic
inverse (P_K N^-1 P_K)^-1; it is a different finite-K prescription.

For each SO(3) block ell=0,...,K-1, k=ell+1,...,K, multiplication
by cos chi has recurrence

 a_(k,ell)=(1/2)sqrt[(k-ell)(k+ell+1)/(k(k+1))].

The Y3 matrix M has
M_kk=[4(a_k²+a_(k-1)²)-1]/sqrt(V),
M_(k,k+2)=4a_k a_(k+1)/sqrt(V).
In particular a_K² must remain: the intermediate K+1 mode contributes
to the multiplication matrix even though it is not a dynamical mode.

With D0=diag(k), the exact finite-cutoff Hamiltonian is

 H_epsilon=(1/2)p^T P_epsilon p+(1/2)q^T Q_epsilon q,
 P=I+epsilon M, Q=D0²+epsilon A,
 A_ij=[(ki²+kj²)/2-4/3]M_ij.                          (T1)

Every block has multiplicity (2ell+1)n_s. The full shell trace of
M_kk vanishes, including the top shell. Therefore the one FIXED
initial Einstein-vacuum state has <partial_epsilon H>=0.
There is no branch-dependent replacement by a new oscillator vacuum.

## T2. Genuine normal unitaries and their CTP overlap

Because ||Y3||infinity=3/sqrt(V), the q form is
integral[(1+epsilon Y3)|grad q|²+(1+(11/3)epsilon Y3)q²].
The sufficient condition |epsilon|<sqrt(V)/11 makes P,Q positive
uniformly in K. The finite-dimensional canonical change
q=P^(1/2)x, p=P^(-1/2)p_x, followed by an orthogonal rotation,
identifies H with a sum of positive harmonic oscillators.
Thus it is self-adjoint with its transported oscillator domain
and a Schwartz core; U_epsilon(T)=exp(-iT H_epsilon) is an actual
unitary on finite-mode Fock space, not just a formal matrix.

Use the SAME normal initial vacuum rho0 on the two CTP branches:

 F(epsilon_+,epsilon_-)
       =Tr[U_+ rho0 U_-*]=<0|U_-* U_+|0>.              (T2)

The trace retains all evolved source states. The vacuum-overlap
expression is not a postselection or discarded failure record.
F has unit physical diagonal, conjugation symmetry and a positive
Gram kernel over history labels. Labels may be represented by an
external register, but that fact does not construct quantum geometry.

## T3. Metaplectic phase and an independent Gaussian check

Let J=[[0,I],[-I,0]], G=diag(Q,P),
S_epsilon=exp(T JG), U_epsilon* (q,p) U_epsilon=S_epsilon(q,p).
For V=U_-*U_+, S_rel=S_-^-1 S_+.
Scale by diag(D0^1/2,D0^-1/2), and write its blocks as
[[A_s,B_s],[C_s,D_s]]. The Heisenberg Bogoliubov coefficient is

 alpha_rel=(A_s+D_s+iC_s-iB_s)/2.

The block influence, including phase, is

 F_block=exp[-(1/2) Log_cont det(conjugate(alpha_rel))]. (T3)

It starts from F=1 at T=0. For a free oscillator alpha=e^-ikt,
this gives exp(-ikt/2), fixing the sign.
Multiply block logarithms by n_s(2ell+1).
A common normal-ordering/Casimir scalar cancels between equal-duration
branches. Branch-dependent real counterterms do not cancel and must
be transported as the corresponding CTP phase.

For an independent coordinate-Gaussian check, in unscaled S blocks
put J_e=A+iBD0, Z_e=(D_s D0-iC)J_e^-1. The evolved wavefunction has
width Z_e, Re Z_e>0, and prefactor det_cont(J_e)^-1/2.
Direct Gaussian integration of the two wavefunctions gives the
same complex overlap as (T3).

The certificate chooses K=8, T=.02, |epsilon|<=.08.
A scaled perturbation norm bound is
Cg=3(K^(3/2)+4/3)/sqrt(V).
On the actual relative path t in [0,T],

 ||S_rel-I||<=r=T|epsilon_+-epsilon_-|Cg
                  exp[2T(K+.08Cg)].

It verifies r<1 and K[-log(1-r)]<pi. Therefore the continuous
relative determinant log stays on the local principal branch.
The regression also checks the independent Gaussian expression;
it does not replace the analytic phase prescription.

## T4. Initial-slice cumulants: noise AND causal phase

The pair-creation matrix from (T1) is

 B_ij=[(ki-kj)²-8/3]M_ij/(8sqrt(ki kj)).

All block degeneracies give the SAME finite weights as SPATIAL_NOISE:
w_n=C3 for n=4,6,...,2K-2 and w_(2K)=(2/3)C3.
This independently tests the action-to-source mapping and catches
the missing-intermediate-mode error.

Define
N_T,K=2sum_n w_n(1-cos nT)/n²,
R_T,K=2sum_n w_n(nT-sin nT)/n².
The exact finite-initial second derivatives are

 log F=-(epsilon_+-epsilon_-)² N_T,K/2
       +i(epsilon_+²-epsilon_-²)R_T,K/2+O(epsilon³),

 partial_+² logF=-N+iR,
 partial_-² logF=-N-iR,
 partial_+partial_- logF=N.                            (T4)

The finite matrix certificate checks all three complex entries.
Matching only |F| would miss the response phase and its sign.

## T5. A controlled full-field SECOND-CUMULANT limit

For 0<=T<=pi the exact full-field noise coefficient is

 N_T,infinity=C3[(pi T-T²)/2-sin²T].                    (T5)

The rectangular time test is legitimate for this single density
harmonic's L² extension. It does not establish a sharp-switch
momentum/shear domain or a finite-amplitude Hadamard limit.

R_T,K=T chi_K(0)-2sum_n w_n sin(nT)/n² has the same local logarithm
as WEYL_RESPONSE. Apply the SAME scheme
gamma_(W,K)=gamma_R-n_s H_K/(960V). Then

 R_T,ren=T(320gamma_R/3-C3)
                  -(C3/2)sum_(j=2)^infinity sin(2jT)/j². (T6)

Safe absolute errors are

 0<=N_infinity-N_K<=C3[1/(3K²)+1/K],
 |R_ren-R_K,ren|
             <=C3[T/(3K)+1/(6K²)+1/(2K)].              (T7)

The certificate encloses these full-field finite-initial Hessian
coefficients using K=10000, separately from the finite-amplitude
K=8 determinant. Real counterterm phases preserve the exact finite-K
Gram positivity. The quadratic cumulant model with N>=0 is also
a positive Gaussian kernel, but is not identified with the full
nonlinear influence at finite amplitude.

Completed: a same-state, finite-initial two-lapse normal influence,
its phase-correct source/contact mapping and renormalized second
cumulants. Still open: the full finite-amplitude all-field limit,
smooth metric/boundary renormalization, all tensor columns and the
joint Einstein-CTP state/evolution.

Primary phase reference checked: Guaita--Hackl--Quella,
https://arxiv.org/abs/2409.11628, sections IV.1 and IV.3.
The continuous metaplectic lift fixes the vacuum-overlap sign;
our explicit free-oscillator check fixes the conjugation convention.

There is also a concrete nonuniform initial-time limit:
N_T,infinity=(pi C3/2)T-(3C3/2)T²+O(T⁴), whereas fixed K has
N_T,K=Var(V_K)T²+O(T⁴). Thus the small-time expansion cannot be
interchanged with the field cutoff. This limits sharp initial
stress/energy claims without deciding the full propagator limit.
