# U. Full-field normal static lapse dynamics in a named spectral prescription

## U1. Exact operator and uniform positive forms

This continues T's actual canonical regulator for the conformally coupled
free scalar on the fixed static spacetime
g_N=-N(x)^2 dt^2+dOmega_3^2, N=1+epsilon f,
f=Y3=(4cos^2 chi-1)/sqrt(V), V=2pi^2.
It is a spatially nonuniform classical metric comparison, not the selected
homogeneous u-clock model and not a joint quantum Einstein solution.

On the real one-particle L2(S3) space let D=sqrt(-Delta+1).
Its eigenvalues k=1,2,... have multiplicity k^2.
The exact canonical quadratic Hamiltonian has kinetic operator P=N and

 Q=-div(N grad)+N-Delta N/3
  =(D^2 N+N D^2)/2+Delta N/6
  =D N D+epsilon B,
 B=[D,[D,f]]/2-4f/3.                                      (U1)

The Y3 recurrence in T implies that B has only k-l=0,+2,-2 blocks.
Its diagonal coefficient is -4M_kk/3 and its two off-diagonal
coefficients are 2M_(k,k+2)/3. Each |M_ij|<=1/sqrt(V), hence

 ||B|| <= 8/(3sqrt(V)).                                    (U2)

Write p_-=1-3|epsilon|/sqrt(V), p_+=1+3|epsilon|/sqrt(V),
q_-=1-11|epsilon|/sqrt(V), q_+=1+11|epsilon|/sqrt(V).
For |epsilon|<sqrt(V)/11, all are positive and the full forms obey
p_- I<=P<=p_+ I and q_- D^2<=Q<=q_+ D^2.
These are form inequalities on the correct Sobolev domains.

Define positive self-adjoint elliptic operators

 Y=P^(1/2) D P^(1/2),
 Omega=(P^(1/2) Q P^(1/2))^(1/2),
 C=Omega^2-Y^2=epsilon P^(1/2) B P^(1/2).                  (U3)

Then ||C||<=c_B=p_+|epsilon|8/(3sqrt(V)).
Min-max applied to the positive congruences gives, with ordered
multiplicities, lambda_j(Y)>=b lambda_j(D),
lambda_j(Omega)>=a lambda_j(D), where
b=p_- and a=sqrt(q_- p_-).
The stronger form comparison needed below is
Omega^2 >= (q_-/p_+) Y^2, and similarly an upper bound.
No unproved operator inequality Omega>=aD is used.

## U2. Actual Bogoliubov coefficient and a finite full-field norm

The canonical change q=P^(1/2)x, p=P^(-1/2)y yields oscillator
frequency Omega. Relative to the OLD ESU annihilator a_D, its
annihilator is b_N=alpha a_D+beta a_D^dagger, where

 beta=(1/2)Omega^(-1/2)(Omega-Y)P^(-1/2)D^(-1/2).            (U4)

The polar decomposition P^(-1/2)D^(-1/2)=Y^(-1/2)V0 has a
unitary V0 (both factors are injective with dense range). Thus beta
has the same singular values as
beta_tilde=(1/2)Omega^(-1/2)(Omega-Y)Y^(-1/2).

X=Omega-Y is the unique bounded solution of
Omega X+X Y=C, namely integral_0^infinity exp(-tOmega) C exp(-tY)dt.
In the separate eigenbases of Omega and Y,

 ||beta||_HS^2
 = (1/4) sum_jk |C_jk|^2/[omega_j y_k(omega_j+y_k)^2]
 <= (1/16)||Omega^(-1) C Y^(-1)||_HS^2
 <= ||C||^2 sqrt(Tr Omega^(-4) Tr Y^(-4))/16.               (U5)

Since Tr D^(-4)=sum k^2/k^4=pi^2/6, n_s independent fields obey

 ||beta_total||_HS <= sqrt(n_s) pi c_B/(4sqrt(6) a b).       (U6)

An independent heat/Schatten estimate, useful for convergence, is

 ||Omega^(-1/2) exp(-tOmega)||_4
       <= a^(-1/2)(exp(4at)-1)^(-1/4),
 ||beta_total||_HS
       <= sqrt(n_s) pi c_B/[8 min(a,b)sqrt(ab)].            (U7)

Indeed the product of the two heat bounds is at most
(ab)^(-1/2)(exp(4mt)-1)^(-1/2), m=min(a,b), whose integral is
pi/(4m). Its t^(-1/2) singularity is integrable. These are
full-field estimates, not extrapolations from a finite matrix.

The Shale criterion gives an actual unitary implementer W_N on
the old Fock space. Fix its phase by <0_D|W_N|0_D> > 0.
The new ground vacuum is W_N|0_D>, a normal pure state.
Its overlap and trace distance satisfy

 |<0_D|0_N>|^2=det(I+beta beta^dagger)^(-1/2)
       >= exp(-||beta||_HS^2/2),
 D_tr(|0_N>,|0_D>) <= sqrt(1-exp(-||beta||_HS^2/2)).         (U8)

The determinant is a Fredholm determinant of a trace-class
perturbation of I. There is no assumption that det(alpha) exists.
Normality by itself makes no Hadamard or finite-energy claim;
V examines the precise Hadamard distinction.

## U3. Genuine convergence of the canonical mode cutoff

Let Pi_K project onto ALL k<=K modes, with the same source and
canonical cutoff on both branches. Extend the finite kinetic
matrix by the identity on its tail:

 P_K=I+epsilon Pi_K f Pi_K, B_K=Pi_K B Pi_K,
 Q_K=D P_K D+epsilon B_K,
 Y_K=P_K^(1/2) D P_K^(1/2),
 C_K=epsilon P_K^(1/2) B_K P_K^(1/2).

This is the actual low-mode Hamiltonian in T plus a free D tail.
All preceding positive bounds hold uniformly in K. P_K and its
bounded powers converge strongly. Since D^(-1) is compact,

 Y_K^(-1)=P_K^(-1/2)D^(-1)P_K^(-1/2) -> Y^(-1)
 in operator norm. C_K -> C strongly and is uniformly bounded.
Consequently the compact sandwiches
Z_K=I+Y_K^(-1) C_K Y_K^(-1) converge in norm.
Moreover Z_K >= (q_-/p_+) I, so the inverses converge in norm and

 Omega_K^(-2)=Y_K^(-1) Z_K^(-1) Y_K^(-1) -> Omega^(-2).    (U9)

These formulas are interpreted as inverses of positive closed
forms; no product of incompatible unbounded domains is assumed.

For each t>0 the heat weights Omega_K^(-1/2)exp(-tOmega_K)
converge in operator norm by continuous functional calculus of
the compact inverse. Their uniform Schatten-2 bounds and norm
convergence imply Schatten-4 convergence by interpolation.
The same holds for Y_K. Strongly convergent bounded C_K between
compact Schatten factors then gives HS convergence of the
Sylvester integrands. The common integrable bound (U7) proves
beta_tilde_K -> beta_tilde in HS by dominated convergence.

The polar unitaries also converge strongly and adjoint-strongly.
On the dense D(D^(1/2)) core use
V_K=Y_K^(-1/2)P_K^(1/2)D^(1/2); uniform norm one extends
the convergence. Multiplication by the compact HS coefficient
then proves beta_K -> beta in HS in the ORIGINAL canonical
one-particle identification, not merely in moving eigenbases.

For completeness,
alpha_K=beta_K+Omega_K^(-1/2)P_K^(1/2)D^(1/2).
The second term converges strongly on that same dense core and
has norm squared <=sqrt(p_+/q_-); hence alpha_K -> alpha
strongly everywhere. The canonical identity
alpha_K alpha_K^dagger=I+beta_K beta_K^dagger gives adjoint-strong
convergence. alpha_K^(-1) are uniformly bounded by one.
The symmetric squeezing kernels
Zs_K=-alpha_K^(-1)beta_K converge in HS, with a common norm <1.
The normalized squeezed vacua, whose vacuum coefficients are
det(I-Zs_K^dagger Zs_K)^(1/4)>0, therefore converge in Hilbert norm.
Weyl coherent-vector intertwining upgrades this to W_K -> W_N
and W_K^dagger -> W_N^dagger strongly.

This is a cutoff limit proof. A uniform bound on ||beta_K||_HS
alone would not prove these conclusions.

## U4. Self-adjoint dynamics and the normal CTP kernel

In the explicitly named SPECTRAL-ZERO prescription define

 H_N^(0)=W_N dGamma(Omega) W_N^dagger >= 0,
 D(H_N^(0))=W_N D(dGamma(Omega)),
 U_N^(0)(t)=W_N Gamma(exp(-itOmega)) W_N^dagger.            (U10)

These are genuine self-adjoint operators and unitary groups.
Norm convergence of the positive inverse in (U9) implies
norm-resolvent convergence of Omega_K and strong convergence of
its one-particle unitaries, uniformly on compact time intervals.
Second quantization and the implementer convergence give

 U_N,K^(0)(t) -> U_N^(0)(t), and adjoints, strongly,
 uniformly on compact time intervals.                    (U11)

On physical low-mode states with vacuum tail this is exactly the
finite-K Hamiltonian minus its ground energy. The free-tail
extension used in the proof does not change that restriction.
Identity-tail extensions have the same strong limit by density
of finite-mode, finite-particle vectors.

For any one fixed normal initial density (including a reference
factor), or trace-norm-convergent cutoff densities, the actual
two-branch kernels U_+,K^(0) rho_K U_-,K^(0)dagger converge
in trace norm. Finite sequences of bounded normal CP operations
preserving their complete outcomes have the corresponding
normal limits. There is no operator-norm or diamond convergence
claim on the unrestricted input space.

For the SAME old ESU vacuum, the limit influence is a normalized
positive Gram kernel and is nonzero for each pair of fixed
branches and finite t. The relative implementable symplectic
map has HS beta_rel, so its modulus squared is
det(I+beta_rel beta_rel^dagger)^(-1/2)>0.
The actual phase is defined by (U10) and (U11), not by replacing
a missing infinite det(alpha_rel) by a formal expression.
For arbitrary normal inputs the trace limit exists but can vanish.

## U5. Spectral subtraction does not settle the gravitational phase

At finite K let E_gs,N,K=(n_s/2)Tr_(Pi_K H) Omega_N,K.
This trace is over the finite low-mode block only, not the free-tail
extension used in the cutoff convergence proof. Then

 F_K^(0)=exp{iT[E_gs,+,K-E_gs,-,K]} F_K^bare.               (U12)

Subtracting the ENTIRE N-dependent ground energy defines the
preceding full-field limit. It is not yet proved equivalent to
allowed local covariant gravitational and boundary counterterms
with fixed finite renormalization conditions. Adding a real
e(N)I to (U10) preserves every same-background density channel
but multiplies the two-branch influence by
exp{-iT[e(N_+)-e(N_-)]}. This matters when lapse is dynamical.

There is a precise second-order check against WEYL_RESPONSE.
H_epsilon,K is linear in epsilon and E_gs'(0)=0, so ordinary
finite-oscillator perturbation theory gives

 E_gs''(0)=-chi_K(0)
       =-C3[H_K-1-1/(3K)], C3=n_s/(9V).                  (U13)

The spectral-zero phase therefore subtracts ALL static response,
including its finite part. The local Weyl counterterm only fixes
the logarithm and the chosen finite parameter:
gamma_W,K=gamma_R-n_s H_K/(960V).
Its lapse Hessian is 320gamma_W,K/3.
The divergent parts agree; this does not establish an all-orders
local phase equivalence or select the physical finite gamma_R.

Completed here: a full-field normal static Gaussian state,
actual cutoff convergence, self-adjoint spectral-zero dynamics
and normal two-branch kernels. Still open: the locally covariant
finite-amplitude phase, a legal common Hadamard preparation for
different geometries, all tensor responses and joint Einstein-CTP
backreaction.

Primary mathematical reference actually checked:
Bruneau--Derezinski, J. Math. Phys. 48, 022101 (2007),
https://users.fuw.edu.pl/~derezins/bogoliubov.pdf ,
Theorems 4.1 and 4.2, and the introduction's distinction between
vacuum-expectation-zero and spectral-infimum-zero generators.
The explicit S3 estimates and actual canonical cutoff proof above
are supplied here; the citation does not stand in for them.

More explicitly, for the pure Weyl finite convention just stated,
write W_f(epsilon)=2 integral epsilon^2|HessTF f|^2/(1+epsilon f)dV.
Its second derivative is 320/3. Since the Lorentzian action
contributes T gamma_W,K W_f, its Hamiltonian scalar is
-gamma_W,K W_f. Thus the renormalized static ground curvature is
E_ren,K''(0)=C3[1+1/(3K)]-320gamma_R/3.
If a physical locally renormalized Hamiltonian with that convention
is related to H^(0) by a scalar e(epsilon), it must satisfy
e''(0)=C3-320gamma_R/3, apart from separately declared other finite
local terms. Spectral zero sets e identically zero; tuning
gamma_R=n_s/(960V) matches this one Hessian only. It does not
prove higher-amplitude phase equivalence. The statement uses
finite-K derivatives followed by their explicit limit, with no
unproved exchange of differentiation and an all-orders field limit.
