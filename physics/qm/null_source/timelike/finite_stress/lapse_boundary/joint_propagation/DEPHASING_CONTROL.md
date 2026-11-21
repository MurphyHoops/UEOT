# Smooth phase hiding, its exact resource cost, and the retained record

## D1. A concrete changed preparation

Fix a normalized smooth compact C5 profile g on [a,b] in (0,infinity),
n(kappa)=|g(kappa)|^2 and G(kappa)=integral_a^kappa n.
G is chosen from this declared profile once; it is not recomputed
nonlinearly on an unknown output density. For odd N=2r+1 set

    U_m=exp[2 pi i m G(kappa)], m=-r,...,r,
    E_N(rho)=N^-1 sum_m U_m rho U_m*.

This is a normal random-unitary channel at each finite N. For the
pure C5 input psi define psi_m=U_m psi and sigma_N=E_N(|psi><psi|).
The orthogonality is exact:

    <psi_l,psi_m>=integral n exp[2 pi i(m-l)G]d kappa=delta_lm.

The substitution t=G is valid for the atomless profile measure even
if g has gaps. Equivalently integrate the derivative of the exponential.
Thus

    purity(sigma_N)=1/N, entropy(sigma_N)=log N,
    D_tr(sigma_N,|psi><psi|)=1-1/N, ||sigma_N||=1/N.

The entropy is in nats. The geometry probability law and the complete
reduced source marginal are unchanged by E_N; the complete joint
preparation is changed substantially.

For a fixed normal low/reference input tau in the C5 encoding,
the phase branches are orthogonal isometries and
sigma_N is isomorphic to (P_N/N) tensor tau, where P_N projects onto
N Fourier modes. Consequently purity=Tr(tau^2)/N,
entropy=log N+S(tau) when finite, distance from the original
fixed-profile encoded state=1-1/N, and operator norm<=1/N.
This does not compare arbitrary unrelated extensions.

## D2. Exact reduced phase-hiding bound

Define T:L^2[0,1]->H by (Tf)(kappa)=f(G(kappa))psi(kappa).
It is an isometry. For a generalized quantile Q_mu,
Q_mu(G(kappa))=kappa almost everywhere for the profile measure.
For the ACTUAL derived layer F_s=exp[is/(2kappa)],

    F_s T=T M_{f_s},
    f_s(t)=exp[is/(2Q_mu(t))],
    sigma_N=T(P_N/N)T*.

Let Q_N=M_{f_s}P_N M_{f_s}*. The rank of P_N-Q_N is at most 2N.
Trace/Hilbert--Schmidt Cauchy--Schwarz and Fourier expansion give

    D_tr(P_N/N,Q_N/N)^2
       <=1-Tr(P_N Q_N)/N
        =sum_{l in Z} min(1,|l|/N)|fhat_s(l)|^2.

The phase w(t)=1/(2Q_mu(t)) is monotone with variation
L=(1/a-1/b)/2. Its periodic exponential has total variation at most
2|s|L, including the endpoint jump. Stieltjes integration by parts
gives |fhat_s(l)|<=|s|L/(pi|l|) for l!=0. Summing the harmonic head
and inverse-square tail yields the uniform bound

    sup_{|s|<=S}D_tr(F_s sigma_N F_s*,sigma_N)
      <=min{1, (sqrt(2) S L/pi) sqrt[(log N+3)/N]}.       (D.1)

The constant is conservative; no strict positivity of n or maximum
quantile-bin width is assumed. This is an exact smooth alternative
to sharp-bin dephasing, whose cut wavefunctions would generally leave
the geometry form domain.

## D3. Exact positive form resource and actual initial means

Every U_m is smooth with bounded derivatives at fixed m, and equals
one outside the compact profile region. At each finite K,N it
preserves the regular compact-kappa/source-Schwartz comparison class.
For the actual covariant geometry derivative D_kappa, including its
source connection,

    U_m* D_kappa U_m=D_kappa+2 pi m n(kappa).

The symmetric m average cancels every linear cross term without
assuming it vanishes in an individual branch. Since
average m^2=(N^2-1)/12, the exact added positive geometry form is

    A_N=Delta q_eta
       =pi^2(N^2-1)/3 J_n,
    J_n=integral n(kappa)^3/kappa d kappa>0.

The initial geometry current is unchanged by the average. All other
source/dilation/multiplication terms commute with U_m, so the complete
original Hamiltonian mean shift is exactly alpha_K A_N.
On the cofinal negative-g patch alpha_K<0: A_N is a positive FORM
resource, not a claim of positive total-energy cost. Holder gives
J_n>=1/[b(b-a)^2], making the resource growth explicit.

If one wants the C9 mean/current targets again, they must be retuned
rather than inherited. The Fourier form addition is the same for
the ground, odd and rare-phase components. Their complete mean gap
Delta E_K is unchanged. Re-select once at u_i

    p_{K,N}=p_K-alpha_K A_N/Delta E_K.

Then the original E_* and nu initial targets hold again, with the same
geometry law. The rare phase and symmetric Fourier phase commute;
all cross terms odd in m cancel. For N^2=o(K),

    p_{K,N}-p_K=O(N^2/[K log K]), p_{K,N}~1/(2log K),

and 0<p_{K,N}<1 eventually. This is a new preparation calculation.
E_N preserves its OWN input source marginal, but this retuning of p
slightly changes the old C9 source marginal. Those statements must
not be combined into an exact old-marginal preservation claim.

## D4. An explicit diagonal in the actual complete evolution

The INITIAL_LAYER proof is linear in the profile and its constant is
bounded by a fixed H^4 profile budget. For g_m=U_m g,

    ||g_m||_{H^4}<=C_g(1+|m|)^4,
    sup_{s<=S}||[V_K(s)-F_s]U_m Psi_C5,K||
       <=C_S(1+|m|)^4/sqrt(log K).

Support, J and the regular low moment budget are fixed. Averaging the
full CQ branch errors gives C_S N^4/sqrt(log K). Choose explicitly
an odd integer N_K asymptotic to (log K)^(1/10), for example

    N_K=2 floor[(log K)^(1/10)/2]+1.

The actual propagation error is O((log K)^-1/10). Combining it with
(D.1) proves that the reduced prepared state in the COMPLETE original
evolution becomes asymptotically motionless on every fixed rescaled
window. The reduced phase-hiding term is
O(sqrt(log log K)(log K)^-1/20).
For the retuned C9 mixture add at most 2[p_{K,N_K}+r_K] at the
two endpoints, which also tends to zero.

Every finite K state is smooth and normal. The added form is
O((log K)^(1/5)); before retuning the mean shift is
O((log K)^-4/5), and the probability correction is
O(1/[K(log K)^(4/5)]). The quantitative diagonal uses the fixed
REGULAR low moment class. Arbitrary normal low inputs still have
fixed-N convergence and an existence-only slow diagonal, not this
unconditional rate.

## D5. Why this fails the required normal prepared-kernel gate

For the Fourier C5 states ||sigma_{N,K}||<=1/N. Every component of the
retuned C9 mixture has the same bound, so its convex mixture does too.
As N_K tends to infinity, all compact tests tend to zero: for a
finite-rank C, |Tr sigma C|<=||C||_1/N, and operator-norm approximation
extends this to any compact C. No trace-norm convergent subsequence
exists, because a putative trace-one normal limit would vanish on
every rank-one test and hence be zero.

There is an even stronger exact statement for the original model,
without any rescaled approximation. For any two allowed original
clock times u,v,

    ||U_K(u) sigma_{N,K} U_K(v)*|| <=1/N.

For any fixed original compact-kappa spacetime tests,

    |eta_{sigma,K}(Phi,Psi)|
       <=N^-1 [integral ||f_kappa Phi||du]
                [integral ||f_kappa Psi||du] ->0.

Thus its prepared vector-test two-time kernel collapses to ZERO,
although every finite-K recovered weighted diagonal has trace one.
It cannot pass the nonzero normalized prepared-kernel gate. The
state-independent rigging is a different object; this operator-norm
argument alone does not address it. INTERIOR_COLLAPSE separately
proves that the actual state-independent rigging also vanishes on
fixed original-clock vector tests in the frozen bulk comparison.
Multiplying this kernel by N changes the weighted trace to N, so
it does not restore the same trace-one preparation.

This excludes this explicit high-rank escape family, more generally
families with operator norm tending to zero. It does not exclude all
nonnormal alternatives or every changed representation.

## D6. Keeping the memory preserves the original distinction

Keep even a classical record of the chosen m:

    Omega_N=N^-1 sum_m |m><m| tensor U_m rho U_m*.

Because U_m commutes with F_s, block trace norms give exactly

    D_tr[(I tensor F_s)Omega_N(I tensor F_s*),Omega_N]
       =D_tr(F_s rho F_s*,rho).

The coherent Stinespring isometry
W_N psi=N^-1/2 sum_m U_m psi tensor |m>
commutes with F_s and gives the same equality by isometric invariance.
The reduced small motion is obtained by discarding this record.

For the explicit N_K diagonal the complete actual CQ propagation
error tends to zero by D4. For any fixed s>0, the retained record
therefore keeps the original positive normal-state phase gap, while
the reduced state motion tends to zero. The retuned C9 comparison
changes this by at most 2[p_{K,N_K}+r_K].
No autonomous local implementation, apparatus stress or thermodynamic
work cost is claimed by this abstract preparation.

## D7. Information calculation for the effective clock

For the pure-profile Fourier family in its cyclic space, sigma_N=P_N/N
and the bounded effective generator is w(t)=1/(2Q_mu(t)).
The SLD operator L_SLD=2i[(I-P_N)wP_N-P_Nw(I-P_N)] gives exactly

    F_Q(sigma_N,w)
       =4/N ||(I-P_N)wP_N||_2^2
       =4 sum_l min(1,|l|/N)|what(l)|^2
       <=(8 L^2/pi^2)(log N+2)/N ->0.

This also holds with a shared fixed low/reference factor. In contrast,
the retained classical record and coherent purification have effective
QFI exactly 4 Var_mu[1/(2kappa)]>0, independent of N.
These are calculations for the derived rescaled s parameter and the
specified Fourier family. They are not the original mixed C9 clock
variance, a physical clock calibration, or an inferred full tensor
noise bound.

The executable checks cover exact orthogonality, finite rank distance,
moments of m, form/coupling algebra, the diagonal exponents and outward
hiding/resource bounds. The infinite-dimensional propagation and
normality conclusions are proved above and in the source-bound
INITIAL_LAYER theorem.
