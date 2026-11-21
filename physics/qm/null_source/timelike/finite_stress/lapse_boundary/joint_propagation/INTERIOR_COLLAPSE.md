# Actual interior propagation: fixed-clock test kernels collapse

## I1. Uniform reset theorem for the complete evolution

Fix a compact original-u clock chart J_u, and a smaller compact
J_u' with positive room to its right endpoint. For all sufficiently
large K the original g_K is negative throughout J_u. With
epsilon_K=log K/K, the INITIAL_LAYER theorem strengthens to

    sup_{u_0 in J_u', 0<=s<=S}
      ||[Ucal_K(u_0+epsilon_K s,u_0)-F_s]psi|| ->0,
    F_s=exp[is/(2kappa)],

for every fixed bulk vector psi. Uniform strong adjoint convergence
holds too.

To check the uniformity, alpha_K=-2/log K+O((log K)^-2) and
alpha_K'=O((log K)^-2) hold uniformly on J_u. The complete L_K bounds
on each fixed regular low input are uniform there. W_K,T_K,Gamma_K,
F_K,G_K and the C5 comparison inputs do not depend on the reset u_0.
Replace only the lower limit of the trial phase integral by u_0.
All support, inverse-gap and residual bounds use one C_{J_u,S}.
The same dense-span argument then proves the asserted all-vector
limit. No actual evolved state at u_0 is assumed to remain a Gaussian,
Schwartz vector, or to have a uniform energy budget.

## I2. A direct fixed-time-test theorem

Let h be a fixed smooth compactly supported scalar test inside the
chart, and define

    B_K(h)x=integral h(u)Ucal_K(u_i,u)x du.

The reference u_i and all supports lie in the same common chart.
Only exact unitarity is used for this potentially long propagation.
Fix s>0 and delta_K=epsilon_K s. For large K the support and its shift
remain inside the chart. Set

    I_K x=integral h(u)Ucal_K(u_i,u+delta_K)x du.

Changing variables gives

    ||I_Kx-B_K(h)x||
       <=||h(. -delta_K)-h||_1 ||x|| ->0.

Exact composition and I1's uniform RESET ADJOINT limit also give

    ||I_Kx-B_K(h)F_s* x|| ->0,

because Ucal_K(u_i,u+delta)=Ucal_K(u_i,u)Ucal_K(u,u+delta).
Therefore B_K(h)(F_s*-I)x tends to zero for every fixed x.

The range of F_s*-I is dense: its orthogonal complement is
ker(F_s-I), which is zero because the kappa phase-one level set is
countable and null. Since ||B_K(h)||<=||h||_1, this proves

    B_K(h) ->0 STRONGLY.                              (I.1)

Finite sums of h_j(u)x_j are dense in Bochner L^1 on a compact
time window. The uniform integral bound then yields the main result:

    T_K X=integral Ucal_K(u_i,u)X(u)du ->0 in H
    for EVERY fixed X in L^1(du;H) with compact chart support. (I.2)

No positivity, preparation hypothesis, generator moment, projected
evolution or invariant compact orbit is used in this proof.

## I3. The original constraint kernel and its nonzero gate

In the ORIGINAL endpoint congruence use X=f_kappa Phi with
f_kappa=kappa^-1/2. A fixed compact-kappa smooth vector test is
admissible, more generally any fixed f_kappa Phi in L^1(du;H).
Equation (I.2) gives

    eta_C,K(Phi,Psi)=<T_K f_kappa Phi,T_K f_kappa Psi> ->0.

For ANY finite-K normal trace-one preparation rho_K, even with no
normal state limit,

    |eta_{C,rho_K}(Phi,Psi)|
      =|<T_K f_kappa Phi,rho_K T_K f_kappa Psi>|
      <=||T_K f_kappa Phi||||T_K f_kappa Psi|| ->0.

Thus both the state-independent rigging pairings and every normally
prepared two-time pairing collapse to ZERO on the declared common
fixed original-clock vector tests. This rejects the nonzero normalized
fixed-test N3 gate for the complete nonautonomous original model in
this bulk comparison. It is not merely a frozen-snapshot diagnostic.

There is no contradiction with finite-K physical Hilbert spaces.
Each finite-K exact quotient still completes to H and has normal
trace-one slice states. Its adapted section J_{h,K} depends on K and
still satisfies T_K f_kappa J_{h,K}=I, equivalently T_C,K J_{h,K}=I. Such moving tests are outside (I.2).
Likewise slice delta evaluation, unbounded traces, and the rescaled
tests epsilon_K^-1 Phi((u-u_i)/epsilon_K) are not fixed L^1 vector
tests. RESCALED_KERNEL supplies a positive, normalized limit on that
explicitly different test family.

This conclusion uses the fixed BULK identification of N1, with the
original W_K already included in Ucal_K. A fixed raw test pulled
through W_K can become K-dependent in bulk. Such a new comparison,
or a new normalization/action/physical observable algebra, requires
its own test theorem and is not silently rejected here.

## I4. Independent positive-average check and normal histories

For completeness, a second argument makes the normality loss visible
on actual density histories. Let rho_K(u) be any complete normal
trace-one history and let h>=0 be smooth, supported in the interior,
with integral h=1. Put sigma_K=integral h(u)rho_K(u)du.

For a compact operator A, I1's forward/adjoint strong convergence
gives uniform OPERATOR-NORM convergence of
Ucal_K(u,u+delta) A Ucal_K(u+delta,u) to F_s* A F_s.
This follows first for rank-one A and then by compact approximation.
Exact propagation and the small L^1 shift of h imply

    Tr A[sigma_K-F_s sigma_K F_s*] ->0
    for every compact A.

Any bounded sequence of positive trace-class operators of trace one
has a subsequence converging against all compact operators to a
positive trace-class sigma with Tr sigma<=1. A self-contained proof
uses a diagonal subsequence of all matrix elements in a countable
basis; positivity and bounded finite partial traces give a positive
trace-class limit, and finite-rank approximation handles all compacts.
The displayed identity makes that limit commute with F_s.
There is no nonzero positive trace-class operator commuting with F_s,
by the finite-dimensional eigenspace argument in RESCALED_KERNEL.
Every such subsequential limit is therefore zero. Consequently

    Tr sigma_K A ->0 for EVERY compact A,             (I.3)

although Tr sigma_K=1 for every K. In particular no positive fixed
original-time averaged density has a trace-normal trace-norm limit.

There is also no L^1(original time;trace class) normal trace-one history
limit on any positive original-time interval. If rho_K->rho in that
space, translation continuity gives rho_K(u+delta_K)->rho(u).
Exact propagation, I1 and approximation of rho by finite simple
trace-class functions give instead F_s rho(u)F_s*. This would make
rho(u) a nonzero normal invariant state almost everywhere.
Almost-everywhere pointwise trace convergence implies this L^1
convergence by dominated convergence, so it is excluded as well.
These conclusions hold for arbitrary preparation sequences.

## I5. Fixed forcing responses and precise remaining scope

For fixed X in L^1([a,b];H), put
F_K(t)=integral_a^t Ucal_K(u_i,u)X(u)du.
Equation (I.2) gives convergence to zero at every fixed t, while

    ||F_K(t)-F_K(v)||<=integral_v^t ||X(u)||du

is a common modulus. A finite time grid makes the convergence uniform.
Therefore the actual retarded response
integral_a^t Ucal_K(t,u)X(u)du=Ucal_K(t,u_i)F_K(t)
tends uniformly to zero. The advanced fixed-forcing response does too.
This is not operator-norm convergence of the Duhamel maps and does
not cover unbounded or K-dependent stress/preparation insertions.

Still undecided by this theorem: a single isolated fixed positive-time
state limit, a selected noncompact record such as B(kappa), the old N4
prepared readout sequence, cutoff-dependent endpoint comparisons,
or other singular/algebraic physical representations.
The full original fixed-test N3 normalization is now REJECTED;
a four-dimensional physical unification result is not obtained.
