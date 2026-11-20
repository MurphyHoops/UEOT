# Finite-error alternatives and their actual costs

The exact original P law is an idealized contract. The phase-diagram
selection of the critical point must be tested against finite-error
contracts before being interpreted physically.

## 1. Smooth source cutoff and unbounded observable budgets

Let F(P) be real, smooth, between zero and one, equal to one for
P2<=K2*r0 and zero for P2>=K2*r1, with r_hi<r0<r1.
If Tr rho_old(1-F2)<=epsilon, the normalized source
rho_F=F rho_old F/Tr(F rho_old F) obeys
Dtr(rho_F,rho_old)<=sqrt(epsilon), where Dtr=||rho-sigma||1/2.
The smooth cutoff preserves all Q moments of the Gaussian input.

For R0=sqrt(K2*r0), m_hi=sqrt(K2*r_hi), a=R0-m_hi>0 and
x=a2/(2v_seed), the Gaussian tail obeys epsilon<=exp(-x).
Trace distance alone does not control unbounded stress moments.
For integer k>=1, the two-dimensional radial Gaussian tail gives
\[
 \mathbb E[P^{2k}1_{|P|>R_0}]
 \le2^{2k-1}e^{-x}
 \left[m_{\rm hi}^{2k}+(2v_{\rm seed})^k k!
                         \sum_{j=0}^k{x^j\over j!}\right].
\tag{45}
\]
This uses |P|<=m_hi+|Z| and the exact incomplete-gamma tail of |Z|2.
The normalized source moment change is at most
(tailmoment_k+epsilon E P^(2k))/(1-epsilon).
These are source-only, prescribed-background budgets. The actual
geometry's inverse-volume factors remain separate.

## 2. A fixed supercritical example really has negative states

Choose mu=q/2, gamma=q/8 and delta=sqrt(2)delta_c. Put
s=(V0/mu)^(3/2) and E_*=mu s. The necessary cap of PHASE_DIAGRAM.md
is P2<Rsc2=V0^3/mu2. For P2<=2K2 and r_crit>=1,
chi=P2/Rsc2<=1/2. On v/s=w in [1/2,1],
\[
 F_P(v)/E_*=w-\tfrac32 w^{1/3}+{\chi\over2w}
 \le-c_*,\quad c_*=\tfrac32\,2^{-1/3}-1>0.
\tag{46}
\]
The function is convex, so its maximum is at an endpoint.

There are at least three consecutive lattice sites in [s/2,s] when
delta/s<1/8, as verified for the frozen constants. Take an ell2-normalized
Dirichlet sine sequence f on L>=3 such sites, with
lambda_L=4sin2(pi/(2(L+1))), and
g_n=f_n/sqrt(v_n)/sqrt(Z), Z=sum |f_n|2/v_n.
For the parity-transformed operator the positive kinetic energy is
gamma lambda_L/Z<=gamma s lambda_L. Since gamma/mu=1/4,
\[
 \langle g,H_Pg\rangle/E_*
 \le-c_*+\sin^2(\pi/8)=-g_*<0.
\tag{47}
\]
Also H_P>=-E_*/sqrt(2). The confining Jacobi form has compact
resolvent, so each fiber in this compact P ball has a ground state in
[-E_*/sqrt(2),-g_*E_*]. The ground eigenvalue is simple, its real
eigenvector is smooth on compact P sets, and the domain argument below
gives all volume moments.

A smooth cutoff from r0=1.99 to r1=2 loses an exponentially tiny original
P tail; the certificate reports its logarithmic upper bound. This
example does not preserve the full bare source coherence: its geometric
ground state depends on P. The next construction includes that cost.

## 3. A model sequence with controlled full bare initial-state error

Write d0=3V0/2. For large integers N choose the model parameters
\[
 \mu_N={d_0\over8\delta_c^{2/3}}N^{-2/3},\quad
 \delta_N=\delta_c(1-\mu_N/q)^{-1/2},\quad
 \gamma_N=(q-\mu_N)/4 .
\tag{48}
\]
Take N large enough that mu_N<=q/2.
This is a sequence of distinct fixed models, not time-dependent
parameters or a state limit in one fixed mu>0 theory.

Let L_N=floor(N^(2/3)) and choose a fixed real smooth compact bump chi
in (-1,1). A normalized common envelope
g_N(n) proportional to L_N^-1/2 chi((n-N)/L_N)
has support in [N-L_N,N+L_N], contained in [N/2,3N/2] for large N.
All formulas in this section are in the parity representation; apply
the same J to g_N and every filtered vector to return to the original H.

Set
\[
 E_N=\mu_N\delta_N N-d_0(\delta_NN)^{1/3},\qquad
 \Lambda_N=-E_N.
\]
Since delta_c<=delta_N<=sqrt(2)delta_c,
\[
 \tfrac34d_0\delta_c^{1/3}N^{1/3}
 \le\Lambda_N\le2^{1/6}d_0\delta_c^{1/3}N^{1/3}.
\tag{49}
\]
For every fixed compact |P|<=Pcap, smooth difference and mean-value
bounds yield
\[
 \|(H_P-E_N)g_N\|\le R_N,
\]
\[
 R_N\le C_\chi\gamma_c\delta_c
       (N/L_N^2+1/L_N+1/N)
 +d_0\delta_c^{1/3}(2^{5/6}/3+\sqrt2/8)
 +P_{\rm cap}^2/(\delta_cN)=O(1).
\tag{50}
\]
Here C_chi is fixed by the bump's first two derivatives and normalization;
it is independent of N,P. The kinetic estimate follows either directly
from two differences of sqrt(n)g_N or from its leading n second
difference and first-difference terms. The other terms in (50) use
n>=N/2 and L_N<=N^(2/3).

Choose fixed 0<=f<=1, compact smooth in (-3/2,-1/2), and f=1 on
[-5/4,-3/4]. Since |1-f(e)|<=4|e+1|,
\[
 \eta_N:=\sup_{|P|\le P_{\rm cap}}
 \|(1-f(H_P/\Lambda_N))g_N\|
 \le4R_N/\Lambda_N=O(N^{-1/3}).
\]
For eta_N<=1/4 the normalized filtered section phi_P obeys
||phi_P-g_N||<=2eta_N. Its energy support is contained in
[-3Lambda_N/2,-Lambda_N/2].

Let H_cap=1_{|P|<=Pcap} H_source, which contains the support of rho_F.
The map V_N psi(P)=phi_P psi(P) is an isometry on H_cap; no negative
spectral section at all P is claimed for a fixed supercritical model.
The product isometry J_N psi(P)=g_N psi(P) is defined on the full
source space. They satisfy ||V_N-J_N|_{H_cap}||<=2eta_N.
Purification, the triangle inequality against J_N rho_old J_N*,
and partial-trace contractivity imply
\[
 D_{\rm tr}(\operatorname{Tr}_{g}V_N\rho_FV_N^*,\rho_{\rm old})
 \le\sqrt{\epsilon_{\rm tail}}+2\eta_N .
\tag{51}
\]
The same bound holds before the partial trace against the common-packet
product embedding of rho_old. Thus the geometry-induced decoherence
has been included, rather than mistaken for a diagonal P-law comparison.

## 4. The required graph domains are established

For each fixed mu>0 and compact P set, the leading diagonal coefficient
of the parity Hamiltonian is (2gamma+mu)delta N. The two weighted shifts
are relatively bounded with combined relative bound
2gamma/(2gamma+mu)<1. The N^(1/3) term has relative bound zero, and
the inverse-N term is bounded. Kato-Rellich and Carleman uniqueness give
D(H_P)=D(N) with equivalent graph norms.

For each integer k, the weighted conjugation
N^k H_P N^-k-H_P consists of bounded weighted shifts:
their coefficients are a_n[((n+1)/n)^k-1]=O_k(1), with harmless first
row terms. Diagonal potentials commute. Using the maximal Jacobi
domain, induction gives both inclusions
\[
 D(H_P^k)=D(N^k),\qquad
 \|N^k\psi\|\le C_k\sum_{j\le k}\|H_P^j\psi\|.
\tag{52}
\]
For example, if u is in D(H^(k+1)), the induction hypothesis places u
and Hu in D(N^k); the distributional identity for H N^k u and bounded
conjugation remainder places N^k u in the maximal domain D(H)=D(N).
The reverse inclusion follows by applying the finite-band expression.
These constants are uniform on a fixed compact P set, but not as mu
tends to zero.

Every compact energy-band vector above therefore has every volume
moment, uniformly through its fixed unitary history. Smooth P dependence
and a smooth source cutoff also give finite Q moments.

## 5. The constructed approximation has explicit costs

The dust mean lies in [Lambda_N/2,3Lambda_N/2]=Theta(N^(1/3)).
Because phi_P differs in norm by at most 2eta_N from the compact packet,
\[
 \langle v\rangle_P\ge
 \delta_N(N-L_N)(1-4\eta_N^2)=\Omega(N).
\]
Negative mean energy and H>=mu_Nv-d0v^(1/3), followed by Jensen, give
\[
 \langle v\rangle_P\le(d_0/\mu_N)^{3/2}
                  =16\sqrt2\,\delta_c N.
\tag{53}
\]
Thus this particular approximation has volume Theta(N) and dust energy
Theta(N^(1/3)). These are not optimal lower bounds for every conceivable
approximate extension.

In fact, using the original untransformed h=(2-S-S*)/4,
\[
 m(P)\ge {q\over4\gamma_N}
       -{d_0\over4\gamma_N}\langle v\rangle_P^{-2/3}
       \ge1-O(N^{-2/3}).
\]
It approaches the top of the polymer kinetic band, not the small-h
quadratic regime. The declared reference gap tends at least to
pi2/4-1. A real initial envelope may have zero mean expansion without
being in the original low-dispersion geometry.

## 6. A normal clock does not conceal the bare-state cost

For a fixed even compact clock envelope h with support smaller than
Lambda_N/2, FINITE_CLOCK.md gives a normal positive-clock lift.
Let the common packet be supported in n>=cN, and let
C=2sqrt(2)alpha_N. The weighted conjugation
N^-1 H_g N-H_g is bounded by C, so
||N^-1 exp(-itH_g)g_N||<=exp(C|t|)/(cN).
Duhamel then bounds the joint source/geometry interaction against the
common H_g evolution. If L4=sqrt(E_old P4), the unconditioned clock
source obeys
\[
 D_{\rm tr}(\rho_{\rm source}^{clock},\rho_{\rm old})
 \le\sqrt{\epsilon_{\rm tail}}+2\eta_N
 +{L_4\over2\delta_N cN}{e^{CT}-1\over C}
 +\int_{|t|>T}|\widetilde h(t)|^2dt .
\tag{54}
\]
The time average is CPTP, so it preserves the initial joint trace bound.
First choose the source tail and T, then N. This can make the initial
bare-source error arbitrarily small with a fixed nonzero clock residual.
The volume and dust-energy costs in (53) remain.

Equation (54) compares with the frozen input source state, not its old
A-dependent free history. In particular actual dot Q=P/v generally
differs from P/A3. This construction disproves finite-error uniqueness
of the critical point; it does not restore the original AE history,
mean geometry or local apparatus.

## 7. Uniform cost along this constructed history

The energy band yields a stronger all-time volume lower bound.
Since H>=-d0 v^(1/3) and E=-H>=Lambda_N/2 on the state,
Jensen gives
\[
 \langle v\rangle_t\ge(\Lambda_N/(2d_0))^3
                  \ge(27/512)\delta_c N .
\]
The upper bound (53) also holds at every time. Both bounds survive the
normal clock's time average. Hence this explicit route's volume and
positive vacuum total energy are Theta(N) throughout its history;
the dust mean is only Theta(N^(1/3)) and must not be mistaken for the
whole source cost. The constants do not assert an optimal cost for
other extensions.
