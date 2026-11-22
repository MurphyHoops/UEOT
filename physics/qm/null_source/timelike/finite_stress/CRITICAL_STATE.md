# A normal joint state at the critical point

All choices below are made once. There is one self-adjoint H, one initial
normal state and the evolution exp(-itH), with no time-by-time roots.

## 1. Uniform negative spectral mass

At q=4gamma, use J u_n=(-1)^n u_n. Then
\[
 JH_PJ=\alpha T-dN^{1/3}+\epsilon N^{-1},\quad
 T=\sqrt N(2-S-S^*)\sqrt N\ge0.
\tag{8}
\]
Here N is the number operator; write B for a positive real packet center.

Choose the fixed real smooth bump
\[
 w(s)=\exp(4-1/[(s-1)(2-s)])\quad(1<s<2),
\]
and zero outside. For B>=8 put
\[
 Z_B^2=B^{-1}\sum_n w(n/B)^2,\quad
 b_B(n)=B^{-1/2}w(n/B)/Z_B,\quad \chi_B=Jb_B.
\]
On [5/4,7/4], w>=exp(-4/3), so
\[
 (3/8)e^{-8/3}\le Z_B^2\le9/8.
\]
Flatness of the bump at its endpoints gives smooth dependence on all
real B, including values where a lattice site enters the support, and
||partial_B^k b_B||<=C_k B^-k.

Let h(s)=sqrt(s)w(s). A central second-difference bound gives
||T b_B||<=C_T/B. An explicit conservative choice is C_T=16000.
Indeed, with z=1/[(s-1)(2-s)]>=4,
|w'|<=16, |w''|<=416 and |h''|<=416sqrt(2)+16+1/4<605.
The support count and square-root factors give
C_T,derived<=4*605/[(sqrt(3/8))exp(-4/3)]<16000;
we use the larger fixed constant C_T=16000 throughout.
This estimate applies to b_B; the original-H seed is chi_B=Jb_B.

Choose
\[
 B(P)=B_*+\eta(1+|P|^2)^{3/4},\quad M(P)=B(P)^{1/3},
\]
\[
 B_*\ge8,\quad B_*^{4/3}\ge4\alpha C_T/d,\quad
 \eta^{4/3}\ge2/(\delta d).
\tag{9}
\]
Momentum and constants are in the declared model units. One choice is
B_*=8 and eta=(4/(delta d))^(3/4); the frozen input intervals verify (9).
All P are retained, including every Gaussian tail.

The support B<n<2B and (9) imply
\[
 \langle H_P/M\rangle_{\chi_B}\le-d/2=-m,\qquad
 \|(H_P/M)\chi_B\|\le d(2^{1/3}+1/2)=M_0.
\tag{10}
\]
The gradient and matter terms each cost at most d/4 in these bounds.

Set r=m/2 and R=4M_0^2/m. The negative first moment of the spectral
measure in (10) is at least m. The pieces (-r,0) and (-infinity,-R)
contribute at most m/2 and M_0^2/R=m/4, respectively. Thus the band
[-R,-r] has probability at least
\[
 q_*={m^2\over16M_0^2}
 ={1\over64(2^{1/3}+1/2)^2}>0.
\tag{11}
\]
No approximate-eigenvector assumption is used here.

Fix one real f in C_c^infinity(R), with support contained in
[-2R,-r/2], 0<=f<=1, equal to one on [-R,-r]. An explicit choice is
f(e)=s((e+2R)/R)s((-e-r/2)/(r/2)),
where s(x)=0 for x<=0, s(x)=1 for x>=1, and for 0<x<1,
s(x)=exp(-1/x)/(exp(-1/x)+exp(-1/(1-x))).
Define
\[
 \phi_P={f(H_P/M(P))\chi_{B(P)}
              \over\|f(H_P/M(P))\chi_{B(P)}\|}.
\tag{12}
\]
The denominator is at least sqrt(q_*). The support is entirely in
[-2RM(P),-rM(P)/2], and every H moment is bounded by (2RM(P))^k.
This f is a mathematical ingredient in defining a normal initial state;
a laboratory postselection instrument realizing it is not asserted.

## 2. Normality and exact momentum law

On the original zero-mode Hilbert space L2(R2,d2P), define
(V psi)(P)=phi_P psi(P). This is an isometry. For the frozen original
normal zero-mode density rho_old set
\[
 \Omega=V\rho_{\rm old}V^*,\qquad
 \Omega=\Pi\Omega\Pi,\quad \Pi=1_{(-\infty,0)}(H).
\tag{13}
\]
It is positive, trace one and normal. It is not a diagonal distribution
in the continuous P label. In particular
\[
 \Omega_{nn'}(P,P')=\phi_P(n)\rho_{\rm old}(P,P')
                                      \overline{\phi_{P'}(n')}.
\]
The entire joint P law is exactly unchanged; P is also conserved under H.
The bare source density becomes
\[
 \rho_{\rm new}(P,P')=\rho_{\rm old}(P,P')
                              \langle\phi_{P'},\phi_P\rangle.
\tag{14}
\]
Thus preservation of momentum/stress data does not imply preservation of
the full bare state.

## 3. Smooth section and source moments

The common-domain bounded perturbation H_s=H_0+sD, ||D||=1/(2delta),
makes functional calculus differentiable in s. For
F(s,M)=f(H_s/M),
\[
 \|\partial_M^a\partial_s^b F\|
 \le C_{ab} M^{-a-b}\|D\|^b.
\tag{15}
\]
To see this without differentiating an unbounded operator in norm, first
write partial_M^a f(lambda/M)=M^-a g_a(lambda/M),
with g_a compact and smooth. Then apply the Fourier representation and
the bounded-perturbation Duhamel formula for s derivatives; its integrals
are bounded by Schwartz seminorms of g_a.

The derivatives of B(P), M(P), the seed and the nonvanishing normalization
are at most polynomial in P. Hence all partial_P^k phi_P have polynomial
bounds. The frozen source is a Gaussian mixture with a compact set of
centers; its wavefunctions are Schwartz uniformly in the mixture label.
All zero-mode Q and P polynomial moments of (13) are finite. On every
finite time window, bounded-P-perturbation Duhamel estimates for
exp(-itH_P) preserve this conclusion.

The section can be globally chosen real. Normalization then gives
<phi_P,partial_j phi_P>=0. Initially, bare Q means and symmetrized QP
are preserved, while the real symmetrized QQ covariance gains
\[
 \Delta\langle Q_jQ_k\rangle
 =\int p_{\rm old}(P)
           \langle\partial_j\phi_P,\partial_k\phi_P\rangle\,d^2P,
\tag{16}
\]
a finite positive semidefinite matrix. These are bare partial-trace
moments, or moments of the physical compressed Q measurement POVM;
they do not establish a physical canonical self-adjoint Q on Pi.

## 4. Evolution and the remaining gate

VOLUME_MOMENTS.md proves that smooth negative-energy filtering preserves
all positive polynomial volume moments, including <v2>. The coefficients
of those bounds grow at most polynomially with P for (12), so the full
Gaussian mixture is integrable. POSITIVE_SOURCE.md then proves finite
constituent means and total positive-energy second moment throughout each
finite proper-dust-time window.

The exact equation is i partial_t Omega=[H,Omega], and the dust constraint
holds in the physical inner-product construction. It is not the old
AE mean-SCE equation, and no classical metric trajectory is identified
with a moment without a further approximation argument. Actual local
Hadamard/RSET and an autonomous preparation apparatus remain open.
