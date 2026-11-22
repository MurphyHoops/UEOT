# JC24 — A body-only Wick subtraction does not close the bare-clock graph

## Exact question and scope

Keep the same bare clock functions, the same independent initial Gaussian
clock/body preparation and fixed g != 0. Replace only the body fourth power
in the quartic actuator by its Wick power. This removes its vacuum mean.
It does not produce a bounded Hamiltonian image on this specified initial
sequence. The statement is a graph diagnostic, not a claim that every
renormalized interacting theory or strong-resolvent limit is impossible.

Let V=2 pi^2, mu=1/5 and
\[
 S(s)=F_0(s)^2+F_1(s)^2,\qquad
 V_{4,K}^{W}={g^2\over4}\int S(gX_K(x))
                  :\Phi_{+,K}(x)^4:_{\Omega_{+,K}}\,dx .
\]
The body ground, clock and Y programs initially form the declared product
state Psi_K. The clock has g<X>=t_i, zero-mode coordinate variance a=4,
and its k>=2 modes are the minimal massless vacuum. Its equal-time
variance and covariance are
\[
 \sigma_K^2={a\over V}+{1\over2V}
                 \sum_{k=2}^K{k^2\over\sqrt{k^2-1}},
\]
\[
 C_{X,K}(\gamma)={a\over V}+{1\over2V}
       \sum_{k=2}^K{k\over\sqrt{k^2-1}}
                         {\sin(k\gamma)\over\sin\gamma}.
\]
All products in this entry are finite-mode operators.

## 1. A positive clock probability on a shrinking spatial annulus

Set gamma=r/K with 1/2<=r<=1. Uniform Riemann sums give
\[
 {\sigma_K^2\over K^2}\to{1\over4V},\qquad
 {C_{X,K}(r/K)\over K^2}\to{1-\cos r\over2Vr^2},
 \quad
 \rho_K(r)\to {2(1-\cos r)\over r^2}.
\]
Uniformity follows from the smooth integrands on this compact r interval;
the replacement k/sqrt(k^2-1)=1+O(k^-2), the finite zero mode and
sin(r/K)/(r/K)=1+O(K^-2) have uniformly vanishing normalized errors.
The elementary cosine bounds imply
\[
 {11\over12}\le\rho(r)\le1-{29\over1440}<1.
\]
Thus, for all sufficiently large K,
\[
 0\le\rho_K\le1-d,\quad d={29\over2880},\qquad
 {K^2\over4V}\le\sigma_K^2\le{K^2\over V}.
\]
The variance lower bound also follows directly from the positive sum
and a=4.

Choose a closed interval I of length L on which S>=m>0, and put
M=max_{s in I}|s-t_i|. If also
K>=2 sqrt(V) M/(|g|sqrt(d)), the joint density of
(gX_K(x),gX_K(y)) throughout I^2 is at least
\[
 {V\over2\pi e\,g^2K^2}.
\]
Indeed the covariance's smallest eigenvalue is at least
g^2 K^2 d/(4V), while the Gaussian exponent on I^2 is at most one.
Therefore
\[
 \mathbb E_X[S(gX_K(x))S(gX_K(y))]
 \ge{m^2 L^2 V\over2\pi e\,g^2K^2}.                 \tag{1}
\]
This is an eventual fixed-g estimate; its onset is not uniform as g->0.

For the actual profiles one may take I=[-1/40,1/40], L=1/20 and m=1/4.
The normalization integral of w is <=2. In the convolution for b,
restrict its integration variable to I. Both arguments of w then have
absolute value <=1/2, so
b(s)>=(5/4)exp(-2/3)>1/2. Since cos(2s) is positive and <=1,
F_0(s)>=b(s), proving S>=1/4.

## 2. The surviving four-body vector diverges

On the same annulus the plus-body covariance obeys
\[
 C_{+,K}(\gamma)
 ={1\over2V}\sum_{k=1}^K{k\over\sqrt{k^2+\mu}}
                         {\sin(k\gamma)\over\sin\gamma}
 \ge{\sin(1)\over4V\sqrt{1+\mu}}K(K+1).
\]
Use sin(k gamma)>=sin(1) k gamma and sin gamma<=gamma.
The annulus around each x has volume at least 14/(3 pi K^3).

The Wick identity and clock/body independence give exactly
\[
 \|V_{4,K}^{W}\Psi_K\|^2
 ={3g^4\over2}\int dx\,dy\
       \mathbb E_X[S(gX_K(x))S(gX_K(y))]
                          C_{+,K}(x,y)^4 .
\]
The integrand is nonnegative everywhere, so restricting to the annulus
is legitimate. Combining this with (1) yields
\[
 \boxed{\|V_{4,K}^{W}\Psi_K\|^2
 \ge c_*g^2K^3,\qquad
 c_*={7m^2L^2\sin(1)^4\over
          512\pi^2 e V^2(1+\mu)^2}>6\,10^{-11}.}       \tag{2}
\]
The numerical constant uses the conservative explicit I,m above.
No numerical onset K_0(g) is asserted.

Let P_{4,+} be the body four-particle projection relative to the plus
ground, tensored with the identity on clock/Y/other fields.
The Wick quartic acting on the body vacuum lies entirely in that
sector. Terms of total body degree at most three, even with arbitrary
clock-dependent coefficients, cannot contribute there. In particular
the retained cubic actuator, scalar subtractions and quadratic
mass/kinetic subtractions cannot cancel it. For a candidate H_K^W
with this quartic and only those additional terms,
\[
 P_{4,+}H_K^W\Psi_K=V_{4,K}^{W}\Psi_K .
\]
Consequently the specified initial sequence has an unbounded
Hamiltonian image. A scalar or body-only Wick subtraction does not
supply its finite-image graph limit.

## What remains possible

A new clock composite, a different quartic counterterm, a changed
correlated preparation or a different recovery sequence changes this
test and must be analyzed on its own terms. Divergence on this input
does not by itself rule out strong-resolvent convergence or a
renormalized local QFT. It also does not upgrade the finite-K actual
instrument to a continuum apparatus. These are the next construction
obligations, not completed steps.
