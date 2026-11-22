# AI. Free composite noise and the modes omitted by a homogeneous controller

## AI1. Exact ESU spectral normalization

The unit spatial \(S^3\) has \(V_0=2\pi^2\). Real harmonics \(Y_{\ell a}\)
are \(L^2\)-normalized, with multiplicity \((\ell+1)^2\).
For independent free conformal scalar fields \(\phi,\psi\), define the
spatially smeared composite
\[
 B_{\ell a}(t)=\int_{S^3}Y_{\ell a}(y)\phi(t,y)\psi(t,y)\,dV_y .
\]
There is no same-field contraction between \(\phi\) and \(\psi\).
All expressions below are vacuum distributional expressions. In
particular \(B_{\ell a}(t)\Omega\) is not asserted to be a vector.

The conformal two-point function is
\[
 W_0(\tau,\gamma)=\frac1{2V_0}
     \sum_{j\ge1} U_{j-1}(\cos\gamma)e^{-ij\tau},
\]
where \(U\) is a Chebyshev character. The identity
\[
 U_{j-1}U_{k-1}
 =\sum_{\ell=|j-k|,\ {\rm step}\ 2}^{j+k-2}U_\ell
\]
has coefficient one. At \(n=j+k=\ell+2+2r\), the allowed values of \(j\)
are \(r+1,\ldots,r+\ell+1\), hence there are \(\ell+1\).
Spatial projection of \(U_\ell\) on a normalized harmonic contributes
\(V_0/(\ell+1)\). These factors yield the exact covariance
\[
 \langle B_{\ell a}(t)B_{\ell a}(s)\rangle
  =\frac1{4V_0}\sum_{r\ge0}
       e^{-i(\ell+2+2r)(t-s)}.                                \tag{AI.1}
\]
For \(\widehat g(\omega)=\int g(t)e^{i\omega t}dt\), real smooth compact \(g\),
\[
 \operatorname{Var}B_{\ell a}(g)
  =\frac1{4V_0}\sum_{r\ge0}
       |\widehat g(\ell+2+2r)|^2<\infty.                      \tag{AI.2}
\]
The sharp-time sum diverges even though the input is Hadamard.

## AI2. Actual free canonical cutoffs, spatial regularity and tails

Cut off each constituent field at frequency \(K\).
At a permitted \(n=\ell+2+2r\), the actual pair count is
\[
 c_{n,K}=\max\{0,\min(\ell+1,2K-n+1)\}.
\]
Thus the coefficient in (AI.2) becomes
\(c_{n,K}/[4V_0(\ell+1)]\). This is the actual pair restriction,
not an arbitrary cutoff imposed on the final composite frequency.
The coefficients increase to those of (AI.2). Orthogonal free
two-particle sectors also give convergence of the actual vectors
\(B_{\ell a,K}(g)\Omega\), not only convergence of their norms.

Summing the full spatial multiplicities gives
\[
 \sum_{\ell,a}\|B_{\ell a}(g)\Omega\|^2
   =\frac1{24V_0}\sum_{n\ge2}n(n^2-1)|\widehat g(n)|^2,        \tag{AI.3}
\]
using
\(\sum_{j=n-1,n-3,\ldots>0}j^2=n(n^2-1)/6\).
At finite \(K\) the coefficient is instead
\[
 \frac1{4V_0}\sum_{j=n-1,n-3,\ldots>0}
        j\,\max\{0,\min(j,2K-n+1)\}.
\]
All pairs with \(n\le K+1\) are included. Consequently the squared norm of
the omitted full vector is bounded by the tail of (AI.3) over \(n>K+1\).

For spatial Sobolev weight \((\ell+1)^{2s}\), \(s\ge0\), one has
\[
 \sum_{\ell,a}(\ell+1)^{2s}\|B_{\ell a}(g)\Omega\|^2
 \le\frac1{24V_0}
      \sum_{n\ge2}n^{2s+1}(n^2-1)|\widehat g(n)|^2 .
\]
The bound is finite after \(N>s+2\) time integrations by parts.
Thus the time-smeared free vector has every finite spatial Sobolev moment.
This does not establish the interacting stress or a self-adjoint nonlinear
local Hamiltonian.

## AI3. A local controller is forced in its nonzero spatial modes

Consider the first Dyson vector of the local interaction
\[
 H_I(t)=\lambda g(t)\int_{S^3}\chi(t,y)\phi(t,y)\psi(t,y)\,dV_y
\]
in three free vacua, with controller frequency \(\nu_\ell>0\).
For one controller harmonic \((\ell,a)\), its squared first-order amplitude is
\[
 \frac{\lambda^2}{8\nu_\ell V_0}
   \sum_{r\ge0}|\widehat g(\nu_\ell+\ell+2+2r)|^2.             \tag{AI.4}
\]
When the controller is conformal, \(\nu_\ell=\ell+1\), the full sum is
\[
 \frac{\lambda^2}{64V_0}
     \sum_{\substack{n\ge3\\n\ {\rm odd}}}
        (n^2-1)|\widehat g(n)|^2.                            \tag{AI.5}
\]
Again actual three-field cutoff vectors converge by their orthogonal
three-particle decomposition and the smooth Fourier tail.

This is a norm of a first-order vector. It is not a claim that a continuum
probability equals this expression plus a uniformly controlled
\(O(\lambda^4)\) remainder: neither that remainder nor the full interacting
dynamics is established here. The cubic stability issue is examined in AK.

Not every nonzero compact test has a nonzero value at every spectral
frequency, so we give a concrete test:
\[
 \tau=\tfrac1{10},\qquad
 g(t)=\exp[1-1/(1-(t/\tau)^2)]\ (|t|<\tau),\quad g=0\ {\rm otherwise}.
\]
On the central half interval, \(g\ge e^{-1/3}\); hence
\(\int g\ge\tau e^{-1/3}\). Throughout its support
\(\cos(5t)\ge\cos(1/2)>0\), so
\[
 \widehat g(5)\ge\tfrac1{10}e^{-1/3}\cos(1/2)>0.
\]
For each \(\ell=1\) controller harmonic, \(\nu_1=2\), the \(r=0\) contribution
in (AI.4) is at least
\[
 \boxed{\frac{\lambda^2e^{-2/3}\cos^2(1/2)}{1600V_0}>0.}      \tag{AI.6}
\]
The proposed local controller therefore has nonzero first-order amplitude
in modes omitted by a purely homogeneous controller ansatz. This is a
specific diagnostic, not a complete nonlinear solution or a no-go theorem
for all local preparations.

## Acceptance

Accepted: normalized free composite covariance, actual cutoff vector
limits, smooth time/spatial bounds, and a positive first-order omitted-mode
coefficient for the specified compact test. Open: complete interacting
normal state, causal instrument, stress renormalization and Einstein closure.
