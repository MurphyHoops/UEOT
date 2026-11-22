# JC2 — A specified covariant stationary datum and an actual mean background

## Contract

This is a **new stationary comparator**, using the coupled AP ground state
\(\Omega_r\), \(r=1/5\), on a round Einstein static universe. It is not the
finite-time AQ ramp state, the original minimally coupled geometry, an
autonomous apparatus, or a calibrated physical cosmology. Finite curvature
couplings are part of the declaration below. The Core remains unchanged.

Use \(V_0=2\pi^2\), radius \(a>0\), fixed dimensionful source \(r\), and
\(z=ra^2<1\). The two normal fields have frequencies
\[
 \omega_{\sigma k}(a)=a^{-1}\sqrt{k^2+\sigma z},\qquad
 \sigma=\pm,\quad k\geq1,\quad {\rm multiplicity}=k^2 .
\]
All derivatives with respect to \(a\) below hold \(r\), the renormalization
scale and the finite couplings fixed.

## 1. Energy data alone did not specify the stress

The inherited AP energy, at unit radius, is
\[
 e(z)=\sum_{k\geq1}k^3\left\{
 \frac{\sqrt{1+z/k^2}+\sqrt{1-z/k^2}}2-1+
 \frac{z^2}{8k^4}\right\}
 =-\sum_{n\geq2}a_nz^{2n},
\]
where
\[
 a_n=c_n\zeta(4n-3),\quad
 c_n=-{1/2\choose2n}
 =\frac{{4n\choose2n}}{16^n(4n-1)}>0.
\]
It does not, by itself, determine a covariant pressure. In particular,
differentiating \(a^{-1}e(ra^2)\) omits a logarithmic contribution.

Here is an explicit completion. On the compact Euclidean section
\(S^1_\beta\times(S^3,a^2\gamma)\), use the local zeta determinant of
\[
 P_\sigma=-\partial_\tau^2-\Delta_{a^2\gamma}
              +R[a^2\gamma]/6+\sigma r .
\]
Its spectrum is positive since \(z<1\). Use the associated conserved
point-split stress and then take \(\beta\to\infty\). The positive gap gives
exponential decay of the thermal correction, including parameter
derivatives on a compact positive-gap neighborhood. The equality of local
zeta and point-splitting prescriptions, and the external-potential Ward
identity, are the relevant results of Moretti's Theorem 2.2 in
[gr-qc/0109048](https://arxiv.org/abs/gr-qc/0109048) and Theorems 2.4–2.5 in
[gr-qc/9809006](https://arxiv.org/abs/gr-qc/9809006). These existing theorems
are not counted as new results here.

For the zero-point energy the meromorphic expression is
\[
 \mu_{\rm ren}^{2s}a^{2s-1}\left[
 \zeta(-3+2s)+\left(-\frac18+\frac{s^2}2\right)
 z^2\zeta(1+2s)
 +\sum_{n\geq2}{1/2-s\choose2n}
 z^{2n}\zeta(4n+2s-3)\right].
\]
Its pole is \(-r^2a^3/(16s)\); the scale-dependent finite term is
\(-r^2a^3\log(a\mu_{\rm ren})/8\). Finite local differences between this
finite-part expression and the determinant prescription are absorbed in
the stated source-square datum, rather than presumed absent.

Add the Lorentzian finite local action
\[
 S_{\rm fin}=\alpha\int\sqrt{-g}\,R^2+
             c_s\int\sqrt{-g}\,r^2,\qquad
 \alpha=\frac1{4320V_0}.
\]
The first term contributes
\[
 T_{\mu\nu}^{R^2}=-2\alpha\{2RR_{\mu\nu}
 -\tfrac12g_{\mu\nu}R^2+
 2(g_{\mu\nu}\Box-\nabla_\mu\nabla_\nu)R\}.
\]
Thus \(E_{R^2}=-36\alpha V_0/a=-1/(120a)\); it cancels the
two-field conformal Casimir energy. Fix \(c_s\), at a fixed scale, so
\(E(1,r)=e(r)\) for the nearby source family. Fix all other available finite
local coefficients to zero relative to this zeta prescription. This yields
\[
 \boxed{E(a,r)=a^{-1}e(ra^2)-\frac{r^2a^3}{8}\log a.}                 \tag{1}
\]
The unit of radius implicit in \(\log a\) is the fixed reference unit.
No logarithm of a dimensionful number is intended.

This is a stationary closed-time-circle or compact-variation datum.
An \(R^2\) finite-slice boundary action and its full two-branch CTP extension
are not supplied by this calculation.

## 2. Same-cutoff matching for the homogeneous radius family

Let \(e_K\) be the displayed constituent sum through \(k=K\). Define the
**new restricted radius prescription**
\[
 E_K^{\rm cov}(a,r)=a^{-1}e_K(ra^2)-r^2a^3\log a/8 .                 \tag{2}
\]
At \(a=1\) it equals the inherited finite-mode ground energy. At general
radius the additional term is necessary: a comoving cutoff \(K\) represents
proper scale \(K/a\), whereas the physical subtraction scale is fixed.
Equation (2) specifies that matching explicitly. It is not an assertion
that a sharp finite spectral cutoff is locally covariant for arbitrary
spatial metrics. No inherited counterterm is silently differentiated into
a new stress tensor.

The \(k^{-5}\) remainder and its first two source derivatives converge
uniformly on a compact \(z<1\) interval. Consequently (2), its radius
derivatives and its source derivatives recover (1) in this restricted
family. This is the finite-mode link used in the numerical certificate.

## 3. Mean Einstein equations with one selection of constants

Define
\[
 \rho(a)=\frac{E(a,r)}{V_0a^3},\qquad
 p(a)=-\frac{\partial_aE(a,r)}{3V_0a^2}.
\]
At unit radius,
\[
 \rho_0=\frac{e}{V_0},\quad
 p_0=\frac{e-2re'+r^2/8}{3V_0},\quad
 F(r)=4e-2re'+r^2/8
 =r^2/8+\sum_{n\geq2}(4n-4)a_nr^{2n}>0.
\]
In particular \(\rho_0+p_0=F/(3V_0)>0\). The trace contains the
source-square anomaly,
\[
 -\rho_0+3p_0=-2re'/V_0+r^2/(8V_0).
\]
A finite source-square constant shifts \(\rho\) and \(p\) oppositely and
does not change this enthalpy.

Select once
\[
 \boxed{G_N=\frac{3V_0}{4\pi F(r)}>0,\qquad
 \Lambda=3-\frac{8\pi G_Ne(r)}{V_0}.}                               \tag{3}
\]
Then
\[
 3-\Lambda=8\pi G_N\rho_0,\quad
 \Lambda-1=8\pi G_Np_0,\quad \langle T_{0i}\rangle=0
\]
hold exactly. This signs a mean static solution of the specified
renormalized semiclassical equations, with the finite curvature datum
included. It does not establish gravitational stability, full quantum
constraints, SI values of \(G_N,\Lambda\), or a finite-past ground-state
preparation.

## 4. Controlled intervals and a second-order radius diagnostic

The independent certificate uses \(K=256\), outward interval arithmetic,
and direct constituent sums. With \(\kappa=1-r\),
\[
 |e-e_K|\leq\frac{5r^4}{512(1-r^2)K^4},\quad
 |e'-e_K'|\leq\frac{5r^3}{128(1-r^2)^2K^4},\quad
 |e''-e_K''|\leq\frac{15r^2}{128\kappa^{7/2}K^4}.                  \tag{4}
\]
Each omitted derivative is negative. These follow by the even binomial
expansion (or its differentiated Taylor remainder) and
\(\sum_{k>K}k^{-5}\leq1/(4K^4)\). The coefficients decrease:
\(c_{n+1}/c_n=(4n-1)(4n+1)/[4(2n+1)(2n+2)]<1\).
The certificate also encloses the inherited AP energy interval as a
consistency check, without executing that module.

For the static radius-family scalar constraint define
\[
 {\cal C}(a)=6/a^2-2\Lambda-16\pi G_N\rho(a).
\]
Equations (1)–(3) give
\[
 {\cal C}(1)={\cal C}'(1)=0,\qquad
 \boxed{{\cal C}''(1)=24\{rF'(r)/F(r)-1\}>24.}                     \tag{5}
\]
The strict inequality follows because \(F\) is a positive series with
powers at least two and with nonzero higher powers. It demonstrates a
nonzero second-order geometric direction which must be retained in a
subsequent compatibility calculation. It is not a nonstatic evolution,
nor proof that this direction solves a coded or apparatus-sourced
constraint.
