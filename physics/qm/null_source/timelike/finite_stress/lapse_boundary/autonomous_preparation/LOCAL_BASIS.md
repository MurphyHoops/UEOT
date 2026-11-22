# AL. A complete polynomial local candidate and its perturbative UV boundary

## AL1. Symmetry contract and complete potential basis

This is a new local three-scalar candidate; it does not relabel the frozen
global-controller Z model. Impose simultaneous sign reversal of any two
of \(\chi,\phi,\psi\), and exchange \(\phi\leftrightarrow\psi\).
A monomial invariant under the sign group has three exponents of equal
parity. Up to total degree four, exchange symmetry therefore gives exactly
\[
 1,\quad\chi^2,\quad S=\phi^2+\psi^2,\quad\chi\phi\psi,\quad
 \chi^4,\quad\phi^4+\psi^4,\quad\phi^2\psi^2,\quad\chi^2S .
\]
The complete potential with this symmetry is
\[
 V=\Lambda+\frac a2\chi^2+\frac b2S+g\chi\phi\psi
 +\frac\alpha4\chi^4+\frac\beta4(\phi^4+\psi^4)
 +\frac\kappa2\phi^2\psi^2+\frac\eta2\chi^2S.                \tag{AL.1}
\]
The four quartic coefficients are independent. Dimensional power counting
in four spacetime dimensions makes \(g\) a mass-dimension-one coupling
and \(\alpha,\beta,\kappa,\eta\) dimensionless.

The full generally covariant allowed action also contains independent
kinetic normalizations \(Z_\chi,Z_s\), nonminimal
\(\xi_\chi R\chi^2/2,\xi_sRS/2\), and vacuum/gravity terms
\(1,R,R^2,R_{\mu\nu}R^{\mu\nu},R_{\mu\nu\rho\sigma}R^{\mu\nu\rho\sigma},
\Box R\), with the usual possible bulk topological redundancies.
Total derivatives and their finite-time boundary completions must be
retained under the selected variational contract. A potential basis
alone is not a complete gravitational action.

## AL2. Exact one-loop polynomial closure

The mass Hessian is
\[
 {\cal M}=\begin{pmatrix}
 a+3\alpha\chi^2+\eta S&g\psi+2\eta\chi\phi&g\phi+2\eta\chi\psi\\
 g\psi+2\eta\chi\phi&b+\eta\chi^2+3\beta\phi^2+\kappa\psi^2&
                                  g\chi+2\kappa\phi\psi\\
 g\phi+2\eta\chi\psi&g\chi+2\kappa\phi\psi&
                         b+\eta\chi^2+3\beta\psi^2+\kappa\phi^2
 \end{pmatrix}.
\]
Let \(P=\tfrac12\operatorname{tr}{\cal M}^2\). Its complete coefficients are:

| Monomial / orbit | Coefficient in \(P\) |
|---|---|
| \(1\) | \(a^2/2+b^2\) |
| \(\chi^2\) | \(3a\alpha+2b\eta+g^2\) |
| \(S\) | \(a\eta+b(3\beta+\kappa)+g^2\) |
| \(\chi\phi\psi\) | \(4g(2\eta+\kappa)\) |
| \(\chi^4\) | \(9\alpha^2/2+\eta^2\) |
| \(\phi^4+\psi^4\) | \((\eta^2+9\beta^2+\kappa^2)/2\) |
| \(\phi^2\psi^2\) | \(\eta^2+6\beta\kappa+4\kappa^2\) |
| \(\chi^2S\) | \(\eta(3\alpha+3\beta+\kappa+4\eta)\) |

This is explicit one-loop closure of the polynomial potential.
Writing \(\zeta_\chi=\xi_\chi-1/6,\zeta_s=\xi_s-1/6\), the field-dependent
curvature and total-derivative coefficients accompanying \(P\) are
\[
 R\{(3\alpha\zeta_\chi+2\eta\zeta_s)\chi^2+
       [\eta\zeta_\chi+(3\beta+\kappa)\zeta_s]S\},
\]
\[
 -\frac16\{(3\alpha+2\eta)\Box\chi^2+
                     (\eta+3\beta+\kappa)\Box S\}.          \tag{AL.2}
\]
The complete field-independent heat polynomial also includes
\[
 \frac{a^2}2+b^2+(a\zeta_\chi+2b\zeta_s)R
 +\frac12(\zeta_\chi^2+2\zeta_s^2)R^2
 +\frac{R_{\mu\nu\rho\sigma}^2-R_{\mu\nu}^2}{60}
 +\left[\frac1{10}-\frac{\xi_\chi+2\xi_s}{6}\right]\Box R.    \tag{AL.3}
\]
All are within the common factor \(1/(16\pi^2)\).
If \(P\) is used including its constant term, do not add that constant a
second time from (AL.3). These formulas follow from the same heat
coefficient convention as AK, not from an independent noise ansatz.

## AL3. Nonempty classical stability region

A sufficient nonempty stability region is
\[
 \alpha>0,\quad\beta>0,\quad\kappa>-\beta,\quad\eta\ge0.
\]
Put \(m_4=\min\{\alpha,\beta+\min(\kappa,0)\}>0\),
\(c_4=m_4/12\), \(R_*= (\chi^2+\phi^2+\psi^2)^{1/2}\), and
\(c_2=\frac12\max\{(-a)_+,(-b)_+\}\).
Then the quartic part is at least \(c_4R_*^4\), while
\[
 |g\chi\phi\psi|\le |g|R_*^3/(3\sqrt3).
\]
Two elementary Young bounds give
\[
 V-\Lambda\ge\frac{c_4}{2}R_*^4-
       \left[\frac{g^4}{108c_4^3}+\frac{c_2^2}{c_4}\right]. \tag{AL.4}
\]
Thus the candidate is classically stable even for finite negative mass
coefficients. This raw potential statement is not a uniform bound after
cutoff-dependent Wick ordering or renormalization.

## AL4. One-loop closure does not give a weakly coupled UV completion

For canonical pure scalars in four-dimensional minimal subtraction,
the scalar one-loop potential is
\[
 V_1=\frac1{64\pi^2}\operatorname{tr}
 \{{\cal M}^2[\log({\cal M}/\mu^2)-3/2]\}.
\]
The field-independent derivative of the logarithm fixes
\(\mu\partial_\mu V_1=-P/(16\pi^2)\).
At this order this canonical scalar theory has no wavefunction pole:
the quartic tadpole is momentum independent and the cubic bubble's
momentum-dependent part is UV convergent in four dimensions.
Consequently the one-loop potential beta polynomial is
\(\beta_V=P/(16\pi^2)\).
The normalization can be checked against the scalar specialization of
Martin's one-loop formulas in
[hep-ph/0111209](https://arxiv.org/abs/hep-ph/0111209).

In particular
\[
 \boxed{\frac{d\alpha}{d\log\mu}
       =\frac{18\alpha^2+4\eta^2}{16\pi^2}} .               \tag{AL.5}
\]

The other quartic beta polynomials, in the same \(16\pi^2\) normalization, are
\[
 2(\eta^2+9\beta^2+\kappa^2),\quad
 2(\eta^2+6\beta\kappa+4\kappa^2),\quad
 2\eta(3\alpha+3\beta+\kappa+4\eta)
\]
for \(\beta,\kappa,\eta\), respectively.
The raw stability cone in AL3 is invariant under this formal forward
one-loop flow until the flow/approximation ends: \(\alpha,\beta\)
increase, the sign of \(\eta\) cannot cross zero, and
\[
16\pi^2\frac{d(\beta+\kappa)}{d\log\mu}
 =2[2\eta^2+(3\beta+\kappa)^2+4\kappa^2]\ge0 .
\]
This is a useful finite-scale consistency check, not exact RG stability.

For \(\alpha_0>0\), a formal one-loop trajectory reaches any fixed
\(\alpha_w>\alpha_0\), or exits the other assumptions earlier, by
\[
 \Delta\log\mu\le\frac{16\pi^2}{18}
                \left(\frac1{\alpha_0}-\frac1{\alpha_w}\right).
                                                               \tag{AL.6}
\]
Its formal pole is no later than \(16\pi^2/(18\alpha_0)\).
The approximation loses controlled weak-coupling validity before using a
formal pole as a physical assertion. This is not a nonperturbative
triviality theorem, nor a no-go theorem for UV completions with additional
fields or different dynamics. It prevents treating one-loop algebraic
closure as sufficient evidence for the current pure-scalar UV completion.

## AL5. A spatial lapse contact invisible to the homogeneous average

For an allowed \(R^2\) term \(I=\gamma_R\int N\sqrt h\,R^2\), static \(h\),
zero shift and a closed slice, \(R=R_h-2\Delta_hN/N\) implies
\[
 \frac{\delta I}{\delta N}
 =\gamma_R\sqrt h\,[2R_hR-R^2-4\Delta_hR].
\]
At \(N=1\) and constant \(R_h=6\), its second lapse derivative acts as
\[
 \eta_N\longmapsto8\gamma_R\sqrt h\,\Delta_h^2\eta_N.         \tag{AL.7}
\]
The homogeneous mode sees zero, whereas a degree-\(\ell\) harmonic has
coefficient \(8\gamma_R[\ell(\ell+2)]^2\).
This is a deterministic local response contact, not stochastic noise.
Its coefficient is a renormalization datum. The \(R^2\) bulk divergence
in (AL.3) vanishes when all fields are conformally coupled; no nonzero
\(\gamma_R\) is forced in that special case. Other curvature terms and
general metric variations must still be retained in the complete problem.

## Acceptance

Accepted: the complete symmetry-restricted potential, its explicit one-loop
local closure, a nonempty raw stability region, and the limited
perturbative UV conclusion. AM next constructs a normal joint finite-cutoff
CTP object for a concrete stable member and tests its actual UV preparation.
No claim of an exact continuum local theory or physical unification is made.
