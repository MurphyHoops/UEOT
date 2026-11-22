# JC13 — Exact curvature data do not alone fix the metric phase

Use the actual lapse family in LAPSE_HISTORY.md,
\(N=1+f(t)Z\), \(q=fZ/(1+fZ)\).
Direct curvature contraction gives
\[
 R=6(1+q),\quad
 R_{\mu\nu\rho\sigma}R^{\mu\nu\rho\sigma}=12(1+q^2),\quad
 R_{\mu\nu}R^{\mu\nu}=12(1+q+q^2).
\]
Consequently
\[
 C_{\mu\nu\rho\sigma}C^{\mu\nu\rho\sigma}=0,\qquad
 {\cal E}_4=24q .
\]
These formulas hold for smooth time-dependent \(f\); no omitted
\(f'\) or \(f''\) appears in these curvature scalars when the
spatial metric and extrinsic curvature are fixed.

Since \(Nq=fZ\), the spatial integral of
\(\sqrt{-g}{\cal E}_4\) vanishes at every time.
The spacetime integral of \(\sqrt{-g}\Box R\) is a boundary term,
\(-[\int N^{-1}\dot R\,dV]\), which vanishes at the flat endpoints.
For the constant matrix source \(r\sigma_x\),
\(\int Nr^2\,dV=r^2V_0\).

The two conformal fields' traced heat coefficient, with the usual
overall \((4\pi)^{-2}\) removed, is
\[
 r^2+C^2/60-{\cal E}_4/180+\Box R/90 .
\]
Thus the relative integrated \(a_4\) on this family is zero.
The relative \(a_0\) is also zero, and the traced \(a_2\) is zero.
The general heat-coefficient formula is (4.28) of Vassilevich,
[hep-th/0306138](https://arxiv.org/abs/hep-th/0306138);
the substitution and restricted-family cancellations above are
computed here.

There is nevertheless a nonzero finite curvature action.
Writing
\[
 J(f)=\int\frac{dV}{1+fZ}
      =\frac{2V_0}{1+\sqrt{1-f^2}},
\]
one finds
\[
 \int NR^2\,dV=36J(f).
\]
For the explicitly selected
\(\alpha=1/(4320V_0)\) in GROUND_DATUM.md, its relative finite action is
\[
 \Delta S_\alpha
 =\frac1{120}\int
     \frac{1-\sqrt{1-f^2}}{1+\sqrt{1-f^2}}\,dt .                  \tag{1}
\]
In the Hamiltonian the corresponding scalar term is
\(c_\alpha(t)=-\Delta{\cal L}_\alpha\), so the evolution and CTP
factors are respectively
\(e^{i\Delta S_\alpha}\) and
\(e^{i\Delta S_\alpha[f_+]-i\Delta S_\alpha[f_-]}\).
Its lapse-column contribution and initial contact are
\[
 A_\alpha=-\frac{f}
 {60\sqrt{1-f^2}(1+\sqrt{1-f^2})^2},\qquad
 \left.\frac{\delta A_\alpha(t)}{\delta f(s)}\right|_0
       =-\delta(t-s)/240 .                                      \tag{2}
\]
The contact vanishes from the final source-off signal but matters
inside the two-branch variation.

A zero relative ultraviolet pole is **not** proof that a finite
canonical phase equals the covariant zeta/Hadamard phase.
Equation (1) is the known explicit finite action contribution.
A finite anomaly contribution of the underlying prescription, the
chosen incoming state and its endpoint normalization still have to
be matched. No complete arbitrary-metric determinant, metric CTP
Hessian or Einstein solution is signed by these curvature identities.
