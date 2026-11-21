# A genuinely common-geometry positive-window comparison

This certificate compares the **new** two-ring and single-ring invariant preparations of INVARIANT_PREPARATION.md before any readout. It does not change the original actual-state certificate or borrow its posterior geometries.

Both new inputs have identical complete two-point functions and the same invariant mean source as the original static solution. Keep the already certified static mean-SCE root \(a=A\), original \(M^2,U_0\), all high modes and thermal occupations, and the fixed AE prescription. Their mean residuals are both exactly zero. No static root, old checker or old mode ODE is rerun.

Use the same smooth normalized window \(g\) as FLUCTUATIONS.md in \(\tau=\lambda t_{\rm proper}\), with \(T=0.1\). The actual proper duration is \(0.1/\lambda\), approximately 10009 model units. Normalize both equations by the same positive \(3/(2A^2)\).

## Zero mode and static high modes

The source coefficient in either normalized equation is
\[
K_S={M^2\over3A^4}.
\]
For the single ring, \(V_{\rm mid}=4(v/C)L+4(v/C)^2\). Its two-component contribution is \(2K_S^2V_{\rm mid}\).

On a static background the high density is a number Hamiltonian; its vacuum variance is zero. The finite eight thermal \(k=2\) oscillators give
\[
V_{\rho,\rm thermal}={8n(n+1)\over3\pi^4A^4}.
\]
For pressure, the pair coefficient is
\(-2\omega_k\widehat g(2\omega_k/(\lambda A))/3\). Including both fields and shell degeneracy \(k^2\),
\[
V_{p,\rm vacuum}={4\over81\pi^4A^4}
 \sum_{k=2}^\infty k^2\omega_k^2
   |\widehat g(2\omega_k/(\lambda A))|^2.
\]
The thermal number and excess pair terms together obey
\[
V_{p,\rm thermal}\le{40n(n+1)\over27\pi^4A^4}.
\]
These are full infinite-mode expressions, not a pressure variance inferred from energy variance.

## An explicit ultraviolet tail

The quartic Beta(3,3) profile on an interval of width \(T/2\), convolved with a positive smooth mollifier, satisfies
\(\|g^{(3)}\|_1\le300/(T/2)^3=2.4\,10^6\).
The weak third derivative includes its endpoint jumps. Since \(\lambda A<1\),
\[
|\widehat g(2\omega/(\lambda A))|
 \le\min(1,300000/\omega^3).
\]
At \(K=70\),
\[
\sum k^2\omega_k^2|\widehat g|^2
 \le\sum_{k=2}^{70}k^4
       +300000^2\sum_{k>70}{k^2\over(k^2-1)^2}
 \le348259330+{300000^2\,16\over9\cdot70}
 <3\,10^9.
\]
The tail uses \(k^2/(k^2-1)^2\le16/(9k^2)\) and the integral bound \(\sum_{k>K}k^{-2}\le1/K\). No numerical mode integration or unverified cutoff is used.

## Complete source-side result

The inputs are explicitly zero/high product preparations, unlike the correlated poststates in ACTUAL_HISTORY.md. Therefore their centered zero/high covariance is zero by construction. No density/pressure covariance is discarded when summing the two squared components. The single-ring bound is
\[
{\cal R}_{\rm mid}^2
 \le2K_S^2V_{\rm mid}
       +V_{p,\rm vacuum}
       +V_{\rho,\rm thermal}+V_{p,\rm thermal},
\qquad {\cal R}_{\rm mid}<1.4\,10^{-6}.
\]
The interval upper bound is about \(1.309783\,10^{-6}\).

Every high-sector contribution is identical for the pair. Hence the exact difference of squared joint residual norms is
\[
{\cal R}_{\rm two}^2-{\cal R}_{\rm mid}^2
 ={3\over8}\left({M^2\over3A^4}\right)^2,
\]
and \({\cal R}_{\rm two}>0.14\) on this same geometry and same window.

This is a true common-geometry comparison, unlike comparing the old small-domain lower bound with a different finite-initial future construction. The improvement comes from changing the invariant radial preparation and removing a classical mixture variance, while retaining the quantum within-block floor.

The result remains a spatially averaged matter-equation residual moment on a prescribed exact **mean** geometry. It is not a measured metric variance, an exact operator constraint, a stability theorem for the fast semiclassical modes, or a total-source apparatus history. The original angular-equivalence negative result still holds, and the new annulus classifier is a separate source calibration instrument with its own resource costs.
