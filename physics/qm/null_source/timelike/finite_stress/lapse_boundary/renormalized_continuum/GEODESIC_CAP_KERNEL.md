# RC01 — Geodesic-Cap Sensor Kernel on $S^3$: Exact Funk–Hecke Multipliers, Finite-Range Microcausality, and $O(k^{-10})$ Decay

## Scope and Decision

At fixed coupling $g > 0$, `CLOCK_UV` and `WICK_CLOCK_GRAPH` proved that sharp spherical-harmonic truncation $P_K$ of the pointlike autonomous actuator cannot converge as $K \to \infty$: the point clock variance grows like $K^2$ and the four-particle body graph norm diverges. Instead of modifying the canonical field algebra or claiming a pointlike $\rho_0 \to 0$ Wightman interaction, we introduce an explicit **finite-radius geodesic-cap apparatus sensor kernel** on unit $S^3 \subset \mathbb{R}^4$ ($V_0 = 2\pi^2$):
\[
 \kappa_{\rho_0}(x, y) := C_{\rho_0}^{-1}\big(x \cdot y - \cos\rho_0\big)_+^8, \qquad \rho_0 = \frac{1}{20}\text{ rad}. \tag{1}
\]

This kernel is nonnegative, $SO(4)$-invariant, $C^7$-smooth on $S^3 \times S^3$, and strictly supported in the closed geodesic ball $d_{S^3}(x, y) \le \rho_0$. It defines a new finite-range continuum apparatus model; it does not overturn `CLOCK_UV` in the $\rho_0 \to 0$ pointlike limit.

## 1. Exact Nine-Harmonic Funk–Hecke Eigenvalues

On unit $S^3$, the $k$-th spherical-harmonic shell ($k = \ell + 1 \ge 1$, $-\Delta_{S^3} = k^2 - 1$, multiplicity $k^2$) has zonal kernel $\frac{\sin(k\chi)}{k\sin\chi}$ in geodesic angle $\chi = \arccos(x \cdot y) \in [0, \pi]$. By the three-sphere Funk–Hecke theorem, the integral operator $(\mathcal{K}_{\rho_0} f)(x) = \int_{S^3}\kappa_{\rho_0}(x, y) f(y)\,dV_\gamma(y)$ acts on shell $k$ as multiplication by the real scalar
\[
 \hat\kappa_{\rho_0}(k) = \frac{4\pi}{C_{\rho_0} k}\int_0^{\rho_0} (\cos\chi - \cos\rho_0)^8 \sin\chi\,\sin(k\chi)\,d\chi, \qquad C_{\rho_0} = 4\pi\int_0^{\rho_0} (\cos\chi - \cos\rho_0)^8 \sin^2\chi\,d\chi > 0. \tag{2}
\]

Writing $c_0 = \cos\rho_0$, the odd trigonometric polynomial $g(\chi) := (\cos\chi - c_0)^8\sin\chi$ expands exactly via Laurent substitution $\cos\chi = \frac{z + z^{-1}}{2}, \sin\chi = \frac{z - z^{-1}}{2i}$ into nine sine harmonics:
\[
 g(\chi) = \sum_{m=1}^9 \alpha_m(c_0)\,\sin(m\chi), \tag{3}
\]
with exact rational polynomials $\alpha_1(c_0), \dots, \alpha_9(c_0)$ ending at $\alpha_9(c_0) = \frac{1}{256}$. Every integral $\int_0^{\rho_0}\sin(m\chi)\sin(k\chi)\,d\chi$ evaluates in closed elementary form without numerical quadrature.

## 2. Contraction and Finite-Range Microcausality

Because $\kappa_{\rho_0}(x, y) \ge 0$ everywhere and $|\sin(k\chi)| \le k\sin\chi$ on $[0, \pi]$ with strict inequality on $(0, \rho_0]$ for all $k \ge 2$:
\[
 \hat\kappa_{\rho_0}(1) = 1, \qquad |\hat\kappa_{\rho_0}(k)| < 1 \quad (\forall k \ge 2). \tag{4}
\]
For canonical equal-time continuum fields $(\Psi, \Pi)$ on $S^3$, the cap-smeared fields $\Psi_{\rho_0}(x) = (\mathcal{K}_{\rho_0}\Psi)(x)$ and $\Pi_{\rho_0}(x) = (\mathcal{K}_{\rho_0}\Pi)(x)$ satisfy
\[
 \big[\Psi_{\rho_0}(x_1), \Pi_{\rho_0}(x_2)\big] = i\int_{S^3}\kappa_{\rho_0}(x_1, y)\,\kappa_{\rho_0}(x_2, y)\,dV_\gamma(y) = 0 \qquad \text{whenever } d_{S^3}(x_1, x_2) > 2\rho_0 = \frac{1}{10}\text{ rad}. \tag{5}
\]
Thus equal-time smeared composite densities commute strictly outside the sensor diameter $2\rho_0 = 1/10\text{ rad}$, while retaining a nonzero finite-range commutator inside $d_{S^3}(x_1, x_2) < 2\rho_0$.

## 3. Ninefold Integration by Parts and $O(k^{-10})$ Decay

Since $g(-\chi) = -g(\chi)$ is analytic, all even derivatives vanish at the origin: $g^{(2r)}(0) = 0$ for every $r \ge 0$. At the cap boundary $\chi = \rho_0$, the factor $(\cos\chi - \cos\rho_0)^8$ vanishes to eighth order:
\[
 g^{(r)}(\rho_0) = 0 \quad (0 \le r \le 7), \qquad g^{(8)}(\rho_0) = 8!\,\sin^9\rho_0 = 40320\,\sin^9\rho_0. \tag{6}
\]
Integrating $\int_0^{\rho_0} g(\chi)\sin(k\chi)\,d\chi$ by parts nine times eliminates all boundary terms through order eight and yields
\[
 \hat\kappa_{\rho_0}(k) = \frac{4\pi}{C_{\rho_0} k^{10}}\left[-40320\sin^9\rho_0\cos(k\rho_0) + \int_0^{\rho_0} g^{(9)}(\chi)\cos(k\chi)\,d\chi\right], \tag{7}
\]
whence for every integer $k \ge 1$,
\[
 |\hat\kappa_{\rho_0}(k)| \le \frac{B_{\rho_0}}{k^{10}}, \qquad B_{\rho_0} := \frac{4\pi}{C_{\rho_0}}\left(40320\sin^9\rho_0 + \int_0^{\rho_0} |g^{(9)}(\chi)|\,d\chi\right). \tag{8}
\]
At $\rho_0 = 1/20$, $\hat\kappa_{\rho_0}(2) \in (0.9998214, 0.9998215)$ and $\hat\kappa_{\rho_0}(k)^2 \le B_{\rho_0}^2 k^{-20}$, making all continuum variance, Sobolev $H_{0,3}$, and four-particle graph sums rapidly convergent.
