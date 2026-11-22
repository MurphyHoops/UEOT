# RC08 — Continuum Eight-Projection Total-Source Inverse on the Dynamical Closed-FRW Bounce History

## Scope and Results

Combining the geodesic-cap continuum apparatus (`RC01`–`RC03`), the six-channel conformal Parseval dipole frame (`RC04`), the non-static sub-critical closed-FRW bounce $a(\tau)$ and re-derived physical clock $\theta(\tau) = g\bar X_{\mathrm{phys}}(\tau)$ (`RC05`–`RC06`), and continuum Hilbert–Schmidt Hadamard transport (`RC07`), we prove that on the **dynamical curved FRW geometry $a(\tau)$** at $K = \infty$:

1. The continuum limiting/parametrix eight-dimensional total-source first-harmonic Jacobian $J_{\mathrm{total,FRW}}^{\rho_0,\infty}$ on the encoding slice $\tau = \pi$ (including the conformal controller improvement $\Delta T_{\mu\nu}^{(Y,\mathrm{imp})}$ and $\mathcal{Q}(H_{0,3}(X))$ minimal-clock domain of `RC03`) satisfies $\|(J_{\mathrm{total,FRW}}^{\rho_0,\infty})^{-1}\| < 0.006$.
2. Every target $\mathbf y$ in the ball $\|\mathbf y\| \le 5 \times 10^{-23}$ (including the curved common two-code target at $\eta = 10^{-13}$) admits a unique continuum limiting control $\mathbf u \in \mathbb{R}^8$ in $\|\mathbf u\| \le 10^{-16}$.
3. Because the 6-channel Parseval completion (`RC04`) fixes $S_{\mathrm{frame}}(\mathbf u) \equiv \lambda_0 I_4$ independently of $\mathbf u$, adjusting $\mathbf u$ to match the 8 dipole projections on $\tau = \pi$ **does not perturb the homogeneous background bounce $a(\tau)$** and **introduces zero $\ell = 2$ controller spatial quadrupole**.

## 1. Curved-FRW Perturbation of the Controller and Matter Blocks

On $\tau \in [-1/5, \pi]$, $0 \le w(\tau) = a(\tau)^2 - 1 \le w(\pi) < 1.21 \times 10^{-4}$, and on the compact pulse support $[-1/5, 1/5]$, $0 \le w(\tau) < 8.1 \times 10^{-8}$ and $1 \le a(\tau) < 1 + 4.1 \times 10^{-8}$.

1. **Conformal controller mode $z_{j0}$ ($\ell = 0, k = 1$)**: In rescaled variables $\tilde z_{j0}'' + \tilde z_{j0} = -\frac{a(\tau)}{2} v_{\mathrm{FRW}}(\tau) F_{j,\mathrm{FRW}}(\theta(\tau))$, where $|a(\tau) v_{\mathrm{FRW}}(\tau) - v_{\rho_0,\infty}| \le v_{\rho_0,\infty}(a(1/5) - 1) + a(1/5)\Delta v_{\mathrm{FRW}}$ on $[-1/5, 1/5]$ (`\Delta v_{\mathrm{FRW}} < 2 \times 10^{-3}` across $[-1, \pi + 3]$ from `RC07`).
2. **Minimal clock dipole $\tilde{\mathbf z}_X = a\mathbf z_X$ ($\ell = 1, k = 2$)**: $\tilde{\mathbf z}_X'' + \big(3 - \frac{a''(\tau)}{a(\tau)}\big)\tilde{\mathbf z}_X = -\hat\kappa_{\rho_0}(2)\frac{a(\tau)^2}{2} v_{\mathrm{FRW}}(\tau) c(\tau)\sum_j \mathbf u_j \partial_\tau\big[F_{j,\mathrm{FRW}}(\theta(\tau))\big]$ (since $\theta'(\tau) = a(\tau)^{-2}$ supplies $a(\tau)^2$ upon converting $F_{j,\mathrm{FRW}}'(\theta)$ to $\partial_\tau[F_{j,\mathrm{FRW}}(\theta(\tau))]$). Since $\big|\frac{a''(\tau)}{a(\tau)}\big| < 2 \times 10^{-4}$ on $[-1/5, \pi]$, Duhamel comparison between $\partial_\tau^2 + 3 - \frac{a''}{a}$ and $\partial_\tau^2 + 3$ bounds the propagator perturbation on $[-1/5, \pi]$ by $\frac{\pi + 1/5}{2\sqrt{3}}\sup_{[-1/5,\pi]}\big|\frac{a''}{a}\big| < 2 \times 10^{-4}$.
3. **Encoding-slice metric rescaling and extrinsic-curvature mixing at $\tau = \pi$**: Physical covariant energy and momentum densities on $ds^2 = a(\pi)^2(-d\tau^2 + d\Omega_3^2)$ carry overall metric factor $a(\pi)^{-4}$ (integrated over $\sqrt{\gamma}\,d^3x$ with physical volume $a(\pi)^3$: $a(\pi)^{-1} \in (0.99993, 1)$) plus extrinsic-curvature shift proportional to $\frac{a'(\pi)}{a(\pi)} < 9.9 \times 10^{-5}$.
4. **Curved matter response**: Duhamel comparison of $\partial_\tau^2 + k^2 + \frac{1}{5}(1 + w(\tau))$ against $\partial_\tau^2 + k^2 + \frac{1}{5}$ over $[-1/5, \pi]$ changes $J_{\mathrm{matter}}^{\rho_0,\infty}$ in norm by $< 0.01$, so $\|J_{\mathrm{matter,FRW}}^{\rho_0,\infty}\| < 6.01$.

Combining (1)–(4) by the Neumann inverse perturbation formula $J_{\mathrm{total,FRW}}^{\rho_0,\infty} = a(\pi)^{-1} J_{\mathrm{app,ESU}}^{\rho_0,\infty} + \Delta J_{\mathrm{app,FRW}} + J_{\mathrm{matter,FRW}}^{\rho_0,\infty}$ yields $\|\Delta J_{\mathrm{app,FRW}}\| < 2.0$ and $\|\Delta J_{\mathrm{app,FRW}} + J_{\mathrm{matter,FRW}}^{\rho_0,\infty}\| < 8.1$, while $\|(a(\pi)^{-1} J_{\mathrm{app,ESU}}^{\rho_0,\infty})^{-1}\| < 0.00541$, proving
\[
 \big\|\big(J_{\mathrm{total,FRW}}^{\rho_0,\infty}\big)^{-1}\big\| \le \frac{0.00541}{1 - 8.1 \times 0.00541} < 0.0057 < 0.006. \tag{1}
\]
