# RC07 — Non-Turnaround Bare-Transplant Obstruction versus Turnaround Conformal Initialization and Continuum Hilbert–Schmidt Cauchy Transport

## Scope and Results

`BACKREACTION_GATE` proved that transplanting static ESU vacuum data onto a slice with $a'(\tau_0) \neq 0$ produces an ultraviolet momentum/squeezing divergence. Here we establish both sides of the curved-FRW quantum state transport problem on the dynamical closed-FRW bounce $a(\tau)$ (`RC06`) across $\tau \in [-1, \pi + 3]$ at $K = \infty$ (`mode_ODE_integrations == 0`):

1. **Exact Shale–Stinespring Non-Normality of Naive Static Transplants ($a'(\tau_0) \neq 0$)**: Transplanting unrescaled canonical data $(q_k, p_k = a^2\partial_\tau\Psi_k)$ without the extrinsic-curvature canonical shift $a'(\tau_0)/a(\tau_0)$ induces shell-$k$ Bogoliubov coefficients $|\beta_k^{\mathrm{naive}}(\tau_0)| = \frac{|a'(\tau_0)|}{2 a(\tau_0)\omega_k}(1 + O(k^{-2}))$, so $\sum_{k=2}^\infty k^2|\beta_k^{\mathrm{naive}}(\tau_0)|^2 = +\infty$.
2. **Exact Turnaround Initialization and Continuum Hilbert–Schmidt Evolution**: Initializing in the Weyl-rescaled canonical representation $(\tilde\Psi = a\Psi, \tilde\pi = \partial_\tau\tilde\Psi)$ at the smooth turnaround bounce $\tau = 0$ ($a(0) = 1, a'(0) = 0$) gives:
   - $\beta_{Y,k}(\tau) \equiv 0$ identically for all six conformal massless controller channels;
   - $|\beta_{\pm,k}(\tau)| \le C_{\beta,\Phi}\,\omega_{\pm,k}^{-2}$ (and $|\beta_{\pm,k}^{\mathrm{ad}}(\tau)| \le C_{\mathrm{ad},\Phi}\,\omega_{\pm,k}^{-3}$ in the instantaneous adiabatic basis) for the conformal body doublet ($\mu_\pm = \pm 1/5$);
   - $|\beta_{X,k}(\tau)| \le C_{\beta,X}\,\omega_{X,k}^{-2}$ (and $|\beta_{X,k}^{\mathrm{ad}}(\tau)| \le C_{\mathrm{ad},X}\,\omega_{X,k}^{-3}$) for all non-zero minimal clock modes $k \ge 2$.
   Since $\sum_{k=1}^\infty k^2 \omega_k^{-4} < \infty$ and $\sum_{k=1}^\infty k^2 \omega_k \cdot \omega_k^{-6} < \infty$, time evolution in the rescaled $(\tilde\Psi, \tilde\pi)$ representation is **unitarily implementable on a single continuum Fock space** across all $\tau \in [-1, \pi + 3]$ and defines a normal, finite-adiabatic-energy Hadamard state on every Cauchy slice!

We state explicitly the Cortez–Mena Marugán–Velhinho representation distinction: unitary evolution on a single fixed Fock space holds in the Weyl-rescaled $(\tilde\Psi, \tilde\pi)$ representation, whereas transforming back to unrescaled $(\Psi, a^2\partial_\tau\Psi)$ at slices where $a'(\tau) \neq 0$ maps into the unitarily inequivalent instantaneous physical representation on which the algebraic state remains normal Hadamard relative to the local adiabatic vacuum.

## 1. Closed-Form Volterra Integration-by-Parts Bounds ($O(k^{-2})$ and $O(k^{-3})$)

For any rescaled mode satisfying $\tilde y_k''(\tau) + \big(\omega_k^2 + q(\tau)\big)\tilde y_k(\tau) = 0$ on $[-1, \pi + 3]$ with $q(0) = q'(0) = 0$ and $|q(\tau)| \le \frac{1}{2}\omega_k^2$ (specifically $q_\pm(\tau) = \mu_\pm w(\tau)$ with $\omega_{\pm,k} = \sqrt{k^2 + \mu_\pm}$, and $q_X(\tau) = -\big(\frac{a''(\tau)}{a(\tau)} - a''(0)\big)$ with $\omega_{X,k} = \sqrt{k^2 - 1 - a''(0)}$ for $k \ge 2$), the interaction-phase Bogoliubov system
\[
 \tilde\beta_k'(\tau) = -\frac{i q(\tau)}{2\omega_k} e^{i\Phi_k(\tau)}\tilde\alpha_k(\tau), \qquad \Phi_k'(\tau) = 2\omega_k - \frac{q(\tau)}{\omega_k} \ge \frac{3}{2}\omega_k \tag{1}
\]
satisfies the exact Gronwall envelope $|\tilde\alpha_k(\tau)| \le \cosh\!\big(\frac{\|q\|_{L^1}}{2\omega_k}\big)$ and $|\tilde\beta_k(\tau)| \le \sinh\!\big(\frac{\|q\|_{L^1}}{2\omega_k}\big)$. Integrating (1) by parts once using $q(0) = 0$ yields
\[
 |\beta_k(\tau)| \le \frac{|q(\tau)|\,|\tilde\alpha_k(\tau)|}{2\omega_k\Phi_k'(\tau)} + \int_0^{|\tau|}\left[\left|\frac{d}{ds}\!\left(\frac{q(s)}{2\omega_k\Phi_k'(s)}\right)\right||\tilde\alpha_k(s)| + \frac{q(s)^2}{4\omega_k^2\Phi_k'(s)}|\tilde\beta_k(s)|\right]ds \le \frac{C_{\beta,2}(\tau)}{\omega_k^2}. \tag{2}
\]
Subtracting the instantaneous adiabatic boundary squeeze $-\frac{i q(\tau)}{4\omega_k^2}\alpha_k(\tau)$ and integrating by parts a second time using $q'(0) = 0$ yields $|\beta_k^{\mathrm{ad}}(\tau)| \le C_{\mathrm{ad},3}(\tau)\,\omega_k^{-3}$, proving finite adiabatic excitation energy $\sum_{k} k^2\Omega_k(\tau)|\beta_k^{\mathrm{ad}}(\tau)|^2 < \infty$ at $K = \infty$.
