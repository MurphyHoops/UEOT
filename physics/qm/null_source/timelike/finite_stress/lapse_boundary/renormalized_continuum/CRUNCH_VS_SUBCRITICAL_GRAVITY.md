# RC05 — Stiff-Clock Big-Crunch Horizon Theorem ($\Lambda \le 0$) versus the Exact Sub-Critical Compactness Bounce Window ($\frac{4\pi G}{g^2} < 1$)

## Scope and Results

`BACKREACTION_GATE` observed that at $g = 10^{-40}$ in unit-$S^3$ dimensionless coordinates, the homogeneous clock kinetic energy density $\rho_X \sim \frac{1}{2 g^2}$ violates static ESU Friedmann balance if $8\pi G \sim O(1)$. Here we solve the exact nonlinear closed-FRW Friedmann constraint for a minimal massless homogeneous clock ($w_X = +1, \rho_X \propto a^{-6}$), conformal radiation ($w_r = 1/3, \rho_r \propto a^{-4}$), and cosmological constant $\Lambda$:

1. **Exact Big-Crunch Obstruction ($\Lambda \le 0$)**: For **every** $\alpha_G := \frac{4\pi G}{3 g^2} > 0$, **every** $\Lambda \le 0$, and **every** radiation density $\beta_r \ge 0$, the total conformal lifetime between Big Bang ($a = 0$) and Big Crunch ($a = 0$) satisfies $\Delta\tau_{\mathrm{universe}} \le \frac{\pi}{2}$ when $\beta_r = 0$ and $\Delta\tau_{\mathrm{universe}} < \pi$ for all $\beta_r \ge 0$. Thus no $\Lambda \le 0$ closed FRW spacetime can even survive across the apparatus operating window $\tau \in [-1, \pi + 3]$ ($\Delta\tau = \pi + 4 > \pi$).
2. **Exact Sub-Critical Bounce Window ($\Lambda > 0$)**: A smooth closed-FRW turnaround bounce $a(0) = 1, a'(0) = 0, a''(0) > 0$ with $\alpha_G > 0$, positive conformal radiation $\beta_r > 0$, and positive cosmological constant $\lambda_\Lambda := \frac{\Lambda}{3} > 0$ exists **if and only if**
\[
 0 < \alpha_G < \frac{1}{3} \quad \Longleftrightarrow \quad 0 < \frac{4\pi G}{g^2} < 1. \tag{1}
\]

## 1. Proof of the $\Lambda \le 0$ Conformal Horizon Bound

On $ds^2 = a(\tau)^2(-d\tau^2 + d\Omega_3^2)$, conservation $\nabla_\mu(g^{\mu\nu}\nabla_\nu\bar X) = 0 \implies a(\tau)^2 \bar X'(\tau) = \frac{1}{g}$ yields exact stiff-fluid density $\rho_X(\tau) = \frac{1}{2 g^2 a(\tau)^6}$. Setting $u(\tau) := a(\tau)^2 > 0$, the closed-FRW Friedmann equation $(a')^2 + a^2 = \frac{8\pi G}{3} a^4 \rho$ becomes the exact cubic relation
\[
 (u')^2 = 4\big(\alpha_G + \beta_r u - u^2 + \lambda_\Lambda u^3\big) =: 4 Q(u). \tag{2}
\]
When $\lambda_\Lambda \le 0$, $Q(0) = \alpha_G > 0$ and $\lim_{u\to+\infty} Q(u) = -\infty$, while $Q''(u) = 6\lambda_\Lambda u - 2 < 0$ for all $u > 0$, so $Q$ has a unique positive turnaround root $u_1 \in (0, u_0 + R]$ ($u_0 = \frac{\beta_r}{2} \ge 0$, $R = \sqrt{\alpha_G + \frac{\beta_r^2}{4}} > u_0$). Eliminating $\beta_r = u_1 - \lambda_\Lambda u_1^2 - \frac{\alpha_G}{u_1}$ yields the exact factorization on $u \in (0, u_1)$:
\[
 Q(u) = (u_1 - u)\left[\frac{\alpha_G}{u_1} + (1 - \lambda_\Lambda u_1)u - \lambda_\Lambda u^2\right] \ge (u_1 - u)\left(\frac{\alpha_G}{u_1} + u\right) > (u_1 - u)\,u, \tag{3}
\]
which bounds $|u'| = 2\sqrt{Q(u)}$ **from below** and therefore bounds its reciprocal from above:
\[
 \Delta\tau_{\mathrm{universe}} = \int_0^{u_1}\frac{du}{\sqrt{Q(u)}} \le \int_0^{u_1}\frac{du}{\sqrt{(u_1 - u)(\alpha_G/u_1 + u)}} = \frac{\pi}{2} + \arcsin\!\left(\frac{u_1^2 - \alpha_G}{u_1^2 + \alpha_G}\right) \le \frac{\pi}{2} + \arcsin\!\left(\frac{\beta_r}{\sqrt{4\alpha_G + \beta_r^2}}\right). \tag{3'}
\]
At $\beta_r = 0$, $u_1^2 \le \alpha_G$ (`Q(u_1) = \alpha_G - u_1^2 + \lambda_\Lambda u_1^3 = 0 \implies u_1^2 = \alpha_G + \lambda_\Lambda u_1^3 \le \alpha_G`), so $\Delta\tau_{\mathrm{universe}} \le \frac{\pi}{2}$ (with equality at $\Lambda = 0$, $u(\tau) = \sqrt{\alpha_G}\sin(2\tau + \phi_0)$). For every $\beta_r \ge 0$ and $\alpha_G > 0$, $\frac{\beta_r}{\sqrt{4\alpha_G + \beta_r^2}} < 1 \implies \Delta\tau_{\mathrm{universe}} < \pi < \pi + 4$.

## 2. Necessary and Sufficient Sub-Critical Bounce Conditions

Differentiating (2) gives Raychaudhuri's equation in $u = a^2$:
\[
 u'' = 2 Q'(u) = 2\big(3\lambda_\Lambda u^2 - 2 u + \beta_r\big). \tag{4}
\]
At a unit-radius turnaround bounce $u(0) = 1, u'(0) = 0$:
1. Friedmann balance $Q(1) = 0 \iff \beta_r = 1 - \alpha_G - \lambda_\Lambda$.
2. Positive radiation $\beta_r > 0 \iff \lambda_\Lambda < 1 - \alpha_G$.
3. Strict minimum bounce $a''(0) = \frac{1}{2} u''(0) = Q'(1) > 0 \iff 3\lambda_\Lambda - 2 + (1 - \alpha_G - \lambda_\Lambda) = 2\lambda_\Lambda - 1 - \alpha_G > 0 \iff \lambda_\Lambda > \frac{1 + \alpha_G}{2}$.

The open interval $\big(\frac{1 + \alpha_G}{2},\, 1 - \alpha_G\big)$ is nonempty if and only if $\frac{1 + \alpha_G}{2} < 1 - \alpha_G \iff 0 < \alpha_G < \frac{1}{3} \iff 0 < \frac{4\pi G}{g^2} < 1$. In physical units $G_{\mathrm{model}} = (\ell_{\mathrm{Pl}}/R_{S^3})^2$, this condition reads $R_{S^3} > \frac{\sqrt{4\pi}\,\ell_{\mathrm{Pl}}}{g}$.
