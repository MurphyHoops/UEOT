# RC04 — Six-Channel Conformally Coupled Parseval Dipole Frame: Exact Elimination of the $\ell = 2$ Spatial Quadrupole Across All Closed-FRW Histories

## Scope and Breakthrough

In `POST_CLOSURE` §3, the two-channel dipole controller $(Y_0, Y_1)$ was proved to leave a strictly nonzero second-harmonic spatial stress trace $-Q_2(\mathbf u)/g^2$ on the encoding slice $T = \pi$ because $\operatorname{rank}(\boldsymbol\epsilon\boldsymbol\epsilon^T + \boldsymbol\zeta\boldsymbol\zeta^T) \le 2 < 4$ cannot form a nonzero multiple of $I_4$. That result stands unchanged for the two-channel model.

Here we show that enlarging the controller sector to a **six-channel conformally coupled massless ($\xi = 1/6, M = 0$) dipole frame** $(Y_0, Y_1, W_1, W_2, W_3, W_4)$—where $(Y_0, Y_1)$ are the active body-coupled channels and $(W_1, W_2, W_3, W_4)$ are four body-decoupled conformal spectator scalars—eliminates **every** $\ell \ge 1$ background controller stress-energy harmonic (including $-Q_2/g^2$) **identically for all $(\tau, x) \in \mathbb{R} \times S^3$** on **every** closed FRW metric $ds^2 = a(\tau)^2(-d\tau^2 + \gamma_{ij} dx^i dx^j)$, while making the $\ell = 0$ homogeneous controller radiation density strictly independent of the program $\mathbf u$.

## 1. Real-Analytic Positive-Definite Parseval Completion on the Control Ball

On unit static ESU ($a \equiv 1, R_{S^3} = 6$), a conformally coupled massless scalar ($\xi = 1/6, M = 0$) has $\xi R + M^2 = 1$, giving the **exact same quadratic mode dispersion** $\omega_{Y,k} = \sqrt{(k^2 - 1) + 1} = k$ (and $\ell = 1$ dipole frequency $\omega_{Y,2} = 2$) as `CLOCK_ACTUATOR`.

For any control $\mathbf u = (\boldsymbol\epsilon, \boldsymbol\zeta) \in \mathbb{R}^4 \times \mathbb{R}^4$ in the certified closed ball $\|\mathbf u\|^2 = \|\boldsymbol\epsilon\|^2 + \|\boldsymbol\zeta\|^2 \le r_0^2$ ($r_0 = 10^{-16}$), fix once and for all the program-independent scalar
\[
 \lambda_0 := 2 r_0^2 = 2 \times 10^{-32}, \qquad M(\mathbf u) := \lambda_0 I_4 - \boldsymbol\epsilon\boldsymbol\epsilon^T - \boldsymbol\zeta\boldsymbol\zeta^T. \tag{1}
\]
Because $0 \preceq \boldsymbol\epsilon\boldsymbol\epsilon^T + \boldsymbol\zeta\boldsymbol\zeta^T \preceq \|\mathbf u\|^2 I_4 \preceq \frac{1}{2}\lambda_0 I_4$, we have $M(\mathbf u) \succeq r_0^2 I_4 \succ 0$, and the binomial matrix power series for the symmetric positive-definite square root
\[
 \mathbf W(\mathbf u) := M(\mathbf u)^{1/2} = \sqrt{\lambda_0}\left[I_4 + \sum_{n=1}^\infty \binom{1/2}{n}\left(-\frac{\boldsymbol\epsilon\boldsymbol\epsilon^T + \boldsymbol\zeta\boldsymbol\zeta^T}{\lambda_0}\right)^n\right] \tag{2}
\]
converges geometrically ($\|\lambda_0^{-1}(\boldsymbol\epsilon\boldsymbol\epsilon^T + \boldsymbol\zeta\boldsymbol\zeta^T)\| \le 1/2$) and is **real-analytic ($C^\infty$)** across the entire closed ball $\|\mathbf u\| \le r_0$ (avoiding any singular-value crossing singularity at $\mathbf u = 0$ or $\sigma_1 = \sigma_2$). Defining $\mathbf w_1(\mathbf u), \dots, \mathbf w_4(\mathbf u) \in \mathbb{R}^4$ as the columns of $\mathbf W(\mathbf u)$ and writing $(\mathbf v_1, \dots, \mathbf v_6) := (\boldsymbol\epsilon, \boldsymbol\zeta, \mathbf w_1, \mathbf w_2, \mathbf w_3, \mathbf w_4)$ gives the exact Parseval identity
\[
 S_{\mathrm{frame}}(\mathbf u) := \sum_{A=1}^6 \mathbf v_A(\mathbf u)\,\mathbf v_A(\mathbf u)^T = \boldsymbol\epsilon\boldsymbol\epsilon^T + \boldsymbol\zeta\boldsymbol\zeta^T + \mathbf W(\mathbf u)\mathbf W(\mathbf u)^T \equiv \lambda_0 I_4. \tag{3}
\]

## 2. All-Time Curved-FRW Stress-Energy Isotropy and Time-Oscillation Cancellation

On any closed FRW spacetime $ds^2 = a(\tau)^2(-d\tau^2 + \gamma_{ij} dx^i dx^j)$, each conformally coupled massless channel ($\Box_g \phi_A - \frac{1}{6} R_g \phi_A = 0$) admits the exact dipole solution
\[
 \phi_A(\tau, x) = f(\tau)\,\big(\mathbf v_A \cdot Z(x)\big), \qquad f(\tau) := \frac{\cos(2\tau)}{\hat\kappa_{\rho_0}(2)\,a(\tau)\,g}. \tag{4}
\]
Using the unit-sphere embedding identities $\sum_{a=1}^4 Z_a^2 = 1$, $\sum_{a=1}^4 Z_a \nabla_i Z_a = 0$, $\sum_{a=1}^4 \nabla_i Z_a \nabla_j Z_a = \gamma_{ij}$, and Obata's equation $\nabla_i \nabla_j Z_a = -Z_a \gamma_{ij}$ together with (3), the six-channel quadratic bilinears satisfy
\[
 \sum_{A=1}^6 \phi_A^2 = \lambda_0 f(\tau)^2, \quad \sum_{A=1}^6 (\partial_\tau\phi_A)\nabla_i\phi_A \equiv 0, \quad \sum_{A=1}^6 \nabla_i\phi_A\nabla_j\phi_A = \lambda_0 f(\tau)^2\gamma_{ij}, \quad \sum_{A=1}^6 \phi_A\nabla_i\nabla_j\phi_A = -\lambda_0 f(\tau)^2\gamma_{ij}. \tag{5}
\]
Substituting (5) into the covariant improved conformal stress-energy tensor
\[
 T_{\mu\nu}^{\mathrm{conf}}[\phi_A] = \nabla_\mu\phi_A\nabla_\nu\phi_A - \frac{1}{2} g_{\mu\nu}(\nabla\phi_A)^2 + \frac{1}{6}\big(g_{\mu\nu}\Box_g - \nabla_\mu\nabla_\nu + G_{\mu\nu}\big)\phi_A^2 \tag{6}
\]
cancels every spatial gradient, every $a'(\tau), a''(\tau)$ derivative, and every $\cos^2(2\tau), \sin^2(2\tau)$ oscillation identically:
\[
 \rho_{\mathrm{frame}}(\tau, x) \equiv \frac{2\lambda_0}{\hat\kappa_{\rho_0}(2)^2 g^2 a(\tau)^4}, \qquad j_{i,\mathrm{frame}}(\tau, x) \equiv 0, \qquad T^i{}_{j,\mathrm{frame}}(\tau, x) \equiv \frac{2\lambda_0}{3\hat\kappa_{\rho_0}(2)^2 g^2 a(\tau)^4}\,\delta^i_j. \tag{7}
\]
In particular, $Q_{2,\mathrm{frame}}(\mathbf u) \equiv 0$ identically for all $\|\mathbf u\| \le r_0$. Because $W_1,\dots,W_4$ do not enter $V_{\mathrm{int}}$, the eight-dimensional active Jacobian $J_{\mathrm{total}}^{\rho_0,\infty}$ with respect to $\mathbf u = (\boldsymbol\epsilon, \boldsymbol\zeta)$ is **unchanged** (`\partial_{\mathbf u}\rho_{\mathrm{frame}} \equiv 0` has zero $\ell = 1$ projection!).
