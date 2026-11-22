# RC06 — Non-Static Closed-FRW Bounce Trajectory, Re-Derived Curved Clock Evolution, and Conformal Parseval Controller Transport

## Scope and Results

On the sub-critical closed-FRW bounce point $(\alpha_G, \lambda_\Lambda, \beta_r) = \big(\frac{1}{10}, \frac{550001}{1000000}, \frac{349999}{1000000}\big)$ established in `RC05`, we enclose the exact coupled geometry $a(\tau) = \sqrt{u(\tau)}$ across the entire apparatus conformal-time interval $\tau \in [-1, \pi + 3]$ **without any numerical ODE integration** (`geometry_ODE_integrations == 0`), and re-derive the curved-spacetime trajectories of the minimal clock $X$ and 6-channel conformal controller frame $(Y_0, Y_1, W_1, \dots, W_4)$.

## 1. Exact Positive-Series Taylor–Picard Enclosure on $\tau \in [-1, \pi + 3]$

Writing $w(\tau) := u(\tau) - 1$ with $w(0) = w'(0) = 0$, equation (4) of `RC05` reads
\[
 w''(\tau) = 2\varepsilon_0 + 4\mu_0\,w(\tau) + 6\lambda_\Lambda\,w(\tau)^2, \qquad \varepsilon_0 = 2\lambda_\Lambda - 1 - \alpha_G = 2 \times 10^{-6}, \quad \mu_0 = 3\lambda_\Lambda - 1 = \frac{650003}{1000000}. \tag{1}
\]
By induction, the degree-$N$ ($N = 220$) Taylor polynomial $w_N(\tau) = \sum_{k=1}^{110} c_{2k}\tau^{2k}$ has **strictly positive even coefficients** $c_{2k} > 0$ and zero odd coefficients. Its exact ODE residual $d_N(\tau) := 4\mu_0\big(c_{N-1}\tau^{N-1} + c_N\tau^N\big) + 6\lambda_\Lambda\sum_{m=N-1}^{2N}\big(\sum_{j+k=m,\,2\le j,k\le N} c_j c_k\big)\tau^m \ge 0$ is bounded monotonically on $|\tau| \le T_{\mathrm{end}} = \pi + 3$. In the exponentially weighted Banach norm $\|r\|_\gamma := \sup_{|\tau|\le T_{\mathrm{end}}} e^{-\gamma|\tau|}|r(\tau)|$ ($\gamma = 3$), the linear Picard operator has contraction constant
\[
 L_{\mathrm{lin}} = \frac{4\mu_0 + 12\lambda_\Lambda w_N(T_{\mathrm{end}})}{\gamma^2} < 0.31 < \frac{1}{2}, \tag{2}
\]
certifying $\|u - u_{220}\|_{C^0([-T_{\mathrm{end}}, T_{\mathrm{end}}])} \le R_u < 2 \times 10^{-30}$! Across all $\tau \in [-1, \pi + 3]$:
1. $1 \le u(\tau) \le u(\pi + 3) < 1.016 < \frac{3}{2}$, so the **fixed-parameter curved positive-square completion** (`RC02` Eq. (2), requiring $u(\tau) \le 3/2$) holds strictly at every instant with **zero metric-dependent couplings**.
2. The history is strictly non-static: $a'(\pi) > 9.8 \times 10^{-5} > 0$, $a'(\pi + 3) > 0.012 > 0$, and $a(\pi + 3) - 1 > 0.0077 > 0$.
3. Subtracting the 6-channel Parseval controller radiation $\Delta\beta_{\mathrm{frame}} = \frac{8\pi G}{3}\frac{2\lambda_0}{\hat\kappa_{\rho_0}(2)^2 g^2} = \frac{4\alpha_G\lambda_0}{\hat\kappa_{\rho_0}(2)^2} < 9 \times 10^{-33}$ leaves positive background conformal radiation $\beta_{r,\mathrm{bg}} = \beta_r - \Delta\beta_{\mathrm{frame}} > 0.349998$.

## 2. Re-Derived Curved-FRW Clock Trajectory and Autonomous Pulse Profiles

On $ds^2 = a(\tau)^2(-d\tau^2 + d\Omega_3^2)$, the minimal massless homogeneous clock $\nabla_\mu\nabla^\mu\bar X_{\mathrm{phys}} = 0$ does **not** evolve linearly in $\tau$: instead $\partial_\tau\big(a(\tau)^2\partial_\tau\bar X_{\mathrm{phys}}\big) = 0$, so choosing $\bar X_{\mathrm{phys}}(0) = 0$ and conserved canonical momentum $\Pi_X = V_0/g$ yields
\[
 \theta(\tau) := g\bar X_{\mathrm{phys}}(\tau) = \int_0^\tau \frac{ds}{a(s)^2} = \int_0^\tau \frac{ds}{1 + w(s)}. \tag{3}
\]
Because $0 \le w(s) < 0.016$ on $[-1, \pi + 3]$, the geometric series $(1 + w(s))^{-1} = \sum_{m=0}^M (-1)^m w(s)^m + (-1)^{M+1}\frac{w(s)^{M+1}}{1 + w(s)}$ ($M = 10$) integrates term-by-term without quadrature! In particular, $\tau - \theta(\tau) > 0$ strictly for all $\tau \in (0, \pi + 3]$ ($\pi - \theta(\pi) > 7 \times 10^{-5}$ and $(\pi + 3) - \theta(\pi + 3) > 0.0094$).

On curved FRW, the canonical conformal generator $\partial_\tau$ has interaction potential (`RC02` Eq. (2))
\[
 V_{\mathrm{int,FRW}}^{\rho_0}(\tau) = \int_{S^3} dV_\gamma\left[\frac{g a(\tau)}{2}\sum_{j=0}^1 \tilde Y_{j,\rho_0} F_{j,\mathrm{FRW}}(g X_{\rho_0})\,\tilde\Phi_{+,\rho_0}^2 + \frac{g^2}{4}\sum_{j=0}^1 F_{j,\mathrm{FRW}}(g X_{\rho_0})^2\,\tilde\Phi_{+,\rho_0}^4\right]. \tag{4}
\]
Because $\theta : \mathbb{R} \to (\theta_-, \theta_+)$ is a real-analytic strictly increasing diffeomorphism ($\theta'(\tau) = u(\tau)^{-1} > 0$) mapping the pulse support $\tau \in [-1/5, 1/5]$ onto $[-\theta(1/5), \theta(1/5)] \subset (-1/5, 1/5)$, defining the **fixed, program-independent** smooth compact gate functions
\[
 F_{0,\mathrm{FRW}}(\theta) := \frac{b(\tau(\theta))}{a(\tau(\theta))\cos(2\tau(\theta))}, \qquad F_{1,\mathrm{FRW}}(\theta) := \frac{b'(\tau(\theta))}{a(\tau(\theta))\cos(2\tau(\theta))} \qquad (|\theta| < \theta(1/5)) \tag{5}
\]
(where $\tau(\theta)$ is the fixed analytic inverse function of the fixed background clock $\theta(\tau)$, NOT a program-dependent or operator-valued metric coupling!) makes the reference quadratic source on $\tilde\Phi_{+,\rho_0}^2$ along $\tilde Y_{j,\rho_0,\mathrm{cl}}(\tau, x) = \frac{\cos 2\tau}{g}(\mathbf u_j \cdot Z(x))$ and $g\bar X_{\mathrm{phys}}(\tau) = \theta(\tau)$ **identically equal** to $\frac{1}{2}[b(\tau)\boldsymbol\epsilon + b'(\tau)\boldsymbol\zeta]\cdot Z(x)\,\tilde\Phi_{+,\rho_0}^2$!
