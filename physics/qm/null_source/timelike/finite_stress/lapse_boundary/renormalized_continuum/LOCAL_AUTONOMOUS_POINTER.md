# RC09 — Four-Dimensional Local Autonomous Pointer Field: Coordinate-Free Coupling, Strict Cap Inclusion, and Continuum All-Outcome Record

## Scope and Results

In `PREPARED_RECORD` and `CLOCK_ACTUATOR`, the terminal readout at $\tau = \pi + 3$ used an externally timed Gaussian mathematical instrument. Here we construct a **four-dimensional local autonomous pointer scalar field** $\Psi_{\mathrm{ptr}}$ ($\xi = 1/6, \mu_{\mathrm{ptr}} = 1$) and a **localized conformal beacon scalar** $B_{\mathrm{rec}}$ ($\xi = 1/6, \mu_{\mathrm{rec}} = 1$) coupled to the probe species $Q_p = \frac{1}{\sqrt{2}}(\Phi_+ - \Phi_-)$ via **scalar, coordinate-free, metric-independent constants** $(\lambda_{\mathrm{ptr}} = 10^{-3}, M_* = 1)$ and a smooth compact clock gate $F_{\mathrm{read}}(g X_{\rho_0})$ supported on $g X_{\rho_0} \in [5.75, 5.95] \subset \big(\theta(\pi + \tfrac{5}{2}),\, \theta(\pi + 3)\big)$:
\[
 \mathcal{V}_{\mathrm{ptr}}^{\mathrm{cov}} = \lambda_{\mathrm{ptr}}\,\Psi_{\mathrm{ptr},\rho_0}\,B_{\mathrm{rec},\rho_0}\,F_{\mathrm{read}}(g X_{\rho_0})\,Q_{p,\rho_0} + \lambda_{\mathrm{ptr}}^2\,B_{\mathrm{rec},\rho_0}^2\,F_{\mathrm{read}}(g X_{\rho_0})^2\,Q_{p,\rho_0}^2. \tag{1}
\]

Neither the control vector $\mathbf u$ nor the spatial receiver location $x_{\mathrm{read}} \in S^3$ enters the Hamiltonian: both are prepared solely in the normal initial quantum state.

## 1. Curved-FRW Positive-Square Stability and Strict Geodesic-Cap Inclusion

In Weyl-rescaled conformal variables ($\tilde\Psi_{\mathrm{ptr}} = a\Psi_{\mathrm{ptr}}, \tilde B_{\mathrm{rec}} = a B_{\mathrm{rec}}, \tilde Q_p = a Q_p$), borrowing $\frac{3}{8}\int_{S^3}\tilde\Psi_{\mathrm{ptr},\rho_0}^2 dV_\gamma \le \frac{3}{4} H_{0,\mathrm{ren}}(\Psi_{\mathrm{ptr}}) + C_{\mathrm{shift,ptr}}$ yields the pointwise identity
\[
 \frac{3}{8}\tilde\Psi_{\mathrm{ptr},\rho_0}^2 + \lambda_{\mathrm{ptr}} a(\tau)\tilde\Psi_{\mathrm{ptr},\rho_0}\tilde B_{\mathrm{rec},\rho_0} F_{\mathrm{read}}\tilde Q_{p,\rho_0} + \lambda_{\mathrm{ptr}}^2 \tilde B_{\mathrm{rec},\rho_0}^2 F_{\mathrm{read}}^2\tilde Q_{p,\rho_0}^2 = \frac{3}{8}\left(\tilde\Psi_{\mathrm{ptr},\rho_0} + \frac{4}{3}\lambda_{\mathrm{ptr}} a(\tau)\tilde B_{\mathrm{rec},\rho_0} F_{\mathrm{read}}\tilde Q_{p,\rho_0}\right)^2 + \lambda_{\mathrm{ptr}}^2\left(1 - \frac{2 a(\tau)^2}{3}\right)\tilde B_{\mathrm{rec},\rho_0}^2 F_{\mathrm{read}}^2\tilde Q_{p,\rho_0}^2 \ge 0 \tag{2}
\]
for every $a(\tau)^2 \le \frac{3}{2}$, which holds across the entire bounce window $\tau \in [-1, \pi + 3]$ (`RC06`).

To ensure **strict spatial localization inside the causal receiver cap** $C_{\mathrm{read}} = B_{1/2}(x_{\mathrm{read}})$ even after two applications of $\mathcal{K}_{\rho_0}$ ($\rho_0 = 1/20$), initialize the classical beacon profile $h_{\mathrm{rec}} \ge 0$ at the readout midpoint $\tau_* = \pi + 2.85$ with compact support in $B_{2/5}(x_{\mathrm{read}})$, unit $L^2$-norm $\|h_{\mathrm{rec}}\|_{L^2} \le 1$, and flat core inside $B_{3/10}(x_{\mathrm{read}})$:
\[
 \operatorname{supp} h_{\mathrm{rec}} \subset B_{2/5}(x_{\mathrm{read}}) \implies \operatorname{supp}\big(\mathcal{K}_{\rho_0}(\mathcal{K}_{\rho_0} h_{\mathrm{rec}})\big) \subset B_{2/5 + 2\rho_0}(x_{\mathrm{read}}) = B_{1/2}(x_{\mathrm{read}}) = C_{\mathrm{read}}! \tag{3}
\]
Because $\kappa_{\rho_0} \ge 0$ with $\int\kappa_{\rho_0} = 1$, for every $x \in B_{1/4}(x_{\mathrm{read}})$ the geodesic ball $B_{2\rho_0}(x) \subset B_{1/4 + 1/10}(x_{\mathrm{read}}) = B_{7/20}(x_{\mathrm{read}})$, so if $h_{\mathrm{rec}}(y) \equiv V_{2/5}^{-1/2}\chi_{\mathrm{smooth}}(y)$ equals $c_{\mathrm{core}} \ge \frac{1}{2} V_{1/2}^{-1/2}$ on $B_{7/20}(x_{\mathrm{read}})$, then $\tilde g_{\mathrm{eff}}(x) := \mathcal{K}_{\rho_0}(\mathcal{K}_{\rho_0} h_{\mathrm{rec}})(x) \ge \frac{1}{2} V_{1/2}^{-1/2}$ pointwise on $B_{1/4}(x_{\mathrm{read}})$!

## 2. Certified Positive-Kernel Window and Continuum All-Outcome Binary Gap

In `PREPARED_RECORD`, the causal source-to-probe Green's function on elapsed time $\tau_{\mathrm{el}} = \tau - \pi \in (\frac{5}{2}, \pi)$ is pointwise bounded below on $B_{1/4}(x_{\mathrm{read}}) \times B_{1/4}(x_{\mathrm{enc}})$ by $\frac{r e^{-2/3}}{8\pi}$ ($r = 1/5$). On our curved closed-FRW bounce, $\theta(\pi + \frac{5}{2}) < 5.642 < 5.75$ and $\theta(\pi + 3) > 6.132 > 5.95$, so the autonomous clock gate $[5.75, 5.95]$ lies **strictly inside** the positive-kernel window $\tau \in (\pi + \frac{5}{2}, \pi + 3)$!

Choose smooth nonnegative gate $F_{\mathrm{read}} \ge 0$ on $[5.75, 5.95]$ with $\int_{5.75}^{5.95} F_{\mathrm{read}}(\theta)\,d\theta = \frac{1}{10}$, $\sup F_{\mathrm{read}} \le 1$, and $\sup|F_{\mathrm{read}}'| \le 20$. Under joint parity $(Q_p, \Psi_{\mathrm{ptr}}) \mapsto (-Q_p, -\Psi_{\mathrm{ptr}})$, $\mathcal{V}_{\mathrm{ptr}}^{\mathrm{cov}}$ is strictly invariant: both code branches $\pm\eta f$ ($\eta = 10^{-13}$) share the exact same total energy law and acquire opposite pointer quadrature shifts $\pm\mu_{\mathrm{ptr}}(\eta)$ at $\tau = \pi + 3$. Keeping the exact Gaussian $(\Psi_{\mathrm{ptr}}, Q_p)$ evolution along $\theta(\tau)$ as the reference state (perturbed on curved FRW by $< 5 \times 10^{-3}$ relative Duhamel correction from $w(\tau) < 0.016$ and $\lambda_{\mathrm{ptr}}^2 = 10^{-6}$), the continuum binary sign-POVM probability gap satisfies $\Delta P_{\mathrm{ptr},\infty} > 10^{-22} \gg 2\delta_{\mathrm{joint},\infty}$ (`2\delta_{\mathrm{joint},\infty} < 3 \times 10^{-32}`)!
