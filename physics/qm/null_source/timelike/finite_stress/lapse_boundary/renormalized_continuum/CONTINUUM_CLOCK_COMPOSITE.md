# RC02 — Glimm–Jaffe Renormalized Free Generator and Cap-Smeared Continuum Clock Composite

## Decision and Scope

Combining the finite-range geodesic-cap sensor kernel $\kappa_{\rho_0}$ ($\rho_0 = 1/20\text{ rad}$, `RC01`) with the **normal-ordered (Glimm–Jaffe) free Fock Hamiltonian** $H_{0,\mathrm{ren},K} \ge 0$ resolves three separate finite-$K$ obstructions of `CLOCK_ACTUATOR`, `CLOCK_UV`, and `WICK_CLOCK_GRAPH` within the declared finite-sensor model:

1. **Zero-point divergence eliminated**: `CLOCK_ACTUATOR`'s bare zero-point sum $E_{\mathrm{zp},K} \sim K^4$ is replaced by $H_{0,\mathrm{ren},K}|\Omega_{\mathrm{osc}}\rangle = 0$ while retaining a **uniform $K$-independent lower bound** $-C_{\mathrm{shift},\rho_0}$ for all $K \in \mathbb{N} \cup \{\infty\}$ and a canonical Friedrichs self-adjoint realization $H_{\mathrm{ren},\infty}^{\rho_0,\mathrm{Fr}}$ at $K = \infty$.
2. **Fixed-$g$ continuum switch stability**: Smeared variances $\sigma_{X,\rho_0,\infty}^2, \sigma_{Y,\rho_0,\infty}^2, v_{\rho_0,\infty}$ converge rapidly as $K \to \infty$, preventing the fixed-$g$ Gaussian smearing collapse of `CLOCK_UV`.
3. **Four-particle graph convergence and vanishing cutoff Ward residual**: The interaction tail $\|(V_{\mathrm{int},\infty}^{\rho_0} - V_{\mathrm{int},K}^{\rho_0})\Psi_{\mathrm{init},\infty}\|$ decays as $O(K^{-18}) \to 0$, and the finite-$K$ commutator residual $[P_K\mathcal{K}_{\rho_0}, Z_a]$ decays as $O(K^{-10}) \to 0$.

At finite $K$, essential self-adjointness holds on smooth compactly supported configuration vectors; at $K = \infty$, self-adjointness is proved specifically for the **Friedrichs realization** of the closed lower-semibounded form, together with explicit norm bounds on the continuum Duhamel difference on the prepared sector.

## 1. Uniform $K$-Independent Lower Bound and Curved-Slice Stability

Let $H_{0,\mathrm{ren},K}$ be the sum of the homogeneous clock kinetic energy $\frac{1}{2} p_{X,0}^2 \ge 0$ and the normal-ordered oscillator number Hamiltonians of $X_{k\ge 2}$ ($\omega_{X,k} = \sqrt{k^2 - 1}$), the conformal controllers $Y_A$ ($\omega_{Y,k} = k$), and the conformal body doublet $\Phi_\pm$ ($\omega_{\pm,k} = \sqrt{k^2 \pm 1/5}$). For each active channel $j \in \{0, 1\}$, Parseval's identity on $S^3$, $k \ge 1$, and $p_{j,k,m}^2 \ge 0$ give
\[
 \frac{3}{8}\int_{S^3} Y_{j,\rho_0,K}(x)^2\,dV_\gamma = \frac{3}{8}\sum_{k=1}^K \hat\kappa_{\rho_0}(k)^2 \sum_{m=1}^{k^2} q_{j,k,m}^2 \le \frac{3}{4}\sum_{k=1}^K \hat\kappa_{\rho_0}(k)^2 \sum_{m=1}^{k^2}\Big(h_{j,k,m,\mathrm{ren}} + \frac{k}{2}\Big) \le \frac{3}{4} H_{0,\mathrm{ren},K}(Y_j) + \frac{3}{8}\sum_{k=1}^\infty k^3 \hat\kappa_{\rho_0}(k)^2, \tag{1}
\]
since $0 \le \hat\kappa_{\rho_0}(k)^2 \le 1$ and $h_{j,k,m,\mathrm{ren}} \ge 0$. Combining the two active channels $j \in \{0, 1\}$ with the exact algebraic identity (valid for any conformal scale factor $a > 0$ satisfying $a^2 \le 3/2$, including static ESU $a = 1$)
\[
 \frac{3}{8}\tilde Y^2 + \frac{g a}{2}\tilde Y F \tilde\Phi^2 + \frac{g^2}{4} F^2 \tilde\Phi^4 = \frac{3}{8}\left(\tilde Y + \frac{2 g a}{3} F \tilde\Phi^2\right)^2 + \frac{g^2}{4}\left(1 - \frac{2 a^2}{3}\right) F^2 \tilde\Phi^4 \ge 0, \tag{2}
\]
proves the uniform operator/form inequality
\[
 H_{\mathrm{ren},K}^{\rho_0}(a) + C_{\mathrm{shift},\rho_0} \ge \frac{1}{4} H_{0,\mathrm{ren},K} \ge 0 \qquad \forall K \in \mathbb{N} \cup \{\infty\}, \quad \forall a \in (0, \sqrt{3/2}], \tag{3}
\]
with finite $K$-independent vacuum shift
\[
 C_{\mathrm{shift},\rho_0} := \frac{3}{4}\sum_{k=1}^\infty k^3\,\hat\kappa_{\rho_0}(k)^2 < \infty. \tag{4}
\]

## 2. Continuum Variances, Duhamel Vector Error, and Graph Tail

Splitting all mode sums at $K_{\mathrm{split}} = 512$ and bounding $k > 512$ via $|\hat\kappa_{\rho_0}(k)| \le B_{\rho_0} k^{-10}$ gives tight outward-interval enclosures for the continuum ($K = \infty$) variances at $T = 8, a_0 = 4$:
\[
 \sigma_{X,\rho_0,\infty}^2 = \frac{a_0 + T^2/(4a_0)}{V_0} + \sum_{k=2}^\infty \frac{k^2\hat\kappa_{\rho_0}(k)^2}{2 V_0\sqrt{k^2 - 1}}, \qquad
 \sigma_{Y,\rho_0,\infty}^2 = \sum_{k=1}^\infty \frac{k\hat\kappa_{\rho_0}(k)^2}{2 V_0}, \qquad
 v_{\rho_0,\infty} = \sum_{k=1}^\infty \frac{k^2\hat\kappa_{\rho_0}(k)^2}{2 V_0\sqrt{k^2 + 1/5}}. \tag{5}
\]
Replacing the finite-$K$ variance envelopes `(55, 65, 60)` of `CLOCK_ACTUATOR` by these exact $K = \infty$ continuum envelopes yields finite continuum Duhamel constants $C_{1,\rho_0,\infty}, C_{2,\rho_0,\infty}$ and at $g = 10^{-40}, \eta = 10^{-13}$ a continuum joint-vector norm error $\delta_{\rho_0,\infty} < 2 \times 10^{-32}$, preserving the complete continuum binary record gap $> 2.69 \times 10^{-30}$.

For any $K \ge 64$, the four-particle quartic/Wick graph tail satisfies $\sum_{k=K+1}^\infty \frac{k^2\hat\kappa_{\rho_0}(k)^2}{2 V_0\sqrt{k^2 + 1/5}} \le \frac{B_{\rho_0}^2}{36 V_0 K^{18}}$, and for any unit-norm spherical harmonic multiplication $Z_a$ ($\Delta k = \pm 1$), the finite-$K$ projection commutator decays as $\|[P_K, \mathcal{K}_{\rho_0} Z_a]\|_{L^2 \to L^2} = \|(I - P_K)\mathcal{K}_{\rho_0} Z_a - \mathcal{K}_{\rho_0} Z_a(I - P_K)\|_{L^2 \to L^2} \le 2 B_{\rho_0} K^{-10} \to 0$.
