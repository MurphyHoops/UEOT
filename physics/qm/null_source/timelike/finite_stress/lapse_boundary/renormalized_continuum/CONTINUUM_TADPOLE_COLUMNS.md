# RC03 — Continuum Combined Matter-Plus-Controller Jacobian, Conformal Controller Improvement, and $H_{0,3}(X)$ Form Control

## Scope and Results

At $K = \infty$ with the geodesic-cap sensor kernel $\kappa_{\rho_0}$ ($\rho_0 = 1/20\text{ rad}$), we prove that the continuum limiting/parametrix eight-dimensional first-harmonic density and longitudinal-momentum response on unit ESU—including the **exact $\xi = 1/6$ conformal improvement tensor** $\Delta T_{\mu\nu}^{(Y,\mathrm{imp})}$ of the conformally coupled massless controllers—is strictly invertible in **both** natural renormalization prescriptions for the cap-smeared body composite $\Phi_{+,\rho_0}^2$.

## 1. Exact Conformal Controller Block and Finite-Sensor Exchange Balance

Calibrate the initial coherent dipole amplitude as $Y_{j,\mathrm{cl}}(t, x) = \frac{\cos 2t}{\hat\kappa_{\rho_0}(2)\,g}(\mathbf u_j \cdot Z(x))$ so that $Y_{j,\rho_0,\mathrm{cl}}(t, x) = \frac{\cos 2t}{g}(\mathbf u_j \cdot Z(x))$ drives the exact pulse $s_{\mathrm{ref}}(t, x) = [b(t)\boldsymbol\epsilon + b'(t)\boldsymbol\zeta]\cdot Z(x)$ on $\Phi_{+,\rho_0}(x)^2$.

Because $\mathcal{K}_{\rho_0}$ acts with eigenvalue $\hat\kappa_{\rho_0}(1) = 1$ on the homogeneous ($\ell = 0, k = 1$) $Y_j$ mean correction $z_{j0}(t)$ and with eigenvalue $\hat\kappa_{\rho_0}(2)$ on the dipole ($\ell = 1, k = 2$) clock mean correction $\mathbf z_X(t) \cdot Z(x)$:
\[
 z_{j0}'' + z_{j0} = -\frac{v_{\mathrm{eff}}}{2} F_j(t), \qquad \mathbf z_X'' + 3\mathbf z_X = -\hat\kappa_{\rho_0}(2)\,\frac{v_{\mathrm{eff}}}{2}\,c(t)\sum_{j=0}^1 \mathbf u_j F_j'(t). \tag{1}
\]
Unlike minimal mass-one controllers ($\xi = 0, M = 1$), conformally coupled massless controllers ($\xi = 1/6, M = 0$) on unit ESU ($R = 6, G_{00} = 3, G_{0i} = 0$) carry the off-shell conserved improvement tensor $\Delta T_{\mu\nu}^{(Y,\mathrm{imp})} = \frac{1}{6}(g_{\mu\nu}\Box_g - \nabla_\mu\nabla_\nu)(Y_j^2)$, adding $-\frac{1}{6}\Delta_{S^3}(Y_j^2)$ to $T_{00}$ and $-\frac{1}{6}\partial_t\nabla_i(Y_j^2)$ to $T_{0i}$ (`\Delta A_{\mathrm{app},a}^{\mathrm{imp}} = +\frac{1}{2}\int Z_a\sum_j Y_j^2\,dV_\gamma`, `\Delta P_{\mathrm{app},a}^{\mathrm{imp}} = -\int Z_a\sum_j Y_j\dot Y_j\,dV_\gamma`). Consequently, with $A_{\mathrm{app}} = \frac{V_0}{4}\mathbf R_{\mathrm{app}}^{\rho_0,\mathrm{conf}}$ and $P_{\mathrm{app}} = \frac{3 V_0}{4}\mathbf J_{\mathrm{app}}^{\rho_0,\mathrm{conf}}$,
\[
 \mathbf R_{\mathrm{app}}^{\rho_0,\mathrm{conf}} = \mathbf z_X' + \hat\kappa_{\rho_0}(2)^{-1}\sum_{j=0}^1\big(c' z_{j0}' + 2 c z_{j0}\big)\mathbf u_j, \qquad
 \mathbf J_{\mathrm{app}}^{\rho_0,\mathrm{conf}} = \mathbf z_X + \hat\kappa_{\rho_0}(2)^{-1}\sum_{j=0}^1\left(\frac{2}{3} c z_{j0}' - \frac{1}{3} c' z_{j0}\right)\mathbf u_j, \tag{2}
\]
which satisfy the identical retarded exchange identity
\[
 \big(\mathbf R_{\mathrm{app}}^{\rho_0,\mathrm{conf}}\big)' + 3\mathbf J_{\mathrm{app}}^{\rho_0,\mathrm{conf}} = -\frac{v_{\mathrm{eff}}}{2}\sum_{j=0}^1 \Big[\hat\kappa_{\rho_0}(2)\,c(t) F_j'(t) + \hat\kappa_{\rho_0}(2)^{-1} c'(t) F_j(t)\Big]\mathbf u_j. \tag{3}
\]
At $T = \pi$ ($a = \sqrt{3}, S = \sin(a\pi), C = \cos(a\pi), c(\pi) = 1, c'(\pi) = 0$), the repeated $2 \times 2$ conformal controller Jacobian block is
\[
 J_{\mathrm{app}}^{\rho_0,\infty}(v_{\mathrm{eff}}) = \frac{V_0 v_{\mathrm{eff}}}{8}\begin{pmatrix}
 \hat\kappa_{\rho_0}(2)\,S U & \hat\kappa_{\rho_0}(2)\,C V + 2\hat\kappa_{\rho_0}(2)^{-1} Q \\[4pt]
 2\hat\kappa_{\rho_0}(2)^{-1} R - 3\hat\kappa_{\rho_0}(2)\,C U / a & 3\hat\kappa_{\rho_0}(2)\,S V / a
 \end{pmatrix}. \tag{4}
\]

## 2. Invertibility in Both Unsubtracted and Vacuum-Subtracted Tadpole Schemes

1. **Positive-square continuum composite ($v_{\mathrm{eff}} = v_{\rho_0,\infty}$)**:
   Here $\frac{V_0 v_{\rho_0,\infty}}{8} \in (250.73, 250.74)$. Outward-interval bounds prove $\det M_{\mathrm{ctrl}}^{\rho_0,\mathrm{conf}} = (3 u_* - 2 C r_*)v_* + (6 C u_* - 4 r_*)q_* > 10.0$ ($u_* = \hat\kappa_{\rho_0}(2)U/a$), $\|M_{\mathrm{ctrl}}^{\rho_0,\mathrm{conf}}\|_F < 13.5$, and $\|(J_{\mathrm{app}}^{\rho_0,\infty})^{-1}\| < 0.0054$. Since the unsmeared-projection/smeared-pulse matter Jacobian $J_{\mathrm{matter}}^{\rho_0,\infty}$ contracts mode-by-mode by $|\hat\kappa_{\rho_0}(k)\hat\kappa_{\rho_0}(k+1)| \le 1$ so $\|J_{\mathrm{matter}}^{\rho_0,\infty}\| < 6$, the Neumann bound gives
   \[
    \big\|\big(J_{\mathrm{total}}^{\rho_0,\infty}\big)^{-1}\big\| = \big\|\big(J_{\mathrm{app}}^{\rho_0,\infty} + J_{\mathrm{matter}}^{\rho_0,\infty}\big)^{-1}\big\| < 0.0056. \tag{5}
   \]
2. **Vacuum-subtracted normal-ordered composite ($v_{\mathrm{eff}} = 0$)**:
   Replacing $\Phi_{+,\rho_0}^2 \mapsto :\Phi_{+,\rho_0}^2:_\Omega = \Phi_{+,\rho_0}^2 - v_{\rho_0,\infty}$ shifts the lower bound by at most $\Delta C_{\mathrm{Wick},\rho_0} = \frac{1}{2} g^2 V_0 v_{\rho_0,\infty}^2 (M_0^2 + M_1^2) < 2 \times 10^{-69}$. Because $\hat\kappa_{\rho_0}(k) > 0$ for all $1 \le k \le 278$, all pairs $1 \le k \le 277$ retain the exact sign structure of `LOCAL_PREPARATION` with first-pair factor $\hat\kappa_{\rho_0}(1)\hat\kappa_{\rho_0}(2) = \hat\kappa_{\rho_0}(2) > 0.99982$, while the high-mode tail $k \ge 278$ satisfies $2\sum_{k\ge 278}|\hat\kappa_{\rho_0}(k)\hat\kappa_{\rho_0}(k+1)|\,|d_k| W_k \Omega_k^2 \widehat b(\Omega_k) < 10^{-9}$ (using $W_k = \frac{k(k+1)}{32\omega_k\omega_{k+1}} < \frac{1}{32}$ for $k \ge 2$ and $W_1 = \frac{1}{16\omega_1\omega_2}$, cf. `SHARP_CHARGES`). Hence $\det J_{2,\mathrm{matter}}^{\rho_0,\infty} > 7.28 \times 10^{-6}$ and $\|(J_{\mathrm{matter}}^{\rho_0,\infty})^{-1}\| < 10^6$.

## 3. Sharp-Slice Minimal-Clock Form Control via $H_{0,3}(X)$ and Scoping of the $K = \infty$ Inverse

While the conformally coupled body and controller dipole charges $(A_a^{\mathrm{body}}, P_a^{\mathrm{body}}, A_a^Y, P_a^Y)$ have Hilbert–Schmidt pair kernels bounded on $\mathcal{Q}(H_{0,\mathrm{ren}} + I)$ at $K = \infty$, the **minimally coupled clock** sharp-slice charges $(A_a^X, P_a^X)$ lack conformal improvement and carry $O(k)$ pair blocks, which are uniformly controlled at $K = \infty$ on $\mathcal{Q}(H_{0,3}(X))$ ($H_{0,3}(X) := \sum_{k=2}^\infty k^6\sum_m a_{X,k,m}^\dagger a_{X,k,m}$):
\[
 \sum_{k=2}^\infty \sum_{m=1}^{k^2} k\,\|a_{X,k,m}\Psi\| \le \left(\sum_{k=1}^\infty k^{-2}\right)^{1/2} \langle\Psi, H_{0,3}(X)\Psi\rangle^{1/2} = \frac{\pi}{\sqrt{6}}\,\langle\Psi, H_{0,3}(X)\Psi\rangle^{1/2}. \tag{6}
\]
Because $|\hat\kappa_{\rho_0}(k)| \le \overline B_{\rho_0} k^{-10}$, $[H_{0,3}(X), X_{\rho_0}(x)]$ has finite continuum variance $\le \frac{\overline B_{\rho_0}^2}{2 V_0}\sum_{k=1}^\infty k^{-7} < \infty$, keeping every perturbative parametrix order $\chi_n$ in $\mathcal{Q}(H_{0,3}(X))$ uniformly as $K \to \infty$. At $K = \infty$, the sharp-slice contraction theorem is stated explicitly for the **continuum limiting/parametrix total response map** $F_{\mathrm{total,lim}}^{\rho_0,\infty}$ (whereas non-perturbative invariance of $\mathcal{Q}(H_{0,3}(X))$ under $e^{-it H_{\mathrm{ren},\infty}^{\rho_0,\mathrm{Fr}}}$ is not claimed; for finite-$g$ continuum states, spacetime-smeared charges `RC10` remain well-defined on the energy/Hadamard domain).
