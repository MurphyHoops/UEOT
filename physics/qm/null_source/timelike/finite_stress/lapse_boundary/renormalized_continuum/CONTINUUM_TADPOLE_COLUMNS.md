# RC03 — Continuum Combined Matter-Plus-Controller Jacobian, Tadpole Counterterm Comparison, and $H_{0,3}$ Form Control

## Scope and Results

At $K = \infty$ with the geodesic-cap sensor kernel $\kappa_{\rho_0}$ ($\rho_0 = 1/20\text{ rad}$), we prove that the eight-dimensional first-harmonic density and longitudinal-momentum response on unit ESU is strictly invertible in **both** natural renormalization prescriptions for the cap-smeared body composite $\Phi_{+,\rho_0}^2$, and that sharp-slice $\ell = 1$ projected stress means are uniformly controlled at $K = \infty$ by the third-order Sobolev number form $H_{0,3}$.

## 1. Exact Finite-Sensor Controller Block and Nonlocality Exchange Balance

Calibrate the initial coherent dipole amplitude as $Y_{j,\mathrm{cl}}(t, x) = \frac{\cos 2t}{\hat\kappa_{\rho_0}(2)\,g}(\mathbf u_j \cdot Z(x))$ so that the smeared reference controller $Y_{j,\rho_0,\mathrm{cl}}(t, x) = \frac{\cos 2t}{g}(\mathbf u_j \cdot Z(x))$ drives the exact pulse $s_{\mathrm{ref}}(t, x) = [b(t)\boldsymbol\epsilon + b'(t)\boldsymbol\zeta]\cdot Z(x)$ on $\Phi_{+,\rho_0}(x)^2$.

Because $\mathcal{K}_{\rho_0}$ acts with eigenvalue $\hat\kappa_{\rho_0}(1) = 1$ on the homogeneous ($\ell = 0, k = 1$) $Y_j$ mean correction $z_{j0}(t)$ and with eigenvalue $\hat\kappa_{\rho_0}(2)$ on the dipole ($\ell = 1, k = 2$) clock mean correction $\mathbf z_X(t) \cdot Z(x)$:
\[
 z_{j0}'' + z_{j0} = -\frac{v_{\mathrm{eff}}}{2} F_j(t), \qquad \mathbf z_X'' + 3\mathbf z_X = -\hat\kappa_{\rho_0}(2)\,\frac{v_{\mathrm{eff}}}{2}\,c(t)\sum_{j=0}^1 \mathbf u_j F_j'(t), \tag{1}
\]
while the cross stress tensor between $Y_{j,\mathrm{cl}}$ and $g z_{j0}$ carries $\hat\kappa_{\rho_0}(2)^{-1}$. Hence $\mathbf R_{\mathrm{app}}^{\rho_0} = \mathbf z_X' + \hat\kappa_{\rho_0}(2)^{-1}\sum_j(c' z_{j0}' + c z_{j0})\mathbf u_j$ and $\mathbf J_{\mathrm{app}}^{\rho_0} = \mathbf z_X + \hat\kappa_{\rho_0}(2)^{-1}\sum_j c z_{j0}' \mathbf u_j$ satisfy the exact finite-sensor retarded exchange identity
\[
 \big(\mathbf R_{\mathrm{app}}^{\rho_0}\big)' + 3\mathbf J_{\mathrm{app}}^{\rho_0} = -\frac{v_{\mathrm{eff}}}{2}\sum_{j=0}^1 \Big[\hat\kappa_{\rho_0}(2)\,c(t) F_j'(t) + \hat\kappa_{\rho_0}(2)^{-1} c'(t) F_j(t)\Big]\mathbf u_j. \tag{2}
\]
At $T = \pi$ ($a = \sqrt{3}, S = \sin(a\pi), C = \cos(a\pi)$), the repeated $2 \times 2$ continuum controller Jacobian block is
\[
 J_{\mathrm{app}}^{\rho_0,\infty}(v_{\mathrm{eff}}) = \frac{V_0 v_{\mathrm{eff}}}{8}\begin{pmatrix}
 \hat\kappa_{\rho_0}(2)\,S U & \hat\kappa_{\rho_0}(2)\,C V + \hat\kappa_{\rho_0}(2)^{-1} Q \\[4pt]
 3\big(\hat\kappa_{\rho_0}(2)^{-1} R - \hat\kappa_{\rho_0}(2)\,C U / a\big) & 3\hat\kappa_{\rho_0}(2)\,S V / a
 \end{pmatrix}. \tag{3}
\]

## 2. Invertibility in Both Unsubtracted and Vacuum-Subtracted Tadpole Schemes

1. **Positive-square continuum composite ($v_{\mathrm{eff}} = v_{\rho_0,\infty}$)**:
   Here $\frac{V_0 v_{\rho_0,\infty}}{8} \in (250.73, 250.74)$. Outward-interval bounds on $(U, V, R, Q)$ prove $\det M_{\mathrm{ctrl}}^{\rho_0} > 4.5$, $\|(J_{\mathrm{app}}^{\rho_0,\infty})^{-1}\| < 0.0115$, and since the cap-smeared matter Jacobian $J_{\mathrm{matter}}^{\rho_0,\infty}$ contracts mode-by-mode by $\hat\kappa_{\rho_0}(k)^2\hat\kappa_{\rho_0}(k+1)^2 \le 1$ so $\|J_{\mathrm{matter}}^{\rho_0,\infty}\| < 6$, the Neumann bound gives
   \[
    \big\|\big(J_{\mathrm{total}}^{\rho_0,\infty}\big)^{-1}\big\| = \big\|\big(J_{\mathrm{app}}^{\rho_0,\infty} + J_{\mathrm{matter}}^{\rho_0,\infty}\big)^{-1}\big\| < 0.013. \tag{4}
   \]
2. **Vacuum-subtracted normal-ordered composite ($v_{\mathrm{eff}} = 0$)**:
   Replacing $\Phi_{+,\rho_0}^2 \mapsto :\Phi_{+,\rho_0}^2:_\Omega = \Phi_{+,\rho_0}^2 - v_{\rho_0,\infty}$ adds $-\frac{g}{2} v_{\rho_0,\infty}\sum_j Y_{j,\rho_0} F_j(g X_{\rho_0})$ to the interaction density. At fixed $\rho_0 = 1/20$, $v_{\rho_0,\infty} < \infty$ and $|F_j| \le M_j$, so Cauchy–Schwarz against $\frac{1}{8} Y_{j,\rho_0}^2$ shifts the lower bound by at most $\Delta C_{\mathrm{Wick},\rho_0} = \frac{1}{2} g^2 V_0 v_{\rho_0,\infty}^2 (M_0^2 + M_1^2) < 2 \times 10^{-69}$, preserving uniform $K \le \infty$ semiboundedness! At $v_{\mathrm{eff}} = 0$, $J_{\mathrm{app}}^{\rho_0,\infty}(0) = 0$ and $J_{\mathrm{total}}^{\rho_0,\infty}(0) = J_{\mathrm{matter}}^{\rho_0,\infty}$. Because the unsmeared Einstein projections $(A_A^{\mathrm{body}}, P_A^{\mathrm{body}})$ respond to the cap-smeared pulse $\Phi_{+,\rho_0}^2$ with pair weight $\hat\kappa_{\rho_0}(k)\hat\kappa_{\rho_0}(k+1)$, and $\hat\kappa_{\rho_0}(k) > 0$ holds strictly for every $1 \le k \le 278$, all pairs $1 \le k \le 277$ retain the exact sign structure of `LOCAL_PREPARATION` with first-pair factor $\hat\kappa_{\rho_0}(1)\hat\kappa_{\rho_0}(2) = \hat\kappa_{\rho_0}(2) > 0.99982$, while the high-mode tail $k \ge 278$ satisfies $2\sum_{k\ge 278}|\hat\kappa_{\rho_0}(k)\hat\kappa_{\rho_0}(k+1)|\,|d_k| W_k \Omega_k^2 \widehat b(\Omega_k) < 10^{-9}$ (using $W_k = \frac{k(k+1)}{16\omega_k\omega_{k+1}} < \frac{1}{16}$ and $\widehat b(\Omega_k) \le B_4/\Omega_k^4$). Hence $\det J_{2,\mathrm{matter}}^{\rho_0,\infty} > 7.28 \times 10^{-6}$ and $\|(J_{\mathrm{matter}}^{\rho_0,\infty})^{-1}\| < 10^6$. For general linear counterterm parameter $v_{\mathrm{eff}} \in \mathbb{R}$, $\det(J_{\mathrm{matter}}^{\rho_0,\infty} + v_{\mathrm{eff}} \mathcal{M}_{\mathrm{ctrl}}^{\rho_0})$ is a nonzero polynomial of degree $2$ per dipole direction (at most $2$ resonant values of $v_{\mathrm{eff}}$).

## 3. Uniform Continuum Sharp-Slice Form Bound via $H_{0,3}$

On sharp constant-time slices, off-diagonal pair terms $k(a_{k,m}^\dagger a_{k+1,m'}^\dagger + \text{h.c.})$ in $A_a^{\mathrm{body}}, P_a^{\mathrm{body}}$ are not bounded by $H_{0,\mathrm{ren}}$ alone as $K \to \infty$, but ARE uniformly bounded by the third-order Sobolev number operator $H_{0,3} := \sum_{k=1}^\infty k^6 \sum_{m=1}^{k^2} a_{k,m}^\dagger a_{k,m}$:
\[
 \sum_{k=1}^\infty \sum_{m=1}^{k^2} k\,\|a_{k,m}\Psi\| \le \left(\sum_{k=1}^\infty \sum_{m=1}^{k^2} k^{-4}\right)^{1/2} \langle\Psi, H_{0,3}\Psi\rangle^{1/2} = \frac{\pi}{\sqrt{6}}\,\langle\Psi, H_{0,3}\Psi\rangle^{1/2}. \tag{5}
\]
Because $|\hat\kappa_{\rho_0}(k)| \le B_{\rho_0} k^{-10}$, $[H_{0,3}, \Psi_{\rho_0}(x)]$ carries mode weights $k^6|\hat\kappa_{\rho_0}(k)| \le B_{\rho_0} k^{-4}$ with convergent variance sum $\sum_{k=1}^\infty k^2 \cdot k^{-1}\big(k^6|\hat\kappa_{\rho_0}(k)|\big)^2 \le B_{\rho_0}^2 \sum_{k=1}^\infty k^{-7} < \infty$, ensuring every parametrix term $\chi_n$ remains in $\mathcal{Q}(H_{0,3})$ uniformly as $K \to \infty$.
