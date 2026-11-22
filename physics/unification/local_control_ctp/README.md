# Split-Core UV Dressing Rate, 4D Local Control Field & Smooth-Lapse Einstein–CTP (`HG-1` to `HG-3`)

```text
Result ID: P-UNIF-CTRL-01, P-UNIF-CHI-02, P-UNIF-CTP-03
Core dependencies: Finite quantitative transport and complete nonselective record conservation
Bridge dependencies: Split-core ultraviolet squeezing unitary W_{>K0}; Hubbard-Stratonovich CTP-to-Langevin bridge
Sector inputs: Conformal scalar coupling xi = 1/6, local Yukawa/trilinear scalar control r = lam_c * chi, local Weyl^2 renormalization
Standard physical inputs: Einstein-cylinder background S^3 x R, Fock representation, Hadamard common past
Effective assumptions: Second-cumulant CTP expansion O(eps^2) for inhomogeneous lapse modes m >= 3
Formal status: Algebraic/stability/cancellation theorems proved in Lean 4 (ConformalControlGravityGates.lean, 0 sorryAx) + 40-digit outward-interval certificate
Observable/benchmark: Same-cutoff H vs H_{K0} UV probe error < 9.66e-5 at K0=10000; truncated K0=1 outside collision contrast 0.00296895 (full-field M=1, p0=10 remains OPEN because matched K0=1 omitted-mode k>=2 bound exceeds 0.00297)
Falsification condition: Violation of m_chi^2 >= lam_c^2 / (2 g_4) (when g_chi = 0) yields negative classical energy rays; omission of Weyl^2 leaves divergent static susceptibility
```

## 1. Split-Core UV Dressing & Outside Wavepacket Collision (`P-UNIF-CTRL-01`)

For the autonomous full-field Hamiltonian $H = \lim_{K\to\infty} H_K$ on $L^2(\mathbb{R}_x)\otimes \mathcal{F}(L^2(S^3)\oplus L^2(S^3))$ with $r(x) = 0.2\exp\bigl(4 - \frac{1}{x(1-x)}\bigr)\mathbf{1}_{(0,1)}(x)$:
- Exact calculus bounds enclose $\|r'\|_\infty \in [0.84712808, 0.84712809]$ (attained at $\frac{1}{x(1-x)} = 3 + \sqrt{3}$) and $\|r''\|_\infty \in [6.45085151, 6.45085152]$ (attained near $w \approx 6.6728237010$), tightening prior connection bounds by $>11\times$.
- Dressing only ultraviolet modes $k > K_0$ via $\mathcal{W}_{>K_0} = \int_{\mathbb{R}}^\oplus W_{>K_0}(x)\,dx$ leaves the common-past `Z5` preparation on $[-2,-1]$ unchanged ($\mathcal{W}_{>K_0}^\dagger \Psi_\pm(0) = \Psi_\pm(0)$) while eliminating high-mode frequency shifts ($d\Gamma_{>K_0}(\omega(x))|0\rangle_{>K_0} \equiv 0$).
- This yields an explicit **$O(K_0^{-1/2})$ Hilbert-space norm convergence rate** for the Mosco limit and, by particle-number orthogonality $\langle 0_{>K_0} | E_{\mathrm{probe}} | 2_{>K_0}\rangle = 0$, an **$O(K_0^{-1})$ convergence rate** on $k=1$ probe expectations ($< 9.66\times 10^{-5}$ per branch at $K_0 = 10000$, $t = 0.22$).
- Direct unitary evolution of the truncated $K_0 = 1$ (`k = 1` pair) `Z5` outside $H^2$ wavepacket ($M=1, p_0=10, \langle H\rangle_{\mathrm{in}} = 56.5, \mathrm{Var}(H)_{\mathrm{in}} = 1290.5$) colliding with $(0,1)$ gives truncated $k=1$ binary momentum-reader contrast $0.0029689533$ at $t = 0.22$ ($\sigma = 0.1, \langle H\rangle_{\mathrm{out}} = 69.0$). Because the matched $K_0 = 1$ Split-Core bound covering all omitted modes $k \ge 2$ exceeds $0.00297$ at $M = 1, p_0 = 10$ (whereas the $K_0 = 10000$ tail bound $0.0001931272$ covers only modes $k > 10000$ relative to $H_{10000}$), full-field $M = 1, p_0 = 10$ collision remains explicitly **OPEN** pending intermediate-mode $2 \le k \le K_0$ control.

## 2. Four-Dimensional Local Control Field $\chi(x^\mu)$ (`P-UNIF-CHI-02`)

Promoting $r(x) = \lambda_c \chi(x^\mu)$ ($[\lambda_c] = +1$, super-renormalizable in $3+1$ dimensions) identifies the `PROBE_PHASE` vacuum counterterm $-\frac{H_K}{16\pi^2}\int\sqrt{-g}\,r^2$ with the standard one-loop fish-diagram mass renormalization $\delta m_\chi^2 = \frac{\lambda_c^2 H_K}{8\pi^2}$, avoiding the nonrenormalizable four-derivative $v^4$ divergence of nonlinear target-space $\sigma$ models. Adding $V_{\mathrm{stab}} = \frac{g_\chi}{4}\chi^4 + \frac{g_4}{4}(\phi^2+\psi^2)^2$ satisfies the exact polynomial sum-of-squares identity (`ConformalControlGravityGates.lean`):
$$\frac{1}{2}m_\chi^2\chi^2 + \frac{g_\chi}{4}\chi^4 + \frac{g_4}{4}(\phi^2+\psi^2)^2 + \lambda_c\chi\phi\psi = \frac{g_4}{4}(\phi^2-\psi^2)^2 + \frac{g_4}{4}\left(2\phi\psi + \frac{\lambda_c}{g_4}\chi\right)^2 + \left(\frac{1}{2}m_\chi^2 - \frac{\lambda_c^2}{4g_4}\right)\chi^2 + \frac{g_\chi}{4}\chi^4,$$
giving global nonnegativity at $g_\chi = 0$ iff $m_\chi^2 \ge \frac{\lambda_c^2}{2g_4}$, sharp semiboundedness $\ge -\frac{\lambda_c^4}{16 g_\chi g_4^2}$ for $m_\chi^2 \ge 0, g_\chi > 0$, and exact covariant stress-energy conservation $\nabla^\mu T_{\mu\nu}^{\mathrm{tot}} \equiv 0$.

## 3. Smooth Inhomogeneous-Lapse Full-Field CTP & $\mathrm{Weyl}^2$ Cancellation (`P-UNIF-CTP-03`)

For smooth compactly supported inhomogeneous lapse histories $N_\pm(t,\mathbf{x}) = 1 + \epsilon_\pm\eta_\pm(t)Y_m(\mathbf{x})$ ($m \ge 3, \ell = m^2 - 1$) sharing a common Hadamard ESU past, three integrations by parts isolate the unique local divergence $\frac{1}{2}\chi_K(0)\int_0^T(\epsilon_+^2\eta_+^2 - \epsilon_-^2\eta_-^2)\,dt$, which cancels identically across **all** harmonics $m \ge 3$ against $\gamma_{W,K}\int\sqrt{-g}\,C_{abcd}C^{abcd}$ under $\gamma_{W,K} = \gamma_R - \frac{n_s H_K}{960 V}$, leaving a manifestly positive $O(K^{-3})$-convergent Gram noise kernel and an $O(K^{-2})$-convergent causal Einstein–Langevin memory kernel.

Evidence: [verify_control_ctp.py](verify_control_ctp.py) · [result.json](result.json)
