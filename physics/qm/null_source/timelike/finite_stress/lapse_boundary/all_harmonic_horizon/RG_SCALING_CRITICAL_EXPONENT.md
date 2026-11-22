# AH02 — Exact $\rho_0 \to 0$ Renormalization Group Scaling Trichotomy and Fixed-$G$ Crunch Barrier

## 1. Setup: Wilsonian Sensor-Shrink Family on Closed $S^3$

To test the mathematical alternative in `NEXT_GATE.md` Gate 1 — whether coupling renormalization $g = g(\rho_0)$ as $\rho_0 \to 0^+$ can eliminate the finite sensor radius while preserving an operational autonomous clock on a sub-critical closed FRW background — consider the one-parameter power-law renormalization family referenced to $(\rho_{\mathrm{ref}}, g_{\mathrm{ref}}) = (1/20, 10^{-40})$:
$$g(\rho_0) := g_{\mathrm{ref}}\left(\frac{\rho_0}{\rho_{\mathrm{ref}}}\right)^\nu \quad (\nu \in \mathbb{R}), \qquad p_X(\rho_0) := \frac{V_0}{g(\rho_0)} \quad (\text{unit turnaround clock speed }\dot{\bar X}(0) = 1/g(\rho_0)).$$

## 2. Two-Sided Uniform Finite-$\rho_0$ Clock Variance Equivalence and $\rho_0^{-4}$ Vacuum-Shift Divergence

Recall from `RC02` Eq. (4)–(5) ($T = 8, a_0 = 4, V_0 = 2\pi^2$) that
$$\sigma_{X,\rho_0,\infty}^2 = \frac{a_0 + T^2/(4a_0)}{V_0} + \sum_{k=2}^\infty \frac{k^2\hat\kappa_{\rho_0}(k)^2}{2 V_0\sqrt{k^2-1}}, \qquad C_{\mathrm{shift},\rho_0} = \frac{3}{4}\sum_{k=1}^\infty k^3\,\hat\kappa_{\rho_0}(k)^2.$$
By `AH01`, $\hat\kappa_{\rho_0}(k) > 5/6$ for all $1 \le k \le N(\rho_0) = \lfloor\rho_0^{-1}\rfloor$ when $\rho_0 \in (0, 1/3]$. Hence:
- **Friedrichs vacuum-shift quartic divergence**: Since $N(\rho_0) + 1 > \rho_0^{-1}$ and $N(\rho_0) \ge \frac{3}{4}(N(\rho_0)+1)$ for $N(\rho_0) \ge 3$, Nicomachus's identity $\sum_{k=1}^N k^3 = \bigl(\frac{N(N+1)}{2}\bigr)^2 > \frac{9}{64}\rho_0^{-4}$ yields for **every** $\rho_0 \in (0, 1/3]$:
  $$C_{\mathrm{shift},\rho_0} > \frac{3}{4}\cdot\frac{25}{36}\left(\frac{N(\rho_0)(N(\rho_0)+1)}{2}\right)^2 > \frac{25}{48}\cdot\frac{9}{64}\,\rho_0^{-4} = \frac{75}{1024}\,\rho_0^{-4} \xrightarrow{\rho_0\to 0^+} +\infty.$$
- **Two-sided clock variance bracket**: Dropping the positive zero-mode packet spread $\frac{8}{V_0} > 0$ preserves `AH01`'s strict lower bound $\sigma_{X,\rho_0,\infty}^2 > \underline{c}_\sigma \rho_0^{-2}$ ($\underline{c}_\sigma = \frac{25}{576\pi^2}$). For the upper bound on $\rho_0 \in (0, 1/3]$, $\frac{8}{V_0} \le \frac{8}{9V_0}\rho_0^{-2}$, $\frac{k^2}{\sqrt{k^2-1}} \le \frac{2}{\sqrt{3}}k$ ($k \ge 2$), and splitting at $M(\rho_0) := \lceil \rho_0^{-1}\rceil \in [3, \frac{4}{3}\rho_0^{-1}]$ gives:
1. For $2 \le k \le M(\rho_0)$, $|\hat\kappa_{\rho_0}(k)| \le 1$ gives $\sum_{k=2}^{M} k\hat\kappa_{\rho_0}(k)^2 < \frac{(\rho_0^{-1}+1)(\rho_0^{-1}+2)}{2} \le \frac{10}{9}\rho_0^{-2}$.
2. For $k > M(\rho_0)$, $k \le \frac{k^2(k^2-1)}{M(M^2-1)} \le \frac{9}{8}\rho_0^3 k^2(k^2-1)$. By $S^3$ gradient Parseval ($-\Delta_{S^3} Y_{k,m} = (k^2-1)Y_{k,m}$),
   $$\sum_{k=2}^\infty k^2(k^2-1)\hat\kappa_{\rho_0}(k)^2 = V_0\int_{S^3} |\nabla_{S^3}\kappa_{\rho_0}(e_4, y)|^2\,d\mu(y) = \frac{V_0 \int_0^{\rho_0} 64\sin^2\chi(\cos\chi-\cos\rho_0)^{14}\sin^2\chi\,d\chi}{4\pi\Bigl(\int_0^{\rho_0}(\cos\chi-\cos\rho_0)^8\sin^2\chi\,d\chi\Bigr)^2}.$$
   Using $\alpha_0 u \le \sin u \le u$ on $[0, 1/3]$ with $\alpha_0 := 3\sin(1/3)$ gives $\cos\chi-\cos\rho_0 = 2\sin\frac{\rho_0+\chi}{2}\sin\frac{\rho_0-\chi}{2} \in [\frac{\alpha_0^2}{2}(\rho_0^2-\chi^2), \frac{1}{2}(\rho_0^2-\chi^2)]$, whence
   $$\sum_{k=2}^\infty k^2(k^2-1)\hat\kappa_{\rho_0}(k)^2 \le \frac{V_0 \cdot \frac{1}{1024}\rho_0^{33} J_2}{4\pi \cdot \Bigl(\frac{\alpha_0^{18}}{256}\rho_0^{19} J_0\Bigr)^2} = \frac{16 V_0 J_2}{\pi \alpha_0^{36} J_0^2}\,\rho_0^{-5}.$$
Combining zero, low, and high modes proves $\underline{c}_\sigma \rho_0^{-2} < \sigma_{X,\rho_0,\infty}^2 < \overline{c}_\sigma \rho_0^{-2}$ for **every** $\rho_0 \in (0, 1/3]$ with explicit closed-form $\overline{c}_\sigma$:
$$\overline{c}_\sigma := \frac{8}{9 V_0} + \frac{1}{\sqrt{3} V_0}\left(\frac{10}{9} + \frac{18 V_0 J_2}{\pi \alpha_0^{36} J_0^2}\right).$$

## 3. Exact Three-Regime RG Classification as $\rho_0 \to 0^+$

Track simultaneously the **dimensionless quantum gate phase variance** $\Sigma_{\mathrm{gate}}(\rho_0; \nu) := g(\rho_0)^2\sigma_{X,\rho_0,\infty}^2$ and the **closed-FRW gravitational parameter** $\alpha_G(\rho_0; \nu) := \frac{4\pi G}{3 g(\rho_0)^2} = \alpha_{G,\mathrm{ref}}\left(\frac{\rho_{\mathrm{ref}}}{\rho_0}\right)^{2\nu}$ (at fixed physical Newton coupling $G$, referenced to `RC05`'s $\alpha_{G,\mathrm{ref}} = 1/10 < 1/3$):

1. **Sub-critical scaling ($\nu < 1$)**: $\Sigma_{\mathrm{gate}}(\rho_0; \nu) > \underline{c}_\sigma g_{\mathrm{ref}}^2 \rho_{\mathrm{ref}}^{-2\nu}\rho_0^{2(\nu-1)} \xrightarrow{\rho_0 \to 0^+} +\infty$. The clock gate Fourier damping $\exp(-\frac{1}{2}m^2\Sigma_{\mathrm{gate}})$ collapses super-exponentially to zero below explicit washout radius $\rho_{\mathrm{wash}}(\nu)$.
2. **Super-critical scaling ($\nu > 1$)**: $\Sigma_{\mathrm{gate}}(\rho_0; \nu) < \overline{c}_\sigma g_{\mathrm{ref}}^2 \rho_{\mathrm{ref}}^{-2\nu}\rho_0^{2(\nu-1)} \to 0$, **but** $\alpha_G(\rho_0; \nu) = \frac{1}{10}(\rho_{\mathrm{ref}}/\rho_0)^{2\nu} \to +\infty$, crossing `RC05`'s exact Big Crunch boundary $\alpha_G = 1/3$ at $\rho_{\mathrm{crunch}}(\nu) = \rho_{\mathrm{ref}}(3/10)^{1/(2\nu)} > 0$.
3. **Marginal quantum line ($\nu = 1$, $g(\rho_0) = g_{\mathrm{ref}}\rho_0/\rho_{\mathrm{ref}}$)**: $\Sigma_{\mathrm{gate}}(\rho_0; 1) \in (\underline{c}_\sigma g_{\mathrm{ref}}^2/\rho_{\mathrm{ref}}^2,\, \overline{c}_\sigma g_{\mathrm{ref}}^2/\rho_{\mathrm{ref}}^2)$ stays strictly bounded and non-zero for all $\rho_0 \in (0, 1/3]$; **however**, at fixed $G$, $\alpha_G(\rho_0; 1) = \frac{1}{10}(\rho_{\mathrm{ref}}/\rho_0)^2$ still reaches the exact Big Crunch threshold $\alpha_G = 1/3$ at
   $$\rho_{\mathrm{crunch}}(1) = \rho_{\mathrm{ref}}\sqrt{\frac{3}{10}} = \frac{\sqrt{30}}{200}\text{ rad} \approx 0.02738613\text{ rad}!$$
   Even if one instead fixes the bare ratio $g_0 := g(\rho_0)/\rho_0 \le 1$ in Planck units, $\alpha_G < 1/3 \iff \rho_0 > \sqrt{4\pi}\,g_0^{-1}(\ell_P / R_{S^3})$.

Thus no choice of RG exponent $\nu \in \mathbb{R}$ permits sending $\rho_0 \to 0^+$ at fixed $G > 0$ on a non-collapsing spacetime.
