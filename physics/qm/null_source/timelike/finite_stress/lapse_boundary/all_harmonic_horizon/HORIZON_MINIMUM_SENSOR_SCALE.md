# AH01 — Quantum-Gravitational Operational Horizon Exclusion of Pointlike Clocks ($\rho_0 \to 0$)

## 1. Purpose and Gate Addressed

`renormalized_continuum/NEXT_GATE.md` Gate 1 identifies the central ultraviolet question left open by `RC01`–`RC03`: uniform $K \le \infty$ Friedrichs semiboundedness and finite clock variance were proved at a fixed geodesic-cap sensor radius $\rho_0 = 1/20\text{ rad}$, whereas sending $\rho_0 \to 0$ at fixed $g > 0$ re-triggers `CLOCK_UV`. Here we prove two rigorous, non-asymptotic theorems showing that:

1. On unit $S^3$, the `RC01` $C^7$ geodesic-cap vacuum variance $\sigma_{X,\rho_0,\infty}^2$ obeys an **exact finite-$\rho_0$ lower bound** $\sigma_{X,\rho_0,\infty}^2 > \frac{25}{576\pi^2}\rho_0^{-2}$ for every $\rho_0 \in (0, 1/3]$.
2. In 3+1D canonical quantum field theory coupled to gravity, **every normal pure or mixed Fock state $\rho$** (including arbitrarily squeezed or non-Gaussian states, without assuming pointwise positivity of normal-ordered energy density) driving a local $C^7_c(B_L)$ clock gate over causal duration $\Delta t = \eta_t L/c$ ($\eta_t \in (0,1]$) at signal-to-noise ratio $\mathcal{N}_{\mathrm{gate}} \ge 1$ without forming a trapped surface inside radius $\lambda_{\mathrm{sys}} L$ ($\lambda_{\mathrm{sys}} \ge 1$) must satisfy a **strictly positive Planck-scale minimum sensor radius** $L > L_{\min}(\mathcal{N}_{\mathrm{gate}}, \eta_t, \mu_0, \lambda_{\mathrm{sys}})\,\ell_P$.

## 2. Exact Finite-$\rho_0$ Lower Bound on $S^3$

For $\kappa_{\rho_0}(x,y) = C_{\rho_0}^{-1}(x\cdot y - \cos\rho_0)_+^8$ on unit $S^3$ ($V_0 = 2\pi^2$), the Funk–Hecke multiplier is
$$\hat\kappa_{\rho_0}(k) = \frac{\int_0^{\rho_0} (\cos\chi - \cos\rho_0)^8 \frac{\sin(k\chi)}{k\sin\chi}\sin^2\chi\,d\chi}{\int_0^{\rho_0} (\cos\chi - \cos\rho_0)^8 \sin^2\chi\,d\chi}.$$
For any $\rho_0 \in (0, 1/3]$, let $N(\rho_0) := \lfloor \rho_0^{-1}\rfloor \ge 3$. For all $1 \le k \le N(\rho_0)$ and $\chi \in (0, \rho_0]$, $0 < k\chi \le 1 < \pi$, so $\sin(k\chi) > 0$, $0 < \sin\chi < \chi$, and $\sin(k\chi) \ge k\chi - (k\chi)^3/6$. Hence
$$\frac{\sin(k\chi)}{k\sin\chi} > \frac{\sin(k\chi)}{k\chi} \ge 1 - \frac{(k\rho_0)^2}{6} \ge \frac{5}{6} \implies \hat\kappa_{\rho_0}(k) > \frac{5}{6} \quad \bigl(1 \le k \le N(\rho_0)\bigr).$$
Since $\frac{k^2}{\sqrt{k^2-1}} > k$ for all $k \ge 2$ and $N(N+1) - 2 = \frac{1}{2}(N+1)^2 + \frac{1}{2}(N^2 - 5) > \frac{1}{2}\rho_0^{-2}$ for $N \ge 3$, the minimal-clock equal-time vacuum variance satisfies for every $\rho_0 \in (0, 1/3]$:
$$\sigma_{X,\rho_0,\infty}^2 = \frac{1}{2 V_0}\sum_{k=2}^\infty \frac{k^2}{\sqrt{k^2-1}}\,\hat\kappa_{\rho_0}(k)^2 > \frac{25}{72 V_0}\sum_{k=2}^{N(\rho_0)} k = \frac{25\bigl(N(\rho_0)(N(\rho_0)+1)-2\bigr)}{288\pi^2} > \frac{25}{576\pi^2}\,\rho_0^{-2}.$$

## 3. Squeezing-Proof Fock-Space Operational Minimum Sensor Radius Theorem

Let $X(x) = \int \frac{d^3k}{(2\pi)^3}\sqrt{\frac{\hbar c}{2\omega_k}}(a_k e^{ik\cdot x} + a_k^\dagger e^{-ik\cdot x})$ be a real Klein–Gordon clock field of inverse Compton scale $\mu_X \ge 0$ ($\omega_k = \sqrt{|k|^2 + \mu_X^2} \le |k| + \mu_X$) with positive renormalized Hamiltonian $H_{\mathrm{ren}} = \int \frac{d^3k}{(2\pi)^3}\hbar c\,\omega_k a_k^\dagger a_k \ge 0$. Let $w_L(x) = I_1^{-1} L^{-3}(1 - |x|^2/L^2)_+^8 \in C^7_c(B_L)$ ($\int_{\mathbb{R}^3} w_L = 1$), and define $X_L := \int_{\mathbb{R}^3} w_L(x) X(x)\,d^3x$, $\dot X_L := \int_{\mathbb{R}^3} w_L(x)\dot X(x)\,d^3x$.

By Plancherel's identity, $\int \frac{d^3k}{(2\pi)^3}|\hat w_L(k)|^2 = \int w_L^2 = c_{w,2} L^{-3}$ and $\int \frac{d^3k}{(2\pi)^3}|k|^2|\hat w_L(k)|^2 = \int |\nabla w_L|^2 = c_{w,\nabla} L^{-5}$, where $c_{w,2}, c_{w,\nabla}$ are exact rational multiples of $\pi^{-1}$. Writing $\dot X_L = A - A^\dagger$ with $A = -ic\int \frac{d^3k}{(2\pi)^3}\sqrt{\frac{\hbar c\,\omega_k}{2}}\hat w_L(k) a_k$, every normal density matrix $\rho$ with finite total energy $E_{\mathrm{tot}} = \mathrm{Tr}(\rho H_{\mathrm{ren}}) \ge 0$ satisfies:

1. **Exact canonical commutator & Robertson–Heisenberg bound**:
   $$[X_L, \dot X_L] = i\hbar c^2 c_{w,2} L^{-3} \implies \mathrm{Var}_\rho(X_L)\,\mathrm{Var}_\rho(\dot X_L) \ge \frac{1}{4}\hbar^2 c^4 c_{w,2}^2 L^{-6}.$$
2. **State-positivity velocity & second-moment bounds** (using $|\langle a_k\rangle_\rho|^2 \le \langle a_k^\dagger a_k\rangle_\rho$ and $-(A-A^\dagger)^2 = 4A^\dagger A + 2[A,A^\dagger] - (A+A^\dagger)^2 \le 4A^\dagger A + 2[A,A^\dagger]$):
   $$\bigl|\langle \dot X_L\rangle_\rho\bigr|^2 \le \frac{2 c^2 c_{w,2}}{L^3}\,E_{\mathrm{tot}}, \qquad \mathrm{Var}_\rho(\dot X_L) \le \langle \dot X_L^2\rangle_\rho \le \frac{2 c^2 c_{w,2}}{L^3}\,E_{\mathrm{tot}} + \frac{2\overline{c}_{w,\mathrm{kin}}(\mu_0)\,\hbar c^3}{L^4}$$
   whenever $\mu_X L \le \mu_0$, where $\overline{c}_{w,\mathrm{kin}}(\mu_0) := \frac{1}{2}\bigl(\sqrt{c_{w,2} c_{w,\nabla}} + \mu_0 c_{w,2}\bigr) \ge \frac{1}{2}\int \frac{d^3k}{(2\pi)^3} L^4\omega_k|\hat w_L(k)|^2$.
3. **Dimensionless energy threshold**: Requiring local gate distinguishability $\Delta t\,|\langle \dot X_L\rangle_\rho| \ge \mathcal{N}_{\mathrm{gate}}\sqrt{\mathrm{Var}_\rho(X_L)}$ over $\Delta t = \eta_t L/c$ yields $16\eta_t^2 \mathcal{E}(\mathcal{E} + \bar a) \ge \mathcal{N}_{\mathrm{gate}}^2$ for $\mathcal{E} := \frac{E_{\mathrm{tot}} L}{\hbar c}$ and $\bar a := \frac{\overline{c}_{w,\mathrm{kin}}(\mu_0)}{c_{w,2}}$, forcing
   $$E_{\mathrm{tot}} \ge \frac{\mathcal{E}_{\min}(\mathcal{N}_{\mathrm{gate}}, \eta_t, \mu_0)\,\hbar c}{L}, \qquad \mathcal{E}_{\min} := \frac{\mathcal{N}_{\mathrm{gate}}^2}{8\eta_t^2\Bigl(\bar a + \sqrt{\bar a^2 + \frac{\mathcal{N}_{\mathrm{gate}}^2}{4\eta_t^2}}\Bigr)} > 0.$$
4. **Gravitational horizon exclusion of $L \to 0$**: Requiring gravitational non-trapping $\frac{2 G E_{\mathrm{tot}}}{c^4} < \lambda_{\mathrm{sys}} L$ across the causal region of radius $\lambda_{\mathrm{sys}} L$ forces
   $$L > L_{\min} := \sqrt{\frac{2\,\mathcal{E}_{\min}(\mathcal{N}_{\mathrm{gate}}, \eta_t, \mu_0)}{\lambda_{\mathrm{sys}}}}\,\ell_P, \qquad \ell_P := \sqrt{\frac{\hbar G}{c^3}}.$$

## 4. Scope Boundary

This theorem rules out pointlike ($L \to 0$) operational quantum clocks under canonical QFT + spherical hoop/trapped-surface non-trapping; it does not by itself derive a discrete spacetime lattice from `Core v3`.
