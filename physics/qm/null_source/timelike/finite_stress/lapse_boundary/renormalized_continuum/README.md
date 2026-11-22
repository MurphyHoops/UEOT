# Renormalized Continuum Apparatus, Parseval Quadrupole Closure, and Sub-Critical Bounce FRW (`PR #468` Continuation)

This cohort continues directly from `joint_constraints` (`3cd6f7ead5743782173e44ab3344b8129c01c899`), reusing `319` accepted predecessor entries (`294 + 25`) and freezing `1,178` predecessor scientific files (`1090 + 87 + 1`) byte-for-byte without modification or re-execution.

## Entry Points

- **Chinese Unification Progress Report**: [UNIFICATION_PROGRESS_ZH.md](UNIFICATION_PROGRESS_ZH.md)
- **Research Contract**: [CONTRACT.md](CONTRACT.md)
- **Next Acceptance Gate**: [NEXT_GATE.md](NEXT_GATE.md)
- **Session & Multi-Agent Audit Logs**: [SESSION.md](SESSION.md) · [AUDIT.md](AUDIT.md) · [REVIEW.md](REVIEW.md)

## Complete Twelve-Entry Proof & Certificate Index (`RC01`–`RC12`)

### Cycle 1 — Continuum Local Apparatus & Graph Limit
1. `RC01` [GEODESIC_CAP_KERNEL.md](GEODESIC_CAP_KERNEL.md) · `geodesic_cap_kernel.py` — $C^7$ geodesic-cap sensor kernel $\kappa_{\rho_0}(x, y) = C_{\rho_0}^{-1}(x \cdot y - \cos\rho_0)_+^8$ ($\rho_0 = 1/20\text{ rad}$) on $S^3$, exact 9-harmonic Funk–Hecke multipliers, strict equal-time microcausality for $d_{S^3} > 1/10\text{ rad}$, and 9-IBP $O(k^{-10})$ decay.
2. `RC02` [CONTINUUM_CLOCK_COMPOSITE.md](CONTINUUM_CLOCK_COMPOSITE.md) · `continuum_clock_composite.py` — Glimm–Jaffe normal-ordered free generator + cap-smeared interaction, uniform $K \le \infty$ Friedrichs lower bound across $a \in (0, \sqrt{3/2}]$, finite continuum variances overcoming `CLOCK_UV`, $O(K^{-18})$ Wick variance tail ($O(K^{-9})$ vector norm) overcoming `WICK_CLOCK_GRAPH`, and $O(K^{-10})$ cutoff projection commutator $[P_K, \mathcal{K}_{\rho_0} Z_a]$ decay.
3. `RC03` [CONTINUUM_TADPOLE_COLUMNS.md](CONTINUUM_TADPOLE_COLUMNS.md) · `continuum_tadpole_columns.py` — Continuum ($K = \infty$) conformally improved total 8-projection Jacobian ($\det M_{\mathrm{ctrl}}^{\rho_0,\mathrm{conf}} > 10$, $\|(J_{\mathrm{total}}^{\rho_0,\infty})^{-1}\| < 0.0056$), vacuum-subtracted ($v_{\mathrm{eff}} = 0$) comparison, and minimal-clock $\mathcal{Q}(H_{0,3}(X))$ form control.

### Cycle 2 — Spatial Quadrupole Elimination & Closed-FRW Compactness Threshold
4. `RC04` [PARSEVAL_ISOTROPIC_FRAME.md](PARSEVAL_ISOTROPIC_FRAME.md) · `parseval_isotropic_frame.py` — Six-channel conformally coupled ($\xi = 1/6, M = 0$) Parseval $\ell = 1$ frame $(Y_0, Y_1, W_1, \dots, W_4)$ with real-analytic matrix square root $\mathbf W(\mathbf u) = (\lambda_0 I_4 - \boldsymbol\epsilon\boldsymbol\epsilon^T - \boldsymbol\zeta\boldsymbol\zeta^T)^{1/2}$ ($\lambda_0 = 2 \times 10^{-32}$), proving exact all-time curved-FRW homogeneous radiation stress $\rho_{\mathrm{frame}} = 3 p_{\mathrm{frame}} = \frac{2\lambda_0}{\hat\kappa_{\rho_0}(2)^2 g^2 a(\tau)^4}$ and **exact vanishing** of `POST_CLOSURE`'s $\ell = 2$ spatial quadrupole $-Q_2/g^2 \equiv 0$.
5. `RC05` [CRUNCH_VS_SUBCRITICAL_GRAVITY.md](CRUNCH_VS_SUBCRITICAL_GRAVITY.md) · `crunch_vs_subcritical_gravity.py` — Exact $\Lambda \le 0$ stiff-clock Big-Crunch horizon theorem ($\Delta\tau_{\mathrm{universe}} \le \pi/2$ pure clock, $< \pi < \pi + 4$ with radiation) versus the necessary and sufficient sub-critical bounce window $0 < \frac{4\pi G}{g^2} < 1$ ($\alpha_G < 1/3$).
6. `RC06` [DYNAMICAL_FRW_CLOCK_PROGRAM.md](DYNAMICAL_FRW_CLOCK_PROGRAM.md) · `dynamical_frw_clock_program.py` — Degree-220 positive-series Taylor–Picard outward-interval enclosure (`R_u < 2e-30`, zero ODE integrations) of the non-static bounce $a(\tau)$ across $\tau \in [-1, \pi + 3]$, verifying $1 \le u(\tau) < 1.016 < 3/2$ and re-deriving the curved physical clock $\theta(\tau) = \int_0^\tau u(s)^{-1}\,ds$.

### Cycle 3 — Hadamard Cauchy Transport & Curved-FRW Continuum Inverse
7. `RC07` [HADAMARD_CAUCHY_TRANSPORT.md](HADAMARD_CAUCHY_TRANSPORT.md) · `hadamard_cauchy_transport.py` — Non-turnaround unrescaled non-normality ($\|\beta^{\mathrm{naive}}\|_{\mathrm{HS}} = \infty$ for $a'(\tau_0) \neq 0$) versus turnaround Weyl-conformal initialization at $\tau = 0$ and Volterra-IBP $O(k^{-2})$ / adiabatic $O(k^{-3})$ continuum Hilbert–Schmidt transport across $\tau \in [-1, \pi + 3]$.
8. `RC08` [CURVED_CONTINUUM_INVERSE.md](CURVED_CONTINUUM_INVERSE.md) · `curved_continuum_inverse.py` — Continuum limiting/parametrix 8-projection total-source inverse on the dynamical closed-FRW bounce ($\|(J_{\mathrm{total,FRW}}^{\rho_0,\infty})^{-1}\| < 0.0057$) with program-invariant background FRW history.

### Cycle 4 — Local Autonomous Pointer, Continuum Stress Variance, Coupled CTP Kernel & Calibration
9. `RC09` [LOCAL_AUTONOMOUS_POINTER.md](LOCAL_AUTONOMOUS_POINTER.md) · `local_autonomous_pointer.py` — Coordinate-free 4D local autonomous pointer $\Psi_{\mathrm{ptr}}$ and antipodally balanced $r_b/g$-scaled conformal beacon $B_{\mathrm{rec}}$ with strict relativistic light-cone cap inclusion $\frac{31}{80} + \frac{1}{80} + 2\rho_0 = \frac{1}{2}$, zero odd-$\ell$ beacon moments, and $k = 1$ quadrature continuum binary gap $> 4.5 \times 10^{-23}$ inside the certified positive-kernel window.
10. `RC10` [CONTINUUM_STRESS_VARIANCE.md](CONTINUUM_STRESS_VARIANCE.md) · `continuum_stress_variance.py` — Exact $O(K^5)$ sharp-slice minimal-clock pressure variance $\frac{2}{9}\sum_{k=2}^K k^2(k^2 - 1)$ blowup versus uniform $K \le \infty$ spacetime-smeared continuum total stress variance.
11. `RC11` [COUPLED_CTP_TENSOR_KERNEL.md](COUPLED_CTP_TENSOR_KERNEL.md) · `coupled_ctp_tensor_kernel.py` — Connected quadratic two-branch Schwinger–Keldysh kernel across scalar lapse, non-Killing $k_V = 3$ vector shift, and $k_T = 3$ $(2,0)\oplus(0,2)$ TT-graviton sectors with $R^2 + \mathrm{Weyl}^2$ counterterms, symbolically verified $S^3$ Keldysh noise positivity, and $O(K^{-10})$ cutoff Bianchi residual decay.
12. `RC12` [CALIBRATION_AND_OPEN_GATES.md](CALIBRATION_AND_OPEN_GATES.md) · `calibration_and_open_gates.py` — Exact SI / CODATA-2022 Planck dictionary ($R_{S^3} \approx 1046.1\text{ km}$, $L_{\mathrm{sensor}} \approx 52.30\text{ km}$ at $g = 10^{-40}, \alpha_G = 1/10$), KL/Pinsker sample-complexity lower bound $N_{\mathrm{trials}} > 8 \times 10^{41}$, and explicit open unification gates (`"physical_unification": "OPEN"`).
