# Renormalized-Continuum Research Contract (PR #468 Continuation)

## Baseline and Scope Boundaries

- **Parent baseline commit**: `3cd6f7ead5743782173e44ab3344b8129c01c899` on branch `codex/physics-source-response-20261119` (`PR #468`, open draft, unmerged).
- **Parent verification receipt**: `physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/verification.json` (`PASS`, `25` entries, `294 + 25 = 319` reused predecessor entries, `1090 + 87 + 1 = 1178` frozen predecessor scientific files).
- **Exact prior-head CI run**: `44993707266`, job `137120103830` (`reproduce`), artifact `14743200549` (`sha256:9fa85eaa28f47b1cc629ee183982e6fc28c11c68fc3f036111cfc4bb8ce67078`), decoded log SHA-256 `35a7cddb50e246b745bc1528c0201915fdda4a1232a20cfbd0cf9d093a576b53`.
- **Immutable governance**:
  1. `Core v3` is strictly read-only; `GI` remains excluded; `PR #468` remains an open draft PR (do not merge).
  2. All `1,178` predecessor scientific files are frozen byte-for-byte against `3cd6f7ead5743782173e44ab3344b8129c01c899`.
  3. Only `physics/qm/null_source/timelike/finite_stress/lapse_boundary/renormalized_continuum/` and the 4 established routing files (`.github/workflows/ueot-physics-source-response.yml`, `physics/qm/README.md`, `physics/qm/ROADMAP.md`, `physics/qm/null_source/timelike/README.md`) may be modified.
  4. Zero predecessor Python modules are imported or executed (`predecessor_scientific_modules_imported_or_executed == 0`), and zero mode or geometry numerical ODE integrators are executed (`mode_ODE_integrations == 0`, `geometry_ODE_integrations == 0`). All intervals use 100-digit outward interval arithmetic (`mpmath.iv`, `iv.dps = 100`).

## Input Separation and Honest Model Declarations

1. **New explicit continuum apparatus composite (`RC01`–`RC03`)**:
   - The pointlike finite-$K$ truncated interaction of `CLOCK_ACTUATOR` is NOT declared to possess a pointlike Wightman $\rho_0 \to 0$ continuum limit (`CLOCK_UV` and `WICK_CLOCK_GRAPH` stand untouched in their declared scope).
   - Instead, we introduce an explicit **finite-radius geodesic-cap sensor kernel** $\kappa_{\rho_0}(x, y) = C_{\rho_0}^{-1}(x \cdot y - \cos\rho_0)_+^8$ ($\rho_0 = 1/20\text{ rad}$) on $S^3$, combined with the Glimm–Jaffe normal-ordered free Hamiltonian $H_{0,\mathrm{ren},K} \ge 0$ (`H_{0,\mathrm{ren}}|\Omega\rangle = 0`).
   - At $K = \infty$, **equal-time** smeared canonical and interaction densities commute strictly for geodesic separations $d_{S^3}(x_1, x_2) > 2\rho_0 = 1/10\text{ rad}$ (equal-time microcausality outside the finite sensor ball, not pointlike for $d_{S^3} < 2\rho_0$), and define a uniformly lower-semibounded Friedrichs self-adjoint realization $H_{\mathrm{ren},\infty}^{\rho_0,\mathrm{Fr}}$.

2. **New 6-channel conformally coupled Parseval controller frame (`RC04`)**:
   - `POST_CLOSURE`'s proof that a 2-channel dipole controller leaves a nonzero $\ell = 2$ spatial quadrupole $-Q_2(\mathbf u)/g^2 \neq 0$ stands untouched for the 2-channel model.
   - To eliminate all $\ell \ge 1$ controller background spatial stress rows without metric-dependent couplings, we explicitly enlarge the controller sector to a **6-channel conformally coupled massless ($\xi = 1/6, M = 0$) $\ell = 1$ Parseval frame** $(Y_0, Y_1, W_1, W_2, W_3, W_4)$ where all six channels carry common dipole amplitude factor $\frac{\cos(2\tau)}{\hat\kappa_{\rho_0}(2)\,a(\tau)\,g}$ and $(W_1,\dots,W_4)$ are body-decoupled spectators carrying columns of $(\lambda_0 I_4 - \epsilon\epsilon^T - \zeta\zeta^T)^{1/2}$ ($\lambda_0 = 2 r_0^2 = 2 \times 10^{-32}$). On unit static ESU ($a \equiv 1$), $\xi R = 1$ gives the identical quadratic dispersion $\omega_{Y,k} = k$ as `CLOCK_ACTUATOR` (with conformal improvement $\Delta T_{\mu\nu}^{(Y,\mathrm{imp})}$ explicitly included in the dipole stress columns), while on any closed FRW $ds^2 = a(\tau)^2(-d\tau^2 + d\Omega_3^2)$ the 6-channel frame has exact $SO(4)$-homogeneous radiation stress $\rho_{\mathrm{frame}} = 3 p_{\mathrm{frame}} = \frac{2\lambda_0}{\hat\kappa_{\rho_0}(2)^2 g^2 a(\tau)^4}$, $j_i \equiv 0$, $\Pi_{ij} \equiv 0$.

3. **Declared sub-critical gravitational compactness regime (`RC05`–`RC08`)**:
   - At $G \sim O(1)$ with $\Lambda \le 0$ in unit-$S^3$ dimensionless coordinates, the stiff clock enthalpy triggers a Big Crunch within $\Delta\tau < \pi$ (`RC05`, strengthening `BACKREACTION_GATE`).
   - Our common curved-spacetime evolution (`RC06`–`RC08`) explicitly operates in the **sub-critical gravitational compactness regime** $0 < \frac{4\pi G}{g^2} < 1$ ($\alpha_G = \frac{4\pi G}{3 g^2} = \frac{1}{10}$) with positive cosmological constant $\lambda_\Lambda = \frac{\Lambda}{3} = \frac{550001}{1000000}$ and positive conformal radiation $\beta_r = \frac{349999}{1000000}$, initialized at the smooth turnaround bounce $a(0) = 1, a'(0) = 0$. In restored physical units $G = (\ell_{\mathrm{Pl}}/R_{S^3})^2$, $\frac{4\pi G}{g^2} < 1$ corresponds to macroscopic $S^3$ radius $R_{S^3} > \sqrt{4\pi}\ell_{\mathrm{Pl}}/g$.

4. **Local autonomous pointer, smeared stress variance, coupled CTP kernel, and open unification (`RC09`–`RC12`)**:
   - A local 4D autonomous pointer scalar $\Psi_{\mathrm{ptr}}$ and antipodally symmetric $r_b/g$-scaled conformal beacon $B_{\mathrm{rec}}$ replace the externally switched terminal reader inside a causal readout cap pair and smooth clock window $g X_{\rho_0} \in [5.90, 5.92] \subset \big(\theta(\pi + \tfrac{5}{2}), \theta(\pi + 3)\big)$.
   - Full operator-level quantum Einstein equations, removal of the finite sensor scale $\rho_0 > 0$, Standard Model derivation from `Core v3`, and realistic laboratory gravimetry remain **OPEN** (`"physical_unification": "OPEN"`).
