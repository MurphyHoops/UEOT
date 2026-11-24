# `nonperturbative_4d_qg_h1d` — Nonperturbative 4D Reuter UV Fixed Point, Interacting Cluster OS Positivity, Modified Split-Ward Identity & Sharp `H1d` Core

Companion 40-digit outward-interval (`mpmath.iv`) and exact symbolic (`sympy`) verification suite for `UEOTPhysicsUnification.Nonperturbative4DQuantumGravityH1d` (Wave 9 `H1d`):

1. **`P-H1D-FRG-01` (4D Litim/Wetterich FRG Reuter UV Fixed Point & `(3,3,1)` Stability)**:
   - Symbolic + 40-digit interval verification of the 4D Type-Ia Litim FRG equations $(\eta_N, \beta_g, \beta_\lambda)$: exact $\eta_N = -2$ and UV spectral dimension $d_s = 2$.
   - Global existence/uniqueness of the pure-gravity Reuter UV fixed point ($\lambda_* \approx 0.1932005$, $g_* \approx 0.7073209$) with UV-attractive complex spiral exponents $\theta \approx 1.4753 \pm 3.0432 i$.
   - Exact compatibility with `(3,3,1)` 45-Weyl SM ($\lambda_{\mathrm{SM}} \approx -4.3931$, $g_{\mathrm{SM}} \approx 3.2172$, $\theta_{1,2} \approx 3.9261, 2.0827 > 0$) and 48-Weyl SM+$3\nu_R$, universal fixed-point positivity for $\Delta_M \le 11$, screening failure at $\Delta_M \ge 24$, and finite-dimensional higher-curvature $f(R)$ UV critical surface ($\theta_n < 0$ for $n \ge 3$).

2. **`P-H1D-CLUSTER-02` (Interacting Polymer Cluster Expansion, OS Positivity & Projective Tightness)**:
   - Verifies Kotecký–Preiss polymer cluster convergence ($q < 0.40$), uniform thermodynamic free-energy bound $q/(1-q)$, positive mass gap $m_{\mathrm{gap}} > 0.92$, and `ContractiveFixedPoint` Kirkwood–Salsburg convergence.
   - Verifies all-power $T_{\mathrm{int}}^k$ Osterwalder–Schrader reflection positivity and UV trace contraction for bounded-below non-Gaussian quartic potentials ($V \ge V_0$), paired with Prokhorov exponential-moment tightness and `TransportCertificate` bounds.

3. **`P-H1D-WARD-03` (Modified Split-Ward / Nielsen Background Independence)**:
   - Verifies exact IR ($k \to 0$) background-split invariance forcing unique `QuotientDescent` and placing background splits in the `FisherGauge` zero kernel (`P-INV-02`), alongside $O(k^2 |\varepsilon|)$ finite-scale defect suppression.

4. **`C-H1D-CORE-04` (Sharp `H1d` Decomposition)**:
   - Closes `H1d1`, `H1d2`, and `H1d3` in pure-kernel Lean 4 + 40-digit intervals while isolating `H1d4_GlobalNonTruncated4DContinuumMeasureUniqueness` as logically independent and honestly `OPEN`, preserving `"device_certified": false` and `"physical_unification": "OPEN"`.
