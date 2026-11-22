# `unimodular_vacuum_selection` — Unimodular / Sequestered Dimensionless Vacuum Constant $\mathcal{I}_\Lambda$ & Viability Window (`P-UNIMODULAR-LAMBDA-09`)

Companion 40-digit outward-interval verification suite (`mpmath.iv`, `iv.dps = 40`) for `UEOTPhysicsUnification.UnimodularVacuumConstantSelection` (Wave 7 Angle 7C), preserving strict read-only upstream governance (`"Core_v3_modified": false`, `"device_certified": false`, `"physical_unification": "OPEN"`):

1. **Trace-Free / Unimodular Einstein Quotient Descent (`QuotientDescent` + `FisherGauge`)**:
   - Proves on `4 × 4` Lorentzian spacetime tensors ($g^{-1} g = I_4$, $\operatorname{Tr}(g^{-1} g) = 4$) that the trace-free projector $S_{\mu\nu} - \frac{1}{4}(g^{\alpha\beta}S_{\beta\alpha})g_{\mu\nu}$ annihilates arbitrary multi-loop, electroweak/QCD phase-transition, and Planck/Dirac-sea zero-point shifts $T_{\mu\nu} \mapsto T_{\mu\nu} - \Delta\rho_{\mathrm{vac}} g_{\mu\nu}$ ($> 10^{122}\rho_\Lambda^{\mathrm{obs}}$), descending uniquely via `UEOT.V3.Compression.QuotientDescent.existsUnique_descend` and forming an exact `UEOT.V3.FisherGauge.p_inv_02` zero direction (resolving the UV radiative instability of `P-DE-12`).
   - Proves exact tensorial equivalence between $R_{\mu\nu} - \frac{1}{4} R g_{\mu\nu} = 8\pi G(T_{\mu\nu} - \frac{1}{4} T g_{\mu\nu})$ and $G_{\mu\nu} + \Lambda_{\mathrm{int}} g_{\mu\nu} = 8\pi G T_{\mu\nu}$, where contracted Bianchi $\nabla^\mu G_{\mu\nu} = 0$ + stress conservation $\nabla^\mu T_{\mu\nu} = 0$ lock $\Lambda_{\mathrm{int}} = \frac{1}{4}(R + 8\pi G T)$ to a global integration constant conjugate to spacetime 4-volume.

2. **Weinberg Local Scalar Adjustment No-Go vs Global Kaloper–Padilla 4-Volume Sequestering**:
   - Formalizes Weinberg's local adjustment obstruction ($\frac{d}{du}[V(\phi_*(u)) + u] = 1 \neq 0$ whenever $V'(\phi_*) = 0$, and scale-covariant dilaton fine-tuning / vanishing-Hessian runaway dichotomy) versus global 4-volume / 4-form historic-average sequestering $\Lambda_{\mathrm{seq}} = \frac{1}{4}\langle T^\mu_\mu \rangle_{V_4} + \Delta\Lambda_{\mathrm{flux}}$, which cancels arbitrary loop shifts $\Delta\rho_{\mathrm{vac}}$ identically while bounding $|\rho_{\Lambda,\mathrm{eff}} - \Delta\Lambda_{\mathrm{flux}}| \le \frac{1}{4} B_{\mathrm{hist}}$.

3. **Two-Sided `UEOT` Organizational Viability (`ViabilityKernel`, $\Omega > 0$) & Gibbons–Hawking Entropy (`InformationPacking`)**:
   - Proves the exact depressed-cubic sum-of-squares factorization of spherical top-hat halo collapse $P_{\mathrm{halo}}(a) = \frac{\Lambda}{3} a^3 - \kappa_c a + r_s$, deriving Weinberg's exact rational coefficient $\rho_\Lambda < \frac{500}{729}\rho_m \delta_i^3$ and enclosing the Tegmark–Weinberg halo-collapse upper threshold $\mathcal{I}_{\Lambda,\max}(\delta_0, Q, \xi_b) \in [9.1\times 10^{-120},\; 1.04\times 10^{-119}] \sim 10^{-119}$ ($\delta_0 = 150, Q = 2\times 10^{-5}, \xi_b \approx 2.99\times 10^{-28}$), inside which `UEOT.V3.ViabilityKernel` sustains a non-empty controlled-invariant fixed point ($\Omega > 0$).
   - Encloses the unit-gauge-invariant Gibbons–Hawking de Sitter causal-patch entropy $S_{\mathrm{dS}} = \frac{3\pi}{\mathcal{I}_\Lambda^{\mathrm{obs}}} \in [3.197065\times 10^{122},\; 3.331314\times 10^{122}]$ (`InformationPacking` finite-patch history packing bound), explicitly separating proven radiative decoupling + viability window from the open exact integration constant $\mathcal{I}_\Lambda^{\mathrm{obs}} \approx 2.89\times 10^{-122}$.

## Reproducible Verification

```bash
/private/tmp/ueot-lapse-boundary-20261121-venv/bin/python -B physics/unification/unimodular_vacuum_selection/verify_unimodular_lambda.py --write
/private/tmp/ueot-lapse-boundary-20261121-venv/bin/python -B physics/unification/unimodular_vacuum_selection/verify_unimodular_lambda.py --check
```
