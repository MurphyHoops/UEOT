# `mesoscopic_decoherence_gravimetry` — Open-System Lindblad Decoherence Budget, LOCC Non-Classicality Witness & Pre-Registered Blind-Holdout Pipeline (`P-MESO-BMV-06`)

Companion 40-digit outward-interval verification suite (`verify_meso_decoherence.py` + `certificate.json`) for `UEOTPhysicsUnification.MesoscopicDecoherenceGravimetry`, closing the open-system decoherence and pre-registered empirical-pipeline specification of `NEXT_GATE` Frontier 4 (`AH08` flat-space mesoscopic gravimetry + `validation/physics_unification/HARDWARE_CERTIFICATION_CONTRACT.md`) while preserving `"device_certified": false` and `"physical_unification": "OPEN"`.

## 1. Pure-Kernel Lean 4 Theorems (`MesoscopicDecoherenceGravimetry.lean`)

All definitions and theorems operate on genuine $4 \times 4$ complex operators (`Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ`) with `0 sorryAx`, `0 native_decide`, and `0` custom axioms:

1. **Commuting Stabilizer Algebra & Two-Eigenvalue BMV Entanglement Witness (`bmvWitnessOp_hermitian_and_stabilizer_spectrum`)**:
   For $W_{\mathrm{BMV}} := I \otimes I - X \otimes X + Y \otimes Z + Z \otimes Y = I_4 - A_1 - A_2 - A_3$ ($A_1 = X\otimes X$, $A_2 = -Y\otimes Z$, $A_3 = -Z\otimes Y$), $W_{\mathrm{BMV}}^\dagger = W_{\mathrm{BMV}}$, $(A_1, A_2, A_3)$ are pairwise-commuting involutions satisfying $A_1 A_2 = A_3$, and $(W_{\mathrm{BMV}} - 2 I_4)(W_{\mathrm{BMV}} + 2 I_4) = 0$ (exact eigenvalues $\{-2, +2\}$, enabling single-shot commuting Bell/stabilizer readout as well as 3-setting local Pauli readout).
2. **3D Cauchy–Schwarz Separable Bound & LOCC Mediator No-Go (`bmv_trace_product_bloch_exact`, `bloch_correlator_abs_le_one_of_cauchy_schwarz`, `locc_separable_mixture_bmv_witness_nonneg`, `ktm_classical_dephased_gravity_witness_eq_one`)**:
   Every finite convex LOCC combination $\rho_{\mathrm{LOCC}} = \sum_a p_a (\rho(\mathbf{r}_a) \otimes \rho(\mathbf{s}_a))$ with $p_a \ge 0$, $\sum_a p_a = 1$, $\|\mathbf{r}_a\|^2 \le 1$, $\|\mathbf{s}_a\|^2 \le 1$ satisfies $\mathrm{Im}\,\mathrm{Tr}(W_{\mathrm{BMV}}\rho_{\mathrm{LOCC}}) = 0$ and $\mathrm{Re}\,\mathrm{Tr}(W_{\mathrm{BMV}}\rho_{\mathrm{LOCC}}) \ge 0$ via exact 3D Lagrange sum-of-squares, while a classical path-measuring Kafri–Taylor–Milburn gravitational channel ($\nu = 0$) gives $\mathrm{Tr}(W_{\mathrm{BMV}}\rho_{\mathrm{KTM}}) = 1 \ge 0$.
3. **Exact $4 \times 4$ Lindblad Dephased & Depolarized Gravitational Witness & Rate Threshold (`dephase2_commutes_with_gravUnitary`, `bmv_depolarized_witness_trace_exact`, `bmv_dephased_witness_trace_exact`, `bmv_signal_gt_one_of_half_angle_window`, `bmv_lindblad_decoherence_rate_threshold_iff`, `bmv_dephased_witness_le_depolarized_and_both_violate_locc`)**:
   - Spatial-path Lindblad dephasing commutes identically with the diagonal gravitational unitary $U_{\mathrm{grav}}(\phi)$.
   - On $|\psi(\phi)\rangle = \frac{1}{2}(|00\rangle + |01\rangle + |10\rangle + e^{i\phi}|11\rangle)$ with coherence factor $\nu = e^{-\Gamma T} \in (0, 1]$:
     $$\mathrm{Tr}\bigl(W_{\mathrm{BMV}}(\mathcal{D}_\nu \otimes \mathcal{D}_\nu)(|\psi(\phi)\rangle\langle\psi(\phi)|)\bigr) = 1 - \nu^2\bigl(\cos^2(\phi/2) + \sin\phi\bigr),$$
     $$\mathrm{Tr}\bigl(W_{\mathrm{BMV}}(\mathcal{E}_\nu^Z \otimes \mathcal{E}_\nu^Z)(|\psi(\phi)\rangle\langle\psi(\phi)|)\bigr) = 1 - \nu^2\cos^2(\phi/2) - \nu\sin\phi \le 1 - \nu^2\bigl(\cos^2(\phi/2) + \sin\phi\bigr) \quad (\sin\phi \ge 0).$$
   - Whenever $0 < \sin(\phi/2) < 2\cos(\phi/2)$ ($\tan(\phi/2) < 2$) and $\Gamma < \frac{1}{2T}\ln\bigl(\cos^2(\phi/2) + \sin\phi\bigr)$, both open-system channels strictly violate the LOCC separable bound ($\mathcal{W} < 0$).
4. **SPAM-Calibrated Contrast & Pre-Registered Blind-Holdout Non-Vacuity (`noisy_differential_spam_offset_cancels`, `empirical_bmv_witness_confidence_certifies_non_locc`, `no_vacuous_pass_on_empty_calibration_or_missing_raw_shots`)**:
   Proves exact cancellation of asymmetric SPAM offset $(1 - \ell)e_0$ in differential $\pm\Delta\phi_{\mathrm{grav}}$ readout, soundness of finite-shot upper-confidence witness certification, and strict rejection (`deviceCertified = false`) whenever raw HDF5 shot logs are absent, calibration confidence sets are empty, or the LOCC baseline is unviolated (complementing Mathematics v4.2 `StatisticalRiskBoundary` on post-selection vs simultaneous/blind-holdout calibration).

## 2. 40-Digit Outward-Interval Results (`certificate.json`)

For the `AH08` flat-space ($\Lambda = 0$) mesoscopic benchmark ($m = 10^{-14}\text{ kg}$ crystalline diamond microsphere of radius $R_{\mathrm{sphere}} \approx 0.879\,\mu\text{m}$, interferometric excursion half-width $R_{\mathrm{app}} = 50\,\mu\text{m}$ / splitting $\Delta x = 100\,\mu\text{m}$, center separation $d_{\mathrm{sep}} = 200\,\mu\text{m}$, $T_{\mathrm{int}} = 1\text{ s}$):

- **Gravimetric phase & BMV coherent signal**: $\Delta\phi_{\mathrm{grav}} \in [0.31643885, 0.31645309]\text{ rad}$, $\cos^2(\Delta\phi_{\mathrm{grav}}/2) + \sin(\Delta\phi_{\mathrm{grav}}) \in [1.2863568, 1.2863726] > 1$.
- **Maximum tolerable per-packet decoherence rate ($\mathcal{W} < 0$)**: $\Gamma_{\max,\mathrm{depol}} \in [0.125907, 0.125914]\text{ s}^{-1} > 0.1258\text{ s}^{-1}$ (and $\Gamma_{\max,\mathrm{deph}} \in [0.144342, 0.144356]\text{ s}^{-1}$ for pure spatial dephasing).
- **Cryogenic UHV environmental rate ($T_{\mathrm{env}} = 0.5\text{ K}, P_{\mathrm{gas}} = 10^{-15}\text{ Pa}$ ${}^4\mathrm{He}$)**: $\Gamma_{\mathrm{env}} = \Gamma_{\mathrm{gas}} + \Gamma_{\mathrm{bb,sc}} + \Gamma_{\mathrm{bb,em}} \in [0.01809517, 0.01809518]\text{ s}^{-1} < 0.02\text{ s}^{-1}$ ($> 6.95\times$ safety margin below $\Gamma_{\max,\mathrm{depol}}$).
- **Noisy SPAM-calibrated $95\%$ Hoeffding shot counts ($\Gamma_{\mathrm{env,cap}} = 0.02\text{ s}^{-1}$, $\ell = 0.01, e_0 = 0.008, e_1 = 0.012 \implies \eta_{\mathrm{SPAM}} = 0.9702$)**:
  - Differential $\pm\Delta\phi_{\mathrm{grav}}$ phase readout: **$69$ runs** (`[68.408, 68.415]`);
  - Non-LOCC BMV witness ($\mathcal{W} < 0$): **$435 < 450$ total shots** in the commuting stabilizer basis (`431` at unit stabilizer visibility) and **$365 < 450$ shots per Pauli setting** (`347` under pure spatial dephasing) across local $(XX, YZ, ZY)$ settings.
- **Empirical status**: Pre-registered hardware pipeline & negative controls verified; no laboratory HDF5 data archived (`"device_certified": false`, `"physical_unification": "OPEN"`).

## 3. Reproducible Verification Commands

```bash
/private/tmp/ueot-lapse-boundary-20261121-venv/bin/python -B physics/unification/mesoscopic_decoherence_gravimetry/verify_meso_decoherence.py --write
/private/tmp/ueot-lapse-boundary-20261121-venv/bin/python -B physics/unification/mesoscopic_decoherence_gravimetry/verify_meso_decoherence.py --check
```
