# `nonabelian_chiral_constructive` — Non-Abelian Chiral Gauge + Fermion Constructive Continuum Boundary (`P-NONABELIAN-CHIRAL-08`)

Companion 40-digit outward-interval verification suite (`mpmath.iv`, `iv.dps = 40`) for
[`NonAbelianChiralConstructiveBoundary.lean`](../../../formalization/ueot-physics-unification/UEOTPhysicsUnification/NonAbelianChiralConstructiveBoundary.lean).

## Scope & Certified Claims

1. **Lüscher Non-Abelian Chiral Fermion Measure Integrability & Gauge-Orbit Quotient Obstruction**:
   - Lean 4 theorems `luscher_projector_tangent_off_diagonal`, `luscherBerryCurvatureTrace_skew_and_gauge_invariant`,
     `luscher_weyl_action_descends_iff_zero_gauge_coboundary` (`UEOT.V3.Compression.QuotientDescent`), and
     `chiral_gauge_markov_belief_quotient_iff_closedTests` (`ObservableBeliefQuotient.ClosedTests`, `M-40.6`)
     prove off-diagonality and non-Abelian `SU(N)` gauge invariance of Lüscher's chiral projector Berry
     curvature $\mathrm{Tr}(\hat P_- [d_1 \hat P_-, d_2 \hat P_-])$ and prove that unique gauge-orbit descent
     holds if and only if gauge-fibre coboundary / `ClosedTests` anomalies vanish on admissible link configurations.

2. **Symplectic Kramers Reality (`C \tau_2`), Witten $\pi_4(SU(2)) = \mathbb{Z}_2$ Pfaffian Sign & Dai–Freed Mod-16 $\Omega_5^{\mathrm{Spin}}$**:
   - Lean 4 theorems `su2Matrix_unitary_det_and_symplectic_reality`, `su2Cayley_exact_unitary_and_noncommuting`,
     `witten_su2_pfaffian_z2_cancellation_vs_331_invariance`, and
     `dai_freed_mod16_spin_z4_majorana_vs_dirac_dichotomy` prove exact `SU(2)` symplectic conjugation
     $\varepsilon M = \overline{M} \varepsilon$ ($\varepsilon = i\tau_2$), Witten path-integral cancellation
     $Z_0 + (-1)^{N_d} Z_0 = 0$ for odd $SU(2)_L$ doublet counts vs `(3,3,1)` 4-doublet invariance, and the
     mod-16 $\Omega_5^{\mathrm{Spin}^{\mathbb{Z}_4}} \cong \mathbb{Z}_{16}$ Majorana-vs-Dirac dichotomy
     distinguishing $N_{\mathrm{Weyl}} = 15$ (`15 % 16 = 15`, $\mathrm{Tr}\,Q_X = -5$, $\mathrm{Tr}\,Q_X^3 = -125$)
     from $N_{\mathrm{Weyl}} = 16$ (`16 % 16 = 0`, $\mathrm{Tr}\,Q_X = 0$, $\mathrm{Tr}\,Q_X^3 = 0$).

3. **Non-Abelian Asymptotic Freedom, Plaquette Defect Suppression & Explicit $128 \times 128$ 4D `SU(2)` Overlap Audit**:
   - Lean 4 theorems `sm_nonabelian_one_and_two_loop_asymptotic_freedom`,
     `unitary_plaquette_frobenius_eq_twice_wilson`, and `plaquette_defect_boltzmann_power_suppression` prove
     exact 1-loop and 2-loop `(3,3,1)` coefficients (`SU(3)_c`: $b_0 = 7, b_1 = 26$; `SU(2)_L`: $b_0 = 19/6, b_1 = -35/6$)
     and prove the power-law Boltzmann bound $\exp(-\mathrm{distSq}/g_0^2(a)) \le (a\Lambda_{\overline{\mathrm{MS}}})^{2 c_{\mathrm{adm}} b_0} < 1$
     alongside the honest Clay 4D entropy-vs-action exponent boundary $2 c_{\mathrm{adm}} b_0 < 4$ at $\varepsilon_{\mathrm{adm}} = 1/30$.
   - Python `verify_nonabelian_chiral.py` certifies a genuinely non-commuting $2^4$ 4D `SU(2)` Neuberger Overlap
     operator ($128 \times 128$ complex interval matrices) in 40-digit `mpmath.iv`, enclosing $(X^\dagger X)^{-1/2}$,
     $\|\hat\gamma_5^2 - I_{128}\|_F$, $\|P_+ D_{\mathrm{ov}}\hat P_- - D_{\mathrm{ov}}\hat P_-\|_F$,
     the real structure $J = C_E \otimes i\tau_2$ ($J^2 = +I_{128}$) via $\|J D_{\mathrm{ov}} J^{-1} - \overline{D_{\mathrm{ov}}}\|_F$
     (algebraically implying $\mathrm{Im}\det D_{\mathrm{ov}} = 0$), and non-Abelian `SU(2)` gauge covariance:
     $D_{\mathrm{ov}}(U^g)$ is assembled from the Wilson kernel $X(U^g)$ built directly from the transformed links
     $U^g_\mu(x) = g(x)U_\mu(x)g(x+\hat\mu)^\dagger$ with its own Riccati-certified enclosure of
     $(X(U^g)^\dagger X(U^g))^{-1/2}$, and then compared with $G D_{\mathrm{ov}}(U) G^\dagger$, $G\hat P_-(U)G^\dagger$
     and the Lüscher index of $D_{\mathrm{ov}}(U)$, while keeping `"device_certified": false` and `"physical_unification": "OPEN"`.

## Commands

```bash
/private/tmp/ueot-lapse-boundary-20261121-venv/bin/python -B physics/unification/nonabelian_chiral_constructive/verify_nonabelian_chiral.py --write
/private/tmp/ueot-lapse-boundary-20261121-venv/bin/python -B physics/unification/nonabelian_chiral_constructive/verify_nonabelian_chiral.py --check
```
