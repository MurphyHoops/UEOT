# `nonabelian_lattice_massgap_h2` — 4D Lattice Gauge Mass Gap, Chiral Integrability (`H2a–H2c`) & Round 04–07 `H2d` / `IR-X` Frontier Verification

Companion 40-digit outward-interval (`mpmath.iv`, `mp.dps >= 50`, `iv.dps = 40`), exact integer/rational (`fractions.Fraction`), and exact symbolic (`sympy`) verification suite for `UEOTPhysicsUnification.NonAbelianLatticeMassGapAndChiralIntegrabilityH2` (`formalization/ueot-physics-unification/UEOTPhysicsUnification/NonAbelianLatticeMassGapAndChiralIntegrabilityH2.lean`).

Lean 4 kernel audit (`scripts/ExhaustiveAxiomAudit.lean`):
- **39 modules, 3,864 constants, 1,800 theorems, 1,766 definitions, 0 `axiomDecls`, 0 `sorryAx`, 0 `opaque`, 0 `unsafe`, 0 `Lean.ofReduceBool` (`native_decide`)**.

## Verified Layers & Round Coverage

1. **Wave 11 `H2a–H2c` Closure (`P-H2A-TRANSFER-01`, `P-H2B-DOBRUSHIN-02`, `P-H2C-CHIRAL-UV-03`, `C-H2-OPER-04`)**:
   - Positive-transfer $Q_8$ / Wilson plaquette reflection positivity, strong-coupling area law ($\sigma_{\mathrm{SC}} > 0$), and $O(a^2)$ Symanzik coefficients.
   - Uniform finite-volume Dobrushin cluster mass gap ($\alpha < 1$ vs $\alpha = 1$ boundary non-uniqueness) and weak-coupling collapse ($\beta = 20$).
   - Lüscher Berry loop holonomy, $16\times 16$ Overlap $H_W^2$ spectral-gap stability, 15-Weyl `(3,3,1)` + Witten `ℤ_2` anomaly cancellation, `AH01` Planck screening, and `DEAD-20261124-01` ($2 c_{\mathrm{adm}} b_0 < 4$).

2. **Rounds 04–06 `H2d` Constructive Reduction (`h2d_round04_constructive_bridges`, `h2d_round05_deepening_bridges`, `h2d_round06_convergence_bridges`)**:
   - `33,477` Round 04 checks + `153` Round 05 checks + `121` Round 06 checks (with cross-round SHA-256 parity `9b75a43ea352d9c81b36714496f9570e2cd628e5f461e9703d631ce9a8220697`), isolating `H2dMinimalIrreducibleCore` = `{UV-X, IR-X, CHIRAL-X}`, Poincaré-duality Euler vanishing (`χ(SU(2)) = χ(T^4) = 0`), Neuberger `0/0` vs `Z_FMR > 0`, and non-vacuous 5-track unification (`Round06H2dConvergence`).

3. **Round 07 `IR-X` First-Principles Frontier (`Round07IRXFirstPrinciples`, `compute_h2d_round07_irx_frontier()`, `89` 40-digit interval checks)**:
   - **Track 1 & `W3.1-2` (`T1.1`, `W3.1-2`)**: Quotient O'Neill–Bakry–Émery non-negativity (`-1 + 1 + ‖T‖²` FP cancellation, ambient cap `1/12` vs MC ceiling `0.38`, Polchinski 4D Riccati `> 3.035e28` at `a=1e-16`), exact rational exponent `α_st = 3/4` vs `1/2`, and 4D Bianchi cube minimum action `S_min = 2 ε_adm`.
   - **Track 2 (`T2-2`, `T2-3`)**: Cleared-denominator topological-susceptibility gradient-flow bound (`π² c⁴ √χ_t L² ≤ g_GF² · 8 N √κ_4`, Skellam `L ∈ {2,4,8,16}` sweep) and UEOT KL/Hellinger variational spectral-gap structure (`tvDist² ≤ 2 H² ≤ KL`).
   - **Routes A–C (`LA.1–4`, `B-1`, `C-1`, `C-2`, `C4(a)`)**: 1-link `16/(27π)` (`≈ 0.1886`) vs `π/16` (`≈ 0.1963`), 18-neighbor TV threshold `[0.131030, 0.131032]`, exact 2D `SU(2)`/`U(1)` Schwinger–Dyson identity (`< 2.1e-39` residual), twist TV `sinh(ΔF)` error floor (`> 0.47999` at `ΔF = 0.040`), Litmus 6 gap `8 ln 2 - 6π²/11 ∈ [0.16175686, 0.16175687] > 0`, and `C4(a)` `[Φ_diag, ω_3] = 0`.
   - **Wave 3 `W3-1`, `W3-2`, `W3-3` & 7-Way Counterexample Separation**:
     - `W3.1-1`: Mod-2 Plücker `Pf(n) ≡ 0` for all `SU(2)` twist-eaters (vs `tw_inst` `Pf = 1`), zero stabilizer for `tw1, tw3, tw4`, and conditional twisted RG corridor `[0.73, 18..37]` (`K_2L ∈ [65.23, 138.58]`, `77.48%–89.40%` reduction vs `[0.38, 160]` `K_2L = 615.34`).
     - `W3.2-1` / `W3.2-2` / `W3.2-3`: Diagonal RP Cauchy–Schwarz chain (`w_bent6 ≥ |w_{1×2}| ≥ w_{1×1}² ≥ 0`), exact discrete Stieltjes factor `(t-1)^{t-1}/t^t` (`1/4, 4/27, 27/256, 256/3125, 3125/46656`) eliminating `O-B1`, 40-digit complex-`β` KP strip (`|β_KP(0)| = 0.015810` for 4D `SU(2)`), `O-W3.2-1` Beta-Stieltjes (`α = 4`, Hankel PSD `> 0`), and **`C4(b)''` gradient scalar** (`RP + ℤ_2^{(1)} + KP σ ≥ 4.047558 + finite χ_P (∑ |x|^{-8} ≤ 10.272047) + noBulkTransition`, yet `m_{0++} = 0`).
     - `W3.3-1` / `O-T2-4` / `W3.3-O1`: Fractional ground-state Doob `HasDerivAt` Lyapunov identity (`L V_α / V_α = -α(V_pot - E_0) - α(1-α)(g²/8)(W')²`), 1-plaquette antipodal `κ_BE(-I) ∈ [-51.89101572, -51.89101571]` at `g² = 1/20`, and stiffness `I_1(d) = 1.9162 / 2.3876 / 2.7776` (`d_space = 2, 3, 4`).

## Honest Open Status

`H2dMinimalIrreducibleCore` (`UV-X`, `IR-X`, `CHIRAL-X`), `h2d_status`, `irx_status`, `physical_unification` remain strictly **`"OPEN"`**, and `device_certified` remains **`false`**.

## Deterministic Check

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python3 -B physics/unification/nonabelian_lattice_massgap_h2/verify_nonabelian_lattice_h2.py --check
```
