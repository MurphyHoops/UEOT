# Spacetime `D = 4` Selection, Inflation, Dark Sector, Quantum-Gravity EFT & `S^3` Kernel (`G01`, `G03`, `G11`–`G13`, `G15`, `P-GRAV-FM-05`)

```text
Result ID: B-CAUS-01, S-DIM-03, P-INFL-13, P-DM-11, P-DE-12, P-QG-15, P-GRAV-FM-05
Core dependencies: Directed preorder monotone antisymmetry bridge
Bridge dependencies: Spin-2 polarization counting + Ehrenfest radial stability; Fischer-Marsden S^3 harmonic decomposition
Sector inputs: R + alpha R^2 slow-roll inflation; s-wave Boltzmann freeze-out; 1-loop graviton EFT
Standard physical inputs: Planck 2018 + BK18 CMB bounds (n_s, r, Omega_c h^2, rho_Lambda)
Effective assumptions: Slow-roll e-fold window N_e in [50, 60]; long-distance r >> l_Planck EFT regime
Formal status: Pure-kernel Lean 4 theorems (SpacetimeDimensionAndEarlyLateCosmology.lean, 0 sorryAx) + 40-digit outward-interval certificate
Observable/benchmark: Unique D=4 survivor; Starobinsky r in [0.00333, 0.00480] < 0.036 (chaotic m^2 phi^2 excluded); scalaron m ~ 3.1e13 GeV
Falsification condition: Detection of r > 0.01 falsifies pure R + alpha R^2 inflation; frozen single-cap S^3 source fails ell = 1 Fischer-Marsden range condition
```

Closes `PREMISES_AND_RESPONSIBILITIES.md` Responsibilities `G01`, `G03`, `G11`, `G12`, `G13`, `G15` and supplies the Lean 4 `S^3` Fischer–Marsden spectral bridge for `PR #468`'s `NEXT_GATE.md`.

Evidence: [verify_dim_cosmo_qg.py](verify_dim_cosmo_qg.py) · [result.json](result.json)
