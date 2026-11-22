# UEOT Physics Unification Gates & Multi-Sector Convergence Suite

Physical unification remains **OPEN** (`physical_unification = "OPEN"`). Following the Chapter 71 (`v31.15` / Book `3.12`) merge into `main` (`cc5670d5f2ac96f88270c0f38ae6fb6f77e26093`), this directory establishes the cross-sector mathematical derivations, 40-digit outward-interval certificates, empirical holdouts, and pure-kernel Lean 4 bridges required to converge with the active `conformal_action` field-and-gravity cohort (PR #468).

## Multi-Workstream Rendezvous Architecture (Zero Path Overlap with PR #468)

While PR #468 (`codex/physics-source-response-20261119`) advances inside `physics/qm/null_source/timelike/finite_stress/lapse_boundary/` on autonomous global-controller wavepacket preparation, domains, and record stress, this suite closes the **five orthogonal unification gates (`HG-1` through `HG-5`)** in disjoint directories so both branches merge cleanly without touching any frozen predecessor file:

| Subdirectory | Result IDs | Gate Closed | Paired Lean 4 Module |
| :--- | :--- | :--- | :--- |
| [quantum_selection/](quantum_selection/README.md) | `C-QSEL-05` | **HG-4**: Closes Hoffreumon–Woods real-reference (`τ`) and Barrios Hita phase-quotient loopholes via two-copy real-symmetric witness (`+1` vs `0`) and `UEOT.V3.Compression.QuotientDescent` isomorphism | `RealQuotientSelection.lean` |
| [local_control_ctp/](local_control_ctp/README.md) | `P-UNIF-CTRL-01`, `P-UNIF-CHI-02`, `P-UNIF-CTP-03` | **HG-1 / HG-2 / HG-3**: Split-core UV dressing rate (`O(K_0^{-1/2})` norm, `O(K_0^{-1})` probe expectation), `Z5` outside collision contrast (`0.002969 > 0.000193`), 4D local `χ φ ψ` covariant stress conservation & stability (`m_χ² ≥ λ_c² / (2 g_4)`), and smooth inhomogeneous-lapse `Weyl²` CTP cancellation | `ConformalControlGravityGates.lean` |
| [matter_gauge_flavor/](matter_gauge_flavor/README.md) | `P-MATTER-02`, `P-FLAVOR-03` | **HG-5**: Complete `ℕ³` classification of `(3,3,1)` vs `(5,5,2)`, IR `SU(2)_L` uniqueness of `(3,3,1)`, efficiency-free `R_τ` (`>130σ`) exclusion of unbroken 5-color light quarks, and rank-one `(B_d, B_s) → ε_K` phase lock | `GaugeFlavorSelection.lean` |
| [cosmology_perturbation/](cosmology_perturbation/README.md) | `P-COSMO-02` | **HG-3 / HG-5**: Breaks exact `H(z)` background degeneracy between `ΛCDM` and non-phantom canonical scalar (`-1 < w_φ < 0`) via `>44%` primordial-matched `fσ_8(z)` separation and galaxy-bias-cancelling `E_G(z)` | — (ODE/interval benchmark) |

Companion formalization and validation layers:
- Pure-kernel Lean 4 package: [../../formalization/ueot-physics-unification/README.md](../../formalization/ueot-physics-unification/README.md)
- Chapter 71 observed `main` integration receipt: [../qm/kernel/evidence/v31.15/integration-verification.json](../qm/kernel/evidence/v31.15/integration-verification.json)
- Hardware certification contract & validation ledger: [../../validation/physics_unification/HARDWARE_CERTIFICATION_CONTRACT.md](../../validation/physics_unification/HARDWARE_CERTIFICATION_CONTRACT.md)

## Deterministic Reproduction

```sh
python -B physics/unification/run_verification.py --check
```
