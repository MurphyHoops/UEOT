# UEOT Physics Unification Gates & Multi-Sector Convergence Suite

Physical unification remains **OPEN** (`physical_unification = "OPEN"`). Following the Chapter 71 (`v31.15` / Book `3.12`) merge into `main` (`cc5670d5f2ac96f88270c0f38ae6fb6f77e26093`), this directory establishes the cross-sector mathematical derivations, 40-digit outward-interval certificates, empirical holdouts, and pure-kernel Lean 4 bridges required to converge with the active `conformal_action` field-and-gravity cohort (PR #468).

## Multi-Workstream Rendezvous Architecture (Zero Path Overlap with PR #468)

While PR #468 (`codex/physics-source-response-20261119`) advances inside `physics/qm/null_source/timelike/finite_stress/lapse_boundary/` on autonomous global-controller wavepacket preparation, domains, and record stress, this suite closes the **five orthogonal unification gates (`HG-1` through `HG-5`)** in disjoint directories so both branches merge cleanly without touching any frozen predecessor file:

| Subdirectory | Result IDs | Gate Closed | Paired Lean 4 Module |
| :--- | :--- | :--- | :--- |
| [quantum_selection/](quantum_selection/README.md) | `C-QSEL-05` | **HG-4**: Closes Hoffreumon–Woods real-reference (`τ`) and Barrios Hita phase-quotient loopholes via two-copy real-symmetric witness (`+1` vs `0`) and `UEOT.V3.Compression.QuotientDescent` isomorphism | `RealQuotientSelection.lean` |
| [local_control_ctp/](local_control_ctp/README.md) | `P-UNIF-CTRL-01`, `P-UNIF-CHI-02`, `P-UNIF-CTP-03` | **HG-1 / HG-2 / HG-3**: Same-cutoff $H$ vs $H_{K_0}$ Split-core UV dressing rate (`O(K_0^{-1/2})` norm, `O(K_0^{-1})` probe expectation), truncated $K_0=1$ `Z5` collision benchmark (`0.002969`, full-field $M=1$ explicitly `OPEN`), 4D local `χ φ ψ` covariant stress conservation & stability (`m_χ² ≥ λ_c² / (2 g_4)`), and smooth inhomogeneous-lapse `Weyl²` CTP cancellation | `ConformalControlGravityGates.lean` |
| [matter_gauge_flavor/](matter_gauge_flavor/README.md) | `P-MATTER-02`, `P-FLAVOR-03` | **HG-5**: Complete `ℕ³` classification of `(3,3,1)` vs `(5,5,2)`, IR `SU(2)_L` uniqueness of `(3,3,1)`, efficiency-free `R_τ` (`>130σ`) exclusion of unbroken 5-color light quarks, and rank-one `(B_d, B_s) → ε_K` phase lock | `GaugeFlavorSelection.lean` |
| [cosmology_perturbation/](cosmology_perturbation/README.md) | `P-COSMO-02` | **HG-3 / HG-5**: Breaks exact `H(z)` background degeneracy between `ΛCDM` and non-phantom canonical scalar (`-1 < w_φ < 0`) via `>44%` primordial-matched `fσ_8(z)` separation and galaxy-bias-cancelling `E_G(z)` | — (ODE/interval benchmark) |
| [rg_eft_bridge/](rg_eft_bridge/README.md) | `C-RG-01`, `P-EFT-02` | **CORE_CONTRACT §5 / PREMISES Row 9**: Bridges `Object-RG` (`QuotientDescent`) vs Dynkin Markov lumpability (with exact `1/16` Mori–Zwanzig memory witness) and Wilsonian Schur-complement EFT matching with `<10^-35` scheme spread across `MS-bar` and `MOM` | `RGBridgeAndEFTMatching.lean` |
| [thermodynamics_memory/](thermodynamics_memory/README.md) | `P-THERMO-01`, `P-OMEGA-02` | **PREMISES Row 7**: Reeb–Wolf entropy production decomposition, exact `3/80` persistent-bath cycle-2 excess, strict doubly-stochastic Rényi-2 purity decrease (`Ω`-loop no-go without external work), and `N_bath` vs `T` limit-exchange gap | `ThermodynamicsAndLandauerBounds.lean` |
| [spacetime_gravity_bounds/](spacetime_gravity_bounds/README.md) | `B-SIG-01`, `P-EP-02`, `P-GRAV-03`, `P-HORIZON-04` | **G02 / G04 / G05–06 / G14**: Fisher-Rao PSD obstruction vs `(3,4,5)` null-cone Minkowski conformal uniqueness, soft spin-2 universal coupling + reducible-kinematics counterexample, finite-ray Cassini vs Eöt-Wash `f(R)` bounds (`m ≥ 5.112 meV`), and post-Page correlation deficit | `SpacetimeEquivalenceAndGravityBounds.lean` |
| [topological_index_spectrum/](topological_index_spectrum/README.md) | `P-TOPO-01` | **PREMISES Row 12**: `U(1)` torus cocycle flux quantization `Φ ∈ ℤ`, McKean–Singer graded supertrace invariance, Neuberger Overlap Dirac index `|n_+ - n_-| = |m|` (`m ∈ {-2..2}`), and `m=0` spin-structure spectral gap | `TopologicalCarrierAndIndex.lean` |
| [flavor_spam_identifiability/](flavor_spam_identifiability/README.md) | `P-FLAVOR-04`, `P-SPAM-05` | **PREMISES Rows 2 & 11**: Two-channel `(B_d, B_s)` unconstrained realizability vs three-channel `(K, B_s, B_d)` rephasing-invariant `Im(J) = 0, Re(J) ≥ 0` lock, plus 3-outcome `{0,1,leak}` affine SPAM/leakage calibration | `FlavorCyclicAndSPAMContract.lean` |

Companion formalization and validation layers:
- Pure-kernel Lean 4 package: [../../formalization/ueot-physics-unification/README.md](../../formalization/ueot-physics-unification/README.md)
- Chapter 71 observed `main` integration receipt: [../qm/kernel/evidence/v31.15/integration-verification.json](../qm/kernel/evidence/v31.15/integration-verification.json)
- Hardware certification contract & validation ledger: [../../validation/physics_unification/HARDWARE_CERTIFICATION_CONTRACT.md](../../validation/physics_unification/HARDWARE_CERTIFICATION_CONTRACT.md)

## Deterministic Reproduction

```sh
python -B physics/unification/run_verification.py --check
```
