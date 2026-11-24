# UEOT Verified Lemmas & Certificates (`VERIFIED_LEMMAS.md`)

> **准入铁律**：只有通过 `python3 -B research/lab_wiki/gatekeeper.py --mode lean`（涉及数值证书时需 `--mode full`）的引理与证书，才允许写入本表。  
> `gatekeeper.py` 会自动校验本表中引用的文件路径必须真实存在，且严禁出现 `TODO`、`TBD`、`PENDING`、`sorry`、`admit` 等未完成标记。

---

## 已验证清单（对齐 `origin/main` @ `e824ef0b`）

| Lemma-ID | Spec-ID | Lean Symbol / Verification Suite | File | Gate Mode | Gate Status | Commit |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `LEMMA-20261124-01` | `WAVE9-H1D` | `h1d_frontier_sharp_decomposition_and_honest_open_core` (`H1d1 ∧ H1d2 ∧ H1d3` closed; `H1d4` isolated `OPEN`) | `formalization/ueot-physics-unification/UEOTPhysicsUnification/Nonperturbative4DQuantumGravityH1d.lean` | `full` | `PASS` | `8b72be9c` |
| `LEMMA-20261124-02` | `WAVE9-H1D` | `nonperturbative_4d_qg_h1d` 40-digit `mpmath.iv` + `sympy` certificate (`P-H1D-FRG-01`..`C-H1D-CORE-04`) | `physics/unification/nonperturbative_4d_qg_h1d/certificate.json` | `full` | `PASS` | `8b72be9c` |
| `LEMMA-20261124-03` | `PAPER4-V2` | Paper 4 v2.0 correlated-bath response metrology standalone verification | `publications/papers/correlated-bath-response-metrology/VALIDATION.json` | `full` | `PASS` | `397dd224` |
| `LEMMA-20261124-04` | `SPEC-20261124-01` | `h1d4_final_sharp_reduction_and_operational_vs_mathematical_split` (`H1d4a..c` closed, `H1` operationally closed; `H1d4d` `OPEN`) | `formalization/ueot-physics-unification/UEOTPhysicsUnification/Nonperturbative4DMeasureLimitH1d4.lean` | `full` | `PASS` | `1ff5170f` |
| `LEMMA-20261124-05` | `SPEC-20261124-01` | `nonperturbative_4d_measure_h1d4` 40-digit `mpmath.iv` + `sympy` certificate (`P-H1D4-BANACH-01`..`C-H1D4-FINAL-04`) | `physics/unification/nonperturbative_4d_measure_h1d4/certificate.json` | `full` | `PASS` | `1ff5170f` |
| `LEMMA-20261124-06` | `PAPER4-V3` | Paper 4 v3.0 PRA submission outward bounds, dual-engine LaTeX & standalone verification | `publications/papers/correlated-bath-response-metrology/submissions/pra/VALIDATION_PRA.json` | `full` | `PASS` | `e824ef0b` |
| `LEMMA-20261124-07` | `SPEC-20261124-03` | `wilson_plaquette_transfer_positivity_and_strong_coupling_area_law`, `dobrushin_lattice_cluster_mass_gap`, `luscher_berry_loop_holonomy_and_overlap_gap_stability`, `ah01_lattice_uv_screening_and_h2_decomposition` (`H2a..c` closed; `H2d` `OPEN`) | `formalization/ueot-physics-unification/UEOTPhysicsUnification/NonAbelianLatticeMassGapAndChiralIntegrabilityH2.lean` | `full` | `PASS` | `60b347dc` |
| `LEMMA-20261124-08` | `SPEC-20261124-03` | `nonabelian_lattice_massgap_h2` 40-digit `mpmath.iv` + `sympy` certificate (`P-H2A-TRANSFER-01`..`C-H2-OPER-04`) | `physics/unification/nonabelian_lattice_massgap_h2/certificate.json` | `full` | `PASS` | `60b347dc` |
| `LEMMA-20261124-09` | `SPEC-20261124-04` | `two_loop_threshold_collinearity_and_proton_decay_bound`, `jarlskog_invariant_rephasing_and_ceiling`, `two_sided_cosmological_viability_and_operational_ilambda_indistinguishability`, `h3_frontier_sharp_decomposition_and_open_selection` (`H3a..c` closed; `H3d` `OPEN`) | `formalization/ueot-physics-unification/UEOTPhysicsUnification/DimensionlessCouplingsFlavorAndVacuumWindowH3.lean` | `full` | `PASS` | `fe0ba9ec` |
| `LEMMA-20261124-10` | `SPEC-20261124-04` | `dimensionless_couplings_viability_h3` 40-digit `mpmath.iv` + `sympy` certificate (`P-H3A-TWOLOOP-GUT-01`..`C-H3-WINDOW-04`) | `physics/unification/dimensionless_couplings_viability_h3/certificate.json` | `full` | `PASS` | `fe0ba9ec` |
| `LEMMA-20261124-11` | `SPEC-20261124-05` | `chsh_lhv_bound_two_and_tsirelson_two_sqrt_two`, `nonselective_dropout_bias_and_multicell_tv_holdout_soundness`, `calibration_polytope_power_margin_and_paired_baseline_gate`, `h4_frontier_sharp_decomposition_and_honest_device_status` (`H4a..c` closed; `H4d` `OPEN`, `deviceCertified = false`) | `formalization/ueot-physics-unification/UEOTPhysicsUnification/BellCHSHAndBlindHoldoutContractH4.lean` | `full` | `PASS` | `a95d3c69` |
| `LEMMA-20261124-12` | `SPEC-20261124-05` | `bell_chsh_blind_holdout_h4` 40-digit `mpmath.iv` + `sympy` certificate (`P-H4A-CHSH-TSIRELSON-01`..`C-H4-CONTRACT-04`) | `physics/unification/bell_chsh_blind_holdout_h4/certificate.json` | `full` | `PASS` | `a95d3c69` |
| `LEMMA-20261124-13` | `SPEC-20261124-06` | `post_wave10_unified_cross_sector_closure`, `exists_admissible_post_wave10_unified_system`, `post_wave10_frontier_status_and_honest_open_governance` (`38` modules, `854` theorems, 4-way independence, `physicalUnificationStatus = .OPEN`) | `formalization/ueot-physics-unification/UEOTPhysicsUnification/CrossSectorPostWave10UnificationSynthesis.lean` | `full` | `PASS` | `physics/wave11-cross-sector-synthesis` |
| `LEMMA-20261124-14` | `SPEC-20261124-06` | `cross_sector_post_wave10_synthesis` 40-digit `mpmath.iv` + `sympy` certificate (`C-UNIFIED-SYNTH-11`) | `physics/unification/cross_sector_post_wave10_synthesis/certificate.json` | `full` | `PASS` | `physics/wave11-cross-sector-synthesis` |

---

## 追加说明

- `Lemma-ID` 格式：`LEMMA-YYYYMMDD-NN`。
- `File` 列必须使用相对于仓库根目录的路径，且指向真实存在的 `.lean` 或 `.py` / `.json` 文件。
- 每次新增正式证明后，请同时在对应组会纪要中附上 `gatekeeper.py --write-receipt` 的执行摘要。
