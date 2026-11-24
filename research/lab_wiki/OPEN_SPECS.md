# UEOT Open Specifications Registry (`OPEN_SPECS.md`)

本表直接对齐 Wave 11 综合工作树（基线 `origin/main` `e824ef0b` 之上已合入 `M1..M3` 并完成 `M4` `SYNTH-11`：`38` Lean 模块 / `854` 定理、`38` Python 验证套件 + `345` 条 PR #468 回归、`81` 条 `VALIDATION_LEDGER.json` 记录）。  
新增条目请严格遵循下方模板；必须拆解为可机器判定的 Lean 签名或数值证伪阈值，严禁偷渡未声明物理前提。

---

## 活跃规格索引

| Spec-ID | Status | Sector / Wave | Target Artifact | Premise Class | Owner / Round |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `SPEC-20261124-01` | `CLOSED` | Wave 10 / `H1d4` (`H1` operationally closed; `H1d4d` `OPEN`, `H1` NOT sliced further) | `formalization/ueot-physics-unification/UEOTPhysicsUnification/Nonperturbative4DMeasureLimitH1d4.lean` | `C/P/X` | `PR #497` / Round 0 |
| `SPEC-20261124-02` | `OPEN` | Empirical / Device Certification (`device_certified: false`) | `publications/papers/correlated-bath-response-metrology/VALIDATION.json` | `E/O` | Unassigned |
| `SPEC-20261124-03` | `CLOSED` | Wave 11 / `H2` (Lattice Mass Gap & Chiral Integrability; `H2d` `OPEN`) | `formalization/ueot-physics-unification/UEOTPhysicsUnification/NonAbelianLatticeMassGapAndChiralIntegrabilityH2.lean` | `C/B/P/X` | `M1` (`60b347dc`) / Round 2 |
| `SPEC-20261124-04` | `CLOSED` | Wave 11 / `H3` (Dimensionless Couplings, Flavor & Vacuum Window; `H3d` `OPEN`) | `formalization/ueot-physics-unification/UEOTPhysicsUnification/DimensionlessCouplingsFlavorAndVacuumWindowH3.lean` | `C/B/P/E/O` | `M2` (`fe0ba9ec`) / Round 2 |
| `SPEC-20261124-05` | `CLOSED` | Wave 11 / `H4` (Bell-CHSH, Blind Holdout & Portfolio Contracts; `H4d` `OPEN`) | `formalization/ueot-physics-unification/UEOTPhysicsUnification/BellCHSHAndBlindHoldoutContractH4.lean` | `C/B/E/O` | `M3` (`a95d3c69`) / Round 2 |
| `SPEC-20261124-06` | `CLOSED` | Wave 11 / `SYNTH-11` (Cross-Sector Synthesis, Ledger & Monograph Sync; `OPEN` governance) | `formalization/ueot-physics-unification/UEOTPhysicsUnification/CrossSectorPostWave10UnificationSynthesis.lean` | `C/B/P/E/O/X` | `M4` (`wt-wave11-synth`) / Round 2 |

---

## 详细规格卡片

### `SPEC-20261124-01` — Wave 10 `H1d4`: 非截断 4D 连续统测度极限与 `H1` 操作化闭合（已收口）
- **Status**: `CLOSED`
- **Target**:
  - 已在 PR #497（`1ff5170f` / `7e7b5bc7`）完成 `Nonperturbative4DMeasureLimitH1d4.lean` 与 `physics/unification/nonperturbative_4d_measure_h1d4/certificate.json`（`P-H1D4-BANACH-01`, `P-H1D4-OSRECON-02`, `P-H1D4-OPER-03`, `C-H1D4-FINAL-04`）。
  - 证明 `H1d4a ∧ H1d4b ∧ H1d4c` 闭合且 `H1` 在 `AH01` + `ClosedTests` 下**操作化闭合**；同时诚实保留数学核心 `H1d4d_UnconditionalExact4DNonPolynomialDecouplingProof` 为 `OPEN`（`physical_unification: OPEN`）。**Wave 11 明确决议：不再对 `H1` 做任何进一步切片。**
- **Allowed Premises (`C/B/S/P/E/O/X`)**: `C/P/X`，纯内核公理 `{propext, Classical.choice, Quot.sound}`。
- **Acceptance Gate**: 已通过 `lake build`、`ExhaustiveAxiomAudit.lean` 与 `run_verification.py --check`（归档于 `LEMMA-20261124-04` 与 `LEMMA-20261124-05`）。
- **Falsification Criterion**: 若发现截断极限出现多不动点或破坏 OS 反射正性/Ursell 非平凡性，则记入 [DEAD_ENDS.md](DEAD_ENDS.md)；主线已将反例 `strong_mixing_truncation_spurious_fp_counterexample` 显式分离出闭合假设。

### `SPEC-20261124-02` — 真实器件有序原始记录与 `device_certified` 升级边界
- **Status**: `OPEN`
- **Target**: 补齐匹配第 70–72 章 / Paper 4 v3.0 与 `validation/physics_unification/HARDWARE_CERTIFICATION_CONTRACT.md` 的真实器件有序逐 shot 原始记录（`shot_id`, `timestamp_ns`, `block_id`, `setting_code`, `initial_sign`, `reset_telemetry`, `leakage_flag`, `outcome_code`）及 SPAM/漂移误差证据，评估能否将 `"device_certified": false` 升级。
- **Allowed Premises (`C/B/S/P/E/O/X`)**: `E/O`（必须具备可复核来源、原始数据校验和与预注册留出合同）。
- **Acceptance Gate**: 通过 `validation/README.md`、`HARDWARE_CERTIFICATION_CONTRACT.md` 证据合同及 Paper 4 独立校验脚本。
- **Falsification Criterion**: 只要缺少有序逐 shot 原始记录或器件系统误差包络宽于备择信号分离度，就必须保持 `NOT_CERTIFIED` / `device_certified: false`（禁止伪造任何硬件数据）。

### `SPEC-20261124-03` — Wave 11 `H2`: 非阿贝尔晶格质量间隙、Lüscher 几何可积性与手征 UV 屏蔽
- **Status**: `CLOSED`（归档于 `LEMMA-20261124-07`, `LEMMA-20261124-08`；Clay 4D 连续统 `H2d` 诚实保留 `OPEN`）
- **Target**:
  - 在 `wt-wave11-h2`（分支 `physics/wave11-h2-lattice-chiral-gap`）新建纯内核模块 `NonAbelianLatticeMassGapAndChiralIntegrabilityH2.lean` 与 40 位外区间验证套件 `physics/unification/nonabelian_lattice_massgap_h2/verify_nonabelian_lattice_h2.py` + `certificate.json`（Result IDs: `P-H2A-TRANSFER-01`, `P-H2B-DOBRUSHIN-02`, `P-H2C-CHIRAL-UV-03`, `C-H2-OPER-04`）：
    - `H2a`：正转移 Wilson 格子核反射正性、强耦合面积律弦张力 `σ > 0` 衰减 `exp(-σ A)` 与 Symanzik `O(a^2)` 收敛检查；
    - `H2b`：基于 `UEOT.V3.FiniteDobrushin` 的唯一不变 Gibbs 测度与指数关联质量间隙 `m_gap > 0`，结合闭环 Lüscher Berry 上边缘可积性及 Neuberger `H_W^2` 谱隙扰动稳定性；
    - `H2c`：无反常 `(3,3,1)` 手征规范轨道 `QuotientDescent`/`ClosedTests`、`AH01` 操作化 IR/EFT 晶格间距屏蔽，以及尖锐 `H2SubHypothesis` 分解定理（`H2a..H2c` 闭合，`H2d` Clay 4D 连续统非微扰测度与无条件质量间隙诚实保留 `OPEN`）。
  - 导出关键定理：`wilson_plaquette_transfer_positivity_and_strong_coupling_area_law`、`dobrushin_lattice_cluster_mass_gap`、`luscher_berry_loop_holonomy_and_overlap_gap_stability`、`ah01_lattice_uv_screening_and_h2_decomposition`。
- **Allowed Premises (`C/B/S/P/E/O/X`)**:
  - `C`：冻结的 `UEOT.V3.FiniteDobrushin`、`UEOT.V3.Compression.QuotientDescent`；
  - `B/P/X`：已有 `NonAbelianChiralConstructiveBoundary`、`OperationalHorizonMinimumScale` 及显式参数化的有限体积格子转移核/耦合常数条件；
  - 严禁新增未声明 `S` 公设，严禁回退至已被 `DEAD-20261124-01` 证伪的 4D 单格子 Peierls 熵论证。
- **Acceptance Gate**:
  1. `python3 -B research/lab_wiki/gatekeeper.py --mode lean` 返回 `0`（零警告，公理 `⊆ {propext, Classical.choice, Quot.sound}`，`0 sorryAx`/`Lean.ofReduceBool`/自定义 `axiom`）。
  2. `verify_nonabelian_lattice_h2.py --check` 使用纯 `mpmath.iv` (`mp.dps=50, iv.dps=40`)、`sympy`、`fractions.Fraction`（零 `numpy`），`<5s` 确定性返回 `PASS` 且保持 `"physical_unification": "OPEN"`、`"device_certified": false`。
  3. Red-Team Referee 审查给出明确 `PASS` 裁决。
- **Falsification Criterion**: 若在正耦合弱/强区交界出现 Dobrushin 收缩破缺却未显式限定耦合域，或 `H2SubHypothesis` 将 `H2d`（Clay 4D 连续统极限）隐含包装为已无条件导出，或数值证书在声明域边界失稳/依赖单格子 Peierls 熵 `2*c_adm*b0 >= 4` 假定，则判定 `BLOCKED` / `FALSIFIED` 并记入 [DEAD_ENDS.md](DEAD_ENDS.md)。

### `SPEC-20261124-04` — Wave 11 `H3`: 无量纲耦合统一窗口、3 代味循环边界与双侧宇宙学可行性窗
- **Status**: `CLOSED`（归档于 `LEMMA-20261124-09`, `LEMMA-20261124-10`；先验精确常数推导 `H3d` 诚实保留 `OPEN`）
- **Target**:
  - 在 `wt-wave11-h3`（分支 `physics/wave11-h3-couplings-flavor-viability`）新建纯内核模块 `DimensionlessCouplingsFlavorAndVacuumWindowH3.lean` 与 40 位外区间验证套件 `physics/unification/dimensionless_couplings_viability_h3/verify_couplings_viability_h3.py` + `certificate.json`（Result IDs: `P-H3A-TWOLOOP-GUT-01`, `P-H3B-JARLSKOG-02`, `P-H3C-VIABILITY-03`, `C-H3-WINDOW-04`）：
    - `H3a`：2-loop `(3,3,1)` 中间阈值 `(M_I, M_GUT)` 修复多胞体 `Δ_123 = 0` 与 Super-K 维度-6 质子衰变下界 `M_GUT >= M_GUT,min` 及 Higgs 四次耦合稳定性窗口 `0 < λ_H(μ) < 4π`（避开 `DEAD-20261124-02` 1-loop 沙漠 GUT 死路）；
    - `H3b`：3×3 CKM 幺正三角闭合、重相位不变性及代数上界 `|J| <= 1/(6 sqrt(3))`，以及 3 代 Type-I seesaw 迹/行列式界；
    - `H3c`：正向 `ViabilityKernel`（`I_Λ < I_max`）与负向 `Λ` AdS 坍缩下界 + `InformationPacking`/`AH01` 观测者复杂度下界 `I_min` 构成的**双侧可行性窗口**，配合 `BinaryTesting` 有限视界 `I_Λ` 操作不可分辨性及尖锐 `H3SubHypothesis` 分解（`H3a..H3c` 闭合，`H3d` 先验精确值 `I_Λ^*, α_i, y_f` 推导诚实保留 `OPEN`）。
  - 导出关键定理：`two_loop_threshold_collinearity_and_proton_decay_bound`、`jarlskog_invariant_rephasing_and_ceiling`、`two_sided_cosmological_viability_and_operational_ilambda_indistinguishability`、`h3_frontier_sharp_decomposition_and_open_selection`。
- **Allowed Premises (`C/B/S/P/E/O/X`)**:
  - `C`：冻结的 `UEOT.V3.InformationPacking`、`UEOT.V3.BinaryTesting`；
  - `B/P/E/O`：已有 `UnimodularVacuumConstantSelection`、`ElectroweakCustodialAndSeesaw`、`RGBridgeAndEFTMatching`、`CoreUnitGaugeAndDimensionlessConstants` 及显式标注为 `E/O` 的实验/观测输入（低能规范耦合、质子寿命下界、宇宙学密度窗口）；
  - 严禁将条件性参数可行性窗包装成无条件先验常数推导。
- **Acceptance Gate**:
  1. `python3 -B research/lab_wiki/gatekeeper.py --mode lean` 返回 `0`（零警告，纯内核公理）。
  2. `verify_couplings_viability_h3.py --check` 使用纯 `mpmath.iv` (`mp.dps=50, iv.dps=40`)、`sympy`、`fractions.Fraction`（零 `numpy`、零 `iv.acos`），`<5s` 确定性返回 `PASS` 且保持 `"physical_unification": "OPEN"`、`"device_certified": false`。
  3. Red-Team Referee 审查给出明确 `PASS` 裁决。
- **Falsification Criterion**: 若宣称无中间阈值即可实现 1-loop `(3,3,1)` 精确规范耦合统一（撞车 `DEAD-20261124-02`），或双侧可行性窗 `I_min <= I_Λ <= I_max` 退化为空集/隐含先验确定 `I_Λ^*`，或未能显式标注 `E/O` 输入依赖类别，则判定 `BLOCKED` / `FALSIFIED` 并记入 [DEAD_ENDS.md](DEAD_ENDS.md)。

### `SPEC-20261124-05` — Wave 11 `H4`: Bell-CHSH 边界、非选择性盲留出合同与实验组合门禁
- **Status**: `CLOSED`（归档于 `LEMMA-20261124-11`, `LEMMA-20261124-12`；真实硬件执行 `H4d` 诚实保留 `OPEN` 且 `device_certified = false`）
- **Target**:
  - 在 `wt-wave11-h4`（分支 `physics/wave11-h4-chsh-holdout-portfolio`）新建纯内核模块 `BellCHSHAndBlindHoldoutContractH4.lean` 与 40 位外区间验证套件 `physics/unification/bell_chsh_blind_holdout_h4/verify_bell_holdout_h4.py` + `certificate.json`（Result IDs: `P-H4A-CHSH-TSIRELSON-01`, `P-H4B-HOLDOUT-TV-02`, `P-H4C-PORTFOLIO-03`, `C-H4-CONTRACT-04`）：
    - `H4a`：LHV 精确上界 `|S_CHSH| <= 2`、4×4 量子 Tsirelson 等式 `S_CHSH^2 = 4I - [A0,A1]⊗[B0,B1] <= 8`（`2 sqrt(2)`）、Werner 态可见度阈值 `V > 1/sqrt(2)` 与无公平采样假定的探测效率阈值 `η > 2(sqrt(2)-1)`；
    - `H4b`：非选择性丢包偏置界 `2 δ_drop`、`FiniteAlphabetConcentration` + `BinaryTesting` 同步多单元 CDF/TV 留出稳健性（对齐 `HARDWARE_CERTIFICATION_CONTRACT.md` §3）与 anytime-valid Ville/鞅可选停时界；
    - `H4c`：非空标定置信多胞体 `Θ_0.99` 对 `MODEL_SPECIFICATION_REJECTED` 判据、Casimir–Polder + `1/f` 相位漂移功率裕度 `> 2 σ_total`、成对标准基线判据、`P-COSMO-02` 与 3 通道味盲留出的 Lean 合同桥，以及尖锐 `H4SubHypothesis` 分解（`H4a..H4c` 闭合，`H4d` 真实硬件逐 shot 执行诚实保留 `OPEN` 且 `deviceCertified = false`）。
  - 导出关键定理：`chsh_lhv_bound_two_and_tsirelson_two_sqrt_two`、`nonselective_dropout_bias_and_multicell_tv_holdout_soundness`、`calibration_polytope_power_margin_and_paired_baseline_gate`、`h4_frontier_sharp_decomposition_and_honest_device_status`。
- **Allowed Premises (`C/B/S/P/E/O/X`)**:
  - `C`：冻结的 `UEOT.V3.BinaryTesting`、`UEOT.V3.FiniteAlphabetConcentration`、`UEOTQM.BinaryDiscrimination`；
  - `B/E/O`：已有 `MesoscopicDecoherenceGravimetry`、`FlavorCyclicAndSPAMContract`、`MathV42ClosedTestsAndMechanismBridge`；
  - 严禁任何公平采样后选择（`DEAD-20261124-03`）、空置信集空洞通过或伪造硬件 shot 数据。
- **Acceptance Gate**:
  1. `python3 -B research/lab_wiki/gatekeeper.py --mode lean` 返回 `0`（零警告，纯内核公理）。
  2. `verify_bell_holdout_h4.py --check` 使用纯 `mpmath.iv` (`mp.dps=50, iv.dps=40`)、`sympy`、`fractions.Fraction`（零 `numpy`、零 `iv.acos`），`<5s` 确定性返回 `PASS` 且保持 `"physical_unification": "OPEN"`、`"device_certified": false`。
  3. Red-Team Referee 审查给出明确 `PASS` 裁决。
- **Falsification Criterion**: 若定理在 `Θ_0.99 = ∅` 时仍允许通过（空洞假设）、依赖公平采样后选择绕过 `η > 2(sqrt(2)-1)` 或 `2 δ_drop` 界（撞车 `DEAD-20261124-03`）、或在任意路径出现 `device_certified = true` / 伪造硬件数据，则判定 `BLOCKED` / `FALSIFIED` 并记入 [DEAD_ENDS.md](DEAD_ENDS.md)。

### `SPEC-20261124-06` — Wave 11 `SYNTH-11`: 跨扇区后 Wave 10 统一综合、台账与双语专著同步
- **Status**: `CLOSED`（归档于 `LEMMA-20261124-13`, `LEMMA-20261124-14`）
- **Target**:
  - 在 `wt-wave11-synth`（分支 `physics/wave11-cross-sector-synthesis`）合入 `M1..M3` 后，新建 `CrossSectorPostWave10UnificationSynthesis.lean` 与 `physics/unification/cross_sector_post_wave10_synthesis/verify_cross_sector_post_wave10.py` + `certificate.json`（Result ID: `C-UNIFIED-SYNTH-11`），链接只读 Wave 10 `H1` 闭合（`Nonperturbative4DMeasureLimitH1d4`）、`UnifiedCausalChiralUnimodularSynthesis`、`ConformalControlGravityGates` 及 `H2`/`H3`/`H4` 三个新模块；证明四向独立性模型 `(H1d4d, H2d, H3d, H4d)`、`physicalUnificationStatus = .OPEN`、`deviceCertified = false`。
  - 同步更新 `UEOTPhysicsUnification.lean`（38 模块）、`ExhaustiveAxiomAudit.lean`（38 模块）、`physics/unification/run_verification.py`、`verification.json`、`physics/unification/README.md`、`validation/physics_unification/VALIDATION_LEDGER.json`、`physics/unification/WAVE8_11_MONOGRAPH_ADDENDUM.md`（双语 Wave 8–11 专著增补；已封版的 Edition 3.13 `physics/qm/book/UEOT_PHYSICS(.en).md` 与全部 `physics/qm/**` 依 `DEAD-20261124-08` 严格保持零字节冻结），以及 Round 2 `research/lab_wiki/` 晋升记录。
- **Allowed Premises (`C/B/S/P/E/O/X`)**: `C/B/P/E/O/X` 继承自 `SPEC-20261124-01..05` 与主分支既有审计模块；严禁修改冻结路径（`core/`, `formalization/ueot-core/`, `formalization/ueot-qm/`, `mathematics/`, `philosophy/`, `publications/`, `.github/workflows/**`, `physics/qm/**`）。
- **Acceptance Gate**:
  1. `python3 -B research/lab_wiki/gatekeeper.py --mode full --write-receipt` 返回 `0`（38 Lean 模块 + 全量 `run_verification.py --check` 含 345 条 `all_harmonic_horizon` 回归全过）。
  2. `git status --short -uall` 确认无游离 `.lake` 目录、无冻结路径改动、无 `.agents/teamwork/` 污染。
- **Falsification Criterion**: 若四向独立性 `(H1d4d, H2d, H3d, H4d)` 存在隐含耦合导致任一未决前沿被误标为闭合，或任一模块出现 `sorryAx`/`Lean.ofReduceBool`/自定义 `axiom`/数值不确定性，或触发冻结路径修改，则门禁拒绝合并。
