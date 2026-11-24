# UEOT Dead Ends & Falsified Routes (`DEAD_ENDS.md`)

本文件记录所有在探索或红队质询中被**证伪、发散、超时、或依赖未授权额外公设**的路线。  
**维护规则：只追加，不删除。** 这样任何新加入的 AI Agent 在开工前都能第一时间避坑，避免重复消耗算力。

---

## 死胡同索引

| Dead-ID | Spec-ID | Status | Attempted Route | Failure Mode / Counterexample | Reopen Condition | Date & Agent |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `DEAD-20261124-00` | `TEMPLATE` | `ARCHIVED` | 示例：在未检查 `check_no_escapes.py` 前用 `axiom` 暂代中间分析引理 | 违反 UEOT 零逃逸硬门禁，`ExhaustiveAxiomAudit.lean` 直接拒绝 | 永不重开：必须改用构造性证明或将假设显式提升为定理参数 | 2026-11-24 / Setup |
| `DEAD-20261124-01` | `SPEC-20261124-03` | `CLOSED` | 4D 纯杨–米尔斯连续统构造：依赖单格点/单小方格 Peierls 熵压制参数 `2*c_adm*b0` 直接跨越连续统极限 | 在 4D 中需要 `2*c_adm*b0 >= 4` 以抵消时空维数熵因子，但 Lüscher 可容许性阈值（`eps_adm = 1/30` 等）仅给出 `2*c_adm*b0 < 4`（已在 `NonAbelianChiralConstructiveBoundary.lean` 代数证伪），单方格 Peierls 界不足以覆盖无限体积熵 | 仅当引入非单方格多尺度块重整化/Balaban 级数界，且不再假设 `2*c_adm*b0 >= 4` 时方可开辟新路线 | 2026-11-24 / M0 Chair (Survey) |
| `DEAD-20261124-02` | `SPEC-20261124-04` | `CLOSED` | 无中间阈值的 1-loop `(3,3,1)` 沙漠（desert）GUT 规范耦合精准统一 | 在纯 1-loop 沙漠演化下，统一残差 `Delta_123 < -38` 且偏离实验观测超过 `>83 sigma`，在无中间阈值修正下被数值证伪排除 | 仅允许在 `H3a` 中显式引入中间能标阈值 `(M_I, M_GUT)` 或 2-loop 阈值修正窗口；禁止无阈值 1-loop 沙漠重算 | 2026-11-24 / M0 Chair (Survey) |
| `DEAD-20261124-03` | `SPEC-20261124-05` | `CLOSED` | 基于公平采样（fair-sampling）后选择的 Bell-CHSH 违背认证，或在零真实逐 shot 硬件数据时声称 `device_certified = true` | 违反 `HARDWARE_CERTIFICATION_CONTRACT.md` §1.3 & §3：后选择丢弃了非选择性触发记录（可模拟出伪 CHSH > 2 且绕开 `eta > 2*(sqrt(2)-1)` 与 `2*delta_drop` 偏置界），且零逐 shot 数据下任何 `device_certified = true` 均属欺诈 | 永不对后选择重开；`device_certified` 仅当真实原始逐 shot 数据满足 `SPEC-20261124-02` 全部留出与标定门禁后方可重新评估 | 2026-11-24 / M0 Chair (Survey) |
| `DEAD-20261124-04` | `SPEC-20261124-03` | `CLOSED` | 仅用迹不等式 `Tr(S_ov H_W) > 16` 检验 Overlap 符号投影正定性，以及同义反复的 Berry 环路和自检（`verify_nonabelian_lattice_h2.py` Iter 1–2） | Red-Team（`teamwork_reviewer_r2_2` / `teamwork_challenger_r1_2`）构造出反例 `S_swap`（最小本征值 `-1.32667`）仍可通过迹检验；Iter 3 改用 `enclose_hermitian_eigenvalues(abs_H)` 全部本征值包络（`evals_abs_H[0] > 1`）与独立规范轨道/磁通环路校验 | 已按全谱包络条件收口，不得回退至迹检验或同义自检 | 2026-11-24 / M1 & Red-Team |
| `DEAD-20261124-05` | `SPEC-20261124-04` | `CLOSED` | 负宇宙学常数 Big Crunch 下界误用宽松 `9/4` 前置因子 `-3*pi^2/(t_obs/t_P)^2` | 允许 `-3.0e-121` 通过下界检查，但精确 Friedmann 积分显示其在 `11.31 Gyr < 13.80 Gyr` 即发生大坍缩；已按精确积分系数 `-(4*pi^2/3)/(t_obs/t_P)^2` 修复 | 仅在精确解析积分系数下有效，严禁放宽 `9/4` 近似因子 | 2026-11-24 / M2 & Red-Team |
| `DEAD-20261124-06` | `SPEC-20261124-04` | `CLOSED` | 在平坦 `k = 0` FRW（`Λ > 0`）上声称存在无条件正下界 `3*pi^2/((100 Gyr)/t_P)^2` | 在平坦 `k = 0` FRW 中，当 `I_Λ → 0+` 时加速特征时标 `t_Λ → +∞`，不存在无条件正下界；正下界仅在闭宇宙 `k = +1`（`Ω_k0 < 0`）条件下成立 | 必须显式标注 `Omega_k0 < 0` 的 `E/P` 条件前提，不得声称平坦 FRW 存在正 `Λ` 下界 | 2026-11-24 / M2 & Red-Team |
| `DEAD-20261124-07` | `SPEC-20261124-04` | `CLOSED` | 无离散误差填充的 `n = 40` Higgs 四次耦合 RK4 与离散阈值滞后判定 `t_cur.a >= t_portal.b` | 离散化截断误差 `5.74e-8` 与 `20.8%` 阈值步长滞后排除了真实连续解；已修复为精确 `t_portal` 分段与 `n = 100/200` `16*disc` 填充包络 | 仅当网格加密验证且分段点精确对齐时方可接受 | 2026-11-24 / M2 & Red-Team |

---

## 追加条目模板

```markdown
| `DEAD-YYYYMMDD-NN` | `SPEC-YYYYMMDD-NN` | `CLOSED` | <尝试的数学/物理/Lean路线> | <具体失败原因、反例参数或报错信息> | <在什么新条件下才值得重开> | YYYY-MM-DD / <Agent名> |
```
