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

---

## 追加条目模板

```markdown
| `DEAD-YYYYMMDD-NN` | `SPEC-YYYYMMDD-NN` | `CLOSED` | <尝试的数学/物理/Lean路线> | <具体失败原因、反例参数或报错信息> | <在什么新条件下才值得重开> | YYYY-MM-DD / <Agent名> |
```
