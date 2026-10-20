# QSEL-A1-CLASSICAL：作者最终交付与范围审计

**状态：两模块 focused Lake PASS，87 / 87 个显式源声明公理审计 PASS，源码冻结。**

作者：`/root/q316_classical_core`。实际源基线：`427f512745ca70f82cba6a1388edcab904da8a42`。工作树：`/workspace/scratch/474cf6b1f047/qm_v316_work`。完整逐声明记录见 `/tmp/qm316_classical_report.json` 与 `/tmp/qm316_classical_declarations_final.json`。

## 1. 冻结源身份和新增计数

| 文件 | SHA256 | 字节 / 行 | 显式源声明 |
|---|---|---:|---:|
| `formalization/ueot-qm/UEOTQM/ClassicalSector.lean` | `fed2036fce7ca658a74b7457316f6950727924c0f8abc0931a5d5f7ffe33bbb5` | 11,550 / 334 | 36 |
| `formalization/ueot-qm/UEOTQM/CorePurificationBoundary.lean` | `53d957159fa6cf743c4e146e7d146385af81b7ec9c5a12204f90e488d870bce4` | 16,021 / 375 | 51 |

本组共新增 **56 theorem、23 def、4 abbrev、1 structure、3 个具名公共 instance，共 87 个显式源声明**。其中 ClassicalSector 为 24 / 10 / 1 / 1 / 0，CorePurificationBoundary 为 32 / 13 / 3 / 0 / 3。计数不另行展开结构自动生成的构造器、字段和递归器。三个具体商类型的公共实例保留为可复用 API，并全部纳入公理目标；没有为了减少计数而隐藏它们。

未修改冻结 Core、共享导出、全局 AxiomAudit、工作流、Git 引用或书籍文件。

## 2. 实际完成的科学责任

### 完整经典解释与凸极点纯性

`Classical.State X` 是整个有限概率单纯形，复用 `Mixture.Weights` 的非负实权重及归一字段。`Effect X` 包含所有响应值落在 `[0,1]` 内的函数。实际概率配对对所有态有界，全部效应通过点指示效应分离状态。函数推送、Cartesian 复合、实际求和边际、Dirac 制备与凸混合均给出合法归一态；本次显式证明了推送和边际与等权二态混合的相容性。

`IsPure` 对全状态空间的所有 `q,r` 及所有 `0 < t < 1` 量化，是凸极点定义。`dirac_isPure` 从这个定义独立证明 Dirac 纯性。没有把纯性定义成 Dirac，也没有声称完成一般“纯态当且仅当 Dirac”的分类定理；当前否定证书不需要该分类。

`no_pure_extension_halfMix` 证明：若 `x ≠ y`，则 `halfMix (dirac x) (dirac y)` 对 **每个有限辅助类型 B** 都没有 `State (X × B)` 中的凸极点纯扩展。证明从任何候选联合态构造两条质量翻倍的条件行，给出真正非平凡凸分解。类型 B 无 `Nonempty` 假设，空辅助类型被同一个量词覆盖。

`attach` / `marginalLeft_attach` 给普通扩展；`dirac_has_pure_extension` 给真正纯的正例。这两个存在性正例需要明确给定辅助点，不会与空类型情形混淆。

### 任意态随机作用与真实 PMF 接口

`rowState` 取 Core 有限随机核的实际实数行；`stepState K p a` 对任意输入态进行固定动作随机作用。`toPMF` 复用 Core 的 `FiniteProbabilityRow.ofRealRow`，`toPMF_stepState` 证明完整状态上的作用恰等于同一行 PMF 的 `bind`。`toPMF_pushforward` 连接有限实权重的推送与真实 PMF.map。

这不是任意历史反馈策略的额外定理；本次路径结论采用明确的常真策略。

### 同源 Core、真实终端商与实际路径边际

新注册模型使用冻结 `survivalMicroKernel`，明确注册 `observe := id`。`terminal_eq_iff` 从实际注册输出保持定理证明实际 `terminalSetoid` 恰为相等。`terminalControl` 是实际 `organizationalTerminalControl`，其映射单射性由真实商等式消去得到；没有手写恒等商替代算法。

第一行状态是两个不同安全微观点的等权混合，其实际控制商推送仍保持两个不同支持点。`sourcePMF` 直接是该同一控制商的 `micro.transitionPMF`。`actualPathLaw` 是从点初态和明确常真策略生成的实际 `stationaryTrajMeasure`。证明给出全部离散时刻注册安全事件概率一，以及真实首时刻商坐标的测度等式：

`actualPathLaw.map (fun ω => terminalControl.f (ω 1)) = (toPMF firstQuotientState).toMeasure`。

`FiniteCoreSlice` 是 14 条实际已证事实的合取，对应公开 H1–H6 的有限接口组。`classical_purification_separation` 将其与真实路径边际及任意有限经典辅助空间的纯化否定连接。想证明的纯化失败、边际等式都没有作为模型构造输入。

### 必要删除见证

同一核下，冻结原注册模型只观察第一位。`restricted_support_merge` 调用实际 Core 合并定理；其实际商推送由 `restrictedFirstQuotientState_dirac` 证明为 Dirac，再由凸极点定义证明纯。主反例因此明确依赖保留相关可见区分的注册读出。这个特定反例在删除读出后消失，不意味着原受限模型已满足普遍纯化。

## 3. 形式验证证据

固定官方 Lean 为 **4.33.1 / 819816b2e0a3bf405af45ae5c7af2491d8f5bee6**，Lake 路径 `/tmp/lean-4.33.1-linux/bin/lake`。未修改编译器、内核规则、冻结 Core 源码或证明选项。

| 检查 | 结果 | 日志 |
|---|---|---|
| `lake build +UEOTQM.ClassicalSector` | exit 0；模块 20 s；8728 jobs | `/tmp/qm316_classical_focused_round2.log` |
| `lake build +UEOTQM.CorePurificationBoundary` | exit 0；模块 25 s；8772 jobs | `/tmp/qm316_core_boundary_focused_round3.log` |
| 87 项逐声明 `#print axioms` | exit 0；目标集合与源扫描完全一致 | `/tmp/qm316_classical_axiom_audit.log` |

最终两个新模块本身零编译警告；Lake 日志仍回放既有依赖的历史 lint 警告。全部 87 个显式声明的实际公理集合均只含 `propext`、`Classical.choice`、`Quot.sound` 的子集。审计脚本为 `/tmp/qm316_classical_axiom_audit.lean`；审计输出 SHA256 为 `6dce95655d904835c9940fe82d22cd2c1debce859c700d8ed960355afae178d8`。新源扫描无 `sorry`、`admit`、`native_decide` 或新 `axiom` 命令。

为满足新实际 Core 接口，直接 CoreNonvacuousAllTimesWitness 导入闭包共 51 模块，其中 21 个缺失构建目标按 DAG 串行补齐，全部 exit 0；30 个目标使用已有产物并由最终 focused Lake 验证依赖。日志 `/tmp/qm316_core_serial_master.log`，逐目标结果 `/tmp/qm316_core_serial_results.json`。根端另行核验整个 QM 的递归 Core 闭包 56 项；二者覆盖范围不同。

保留了失败迭代日志。最终修复均为证明 elaboration：有限和改写方向、可判定 if 简化、第二命名空间打开 SISC、等式方向、PMF.support 实参及 PMF.toMeasure_map 的显式函数实参。没有弱化声明。首轮 namespace 未解析导致的 Fintype 级连错误在正确打开命名空间后消失；公共 `Fintype.ofFinite` 实例与实际 Core 构造内部实例一致，无需另造商或假设。

主智能体诊断实际 8 GiB cgroup 上限后，仅按明确 PID 停止本作者旧源码及并行 Core 编译并保留记录，改为唯一 Core Lean 的串行目标。中止记录为 `/tmp/qm316_classical_superseded_compile.json` 与 `/tmp/qm316_core_parallel_stop.json`。这是资源调度修复，没有改变数学或验证强度。

## 4. 范围、交叉审查与书稿一致性

本证书证明的是：公开完整经典解释与这组有限 H1–H6 接口相容，并且同一过程的实际可达商混态违反有限经典纯化存在性。因此要从该接口组推出普遍纯化，需要另加可排除此例的独立原则或物理桥。

它不代表全部 106 条 Core 命题的全解释模型，不宣称所有更丰富 UEOT 都不能重构 QM，不选择自然界实际读出与复合规则，不覆盖无限辅助系统，不推出复 Hilbert/Born 结构，更不是完整物理学或最终真理。零奖励只给合法精确控制和值运输，安全常真策略不是从价值优化唯一选出的策略。

Agent C 独立只读审查报告 `/tmp/qm316_classical_cross_review.md` 覆盖全单纯形、任意有限辅助、真实商、实际轨迹、H1–H6 范围、删除与普通扩展正例；已收到最终 PASS 源身份供其绑定。

本作者完整复核根端 `/tmp/qm316_ch54.md` 更新稿，包括 54.1 的任意输入态固定动作 PMF.bind 接合，未发现范围或 Lean 覆盖不一致。x₀/x₁ 明确定义、H1–H6 限定、等权混合措辞、空辅助类型、零奖励解释和真实路径均准确。具体所读书稿 SHA 记录在 JSON；后续书稿集成由根端负责。

等待编译期间还独立只读审查 B 的 `RealLocalTomography.lean`，无数学或范围阻断，报告 `/tmp/qm316_real_tomography_cross_review_by_classical.md`，绑定 SHA `76dfea1aa3ad7f16e699a8529bde5f22120badac9a1db60f0265eaef4eeddc9e`。这不替代 B 的实际编译与公理审计。

## 5. 交付边界

本组作者工作已完成。根端负责共享导出、统一 AxiomAudit、全局构建、总著/状态/工作流集成、Git 提交与远端同步；本报告不提前宣称这些全局步骤完成。
