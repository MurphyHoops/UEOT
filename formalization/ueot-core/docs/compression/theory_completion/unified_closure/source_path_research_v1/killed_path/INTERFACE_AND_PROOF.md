# 同一实际风险路径 → killed 子矩阵幂：最小形式化接口

日期：2026-10-21。状态：**DRAFT_NOT_COMPILED**。

本目录独占于 `math_resume`。只新增私有草稿，没有运行 Lean、lake build 或 native export，没有修改生产七模块、书稿、Git 或远端。`SameSourceKilledPath.lean` 包含完整候选证明体，当前不能称为 Lean 已证。

## 1. 已有证据和本次范围

前置私有模块 `SourcePolicyPathBridge.lean` 的源 SHA256 为
`108500fc13229b8faffc9829d886313167142075112bc3f6c023a086c074ae91`。
它已实际聚焦编译 PASS，收据在 `../resume-source-bridge/COMPILE_PASS.json`；两个端点的公理仅为标准 `propext`、`Classical.choice`、`Quot.sound`。

已独审的 `../resume-source-bridge/CONTRACT_KILLED.md` 修订 2 SHA256 为
`e0efe3d8405060e1c03ce1d00b3e2810fcebcf4697d23669a289d9590e56283e`。
合同中首步来源桥的旧“尚未编译”文字属于当时记录，已由上述独立编译收据更新实际状态；本次没有改写历史合同。

本草稿只覆盖合同 **K1**，再附上从同一行随机模型推出 killed 核非负、行和不超过 1 的基本性质。K2 条件终端 PMF、K3 QSD 初始律、Doob 倾斜、单调性和失败补事件公式尚不纳入本次实现。没有为这些后续结果添加新的并列证书。

## 2. 定义与量词

设 X、A 为有限类型，A 非空；Y 任意。给定一个既有有限控制模型 M、观察 q:X→Y、固定动作 PMF `sigma:Y→PMF A`、任意初始 PMF p₀ 和任意安全域 K⊆X。

- 所有时刻、所有观察历史上的真实策略均为 `sigma(lastObservation)`；它没有额外时间或历史依赖。
- 真实转移直接取 `M.transitionPMF`。
- `liftedStationaryPolicy q sigma` 来自已通过的来源桥。
- `L = policyMatrix M (liftedStationaryPolicy q sigma)` 是既有模型的实际平稳闭环矩阵。
- `killedMatrix M pi K (u,v) = policyMatrix M pi u.val v.val`，没有输入一个自由 Q 或来源等式。
- `safeInitialRow p₀ K u = (p₀ u.val).toReal`，未归一化，总质量通常为 p₀(K)。
- `stateSurvives K 0 x` 定义为 x∈K；后继为前缀存活且新状态在 K 中。

实际动作记录 PMF 为

```lean
causalLaw p0
  (riskMicroControlKernel q (fun _ => M.transitionPMF)
    (observationMarkovPolicy sigma)) n
```

其存活事件采用原风险 API 的

```lean
{h | ¬ riskEverFailure (fun x => x ∉ K) n h}
```

因此时域 n 包含初始状态和 n 次转移。n=0 的存活概率为 p₀(K)，不强制为 1。最终定理只为书写 `toMeasure.real` 而要求 X、A 单点可测；Y 不要求可测结构、有限性或观察 Markov 性。

## 3. 两个目标端点

完整 namespace：

```text
UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceKilledPathCheck
```

| 草稿端点 | 目标结论 |
|---|---|
| `actual_survival_terminal_mass_eq_killed_pow` | 对每个 n 和安全子类型元素 v，真实动作记录路径的“从 0 到 n 存活且终端为 v”质量，等于 `rowApply (safeInitialRow p0 K) (Q ^ n) v`。 |
| `actual_survival_mass_eq_killed_pow_sum` | 对每个 n，真实存活事件质量，等于上述行在所有 `v:K` 上的总和。 |

这里 Q 是前述按定义构造的 `killedMatrix M (liftedStationaryPolicy q sigma) K`。两个结论均不需要 `Nonempty K`、正存活概率、QSD/特征向量、不可约性、闭合安全域或初始安全支撑。

空 K 时，第一个逐点结论为空量化；第二个结论仍有内容，其右侧是空和 0。原过程在 K 外可以返回 K；`stateSurvives` 排除了已经离开过的路径，因而不会把终端重返安全域误当作存活。

## 4. 证明依赖与新增工作

| 层次 | 使用的已有端点 | 本草稿新增的工作 |
|---|---|---|
| 实际风险路径来源 | 私有已过编译的 `actual_state_path_eq_stationary_path` | 证明动作擦除将原 `¬ riskEverFailure` 及终点条件精确送到纯状态路径事件。 |
| 逐步路径质量 | `UEOT.V3.PathError.pmfExtend_apply`；`CoreOperationalAssembly.policyTransitionPMF_apply_toReal` | 展开真实 PMF extension，按末个安全状态分组，推出未归一化递推 `κₙ₊₁=κₙQ`。 |
| 矩阵幂 | `UEOT.V3.QSDPerron.rowApply_mul`；`pow_succ` | 从实际初始截断行出发归纳 `κₙ=η₀Qⁿ`，不复制已有行乘结合律。 |
| PMF 事件质量 | `pmfMeasureReal_eq_sum_finset`；`PMF.toMeasure_map`；`Measure.map_apply` | 将有限指标和识别为原 PMF 的真实事件质量，并使用整条路径推前身份。 |
| killed 基本性质 | `Model.policyTransition_nonneg`；`Model.policyTransition_sum_one`；`Finset.sum_subtype` | 子类型行和是原行在 K 上的部分和，故非负且不超过 1。 |

核心新增有限求和引理 `sum_by_safe_last` 是私有的：若每条 good 历史的末状态属于 K，就可以按该末状态分组。它没有条件化、零概率历史延拓或独立采样前提。

草稿的纯状态中间定理 `state_terminal_mass_eq_killed_pow` 对既有模型的任意平稳随机策略成立；两个实际风险端点内部将该策略实例化为同一个 `sigma` 的提升，并调用已证推前等式。调用者不提供 `Q`、`η₀` 或路径等式的额外身份假设。

## 5. 定向复用检查

源码中已有 `QSDPerron.qsd_survival_mass_pow/qsd_all_steps`，它们是给定左特征关系后的矩阵代数；已有 `CoreInfinitePathClosure.exists_source_micro_all_times_viable_path_law` 是支持于闭合可行核的真实全时域安全。二者都继续保留并复用。

另核对了 `Compression/Objecthood/StationaryCausalPathLawBridge.lean` 的 `fixedPolicyAugmented_current_marginal` 与 `stationaryCausal_pathLaw_eq_stationaryTrajMeasure`：其接口是确定性平稳策略、测度值 complete-history kernel 与无限轨迹。`ExactPathLawDiscountedHittingTransform` 和相关修复模块提供目标命中/折扣占据接口。本次定向检查未找到这里的随机平稳风险 PMF、一般初始截断行与安全子矩阵幂的直接联合质量端点；不据此声称通用现有引理不能推出它。

## 6. 后续编译窗口要求

当前没有运行 Lean。草稿以 `import SourcePolicyPathBridge` 复用已经生成的私有模块，编译时应将

```text
/workspace/scratch/9a8d58b21e30/tmp/finite-encoding-20261021/resume-source-bridge/lean-attempt-002
```

加入 **`lake env` 所生成环境中的 Lean 搜索路径**，同时保留项目原有搜索路径。私有草稿的 `--root` 应指向本目录，输出也写本目录的独立 attempt 目录。由主智能体安排单一编译窗口；失败日志与后续修订分开保留。`#print axioms` 已附在两个最终端点后，待实际输出决定验证状态。

本次静态检查只能确认文件内容、使用端点和预期量词；有限和 tactic、子类型 Fintype 实例以及 definitional equality 的 elaboration 仍需实际 Lean 检验。
