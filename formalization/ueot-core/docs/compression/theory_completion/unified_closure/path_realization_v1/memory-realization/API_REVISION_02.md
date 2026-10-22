# 物理安全见证的公开 API 修订 02

## 本次修订及当前证据

本次只修改 `FiniteMemorySafetyWitness.lean`。其余六个本批 Lean 模块、五个 native 协议文件和既有生产模块保持冻结。本说明是新记录，不覆盖原源码、原聚焦收据、第一次 full build 或第一次 native 执行记录。

| 源码版本 | SHA-256 | 本说明初写时状态（历史检查点） |
|---|---|---|
| 原见证 | `fcc011bd9c7571e9ae95e6df606baaf500e2f7767453be6788af5da470b934e7` | 原聚焦实际 PASS，属于原 `c344bf6657ab31a32c46fba9feff6d5c04846b8f061d444aec8accb4994ad41b` 源指纹的 full build PASS；原 native01 未完成 |
| 修订见证 | `08060447a92c3b129351b95615ed2e1b3214e12e9ded21c638d0c6554c400c88` | 新聚焦、manifest02、full build02、两轮 native 及后续验收均待 root 实际执行；本说明不预填 PASS |

### 后续实际检查点：compile-10 与 manifest02

Root 已对修订见证实际执行 compile-10，结果为 **PASS，3.559897708 秒，退出码 `0`，日志为空**。本说明作者随后读取了完整原始工具文本 `tmp/core-path-realization-20261022/FOCUS_10_TOOL_OUTPUT.txt`，其 SHA-256 为 `81679829b933f34d132c4b949d143952b2ca8acdbbfec4b25123bbacc0bfbef3`；原文绑定上述 `08060447…` 源码、空日志 SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` 与 `FINAL_STATE=PASS`。

Root 随后实际冻结 manifest02 并回报：**691 个模块、73 个源码公开声明、25 条源码提示**，完整源码指纹为 `de7c7e287bd1b351ed3f790de58bfd71edf18df4013f7e5aaf2af55a6b3f6379`。这些源码提示不等同于编译器实际生成的私有声明计数；后者仍须由 native 原样导出。

当前修订已通过聚焦编译；**新源码的 full build02、正式 native 两轮及后续集成验收仍待实际收据**。上表保留初写时的待执行状态，不把旧证据或先前 PENDING 记录改造成新的执行结果。

独立审查方在编辑前逐字节保存了[原见证源码](../independent/memory-api-revision-02/PRIOR_FiniteMemorySafetyWitness.lean.txt)，其哈希与原聚焦接受源完全一致。原数学与来源合同见 [CONTRACT.md](CONTRACT.md)；其中原见证的执行状态只对应上表原哈希。

Root 回报，原 native01 的原始 stored-type `Meta.isDefEq` 检查运行约 13 分钟、使用约 19.1 GB 后被定点中断，记录为失败。独立诊断完成原 328,944 个交叉比较后，把内部无进展对定位为：

```text
FiniteMemorySafetyWitness.safe_source_all_times_mass_one
FiniteMemorySafetyWitness.unsafe_transition_time_one_mass_zero
```

上述是本次 API 检查的触发背景，不是碰撞结论。原 native01 没有完成最终完整导出，不能记为 native PASS，也不能据此声称已经排除了全部类型碰撞。诊断不替代正式 native 收据。原 full build 对原源指纹的 PASS 也不转用于本次新源码。

## 新的公开数学内容

保留同一个实际 Boolean 状态模型：观察、行动和记忆均为 `Unit`，控制器不变，认证谓词恒真，安全集为 `{false}`。这个安全集非空且不等于全集。原初态为一个明确的 `PMF.pure initial`，转移核序列为同一个明确的 `source next`，原实际占据仍由 `coverageDeploymentRowLaw` 给出。

新的公开定理 `physical_safety_premises_independent` 没有新增输入假设。它直接证明一个包含三个实际来源的合取：

| 原初态 / 实际后继 | 自身全时零未认证占据 | 初始安全 | 认证转移支持闭合 | 自身实际坐标质量 | 自身实际全时安全质量 |
|---|---|---|---|---|---|
| `false / false` | 成立 | 成立 | 成立 | 正例使用全时结论 | `1` |
| `false / true` | 成立 | 成立 | **不成立** | 时刻 `1` 安全质量为 `0` | `0` |
| `true / false` | 成立 | **不成立** | 成立 | 时刻 `0` 安全质量为 `0` | `0` |

每一行的零占据、初态、源核和事件都写在同一分支中，没有把一个来源的占据与另一个来源的轨迹质量组合。

相较于原来的五个分散质量结论，新公开定理增加了两项明确的数学结论：

1. 对 `false / true` 来源，认证转移支持闭合为假。证明选取时刻 `0`、安全状态 `false`、唯一行动和实际支持中的后继 `true`；闭合会强迫 `true ∈ {false}`，产生矛盾。
2. 对 `true / false` 来源，原初态安全为假。实际初态支持包含 `true`，而 `true ∉ {false}`。

因此，公开端点现在直接表达：在零未认证占据保持成立时，一条物理前提不能由另一条代替，删除任意一条均有真实同源的概率零反例。这里的“必要性”是原充分条件定理中各前提不可普遍删除；本定理没有声称这些充分条件是所有物理安全过程的充要刻画。

## 五个原质量事实全部保留

下面五个计算的数学命题和证明正文保留，仅将声明可见性改为 `private`：

- `safe_source_all_times_mass_one`；
- `unsafe_transition_time_one_mass_zero`；
- `unsafe_transition_all_times_mass_zero`；
- `unsafe_initial_time_zero_mass_zero`；
- `unsafe_initial_all_times_mass_zero`。

新的公开证明显式引用全部五项。正例继续使用已证明的实际物理安全总定理；时刻 `0` 和 `1` 的反例继续通过实际坐标律计算；两个全时质量零结论继续由全时事件包含于相应坐标事件推出。

所有五个质量结论均是公开合取的直接分量，可以通过合取消去取得。未添加 `opaque`、不可约包装、新结构字段、额外标记或供用户假定的安全结论，也没有把证明事实改写为公理或结构输入。原来的四个其他公开见证端点继续公开。

本次 API 整理的实质是形成一个准确表达两条物理前提独立性的来源完整端点，而非宣布某个旧比较为不相等、跳过某个仍然公开的候选或用新包装暗示类型碰撞已经排除。

## 公开比较域确实改变

五个原公开计算成为私有证明成分，并新增一个公开合取定理，因此本批源码公开候选数从 `77` 变为 `73`，已由实际 manifest02 的源码解析确认。最终清单还须与实际编译器导出相互核对。这是公开比较域的明确变化，不能表述为旧的 77 个公开候选仍然逐对接受了同一轮完整比较。

按新的 `73` 个源码公开候选，与此前 `4272` 个已注册公开命题的完整比较应为：

- 交叉比较：`73 × 4272 = 311856`；
- 本批内部比较：`73 × 72 / 2 = 2628`；
- 合计：`314484`。

native 协议本身保持冻结。新的运行仍须在实际全部公开候选上使用原始 stored-type `Meta.isDefEq`、保留原宇宙参数并执行原完整比较规则；不采用名称、类型头、人工白名单或超时结果代替比较，也不降低透明性来绕过某个候选。

私有化不使这些计算离开编译器事实核查。原协议会枚举七个真实模块拥有的全部定理常量，包括实际生成的私有常量，继续记录并检查所有者、可见性、公理闭包、类型、直接常量和定理依赖。新公开定理必须在实际依赖中真实引用五个私有计算；最终收据须分别明确公开成对比较域与包含私有常量的 compiler-owned 审计域。

## 后续验收责任

新聚焦与 manifest02 已有上文所列实际检查点。独立静态审查、full build02、正式 native 两轮一致性、canonical 和发布治理由 root 按新实际源指纹分别推进；本文件不为后续步骤预先提供成功状态。

本次修订不改变 `106 = 11 generated / 89 adapters / 6 boundaries`、四项 counted 结果或全局 `NOT_ESTABLISHED`。它也不改变原初态、策略、源核、训练/部署来源、参考过程检查预算、统计校准范围或物理经验有效性的责任。
