# UEOT-QM Kernel 1.3 领域验收与交叉审查

日期：2026-10-19 UTC（北京时间 2026-10-20）。变更级别：**Class B / QM 领域结构增量**。依据用户持续推进整个 UEOT-QM、形成内核并同步远端 QM 的授权执行；冻结 Core 定义、106 项覆盖与四个计数生成器保持不变。

当前结论：**本地数学／运行／实例验收 PASS，独立语义与源码审查 CLEAR；PR #335 及 resulting-main 的运行、Lean 与实例验收全部 PASS。** 机器 acceptance marker 位于 [CURRENT.json](../status/CURRENT.json)。本说明遵守 [变更控制](../../../constitution/UEOT_CHANGE_CONTROL.md)、[分支治理](../../../docs/REPOSITORY_BRANCH_GOVERNANCE.md) 与 [Core–Physics 合同](../../interfaces/CORE_PHYSICS_CONTRACT.md)。

## 为什么需要此变更

v31.2 已有实际词效应、有限 presentation 和全词／完整树定理，但 Python 的有理加权可变索引数据尚不能直接作为该数学接口的证明。新版本提供独立、可计算的数值条件和可靠性构造，使每份生成源必须由 Lean 内核重新检查实际权重、矩阵、生成词与闭包等式。

前版的安装失败发生在编译之前，原因为 releases.lean-lang.org 下载的 TLS 错误。修复保持原 Lean 4.33.1 与原官方资产摘要，通过直接官方 GitHub 资产、有限重试、SHA256 和编译器身份检查解决。修复已经在正常 PR #333 和主线 c7aa925f 的工作流 39294335590 中通过；见 [v31.2 集成回执](../kernel/evidence/v31.2/integration-verification.json)。本轮不借该回执认证新源码。

## 作者检查与独立交叉复核

| 审查 | 实际核对 | 结论 |
|---|---|---|
| 加权／可变指标作者范围检查 | sqrt scaling 的实际三种矩阵项、结果依赖 Kraus 类型、全部完整性求和、零结果概率；35 定理及 3 构造实际审计 | [CLEAR](WEIGHTED_RAGGED_REVIEW_v31.3.md) |
| 精确数学构造 | Q(i) 乘法与共轭、解释单射、5 条可计算条件、数值基与真实词绑定、系数行方向、任意词归纳 | [CLEAR](EXACT_CERTIFICATE_REVIEW_v31.3.md) |
| 全包声明覆盖 | 统一入口恰有 13 个模块，196 个显式 theorem，审计恰为其全部加 17 个列举构造，无重复或漏项 | CLEAR；实际 213 项审计 PASS |
| Exporter 数值绑定 | 有理实／虚部、库与上下文、带界 Fin 索引、标签只进入 manifest、原有空分支和新增补零有区分 | CLEAR；15 项新运行测试 PASS |
| 可重复验证器 | fresh source/manifest/index 逐字节匹配；编译前后 SHA、实际日志、公理集合；坏 true 与同前缀 false 双门 | CLEAR；冻结版本实际完整执行 PASS |

加权／可变指标报告是该模块作者的范围检查与机器验收记录。精确证书报告同时记录 Exact 作者检查，以及对主构造和 exporter 的独立交叉复核；统一声明清单与最终文档／证据另由非主构造作者复核。上述角色不混称为同一种独立审查。

验证器最终审查和实际执行均绑定 SHA256 `6d2c5504a2f625441f6fd1b2eb5adf13dc52acb8a574f862f11d85ee880564dd`。最终复审还核对 committed index 的前后摘要检查，以及相对 `--lake` 在切换 cwd 前按调用位置规范化、裸 `lake` 沿用 PATH 的行为。命令使用参数数组调用，没有将生成内容拼成 shell。

`Data` 没有全词充分性、后验相容性或物理结论字段。`Conditions` 仅检查非负、完整性、空词、逐词基效应和逐分支闭包。可靠性构造将它们送入现有 `FiniteObservablePresentation`，再使用已有公共定理得到全词 iff 与自适应后果。源级复审逐项核对了五个条件到构造字段的实际引用。

## 本地机器验收

- 官方 Lean 4.33.1 统一 `lake build UEOTQM` 返回 **0**，13 模块、196 显式定理；日志的 8733 jobs 是构建任务数量。
- `#print axioms` 真实输出 **213 项**，解析清单与请求集合完整一致；允许基础仅 `propext`、`Classical.choice`、`Quot.sound`。
- 新增四个模块分别实际定点编译通过，再经统一入口构建。既有 Core／Observables 的 lint 提醒保持，未引入证明错误。
- 运行回归 **87 方法 PASS，0 failure、0 error、0 skip**；三个完整演示执行成功。
- 六份实例的源码、manifest 与总索引共 **13 文件重新生成后字节一致**。
- **6/6** 正例实际编译成功，**42/42** 命名实例公理审计通过。
- **4/4** 篡改后的原 `check=true` 证明在指定 checked 位置失败；**4/4** 相同数值前缀的 `check=false` 证明成功，四项实际公理审计通过。
- 验证器在 **17:44:58.865–17:46:30.238 UTC** 完整执行，返回 **0**，`problems=[]`；源码与 `.olean` 前后绑定一致。
- 53 个被测源码／锁／脚本／fixture／workflow 文件的摘要和全部九个安装依赖 Git 版本已核对；官方编译器归档摘要再次匹配。

原始输出及其摘要见 [通用证明回执](../kernel/evidence/v31.3/lean-verification.json)、[实例回执](../kernel/evidence/v31.3/lean-exports/verification.json)、[运行回执](../kernel/evidence/v31.3/runtime-verification.json)、[源码清单](../kernel/evidence/v31.3/source-manifest.json)。实例失败源中由 Lean 错误恢复产生的占位公理输出仅保留为失败诊断，不属于被接受证明，也不进入通过的公理集合。

## 证据范围与下一门

通用可靠性定理与具体数据实例已成立；Python/JSON/parser/exporter/标签映射/Gram/消元/搜索/树遍历的全输入正确性未统一证明。有限响应 presentation 可冗余，不给出最小物理 Hilbert 实现。物理量子扇区仍是输入，没有新增实验确认或无条件现实三代结论。对原五份理论材料的解释及科学端口边界继承原件审查。

本地 authoring worktree 从 v31.2 的 c3ec8f4 建立，被测 QM 字节由逐文件 SHA256 标识。发布基线 c7aa925f 已包含 PR #334 对 6 个 Core 库 Lean 文件及 1 个 docs Lean 检查文件的变更；此前将全部增量写成仅元数据的说法不准确。对 QM 统一入口的传递导入分析得到 12 个 Core 模块，其 Git blob 全部与发布基线相同，且与上述 7 个路径没有交集，详见 [导入闭包与远端树比较](../kernel/evidence/v31.3/core-import-closure.json)。本地回执不认证未导入的新 Core 模块，本轮 PR 没有修改任何 Core 文件。

源码提交 `93906b760a2e62d312e08ee3a9b7df7487b2d380` 已通过 PR 工作流 39299160884；正常合并提交 `bad76ffbcf811e878404f860033d43885832803c` 的 Git tree 与其完全相同，并通过主线工作流 39300120071。两个工作流均实际完成 87 项运行测试、213 项通用公理审计、六个正例与四组假值见证。原始本地日志及源码清单保留，新的 [集成回执](../kernel/evidence/v31.3/integration-verification.json) 单列实际远端日志、工作流身份和摘要。最终文档／证据补录只更新这些验收记录，不重新计作数学源码构建。

下一研究主任务已在 [路线图](../ROADMAP.md) 和 [22 项台账](../status/CLAIM_LEDGER_v31.3.json) 中明确为真实量子一步距离／缺陷及正概率后选择稳定性，再复用既有 M-TC。QMB-05/06、物理 G3/HGP、QDRR、CV 与 QFT/RG 分别保留可验收的下一切片。
