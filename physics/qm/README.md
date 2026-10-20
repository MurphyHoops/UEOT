# UEOT-QM

当前研发：**v31.6 / Kernel 1.6 — MAIN_VERIFIED，2026-10-20 UTC**。最新集成身份以 [CURRENT.json](status/CURRENT.json) 为准。

唯一连续理论总著为 [《UEOT物理学》正式 3.2](book/UEOT_PHYSICS.md)：第 0–56 章、6 个附录、117 个编号结果；[完整 PDF](book/UEOT_PHYSICS.pdf) 共 186 页。全部原有理论推导保留，新增章节与真实源码、前提、反例和开放问题逐项对应。

## 本轮三个关键结果

| 方向 | 实际闭合 | 科学边界 |
|---|---|---|
| 经典 Core 边界 | 同一真实核、终端商、控制商及安全路径的实际混合商边际，在任意有限经典辅助系统上无纯化；受限读出下该反例消失 | 只覆盖列明 H1–H6 接口和公开经典解释，不表示全部 UEOT 不可重构 |
| 实局域层析 | 两个真实实联合密度态对全部实局域乘积效应同概率，合法联合实测试给 1/0；允许复局域效应后给 1/2/0 | 实张量模型的精确排除责任，不是唯一复量子重构 |
| 非交换 Doob | 给定正可逆本征度量，构造实际完整仪器；任意初态真实有限条件态与其迭代相连；右本征态另给平稳结果 | 谱对象存在、唯一性、吸引和无限条件过程分开处理 |

完整数学、实际例子和验收见 [本版报告](UEOT_QM_KERNEL_v31.6.md)、[数学审查](audits/CORE_SELECTION_DOOB_REVIEW_v31.6.md)。

## 实际内核与证据

本地统一验收：**22 模块、459 显式定理、573 个实际命名公理报告**。四份具体见证另有 62 定理、22 定义、84 审计。六个精确证书的 42 项审计、四组坏数据真证明拒绝/同数据假证明接受、100 运行方法、四份演示分别记录。允许的基础仅为 propext、Classical.choice、Quot.sound。

[统一证明回执](kernel/evidence/v31.6/lean-verification.json) · [70 项受验源清单](kernel/evidence/v31.6/source-manifest.json) · [远端集成状态](kernel/evidence/v31.6/integration-verification.json)

已经形成的有限内核包括：实际复密度/Kraus/Born 操作、全部有限记录的响应商、有限坐标分类、Ax/p 正事件更新、完整有限自适应树、可靠局部证书、真实效应伪距离与 Core 误差运输、同库混合 TV 预算、Cesàro 平稳存在、对角及非交换有限条件化。本轮进一步给出量子选择的两个明确反模型边界。

## 阅读与工作入口

- [正式总著](book/UEOT_PHYSICS.md)、[PDF](book/UEOT_PHYSICS.pdf)、[逐章档案](book/CHAPTER_DOSSIER.json)。
- [Lean 包](../../formalization/ueot-qm/README.md)、[运行内核](kernel/README.md)、[当前主张台账](status/CLAIM_LEDGER_v31.6.json)。
- [本轮执行合同](UEOT_QM_EXECUTION_v31.6.md)、[路线图](ROADMAP.md)。
- [下一轮已审定合同](UEOT_QM_EXECUTION_v31.7.md)：共同操作/纯化接口；经典记录与量子记忆；当前非对角模型的精确条件态动力学。该合同尚未作为已证明成果计数。

## 科学责任

当前有一个明确、可构建和可审计的有限量子内核；通用 Core 唯一选择复量子结构仍是核心开放问题。现实三代仍依赖完整谱、表示、有效窗口及一致性条件。没有新增实验数据，标准量子定理的形式化数量也不代表完备物理理论已经建立。

历史 [v31.5](kernel/evidence/v31.5/integration-verification.json)、[v31.4](kernel/evidence/v31.4/integration-verification.json)、[v31.3](kernel/evidence/v31.3/integration-verification.json) 保留各自提交和执行身份。冻结 Core 的 106 项、四生成器及五份原始材料身份不由本轮改写。
