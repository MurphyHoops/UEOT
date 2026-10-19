# UEOT-QM Kernel 1：领域验收与证据裁决

日期：2026-10-19（UTC）  
变更分类：Class B，QM 领域结构与实现  
裁决：**ACCEPTED，范围限定为本文及主张台账列出的 Kernel 1 切片。**  
请求依据：用户要求“继续推动 QM 发展，直到形成一个内核”，并已要求同步至远端 QM 目录。

## 1. 验收对象

本次建立 `physics/qm/kernel` 的精确运行内核、`formalization/ueot-qm` 的专用 Lean 包，以及 QM 的说明、状态和证据。Core 以提交 `54378ff962b2a6038d9405edb83a33a3099833cb` 为继承基线。

按 [变更控制](../../../constitution/UEOT_CHANGE_CONTROL.md) 的 Class B 合同，本文件提供领域验收 memo，[CURRENT.json](../status/CURRENT.json) 提供带明确范围与实测证据的 acceptance marker。交叉审查记录见 [语义审查](KERNEL_SEMANTIC_REVIEW_20261019.md)。本次保持 Core 数学源码、冻结计数及生成台账的原状态。

## 2. 实际机器证据

**验收提交：`0791ea34f1ba108c738915921f8e7d923371d0cd`。**

- 工作流：[UEOT QM Kernel，run 39270031506](https://github.com/MurphyHoops/UEOT/actions/runs/39270031506)。
- 事件：PR #331，明确检出该 PR head，完成时间为 2026-10-19T14:35:25Z。
- `runtime` 作业 `118119587396`：成功；32 个独立测试方法全部通过，完整示例运行成功。
- `lean` 作业 `118119587910`：成功；统一根模块构建、公理审计、源码逃逸检查和继承依赖核对均通过。
- Lean 4.33.1，编译器提交 `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`；Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`。

| 模块 | 实际 theorem 声明数 | 验收内容 |
|---|---:|---|
| Basic | 7 | PSD 密度、实迹质量、零质量与归一化 |
| Instrument | 14 | Kraus 分支、概率、后验及有限 ancilla 放大 |
| Operational | 20 | 全词响应、响应商、后验比值和闭合可实现更新 |
| Selector | 11 | 无 atomicity 的三代条件选择及删除前提/复制对照 |
| Transport | 4 | 非负标量预算与 Core 误差链复用 |
| 合计 | **56** | 五模块及统一入口实际编译通过 |

另审计 `normalize`、`Instrument.posterior` 和 `nextReachableResponse` 三个携带证明的构造，共 **59 个实际 `#print axioms` 报告**。提交中的解析器核对了全部请求声明与返回声明，并确认依赖只属于 `propext`、`Classical.choice`、`Quot.sound`。这描述的是标准基础上的核查，不是无公理基础。

构建输出的“8725 jobs”包括依赖构建任务，不是 UEOT-QM 定理数。Python 测试数也不并入形式化定理数。

完整索引见 [lean-verification.json](../kernel/evidence/lean-verification.json)，原始声明文本见 [axiom-audit.log](../kernel/evidence/axiom-audit.log)，机器可读依赖见 [proof-axioms.json](../kernel/evidence/proof-axioms.json)。

## 3. 源码、日志与审查快照

验收回执逐一记录 21 个代码与配置文件的 SHA-256 和 Git blob 身份，核对其与上述不可变提交的远端树一致。构建作业打印的 8 项 SHA-256（五模块、统一入口、依赖清单和工具链）再次与本地文件交叉核对。原先本地 32 项运行回执所绑定的八个 Python 源文件也与同一提交一致。

这里长期保存的构建、公理、身份和运行日志来自实际成功作业，移除了行首 UTC 时间戳及颜色控制符，保留相应输出片段。`proof-axioms.json` 由已提交的解析器重新读取这 59 个真实报告生成。GitHub artifact 的编号和摘要另存于回执；没有把重建的文本冒充为经过本地二次哈希的原 ZIP 字节。

语义审查快照为 2026-10-19T14:19:27.986475+00:00，按原文保留。该快照的 `Instrument.lean` SHA-256 为 `4d848a9dbe7f5335e327ce659214cf3672e94dfaac3a4dd783473ee008ddd230`；本次验收版本为 `aa63084bec63476ffd73a54f1c8b53fab406a8fd15cc678bd2d34d30a5820b80`。

已读取并比较快照提交 `4b53a5fa7957da95f11ce46eba5080cae30da739` 的实际文件：差异仅在 `ancillaKrausMap_entry` 证明体内，包括修正矩阵求和展开、展开 `Matrix.of`、显式消去恒等辅助指标。该定理的声明、前提、定义与其他证明不变。随后五个模块均已在验收提交中通过编译。

工具链多余换行在早期候选提交修正，精确依赖检查实际通过；自动审查线程已按该修复关闭。最后的工作流修正将禁止词审计改为完整词匹配，避免把合法反例名称中的 `admits` 当成 `admit`。标准公理白名单及逐声明覆盖检查继续生效。

最终说明另经只读语义复核，重点核对 W*、闭合更新、ancilla、有限覆盖、G3 和历史状态边界，未发现必须修改的问题。参与协作者的实现角色仍按原语义审查透明披露，不宣称为完全独立的第三方认证。

## 4. 为什么它已构成第一个内核

内核具有明确的输入、内部对象、可复用更新和输出：

1. 输入有限复 PSD 密度态及满足完整性的 Kraus 操作。
2. 从实际操作导出合法有限记录响应，按所有允许词的响应取商。
3. 从前缀记录比值推导更新的纤维相容，而不是把相容性作为待证明结论的结构字段。
4. 得到 `range → input → Option range`；正概率分支携带可实现后验见证，零概率分支为 `none`。
5. Python 计算精确有限效应闭包和坐标更新，输出记录律及声明范围内的比较/误差证书。

前三个实际 Core 消费分别是 `QuotientDescent.existsUnique_descend`、`RecursiveSufficientState.existsUnique_reachableUpdate` 和 `TransportCertificate.weighted_chain_bound`。它们接收具体量子响应或标量误差合同，构成实际调用。

32 项测试包括闭式干涉、复相位、Bell 态与非 CP 负例、全部主子式 PSD 校验、适应记录、零证据、协议扩展、相关环境记忆、局部递推失败和稀有事件放大。其角色是对可执行切片作可复算核查。

## 5. 接受与保留的主张

本次提升为 `VERIFIED_LEAN_BUILD_AND_AXIOM_AUDIT` 的条目是 **QMK-01、02、03、04、08、10**。其声明和前提见 [v31.1 主张台账](../status/CLAIM_LEDGER_v31.1.json)。

三代结论是自然数前提

\[
N_c\ge3,\quad N_f>0,\quad k\le N_f,\quad
2N_ck+N_f=N_cN_f,\quad N_f(N_c+1)<22
\]

下的 `Nc=3, Nf=3, k=1`，不再要求 atomicity。没有把实际谱满足这些前提、现实有效窗口或完整 QFT 一并验收。接入义务见 [G3 物理合同](G3_PHYSICAL_ADAPTER_CONTRACT_20261019.md)。

保留为未完成的事项包括：

- W* 张成、有限坐标 iff、高斯消元和 Python 的 Lean 程序细化；
- 有理复数、加权 Kraus、不同结果指标的形式化 adapter；
- Lean 有限适应树解释器；
- 具体量子距离的统一局部误差合同及一般条件化定理；
- 实际有限谱求和到 G3 前提的桥，以及相应谱/阈值/弱窗口的物理适用性；
- 历史原件字节裁决、后续 CV/QFT 接口和新的实验确认。

有限协议比较只覆盖列出的准备配对与完整树；标量轨迹证书实查初值和每一步递推。两者均不自动提供全部状态、全部协议或 diamond norm 保证。

## 6. 集成与后续执行

[PR #331](https://github.com/MurphyHoops/UEOT/pull/331) 承载本次领域实现与证据。机器回执绑定不可变的已测试祖先及逐文件身份；最终说明和证据提交可以在其后追加而不修改这些源文件。实际主线集成以包含本文的提交、PR 合并记录和主线工作流为准，避免在证据文件中声称它自己尚不存在的提交号。

下一阶段按 [ROADMAP.md](../ROADMAP.md) 执行：先闭合 W* 与有限坐标的机器对应，再接数域/权重/指标 adapter；并行推进 G3 完整谱桥，随后选择具体量子误差合同和实验/扩大扇区出口。
