# UEOT Core 后继参考规范 / Successor Reference Specification

## 定位

本目录是 **独立后继扩展规范 1.0，采用出口 B**。冻结 Core v3.0 继续定义原 106 个 P-ID；本补充用 30 个 `CSX-` 合同集中登记后继数学的输入、假设、量词、来源、反例与消费者责任。它不是 Core v4.0，也不是数学著作 v4.1 的重命名。

**先读正文，再调用来源：**

- [中文规范](UEOT_Core_Successor_Specification.md)
- [English specification](UEOT_Core_Successor_Specification.en.md)
- [范围与 A/B/C 架构裁决](CORE_V3_TO_CURRENT_DELTA.md)

## 合同范围

| 内容 | 合同 |
|---|---|
| 类型化复用、校准、实际预测与有限记忆 | CSX-01—04 |
| 同源安全控制、部署误差、支持可行性、注册采样风险 | CSX-05—08 |
| 目标 gauge、二维因子、连续消费者与谱来源 | CSX-09—13 |
| literal 生命周期、有限钱包联合决策、接受后正确的图、机制后悔 | CSX-14—17 |
| 付费再生、形成、全策略增长、参数 iff、真实反馈、谱系与合法商 | CSX-18—25 |
| 书面 2／3／4 分类、秩三边界、有限响应表载体 | CSX-26—28 |
| 完整随机分析源底座；真实资源、恢复检查与全价格目的 | CSX-29—30 |

每个合同包含十二字段，完整区分数学结论、既有 Lean、可执行检查、书面证明和经验适用性。一般来源工厂与具体有限消费者并列，保留它们各自的论域。自然经验支持仍为 **UNVERIFIED**。

## 可追溯接口

- [CLAIM_INDEX.json](CLAIM_INDEX.json)：30 个合同、163 个明确后继端点、62 个定义文件、33 个证据文件；包括实际源 SHA、公共 import 路线、双语公式和本文档 SHA。
- [V3_PROPOSITION_INTERFACE_MAP.json](V3_PROPOSITION_INTERFACE_MAP.json)：原 106 个 P-ID 逐项映射、163 个原登记源向声明，以及后继关联。这里的原声明数恰好也为 163；它与上一项后继端点是两个不同集合，不能混作覆盖率。
- [证明来源与消费者矩阵](review/PROOF_SOURCE_AND_CONSUMER_MATRIX.md)：现有证据的实际范围及复用条件。

冻结源仍为 183440 字节、3983 行、106 个唯一 P-ID，SHA-256 `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`。`manifest.yaml` 的 `active_core` 保持 3.0；原 106/106 FULL-GREEN 不被新合同重新计数。

## 审查、验证与采用

- [REVIEW.md](REVIEW.md)：三名原生审查者的分工、发现、修正及真实候选身份。
- [VALIDATION.md](VALIDATION.md)：可重跑的静态检查及实际结果。
- [DOWNSTREAM_BOOK_ADOPTION.md](DOWNSTREAM_BOOK_ADOPTION.md)：三书的采用动作、九处 Lean 旧链接修正位置和领域边界。

来源基线是当前任务开始核对的 main `16a89154183c22030d4526413167d095d94e6890`，不是任务书提及的旧切片。本目录的建立不改写三书、Lean 生产源码、历史 proof receipt 或原覆盖账本。实际 GitHub 集成由对应 PR/main 决定；这里不把本地候选或静态 PASS 当作合并事实。

## English reading guide

This independent 1.0 supplement implements **exit B**: preserve frozen Core v3.0 and add 30 successor contracts, each with twelve fields. Start with the English specification, use the claim index to locate actual definitions, and retain every source, quantifier, resource and information premise.

The 163 successor endpoints and the 163 legacy source-facing declarations are separate inventories; neither changes the 106 source-proposition denominator. Existing Lean, source-matched receipts, executable consumers and written results are explicitly distinguished. The 2/3/4 classification and rank-three argument retain their written-proof status. Empirical applicability remains UNVERIFIED. Review, validation and book adoption are linked above.
