# UEOT 数学著作

本目录维护独立的数学主文，包括定义、明确假设、定理与证明、反例、算法，以及可核查的 Lean 对应。

- [完整 Markdown 主文](./UEOT_MATHEMATICS.md)
- [完整来源与 Lean 对应索引](./UEOT_MATHEMATICS_SOURCES.md)
- [现行 Lean 接口的范围说明](./LEAN_API_SCOPE.md)
- [PDF 阅读版](./UEOT_MATHEMATICS.pdf)
- [LaTeX 排版源](./UEOT_MATHEMATICS.tex)
- [编译记录](./BUILD.json)
- [2026-10-26 数学闭环审查与执行方案](./review/MATHEMATICAL_CLOSURE_AUDIT_2026-10-26.md)：当前证明范围、未发布候选、详细数学义务与后续接续卡；独立于本书出版版本。

本版保留原 Core 第 0—31 章和附录，并逐章补充后续形式化的实际范围。第 32—38 章进一步展开层级压缩、关系缺陷与校准、客体和目的接口、同源统一闭合、实际占据、有限支持可行性与注册选择后的联合风险。历史代码与历史运行输出保留各自的身份；新的编译和检验不能替代旧的执行记录。

## 2026-11-11：精确增长参数分类

在已冻结 Core 之上完成一个另行授权的有限数学单元：只放宽概率参数前提，保留原物理事务、两个内部程序、全部公开历史实随机策略、钱包、stop、拒绝与忠实遗传。精确全策略增长因子为 max(1, λ₀, λ₁)，并给出两个既有内部程序达到的充要条件、平手和临界边界。三个新增 Lean 模块由原公共入口导出；数学总论第四部分和哲学第七、十一章消费结果。

[定理、实际端点与本轮验证](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_growth_classification_v1/README.md)绑定这次变更；前一冻结包继续绑定 PR #446 的原发行产物。原 Valid 与选择反馈合同保持，CLASSIFIED_CORE_CLOSED 和经验 UNVERIFIED 不变。完成五项出口后本单元停止，不自动启动其他研究。

## 2026-11-11：有限加固后冻结

当前 Core 保持 `CLASSIFIED_CORE_CLOSED`，本版完成有限定本加固并停止自动扩题。两书将一次新生与完整未来预测、任务依赖的 2／3／4 最小表示，以及同源三公开响应的局部秩三归入现有正文；明确同一程序的实际恢复、增长目标和比较类，修正历史来源义务的时态。新增补充属于书面证明与精确计算，未冒称新增完整 Lean 端点；经验支持仍为 `UNVERIFIED`。

本轮[冻结报告与独立读者验收](review/CORE_DEFINITIVE_FREEZE_2026-11-11/README.md)、[实际验证](review/CORE_DEFINITIVE_FREEZE_2026-11-11/VALIDATION.json)和[最终选页审查](review/CORE_DEFINITIVE_FREEZE_2026-11-11/VISUAL_REVIEW.json)绑定 PR #446 的冻结产物（当时数学书239页、哲学书97页）；旧审查和 PR444 交付清单继续保留各自发行身份。PDF 导出同时修复了数学书原有的 HTML 锚点丢失，全部内部命名链接均已核对。

## 冻结来源与新增工作

[Core Mathematics v3.0 原文](./source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md) 与旧规范账本记录的 SHA-256 完全一致：

`ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`

它的 106 个 P-ID 保持冻结。新书是另一个持续维护的版本，新增章节和更精确的边界说明不自动改变已有 P-ID 覆盖状态。三份提供的历史科学接口资料完整保存在 `source/roadmaps/`。

数学证明接受给定模型与假设；从中得到现实对象、经验定律或规范结论，还要说明相应接口。独立的[哲学著作](../philosophy/README.md)对这些哲学问题给出自己的论证。

生成方法见[两书构建说明](../tools/books/README.md)。文档编译记录与 Lean 证明证据分别维护。

## 2026-11-04：有限钱包联合决策

新增数学书 §39.75—39.81：一次持久未知源、同一钱包与信息协议的实际返回表、原生有限人口 Store、一般期限参数式及反向边界。原全 Core 条件数学合同和八项验收保持完成。证明、实际表、完整有理重放与准确边界见[联合决策交付包](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/joint_decision_closure_v1/README.md)。本次两书构建与选页审查另见[审查目录](review/CORE_JOINT_DECISION_BOOKS_2026-11-04/)。

## 2026-11-06：许可历史的决策充分表示

新增 §39.82—39.88 与附录F：源导出的收据观察器、计数后验、全动作联合充分性、认证共享DAG、原生执行/逐前缀付款、实际节点界与可达正反例。四旧例与预登记八步双写钱包的THIS产物、成本和准确边界见[决策表示交付包](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/decision_representation_closure_v1/README.md)。数学书221页、哲学书89页；实际选页范围及修订记录见[本轮两书审查](review/DECISION_REPRESENTATION_BOOKS_2026-11-06/)。原两项完成合同保持完成，经验支持仍UNVERIFIED。

## 2026-11-06：允许实验下的机制分辨与最坏决策损失

数学书新增 §39.89—39.95 和附录 F 入口：同源 S/G 故障、联合后验、实随机实验的分辨界以及未知机制时的最小最坏后悔。[定理与执行](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/mechanism_decision_closure_v1/README.md)；[本次两书实际选页审查](review/MECHANISM_DECISION_BOOKS_2026-11-06/ROOT_FINAL_VISUAL_REVIEW.json)。

## 2026-11-06：Core 理论定本

本版完成核心声明的分型：已证条件命题、同一真实组织源的正类、精确反例和公开收窄、独立哲学论证及经验未验证分别陈述。数学书新增可独立阅读的七部分核心总论，保留 106 个原 P-ID 与既有章节；哲学书保留六编三十章，以对象—组织—目的为主线补足正面论证、强反对和修订。增长最优仅是有来源的目的分支。

同一受损真实程序在六单位账本下恢复并达到期望增长率最优；实际继承树给出有限时域人口比例概率界，带标记真实谱系和合法表示相容分别证明。代码、完整运行记录、适用范围见[Core 定本交付包](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_theory_closure_v1/README.md)。PDF 的实际构建与选页结果见[两书审查](../mathematics/review/CORE_THEORY_BOOKS_2026-11-08/ROOT_FINAL_VISUAL_REVIEW.json)。原全 Core 条件合同及 PR441、PR442、PR443 保持完成；经验支持 UNVERIFIED。

2026-11-08 的[入口校正记录](../mathematics/review/CORE_READER_ENTRIES_2026-11-08/CORRECTION.json)绑定本版三个入口文件；PR444 的原交付清单继续绑定原发行提交。
