# 客体、演化与意义 / Objects, Evolution, and Meaning

## 3.0 双语学术修订版 · 2026-11-11

原始 UEOT 思想及原始论文作者：钱德桂（Degui Qian）。这是一部围绕客体、
过程、关系、组织、目的、意义与共同生活展开的独立自然哲学著作。
本版完整保留六编三十章、四个附录及全部注释，并以修订后的中文为语义基线
完成整部英文书。ChatGPT 协助写作、编辑与三个原生 AI 审查者的分工检查
已在正文披露；这不构成外部同行评议或出版认可。

| 语言 | 编辑源 | 排印源 | 阅读版 | 编译回执 |
| --- | --- | --- | --- | --- |
| 中文 | [Markdown](UEOT_PHILOSOPHY.md) | [LaTeX](UEOT_PHILOSOPHY.tex) | [PDF](UEOT_PHILOSOPHY.pdf) | [BUILD.json](BUILD.json) |
| English | [Markdown](UEOT_PHILOSOPHY.en.md) | [LaTeX](UEOT_PHILOSOPHY.en.tex) | [PDF](UEOT_PHILOSOPHY.en.pdf) | [BUILD.en.json](BUILD.en.json) |

[版本与权利清单](EDITION_MANIFEST.json) · [实际变更](EDITION_CHANGES.md) ·
[三十章论证与双语对应](CHAPTER_ALIGNMENT.md) · [中英术语](BILINGUAL_TERMINOLOGY.md) ·
[学术审查、文献核验与逐页检查](review/BILINGUAL_EDITION_2026-11-11/README.md) ·
[可复现构建](BUILDING.md) · [版权边界](PUBLICATION_RIGHTS.md)

本版以 main `3d443ec29eb17af1fc00699a74e2d42d73516d81` 的哲学 2.0 为编辑基线。
原始 43 页论文、ZIP、展开来源、数学书、物理书、Lean 和冻结研究证据只读。
正文分别说明原始思想、条件数学结论、独立哲学论证、外部文献与尚待经验检验的主张。
数学状态仍按该基线为 `CLASSIFIED_CORE_CLOSED`，经验支持仍为 `UNVERIFIED`；
本次哲学编辑与英文写作不改变这两个判断。

最终 PDF 的物理页数为中文 **100 页**、英文 **147 页**，两卷各自编号。
正文与附录印刷页分别为 1—96、1—143；封面和三页目录另计。

## 历史版本记录

以下条目记载各自发行时点。PR #447 的中文哲学 PDF 为 98 页；
旧回执、页数和指纹只绑定相应历史产物，不用于本次 3.0 的验收。
当前版的实际文件身份和检查范围见上方清单与审查目录。

## 2026-11-11：精确增长参数分类

在已冻结 Core 之上完成一个另行授权的有限数学单元：只放宽概率参数前提，保留原物理事务、两个内部程序、全部公开历史实随机策略、钱包、stop、拒绝与忠实遗传。精确全策略增长因子为 max(1, λ₀, λ₁)，并给出两个既有内部程序达到的充要条件、平手和临界边界。三个新增 Lean 模块由原公共入口导出；数学总论第四部分和哲学第七、十一章消费结果。

[定理、实际端点与本轮验证](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_growth_classification_v1/README.md)绑定这次变更；前一冻结包继续绑定 PR #446 的原发行产物。原 Valid 与选择反馈合同保持，CLASSIFIED_CORE_CLOSED 和经验 UNVERIFIED 不变。完成五项出口后本单元停止，不自动启动其他研究。

## 2026-11-11：有限加固后冻结

当前 Core 保持 `CLASSIFIED_CORE_CLOSED`，本版完成有限定本加固并停止自动扩题。两书将一次新生与完整未来预测、任务依赖的 2／3／4 最小表示，以及同源三公开响应的局部秩三归入现有正文；明确同一程序的实际恢复、增长目标和比较类，修正历史来源义务的时态。新增补充属于书面证明与精确计算，未冒称新增完整 Lean 端点；经验支持仍为 `UNVERIFIED`。

本轮[冻结报告与独立读者验收](../mathematics/review/CORE_DEFINITIVE_FREEZE_2026-11-11/README.md)、[实际验证](../mathematics/review/CORE_DEFINITIVE_FREEZE_2026-11-11/VALIDATION.json)和[最终选页审查](../mathematics/review/CORE_DEFINITIVE_FREEZE_2026-11-11/VISUAL_REVIEW.json)绑定 PR #446 的冻结产物（当时数学书239页、哲学书97页）；旧审查和 PR444 交付清单继续保留各自发行身份。PDF 导出同时修复了数学书原有的 HTML 锚点丢失，全部内部命名链接均已核对。

## 来源与维护

原始 [43 页 PDF](../UEOT_v3_top.pdf) 与 [LaTeX ZIP](../UEOT_v3_top%5B1%5D.zip) 保持历史地址；展开的七个 LaTeX 来源文件在 [source/original](./source/original/README.md)。旧的提取材料已移入 `source/extracted/`，早期章节脚手架保存在[历史归档](./source/legacy/README.md)。具体字节身份见 [SOURCE_PROVENANCE.json](./source/SOURCE_PROVENANCE.json)。

修改正文时，以 Markdown 为编辑源，同步再生成 LaTeX 和 PDF，并检查实际页面。概念论证的修订、数学证明的变化和经验结果的更新分别说明其依据。生成方法见[两书构建说明](../tools/books/README.md)。

## 2026-11-04 更新

第十章与附录 C 增补同一有限过程中的学习、修复、资源和停止干预：保留实际失败与持续未知原因，区分状态反馈、额外信息的零价值范围及固定流程已最优的情形。技术来源为数学书 §39.75—39.81 与[联合决策交付包](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/joint_decision_closure_v1/README.md)。原完成合同和历史反例保留，数学最优性不替代目的的规范辩护或现实证据。

## 2026-11-06 更新

第八章与附录C增补记忆充分性相对于许可作用和评价成立、规划共享不抹去真实身份、扩大地址权限可能破坏表示。技术依据为数学书 §39.82—39.88 及[决策表示交付包](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/decision_representation_closure_v1/README.md)。本次没有将外部计算成本写成对象内部认知能耗，也未将条件数学提升为经验验证。

## 2026-11-06：允许实验下的机制分辨与最坏决策损失

第十章、第十六章与附录 C 新增：备份价值依赖共同故障结构；有限证据的可分辨性、应对未知机制的最优行动与目的的规范正当性须分别论证。数学书 §39.89—39.95 及[原生执行和定理](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/mechanism_decision_closure_v1/README.md)给出这一合成实例的范围。现实经验支持仍为 UNVERIFIED。

## 2026-11-06：Core 理论定本

本版完成核心声明的分型：已证条件命题、同一真实组织源的正类、精确反例和公开收窄、独立哲学论证及经验未验证分别陈述。数学书新增可独立阅读的七部分核心总论，保留 106 个原 P-ID 与既有章节；哲学书保留六编三十章，以对象—组织—目的为主线补足正面论证、强反对和修订。增长最优仅是有来源的目的分支。

同一受损真实程序在六单位账本下恢复并达到期望增长率最优；实际继承树给出有限时域人口比例概率界，带标记真实谱系和合法表示相容分别证明。代码、完整运行记录、适用范围见[Core 定本交付包](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_theory_closure_v1/README.md)。PDF 的实际构建与选页结果见[两书审查](../mathematics/review/CORE_THEORY_BOOKS_2026-11-08/ROOT_FINAL_VISUAL_REVIEW.json)。原全 Core 条件合同及 PR441、PR442、PR443 保持完成；经验支持 UNVERIFIED。

2026-11-08 的[入口校正记录](../mathematics/review/CORE_READER_ENTRIES_2026-11-08/CORRECTION.json)绑定当时版本的三个入口文件；PR444 的原交付清单继续绑定原发行提交，后继入口更新不回写该历史清单。

## 出版许可说明

[PUBLICATION_RIGHTS.md](PUBLICATION_RIGHTS.md) 保留历史 CC BY 4.0 已授予权利，
并说明本次中文修订和英文新版本的新增表达边界。翻译不使此前合法授权的表达
自动成为独占内容。本次没有修改根 LICENSE、LICENSE_SCOPE.md 或 COPYRIGHT.md。
