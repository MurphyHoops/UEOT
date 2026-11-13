# 《UEOT物理学》：公开版本与未来出版许可

作品：《UEOT物理学》／*UEOT Physics*。现行为 v3.10 双语研究增量，
70 章、6 附录，保留 v3.9 的全部188项结果并追加第69章的6项结果。
新增科学文字、AI辅助推导与程序、翻译和出版维护均按作者本轮项目指示完成；
本说明不裁决可能存在的著作权归属，也不增加一般软件或专利许可。
历史公开许可身份基准（不是本次出版源码基线）：仓库 `main` 提交
`3776da6caf06a1c99837b15313d18857346f4baa`（2026-11-11）。

| 内容文件 | 该基准 Git blob SHA-1 |
| --- | --- |
| `UEOT_PHYSICS.md` | `b8f4f03810d41b2e3a92daeadb7fe1d7dc90fd73` |
| `UEOT_PHYSICS.tex` | `f7b7251b03af5f9604fe55bdd9507d3da8514fc1` |
| `UEOT_PHYSICS.pdf` | `b2eb124e174369326107e11d623b8c81edc9b211` |

表中的哈希是 Git blob SHA-1，不是 SHA-256 或作者独占权证明。
这本书 **不是** 一份未公开的未来出版计划；v3.5 的源码、PDF
已经在公开仓库中发布。旧根 LICENSE 对仓库作者原创材料作广泛
CC BY 4.0 授权，因此此前合法授权的书籍表达继续受 CC BY 4.0
保护，第三方材料与外部文献不因此获得新的许可。

未来正式修订版可对真正新增、权属可确认的著作表达独立安排
出版、翻译和商业发行授权。必须逐项区分旧 CC BY 内容、新增原创
内容及第三方材料，并在 Markdown/TeX/PDF 与发行清单中一致标注。
不能仅更换封面、版式或文件格式就撤回已授权文本。

## 本次双语修订的适用范围 / Scope of this bilingual revision

| 材料类别 | 本次处理 |
| --- | --- |
| v3.5及更早已经合法按CC BY 4.0公开的文字 | 原授权持续有效；继承、翻译和重新排版不撤回原授权。 |
| 继承的v3.7／v31.10及更早研究内容 | 保留原始权属、来源及适用许可；本出版修订不对其他研究线的材料重新授权。 |
| 新增双语导读、科学编辑文字、英文译文和新排印表达 | 依仓库现行范围政策，本次不提供额外的概括性许可授予；其依法存在的权利由相应权利人保留，另行明确授权前不得从公开可读推断商业出版许可。 |
| 第三方论文、图表、数据、程序及依赖 | 保留各自许可。本书使用引用和独立说明，不据此将第三方材料改成项目许可。 |
| v31.11新增Lean、Python及合成记录 | 新增操作等价模块、微观/鲁棒计算和证据脚本；依根LICENSE D项不额外授予一般软件许可，不将新代码声明为Apache-2.0。继承代码与Mathlib、NumPy、SciPy、SymPy等依赖保留原条款。只有明确标记的自生成合成记录，没有新增第三方原始实验数据，也没有声明新的CC0授权。 |

The historical CC BY 4.0 grant remains effective for expression already released
under it. This edition does not withdraw that grant or relicense third-party
material. No additional blanket permission is granted here for newly authored
editorial expression, the English translation, or other new protectable material.
Any rights that subsist remain with the respective rightsholders pending an
express grant. Public availability is not, by itself, a new publishing licence.

中文和英文主稿附录E.4均载明同一许可边界，并进入各自的LaTeX及PDF。
新增与继承的准确文件差异由本次Git提交、既有`SOURCE_MANIFEST.json`、
`CHAPTER_DOSSIER.json`及双语结果映射记录。历史版本快照保留其原字节，
不因本修订重写旧许可记录。内部AI协作审查不表示出版社、期刊或外部
同行已经认可本书，也不构成作者权属裁决。

v3.8的新增与继承划分由第67章、九项稳定编号、现行源清单及
`evidence/v3.8/prior/`中的原v3.7清单共同给出。三名研究子智能体的独立草案、
交叉审查及主智能体集成在`../audits/OPERATIONAL_MICRO_ROBUST_v31.11/`登记。
原始论文只被引用与独立解释，没有把论文全文、出版社图表或依赖软件包复制
进本版。源代码的公开可读与可复现不构成一次新的通用软件许可发布；
未来另选软件许可仍须遵循既有贡献、依赖与授权审查要求。

Edition 3.8 appends Chapter 67 and nine stable results while retaining all
173 prior result identities. Its existing historical grants and edition-specific
notice remain unchanged. The new AI-assisted code and synthetic records are
identified by the source and execution manifests; this revision grants no
additional general software, patent, or CC0 permission. Dependencies retain
their own terms. No third-party paper, publisher figure, or raw experimental
dataset is newly redistributed by this increment.

物理著作的版权与 `../../../formalization/ueot-qm/` 的 Lean 软件、
`../kernel/` 的 Python 计算内核、`../benchmarks/` 的脚本、
外部实验数据分别管理。本文件不修改这些软件或数据的实际许可，
也不宣称物理理论已经得到实验证实。

参阅 [物理研究许可说明](../../LICENSING.md)、
[根许可证](../../../LICENSE)、
[版权政策](../../../COPYRIGHT.md)与
[范围矩阵](../../../LICENSE_SCOPE.md)。


## v3.9 增量范围 / Edition 3.9 increment

本轮第68章六项结果、分段增长与省略计算、内部 AI 审查及新执行回执由 `../audits/GROWING_CUTOFF_v31.12/`、`../growing_cutoff/` 和 `evidence/v3.9/` 标识。原182项结果对象、历史许可和执行身份保留。新增内容没有机器形式化或外部实验确认的隐含声明；没有引入第三方原始器件数据或新的概括性软件许可。

Edition 3.9 adds six paper results, independently checked code and observed execution evidence while retaining all182 prior result objects. The historical and edition-specific permission boundaries above continue unchanged. Public readability is not an additional blanket publishing or software licence.

## 3.10 / v31.13 增量范围

本增量增加同时动力学的书面误差证明、一个有限压缩反例、联合校准及整数区间预测程序、明确标识的合成有序记录和双语第69章。没有新增 Lean 声明或第三方原始器件数据。新增与继承材料继续适用上文既有范围，不新增一般许可，不改写历史授权。NumPy、SciPy、SymPy、mpmath及排版依赖保持各自条款；公开可读不自动产生新的商业出版许可。
