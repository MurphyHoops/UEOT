# UEOT 物理学

《UEOT物理学》是钱德桂（Degui Qian）UEOT 理论及其量子物理工作的正式连续总著，稳定文档身份为 **UEOT-PHYSICS**，当前正式整合版为 **3.1**。本目录保存完整正文、阅读版、来源、逐章修订档案和实际复核记录。

本版正文、PDF 与本地数学/程序验收已经完成，当前仓库集成阶段为 **LOCAL_VERIFIED_CI_PENDING**。最终远端提交、PR 与主线工作流须由本版真实回执确认；历史成功记录保留原版本责任。

## 正式正文与阅读入口

| 文件 | 责任 |
|---|---|
| [UEOT_PHYSICS.md](UEOT_PHYSICS.md) | 唯一规范正文；第 0–53 章及附录 A–F，完整推导与稳定命题锚点 |
| [UEOT_PHYSICS.pdf](UEOT_PHYSICS.pdf) | 从规范正文生成的正式阅读版，171 页 |
| [UEOT_PHYSICS.tex](UEOT_PHYSICS.tex) | 同一构建生成的完整 LaTeX 排印源 |
| [SOURCE_MANIFEST.json](SOURCE_MANIFEST.json) | 原有 11 份材料的独立字节身份、历史文本边界和本版 QM 源集 |
| [CHAPTER_DOSSIER.json](CHAPTER_DOSSIER.json) | 54 章及 6 个附录的命题、来源、分类、修订、验证与开放义务 |
| [结构回执](evidence/v3.1/book-structure.json) | 253 个编号小节、161 个稳定锚点、101 个编号结果的实际结构检查 |

本版继承 3.0 版全部 **88 个稳定编号结果**：其中 78 个源自 2.0，10 个在 3.0 新增；第 51–53 章另增加 **13 个编号命题或反例**，总数为 **101**。原有来源标记完整保留，新条目标为 `NEW_IN_3_1`。全书继续涵盖量子基础、测量、连续变量、多体、热与开放系统、QFT/QED、粒子候选、条件三代、相干见证、实际化、拓扑、格点和实验统计。

新增三章将有限内核推进到实际动力学：第 51 章构造随机混合并证明可计算的 TV 误差预算；第 52 章证明实际密度集合紧性、平均态残差与平稳子极限；第 53 章构造对角存活仪器，并真实消费冻结 Core 的 QSD/Perron/Doob 定理。相应数学前提、反例和未完成义务均写入连续正文。

“正式著作完成”是文档和声明论域的交付状态。Core 无条件唯一选择量子理论、现实规范群和质量谱、三代的无附加前提解释、四维非微扰 QFT、量子引力和真实硬件实验，仍各有独立责任。第 31 章的条件三代定理须连同第 36 章高能五色反例及第 49.7 节谱前提阅读。

### 冻结产物身份

| 产物 | SHA-256 |
|---|---|
| Markdown | `d0d495c2d31680ea12f958367eeefcffb44f6df8dd4114884d51f2e2f0da1587` |
| PDF | `89ed7ed69f3e86ae60ea7d7dc36c1b8bc20e48c89ebdd310ab4414136afadcaa` |
| LaTeX | `c2219ee5464c77c2a2232f989d3afd7f2a1261c9e6732049c8544b699429a5f4` |

[实际构建回执](evidence/v3.1/pdf-build.json) 绑定正文、字体、TeX、PDF 及三遍 XeLaTeX 执行。[视觉验收](evidence/v3.1/pdf-visual-review.json) 为 **PASS**：根审阅者实际查看全部 171 页总览和 4 页细图，另有[协作审阅者对 17 页的完整图像检查](evidence/v3.1/pdf-collaborator-review.json)。记录保留一条非阻断注记：附录 B 的 P-QCE-02 链接锚点落在命题标题的前一页，链接有效，阅读时需继续一页。该回执没有宣称所有页逐字高分辨率重读，也没有用编译成功代替视觉验收。

## 分类与证据如何使用

正文采用三个独立字段，定义见第 0.1、48.2 节以及冻结的 [Core–Physics 接口合同](../../interfaces/CORE_PHYSICS_CONTRACT.md)：

| 字段 | 回答的问题 | 值 |
|---|---|---|
| `argument_status` | 文本正在做什么 | D 定义、P 推导、K 外部定理、H 附加假设、S 解释、E 实验/数值或经验输入、N 反例、O 开放问题 |
| `dependency_class` | 结论的依赖与物理角色 | C Core 结果、B 领域桥、S 扇区选择、P 标准物理输入、E 有效模型假设、O 可观测后果、X UEOT 专属开放科学猜想 |
| `verification_kind` | 怎样核对该结论 | `analytic`、`exact_arithmetic`、`synthetic`、`lean`、`experiment` |

3.1 版按[逐章迁移表](evidence/v3.1/classification-migration.json)和[语义说明](evidence/v3.1/CLASSIFICATION_MIGRATION.md)纠正旧版 `dependency_class` 中 E/O/X 的冲突，保留原有论证字母和数学结论。反例继续用 `argument_status=N`；标准数学待形式化或程序开发待办不自动归为 X；依赖 O 也不表示已取得真实实验数据。章级数组是所含角色集合，具体命题仍以正文前提及实际源码类型为准。附录 E 只有出版/编译合同，因此其物理依赖数组为空。

| 当前证据入口 | 已执行范围及限制 |
|---|---|
| [通用 Lean 本地验收](../kernel/evidence/v31.5/lean-verification.json) | 18 模块、334 个显式定理；实际统一构建与源集匹配 |
| [完整命名公理审计](../kernel/evidence/v31.5/proof-axioms.json) | 392 个唯一命名目标，含 334 定理与 58 个列举定义/构造；允许基础仅 `propext`、`Classical.choice`、`Quot.sound` |
| [内核运行检查](../kernel/evidence/v31.5/runtime-verification.json) | 100 个测试方法，与数学定理计数分开 |
| [四份完整演示](../kernel/evidence/v31.5/demos-verification.json) | 实际有限有理计算，含本版混合、平均与生存模型；没有新增实验数据 |
| [具体 Lean 证书](../kernel/evidence/v31.5/lean-exports/verification.json) | 六正例共 42 命名审计；四坏数据须拒绝原真值证明，并通过同数据假值证明及其 4 项审计 |
| [新增有限动力学见证](../kernel/evidence/v31.5/finite-witnesses/verification.json) | 29 个具体定理、10 个定义、39 个命名审计；独立计数，不加进通用 334/392 |
| [新章整合审查](evidence/v3.1/new-chapters-integration-review.json) | 第 51–53 章实际函数名、前提、公式和形式化范围 |
| [本版旧程序源码复用](evidence/v3.1/legacy-source-reuse.json) | 三套旧程序字节未变；3.1 未重跑它们，历史 757 项检查仍由 3.0 原回执负责 |

本版数学/运行的 [64 项源集](../kernel/evidence/v31.5/source-manifest.json) SHA-256 为 `41375f6703b03d95623f7f2fd80006def004b3386c611a12b503ca8d7f8e333e`，作者工作基线为 `97d033ff83125822e9926f5bd36afd08dbd153ef`。基线提交不是“工作树干净”或最终远端源码提交的声明；实际执行输入由逐文件哈希和[源冻结对照](../kernel/evidence/v31.5/source-freeze-reconciliation.json)绑定。

第 49–50 章的实际词响应、闭合坐标、效应上确界、完整通道收缩、误差递推和正事件后验界继续保留。第 51 章的同库 TV 预算不控制任意未知通道，成员变化仍需另证全输入误差；第 52 章不声称唯一稳态、原始轨道收敛或随机单轨经验遍历；第 53 章是给定谱数据的对角测量制备桥，尚非一般非交换 Perron 理论。第 4、35 章的 trace/diamond 纸面理论、一般旁系统及历史寄存器装配也没有因此全体机器化。

### 继承证据的版本责任

[3.0 基础修订审查](evidence/v3.0/core_foundations_review.md)、[高级来源与数学审查](evidence/v3.0/repo_scope_and_advanced_review.md)、[高级装配核对](evidence/v3.0/advanced_assembly_review.json)以及[三套程序的 3.0 执行回执](evidence/v3.0/legacy-regression.json)保留原版本身份。后者的 757 项有限检查为 237 + 423 + 97，含精确算术、浮点及合成计算；本版的源码复用确认不等于重跑，不自动验证后来新增或修订的正文。

本书审查由 AI 代理分工阅读、源码比对、不同计算路径及实际执行构成。它不是独立人类同行评审、期刊审稿或实验室复现；学术原创性与现实物理有效性仍需对应证据。

## 复现正文检查与 PDF

以下命令从仓库根运行。结构检查将附录 B 的条目绑定到实际 HTML 锚点及紧随的完整命题名，防止短编号误匹配更长编号；此门已接入 PDF 构建器。

```bash
python3 physics/qm/book/build/verify_book.py
```

生成阅读版需要 Pandoc、XeLaTeX、常规 TeX 包及 CJK 字体。精确复现本版字形和换行时使用恢复源包中的 **Droid Sans Fallback**；字体 SHA-256 为 `ee38813ea00c3e32add4268fff7fff9e39417b4913cb13be2415164a47807cc2`。下面路径应替换为实际本地字体路径。

```bash
python3 physics/qm/book/build/build_pdf.py \
  --output-dir /tmp/ueot-physics-v3-1-build \
  --font /path/to/DroidSansFallback.ttf
```

构建器只读取当前完整主文，先检查章号、命题身份、内部链接与占位，再生成 LaTeX 并执行三遍 XeLaTeX；不开启 shell-escape。重新渲染时的日期、字体与工具链可能改变二进制，应重新记录实际源、字体、TeX、PDF 与日志哈希，并重新检查页面。

三套继承科学回归需要 NumPy/SciPy。以下命令供另行复跑时使用；它们不表示已在 3.1 本轮执行：

```bash
python3 physics/qm/book/verification/verify_ueot_quantum.py
python3 physics/qm/book/verification/verify_frontier.py
python3 physics/qm/book/verification/verify_completion.py
```

量子内核的工具链、运行检查及具体证明复核遵循[内核 README](../kernel/README.md)与[形式化包 README](../../../formalization/ueot-qm/README.md)。书的结构检查不代替这些验收。

## 持续维护与授权责任

本轮依据用户继续推进 UEOT-QM、维护正式全面总著的既有授权。ClassB/QM 处理领域数学/软件，ClassC/BookAssembly 处理完整正文、修订和阅读版；冻结 Core 的定义、证明与计数保持独立责任。根代理统一整合实际源身份、验证和远端同步。

后续结果写回所属章节、编号、档案和证据，保留旧有效推导与失败路线。扩大结论须新增对应前提、证明或实验；历史 PASS 不自动移植。当前 **LOCAL_VERIFIED_CI_PENDING** 只描述本版本地已验收且远端集成待完成，不使用前一版本的 CI 代替本版回执。
