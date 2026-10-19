# UEOT 物理学

《UEOT物理学》是钱德桂（Degui Qian）UEOT 理论及其量子物理工作的正式连续总著，稳定文档身份为 **UEOT-PHYSICS**，当前版本 **3.0**。本目录保存完整正文、派生阅读版、来源身份、逐章修订档案和实际复核记录，作为后续建设的固定入口。

## 正式正文与阅读入口

| 文件 | 责任 |
|---|---|
| [UEOT_PHYSICS.md](UEOT_PHYSICS.md) | 唯一规范正文；第 0–50 章及附录 A–F，完整推导与稳定命题锚点 |
| [UEOT_PHYSICS.pdf](UEOT_PHYSICS.pdf) | 从规范正文生成的正式阅读版，160 页 |
| [UEOT_PHYSICS.tex](UEOT_PHYSICS.tex) | 同一构建生成的完整 LaTeX 排印源 |
| [SOURCE_MANIFEST.json](SOURCE_MANIFEST.json) | 原始五源、旧总著及历史文本见证的实际身份和使用边界 |
| [CHAPTER_DOSSIER.json](CHAPTER_DOSSIER.json) | 全部 51 章及 6 个附录的命题、来源、修订、验证与开放义务 |
| [book-structure.json](evidence/v3.0/book-structure.json) | 实际章节、锚点和命题注册身份检查 |

本版完整继承旧总著第 0–48 章的主题与 **78 个稳定编号结果**，补入第 49–50 章的 **10 个编号命题**，共 **88 个**。正文包含量子基础、测量、连续变量、多体、热与开放系统、QFT/QED、粒子候选、条件三代、相干见证、实际化、拓扑、格点和实验统计，新增有限量子内核与实际 Born 概率误差传播。它是一部已完成整合和校核的正式著作；后续结果继续写回所属章节和编号。

“正式著作完成”描述文档和声明论域的交付状态。Core 无条件唯一选择量子理论、现实规范群和质量谱、三代的无附加前提解释、四维非微扰 QFT、量子引力以及真实硬件实验仍有正文列明的开放义务。第 31 章的条件三代结果必须连同第 36 章高能五色反例及第 49.7 节谱前提阅读。

### 冻结产物身份

| 产物 | SHA-256 |
|---|---|
| Markdown | `510d1a08a2b4808e08d058628310727ec7ec48348bd21d96e47c04a450875379` |
| PDF | `20401334130d8cfda9be33a3c654d4284c7daf9a9666033130b93e7b8f5ffdae` |
| LaTeX | `4674e7cc33d0b8d04a3ef52e2f94c5e4270978ac10feed2a0fb9979ec758f9ee` |

PDF 的最终视觉验收已由外部记录 [pdf-visual-review.json](evidence/v3.0/pdf-visual-review.json) 给出 **PASS**：两名协作 AI 审阅者完成全部 160 页的缩略总览，并细看记录中列明的公式、表格和修正页面；这不是对所有页面逐行高分辨率重读。该记录绑定上述正文、PDF 和 TeX。本 README 不以编译成功替代视觉验收。实际 [构建环境](evidence/v3.0/build-environment.json) 记录 Pandoc 3.1.3、TeX Live 2023、Python 及字体身份。重新渲染时，PDF 日期、字体和工具链可能使二进制不同；应重新保存本次实际源、字体、TeX、PDF 与日志哈希。

## 证据如何使用

正文使用三个独立字段，定义见第 0.1、48.2 节：

| 字段 | 回答的问题 | 值 |
|---|---|---|
| `argument_status` | 文本正在做什么 | D 定义、P 推导、K 外部定理、H 附加假设、S 解释、E 经验输入、N 反例、O 开放问题 |
| `dependency_class` | 结论从哪里来 | C Core、B 领域桥、S 扇区选择、P 标准物理输入、E 经验输入、O 开放机制、X 排除/反模型 |
| `verification_kind` | 怎样核对该结论 | `analytic`、`exact_arithmetic`、`synthetic`、`lean`、`experiment` |

两个字段中的 P/S 含义不同，保存或引用状态时必须携带字段名。章级档案列出本章实际使用的类别；具体命题的前提与范围仍以正文和源码类型为准，不能给整章套一个 FORMAL 标签。

| 证据入口 | 已执行范围及限制 |
|---|---|
| [旧主文程序的本版重跑](evidence/v3.0/legacy-regression.json) | 三套程序共 757 项有限检查：237 + 423 + 97；精确算术与浮点/合成计算，未使用真实实验数据 |
| [基础修订审查](evidence/v3.0/core_foundations_review.md) | 原始思想、冻结 Core、OPT 背景、分支商、写入等距与酉、有限闭合及反模型 |
| [高级来源与数学审查](evidence/v3.0/repo_scope_and_advanced_review.md) | 对称/域/统计、QFT/QED、谱与实际化等高级正文及历史来源边界 |
| [高级章节装配核对](evidence/v3.0/advanced_assembly_review.json) | 修订片段身份、顺序装配和旧章节/锚点保存 |
| [通用 Lean 构建](../kernel/evidence/v31.4/lean-verification.json) | 15 模块、256 个显式定理；仅覆盖实际声明的条件与论域 |
| [完整命名公理核对](../kernel/evidence/v31.4/proof-axioms.json) | 287 个命名目标；允许基础为 `propext`、`Classical.choice`、`Quot.sound` |
| [内核运行检查](../kernel/evidence/v31.4/runtime-verification.json) | 87 个运行测试；不同于数学定理计数 |
| [具体 Lean 证书](../kernel/evidence/v31.4/lean-exports/verification.json) | 六个正例、四种数据篡改；坏数据须同时拒绝原真值证明并通过同数据假值证明 |

第 49 章以实际有限 Kraus、全词响应、有限生成和精确证书承载内核；第 50 章以全效应上确界证明完整通道收缩、真实输出缺陷、轨迹误差和正事件后验界。第 4、35 章的 trace/diamond 纸面理论以及一般旁系统、历史寄存器装配，不随这些有限 Lean 结果自动成为机器证明。无限维、重型重构、完整 QFT 和现实谱也不在该形式化清单内。

本版交叉审查由 AI 代理协作完成，包括分工阅读、相互检查、反例核对和统一实际执行。这里“独立核对”指不同计算路径、源码比对或不同代理的交叉检查；**不是独立人类同行评审、期刊审稿或实验室复现**。学术原创性、同行评议与现实物理有效性仍须各自的证据。

## 复现正文检查与 PDF

以下命令从仓库根运行。结构检查使用 Python 标准库，以实际 HTML 命题锚点及其紧随的完整命题名核对附录 B；短编号不得通过其他长编号的后缀匹配。这一门已接入 PDF 构建器。

```bash
python3 physics/qm/book/build/verify_book.py
```

生成阅读版需要 Pandoc、XeLaTeX、常规 TeX 包，以及本版使用的 **Droid Sans Fallback** 中文字体文件。精确复现本版字形和换行时，向 `--font` 传入恢复源包中的字体；其 SHA-256 为 `ee38813ea00c3e32add4268fff7fff9e39417b4913cb13be2415164a47807cc2`。下面路径应替换为字体的实际本地路径。

```bash
python3 physics/qm/book/build/build_pdf.py \
  --output-dir /tmp/ueot-physics-v3-build \
  --font /path/to/DroidSansFallback.ttf
```

构建器只读取当前完整规范正文，先检查章号、命题身份、内部链接和占位，再生成 LaTeX 并执行三遍 XeLaTeX；不开启 shell-escape。输出目录包含 `pdf-build.json`、打印源、TeX、PDF 和三次编译日志。可另用合适 CJK 字体构建新的阅读版，但必须记录新字体身份并重新检查页面，不能冒用本版 PDF 哈希或视觉回执。

三套科学回归需要 NumPy/SciPy；本次实际环境和每项程序身份见 `legacy-regression.json`。重新执行可分别运行：

```bash
python3 physics/qm/book/verification/verify_ueot_quantum.py
python3 physics/qm/book/verification/verify_frontier.py
python3 physics/qm/book/verification/verify_completion.py
```

量子内核的 Lean 工具链、依赖、运行测试及具体证书复核遵循 [内核 README](../kernel/README.md) 和 [形式化包 README](../../../formalization/ueot-qm/README.md)。书的结构检查不代替这些验证。

## 持续维护与授权责任

本轮工作来自用户继续推进 UEOT-QM、构建正式全面且可持续维护总著的直接授权。ClassB/QM 工作保持在量子领域扩展；ClassC/BookAssembly 对既有全书进行正式整合、纠错、增补和生成阅读版。根代理负责各分工的整合、源身份核对、统一验收与按现有授权完成仓库同步。该权限不意味着冻结 Core 的数学定义、证明和计数已被授权改写，也不等于人类学术审稿。

后续每次变更均同步更新本目录的规范正文、受影响章节档案、证据和阅读版；保留原有命题编号及失败路线。扩大结论范围时增加真正对应的前提、证明或实验记录；修改后由实际源哈希绑定结果，历史 PASS 不自动移植。远端提交和工作流的成功状态以对应真实回执为准，不能把本地构建改称远端执行。
