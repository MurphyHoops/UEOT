# UEOT 物理学

《UEOT物理学》是钱德桂（Degui Qian）UEOT 理论及其量子物理工作的正式连续总著，稳定文档身份为 **UEOT-PHYSICS**，当前正式整合版为 **3.2**。本目录保存完整正文、阅读版、原始来源、逐章证明责任及实际验证记录。

本版正文、数学与程序的统一本地验收、排印及实际视觉检查已完成，当前状态为 **LOCAL_VERIFIED_CI_PENDING**。本地结果由[本版发布门记录](evidence/v3.2/local-release-gates.json)及[统一证明回执](../kernel/evidence/v31.6/lean-verification.json)绑定。远端源提交与合入后主线 CI 由根代理另行登记；这里没有把本地通过写成远端通过。

## 正式正文与阅读入口

| 文件 | 责任 |
|---|---|
| [UEOT_PHYSICS.md](UEOT_PHYSICS.md) | 唯一规范正文；第 0–56 章、附录 A–F，完整推导与稳定命题锚点 |
| [UEOT_PHYSICS.pdf](UEOT_PHYSICS.pdf) | 同一规范正文的正式阅读版，186 页 |
| [UEOT_PHYSICS.tex](UEOT_PHYSICS.tex) | 同一真实构建产生的完整 LaTeX 排印源 |
| [SOURCE_MANIFEST.json](SOURCE_MANIFEST.json) | 保留 11 份原材料的独立身份，登记历史文本、旧程序及本版 70 项 QM 源集 |
| [CHAPTER_DOSSIER.json](CHAPTER_DOSSIER.json) | 57 章及 6 附录的来源、分类、结果、修订、机器范围与开放义务 |
| [实际结构检查](evidence/v3.2/book-structure.json) | 272 个章内编号小节、180 个稳定锚点、117 个编号结果及真实命题注册表 |
| [本版档案清单](evidence/v3.2/archive-manifest.json) | 正文、派生文件和本版证据文件的实际哈希 |

本版完整保留原有 **101 个稳定编号结果**：78 项来源于 2.0，10 项为 `NEW_IN_3_0`，13 项为 `NEW_IN_3_1`。第 54–56 章新增 **16 项命题或反例**，按 5／5／6 分布，标为 `NEW_IN_3_2`。各条旧 `origin` 保持原值；编号不是原创性、自然规律、Lean 定理或实验确认的替代计数。

全书继续涵盖量子基础、测量、连续变量、多体、热与开放系统、QFT/QED、粒子候选、条件三代、相干见证、实际化、拓扑、格点和实验统计。正式著作的内容完成与自然界理论的最终完成分别承担证据责任。Core 无条件唯一选择复量子理论、现实规范群与质量谱、三代的无附加前提解释、四维非微扰 QFT、量子引力及真实实验检验仍有明确开放任务。条件三代定理须连同第 36 章的高能五色反例和第 49.7 节的谱前提阅读。

## 本轮三条核心进展

| 章节 | 实际完成内容 | 适用边界 |
|---|---|---|
| 第 54 章：同一 Core 过程上的经典纯化边界 | 完整经典单纯形中的凸极点纯性；任意有限辅助系统的无纯化；同一冻结随机核、真实终端／控制商、安全轨迹及时间 1 商边际；受限读出控制 | 列明的 H1–H6 有限 Core 切片，经典状态、读出及复合解释公开输入；不把一个模型当作全部 106 项的物理完成 |
| 第 55 章：实局域层析分离 | 两个不同实联合密度态对全部实局域产品效应不可区分；合法实联合效应给出 1／0；复局域产品给出 1/2／0；任意有限实产品线性张成的否定 | 真实 Density／Effect 和标准复合结构下的有限证书；完整实 OPT、ESP 与复量子唯一重构仍独立承担责任 |
| 第 56 章：保留相干的量子 Doob 通道 | 左谱条件推出实际 Kraus 完备性；全算符有限交织及任意初态真实有限条件化；额外右谱态给几何生存和平稳；精确有理非对角全矩阵实例 | 正可逆谱数据是明确条件；归一化过滤通常非线性，8/5 是归一化因子；一般谱存在、唯一性和无限时条件极限仍待证明 |

[新章整合审查](evidence/v3.2/new-chapters-integration-review.json)和[章节档案最终核对](evidence/v3.2/dossier-review.json)把 16 项新编号逐条连接到实际源码声明、输入量词和科学边界。[三线 focused 档案](../kernel/evidence/v31.6/focused/files-manifest.json)保留作者、互审、实际成功与失败记录，并区分未运行的审计输入与真正通过的回执。

此前第 49–50 章的实际词响应、闭合坐标、效应距离、通道收缩及正事件后验界继续保留；第 51–53 章的同库混合 TV 预算、Cesàro 平稳子列及实际对角 Core QSD／Doob 桥也保持其原范围。一般旁系统、无限维和完整物理背景不会因有限包通过而自动得到机器证明。

## 冻结产物与真实验收

| 产物 | SHA-256 |
|---|---|
| Markdown | `6289bebfbd4ae0efe5ac2257f6ac15efb37fb7b95bb78612367818eb5d6e4fd4` |
| PDF | `51de239d72d1fb3659fdeb7b7d951c031a5c01913315c88bedb86ec348b5e57a` |
| LaTeX | `f7a3707e55787cb788f63e4a6551f5c5fa0aa776c3a5961dd56ea7ae5503913f` |

[排印回执](evidence/v3.2/pdf-build.json)绑定实际主文、字体、TeX、PDF 和三遍 XeLaTeX 日志，三个执行退出码均为 0，没有登记版面警告。[视觉总回执](evidence/v3.2/pdf-visual-review.json)记录根代理此前对 186 页总览及 5 个完整页面的实际观察，以及[协作审阅者对 24 个完整页面的实际检查](evidence/v3.2/pdf-collaborator-review.json)。最后调整规划段后，逐页 RGB 栅格检查确认 185 页完全相同，仅第 154 页改变；根代理与协作审阅者均实际复看了最终第 154 页。回执分别绑定原始实际观察、前后 PDF 身份、精确相同页面的继承和变化页的新观察。

| 当前证据 | 实际通过范围 |
|---|---|
| [统一 Lean 本地验收](../kernel/evidence/v31.6/lean-verification.json) | 22 模块、459 个显式定理，实际统一构建通过 |
| [完整命名公理审计](../kernel/evidence/v31.6/proof-axioms.json) | 573 个唯一命名目标：459 定理与 114 个列举非定理目标；基础仅 `propext`、`Classical.choice`、`Quot.sound` |
| [依赖身份](../kernel/evidence/v31.6/dependency-identity.json) | 固定 Lean 4.33.1、编译器提交和九项 Git 依赖的实际身份 |
| [实际 Core 导入闭包](../kernel/evidence/v31.6/core-import-closure.json) | 56 个实际递归导入 Core 源与构建身份；与冻结基线一致，未回写 Core |
| [内核运行检查](../kernel/evidence/v31.6/runtime-verification.json) | 100 个实际测试方法，与 Lean 定理及实验分开计数 |
| [四份完整演示](../kernel/evidence/v31.6/demos-verification.json) | 四个有限计算程序实际执行并解析输出；没有新增实验数据 |
| [具体 Lean 证书](../kernel/evidence/v31.6/lean-exports/verification.json) | 六正证书共 42 项审计；四坏数据拒绝原真值证明，并通过同数据假值证明及其 4 项审计 |
| [有限专用见证](../kernel/evidence/v31.6/finite-witnesses/verification.json) | 四组、62 个具体定理、22 个定义、84 项独立审计；不加入主包 459／573 |

主包本轮新增 125 个显式定理及 56 个其他命名目标，共 181 项新增审计，包含两项结构构造器和三项有意公共的商类型实例。主包既有通用数学，也包含明确的有限 Core 模型；源码定义或模型选择不会计成新的物理规律。

本轮实际执行绑定[70 项源清单](../kernel/evidence/v31.6/source-manifest.json)，源集 SHA-256 为 `8a2cea35e060f5341f5672534d0717c605f5c441d998a08cc7677fb50a113115`，已发布科学基线为 `427f512745ca70f82cba6a1388edcab904da8a42`。[源冻结核对](../kernel/evidence/v31.6/source-freeze-reconciliation.json)确认执行前后输入字节一致。本地历史 HEAD、科学基线、实际源集与最终远端提交分别记录。

## 分类和历史证据责任

正文和章节档案沿用冻结的 [Core–Physics 接口合同](../../interfaces/CORE_PHYSICS_CONTRACT.md)，分别登记三个状态轴：

| 字段 | 含义 |
|---|---|
| `argument_status` | D 定义、P 推导、K 外部标准定理、H 附加假设、S 解释、E 实验／数值或经验输入、N 反例、O 开放问题 |
| `dependency_class` | C 已有 Core 结果、B 领域桥、S 扇区选择原则、P 标准物理输入、E 有效模型假设、O 可观测后果、X UEOT 专属开放科学猜想 |
| `verification_kind` | `analytic`、`exact_arithmetic`、`synthetic`、`lean`、`experiment` |

3.1 的[分类迁移表](evidence/v3.1/classification-migration.json)及[语义说明](evidence/v3.1/CLASSIFICATION_MIGRATION.md)继续保留。反例以 `argument_status=N` 表示；一般数学待形式化或程序开发待办不会自动归入 X；依赖 O 也不表示已经取得真实实验数据。章级分类是所含角色集合，具体结论以正文前提及真实源码类型为准。出版流程章节不套物理依赖分类。

本版[旧程序身份核对](evidence/v3.2/legacy-source-reuse.json)确认三套可执行源文件及正文内嵌程序块与既有版本一致，没有重新执行它们。历史 **757 项检查＝237＋423＋97** 继续归属[3.0 的实际执行](evidence/v3.0/legacy-regression.json)，不能替代本轮新增结论的证据。原 11 份材料的登记身份和历史缓存文本的边界原样保留；最终归档没有假称重新读取所有原始附件。

3.0 的[基础审查](evidence/v3.0/core_foundations_review.md)、[高级来源审查](evidence/v3.0/repo_scope_and_advanced_review.md)、[装配核对](evidence/v3.0/advanced_assembly_review.json)及 3.1 的[主线验收](../kernel/evidence/v31.5/integration-verification.json)保留各自版本身份。AI 代理的作者、互审、源码对照与实际执行不等于独立人类同行评审、期刊审稿或实验室复现。

## 复现正文检查和阅读版

从仓库根检查完整章节、附录、稳定编号、实际命题锚点和注册表：

```bash
python3 physics/qm/book/build/verify_book.py
```

阅读版构建需要 Pandoc、XeLaTeX、常规 TeX 包及 CJK 字体。本版实际字体为 **Droid Sans Fallback**，SHA-256 为 `ee38813ea00c3e32add4268fff7fff9e39417b4913cb13be2415164a47807cc2`。将下列字体路径替换为实际本地位置：

```bash
python3 physics/qm/book/build/build_pdf.py \
  --output-dir /tmp/ueot-physics-v3-2-build \
  --font /path/to/DroidSansFallback.ttf
```

构建器先核正文结构，再生成排印源并执行三遍 XeLaTeX，不开启 shell-escape。日期、字体和工具链变化可能改变二进制，需要记录实际哈希并检查新页面。单独重新执行旧科学回归时使用下列命令；它们不表示 3.2 本轮已经重跑：

```bash
python3 physics/qm/book/verification/verify_ueot_quantum.py
python3 physics/qm/book/verification/verify_frontier.py
python3 physics/qm/book/verification/verify_completion.py
```

内核构建、运行及证明产品遵循[内核 README](../kernel/README.md)和[形式化包 README](../../../formalization/ueot-qm/README.md)。正文结构检查和版面检查分别承担各自职责。

## 后续推进与维护

本轮依据用户继续推进 UEOT-QM、维护正式全面总著的既有授权。ClassB/QM 处理领域数学与软件；ClassC/BookAssembly 处理正式总著、来源、修订和阅读版。冻结 Core 的定义、证明和计数保持独立；根代理统一远端同步。

[v31.6 执行合同](../UEOT_QM_EXECUTION_v31.6.md)对应的三条核心线已具备本地实际成果。下一科学优先任务是当前有理非对角模型的精确迭代、唯一不变态和真实条件态几何收敛，并以恒等 Doob 通道检验仅有正谱度量不足以保证混合；随后再推进更一般的不可约／本原谱存在。量子选择线继续明确组合、丢弃、纯化及局域层析的类型与独立物理责任。

新增结果应写回相应章节、编号、档案和证据，保留旧有效推导与失败路线。当前 **LOCAL_VERIFIED_CI_PENDING** 只依据本版已取得的本地回执；远端提交及主线验收补录须有真实执行记录，不改称再次运行 Lean 或再次排印。
