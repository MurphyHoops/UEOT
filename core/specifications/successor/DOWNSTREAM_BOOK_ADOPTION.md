# 三部著作的后续采用清单

状态：`ADOPTION_ACTIONS_ONLY / BOOKS_UNCHANGED`  
日期：2026-11-11  
来源基线：`16a89154183c22030d4526413167d095d94e6890`  
Git tree：`839321b98ddcf368d0673484f7239733b53a5180`

本文件列出后继规范可供三部著作采纳的入口、已确认的来源导航修正和必要边界。**本轮没有修改三部著作、其来源索引、LaTeX、PDF 或出版回执。** 这里的建议不启动自动修书、重开既有数学合同或新增研究；各书后续维护时再按实际版本采纳。

## 1. 当前定位与版本轴

| 对象 | 基线中的当前身份 | 负责的内容 | 本轮与后续采用关系 |
|---|---|---|---|
| [Core 冻结规格](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md) | Core Mathematics v3.0；106 个原 P-ID | 冻结数学语义和旧形式覆盖计数 | 原字节、P-ID、SHA 与覆盖权威保持；不由书或后继补充覆盖 |
| [数学著作](../../../mathematics/README.md) | v4.1，完整中英双语学术编辑版 | 定义、证明、反例、教学组织、当前源与 Lean 对应 | 后继规范提供调用入口；书保留证明展开和教学叙事 |
| [哲学著作](../../../philosophy/README.md) | v3.0，双语学术修订版 | 客体、组织、目的、意义和规范的独立论证 | 可引用更精确的数学合同；解释及规范论证仍由哲学承担 |
| [物理著作](../../../physics/qm/book/README.md) | 出版版 v3.7；研究 v31.10 / UEOT-QM Kernel 1.10 | 领域选择、物理桥接、模型推导、观测及经验状态 | 按现有 Core–Physics 类型规则采用；不因本轮文档升级改变物理来源或证据 |
| 本目录后继规范 | 独立 successor 1.0 候选 | 稳定合同、准确条件、来源与消费者映射 | **不是 Core v4.0，不是数学书 v4.1 的改名，也不自动晋升为 `active_core`** |

原 106 项的计数权威仍为 [V3_COVERAGE_STATUS.md](../../../formalization/ueot-core/docs/V3_COVERAGE_STATUS.md)。后继 `CSX-` 合同、书的 M 编号、物理结果编号和 Lean declaration 各有自己的用途，不合并计数。三书引用新补充时，应保留原 P-ID 和证明源；一个后继合同可能引用多个已有定理，不能把合同数当成新增定理数。

## 2. 共同采用规则

| 采用动作 | 应登记的准确内容 | 完成后不能宣称 |
|---|---|---|
| 增加阅读入口 | 后继规范版本、其实际合并身份、合同 ID；与冻结 v3 和书版号的关系 | “Core v4 已取代 v3”或“书已成为新覆盖账本” |
| 引用具体数学合同 | 对象类型、实际源、必要假设、量词、准确结论、证明等级与实际消费者 | 只因书中词语、类型名称或结构形状相似就获得同一结论 |
| 采用新源码导航 | 保留稳定 declaration；链接实际定义文件，并保留公共 import 的区别 | 导航修正意味着旧证明缺失、重新证明或本轮重编译 |
| 对齐中英引用 | 同一合同、公式、前提、否定范围和来源身份；若链接出现在两种语言中，两者同步 | 英文更宽的量词或更强的经验含义 |
| 复用既有验证 | 明确该回执绑定的文件字节、源版本和验证范围 | 旧回执证明新出版产物、全仓库当前依赖或新自然实验 |

本轮数学内容状态沿用 `CLASSIFIED_CORE_CLOSED`，经验支持沿用 `UNVERIFIED`。这是条件结论和公开收窄后的内容状态；文档采用本身不改变它们。[当前 Core 状态](../../status/CURRENT.md)

## 3. 数学书：九处可执行的源码导航修正

**确认问题：** `mathematics/UEOT_MATHEMATICS_SOURCES.md` 中以下 9 个声明的文件链接仍指向拆分前文件，声明本身存在且可经公共入口到达。后继 JSON 已保留原登记路径与实际定义路径。本轮不修改原来源表；后续数学书维护只需更正定位，保持声明名、数学语义和 P-ID 不变。

共同文件前缀：`formalization/ueot-core/UEOT/V3/`。

| P-ID | 稳定声明 | 现有文件链接 | 应指向的定义文件 |
|---|---|---|---|
| P-FAC-01 | `UEOT.V3.RepresentationCovariance.causalPolicyValue_transport_bundle` | `RepresentationCovariance.lean` | `RepresentationCovarianceFiniteValue.lean` |
| P-CTL-01 | `UEOT.V3.FiniteDiscountedControl.p_ctl_01_causal_optimality` | `FiniteDiscountedControl.lean` | `FiniteDiscountedGreedy.lean` |
| P-CTL-01 | `UEOT.V3.FiniteDiscountedControl.CausalPolicy.infiniteValue_le_optimal` | `FiniteDiscountedControl.lean` | `FiniteDiscountedCausalInfinite.lean` |
| P-CTL-01 | `UEOT.V3.FiniteDiscountedControl.greedy_infiniteValue_eq_optimal` | `FiniteDiscountedControl.lean` | `FiniteDiscountedGreedy.lean` |
| P-QUO-01 | `UEOT.V3.FiniteDiscountedControl.ExactControlQuotient.p_quo_01` | `FiniteDiscountedControl.lean` | `FiniteDiscountedExactQuotient.lean` |
| P-QUO-02 | `UEOT.V3.FiniteDiscountedControl.ApproxControlQuotient.p_quo_02` | `FiniteDiscountedControl.lean` | `FiniteDiscountedApproxQuotientBounds.lean` |
| P-QUO-04 | `UEOT.V3.FiniteDiscountedControl.Model.p_quo_04` | `FiniteDiscountedControl.lean` | `FiniteDiscountedOccupancy.lean` |
| P-QUO-05 | `UEOT.V3.FiniteDiscountedControl.LocalApproxControlQuotient.p_quo_05` | `FiniteDiscountedControl.lean` | `FiniteDiscountedOccupancyRegret.lean` |
| P-KL-02 | `UEOT.V3.PathEventIProjection.p_kl_02` | `PathEventIProjection.lean` | `PathEventIProjectionGlobal.lean` |

明细依据为独立 B 的[形式兼容性审计第 5 节](review/FORMAL_SPEC_COMPATIBILITY_AUDIT.md)及 [106 项机器可读映射](V3_PROPOSITION_INTERFACE_MAP.json)。聚合模块仍可承担合法 import；“可导入”与“在该文件定义”是两个问题，不应靠 namespace 猜测定义文件。

### 3.1 数学书的其余采用动作

| 编号 | 采用位置与动作 | 必须随引用保留的边界 |
|---|---|---|
| M-A1 | 未来在数学 README、来源索引或附录 F 增加后继合同入口；主证明继续留在现行书 | 不复制原第 0—31 章，不把新合同并入原 106，不反向修改冻结文本 |
| M-A2 | 对增长与程序达成的引用区分一般请求策略和内部程序实现 | `ProbabilityValid` 保留 36 原子严格正性；公共 `programPolicy theta` 在任意人口上首先是请求规则，内部解释需其自有 founder/同程序继承桥 |
| M-A3 | 保留增长分类、旧反馈和长期解释的不同状态 | 最小公共指数基底对原完整历史随机策略；旧反馈仍在 `Valid`，先 T 后 n；n 次根/limsup 为书面分析推论；不推出 a.s. 生存或有限截止期人数最优 |
| M-A4 | 2/3/4 任务表示与秩三引用采用独立书面状态 | 固定程序、未来任务与记录不同；不把它们标成新完整 Lean 端点，不推广成自然普遍维数 |
| M-A5 | 将源码导航与公共 API 说明保持一致 | 后继 Core 可经 `UEOT`、Compression/TheoryCompletion 入口访问；`import UEOT.V3` 单独并不包含全部后继分支 |
| M-A6 | 保留来源构造、一般结构定理和有限数值证书的层级 | `certificateOfPrimitive` 是实际源工厂；给定证书的消费者是另一合同；PR443 数值 `native_decide` 的信任依赖只按具体端点登记 |

这些条件在当前书及 [LEAN_API_SCOPE.md](../../../mathematics/LEAN_API_SCOPE.md) 中已有相应说明。采用动作主要是补入口和更正定位，不能为了制造“升级”而重写已正确的数学叙述。

## 4. 哲学书：数学约束与独立论证

后续适合增加引用的入口是附录 C 的数学对应及 C.3 的再生源说明、附录 D 的来源边界。当前哲学书已有条件数学、解释性主张、规范论证和经验未验证的区分；本轮没有发现必须为配合新规范改写全部哲学论证的理由。[哲学书](../../../philosophy/UEOT_PHILOSOPHY.md)

| 编号 | 采用动作 | 精确边界 |
|---|---|---|
| P-A1 | 在现有数学对应旁加入后继合同 ID 与实际数学来源 | “对象”“目的”“闭合”“身份”同名不证明哲学概念与某个数学类型相同；必须说明解释映射及保留什么关系 |
| P-A2 | 引用再生共同见证时保留其同源条件 | 两行重复码、可信 bootstrap、可恢复信息、付费和外供是模型条件；同程序、同受损初态、同六单位事务的结论，不能与另一创始 cohort 的资源合并 |
| P-A3 | 引用增长、反馈或选择时分别指明目标和时域 | 期望人口指数、原身份续存、有限 cohort 比例与无限谱系是不同对象；增长最优不提供道德正当性或唯一人生目的 |
| P-A4 | 保留 Π/Φ、Ω、主体与意义的独立论证边界 | 条件低秩不证明自然普遍二维；非恒定响应不保证允许毁损族中的 Ω 非空；功能组织不能单凭数学定理证明现象意识 |
| P-A5 | 引用表示与机制识别时保留未来权限 | 2/3/4 分类是任务相对的数学例；有限识别能力、可行动作最优性和解释/规范正当性不能互相替代 |

这些是后续引用时的保持条件，不是要求哲学书退化为规范卡或把全部论证改写为 Lean 术语。哲学书应继续独立回答理由与反对意见，数学合同负责其所引用的机制结论。

## 5. 物理书：类型化桥接及 Choi 实例化

采用以现行 [Core–Physics 合同](../../../physics/interfaces/CORE_PHYSICS_CONTRACT.md)为准：Core 推论 C、桥 B、领域选择 S、标准物理 P、有效模型 E、可观测结论 O 与开放目标 X 分开。可在实际物理消费者旁并列后继合同、原 P-ID（如适用）和真正的 Lean/书面来源；不能把 CSX 号登记成新的冻结 P-ID。

### 5.1 第 66 章的准确采用链

当前第 66.6 节已有合法实例化：一般实模凸包结论，应用于带可见结果标签的复线性映射 Choi 家族，得到允许随机化的实现判据。将复矩阵家族作为实模是明确的数学实例化；它不把经典非负矩阵自动认作一般量子 CP 映射。[物理书第 66 章](../../../physics/qm/book/UEOT_PHYSICS.md)

| 必须保留的输入或区分 | 对后续引用的要求 |
|---|---|
| 有限允许动作库，每个动作是完整仪器 | 权重构造出的混合必须仍是实际合法仪器；不能默认形式条件过程已由设备提供 |
| 可见结果标签逐块保留 | 相同无标签通道可以有完全不同的记录律；不能将分支 Choi 块先相加再声称完整记录等价 |
| 同一观察纤维使用共同权重 `w_y(a)` | 不得为控制器看不到的隐藏节点分别选择动作混合；逐节点独立可行不足以保证共同可实施 |
| 输入限制 `R_h` 明确 | `R_h=id` 的指定全空间补全、全部支撑输入和固定初态可达任务不同；较强任务失败不能自动否定较弱任务 |
| 指定逐节点仪器匹配与仅最终输出匹配不同 | 本判据不是任意长量子电路可控性定理，也不是仅匹配终态的一般必要条件 |
| 正负证书可独立检查 | 正证书需归一非负权重及带标签 Choi 等式；负证书需分离不等式；求解器状态文字不足以替代 |

### 5.2 其他物理采用边界

| 编号 | 采用动作 | 必须保留的边界 |
|---|---|---|
| Q-A1 | 在 Core 依赖栏连接实际后继接口 | 复 Hilbert、Born、张量、CP 结构、领域重构条件及物理常量仍按各自来源登记；本轮不证明 Core 唯一选择量子域 |
| Q-A2 | 引用 Perron、Doob 或不变性时核对所用类型 | 有限非负矩阵、特定可逆谱源与一般非交换 CP 半群不同；Cesàro/弱不变性不等于混合或所有轨迹收敛 |
| Q-A3 | 保持 Object-RG、过程合并与 Wilsonian RG 的区分 | 同名或形式相似不能替代积分自由度、耦合流及物理匹配桥 |
| Q-A4 | 引用初始化、滤波与重试时保留任务和资源 | 未知系统边缘与含参考的联合态不同；独立重新准备与重置须实际提供；初始筛选失败、早停、准备和重置计入成本 |
| Q-A5 | 保持误差与数值证据的层级 | 完整合法仪器误差、接受条件化放大、精确秩和支撑、浮点诊断分别登记；机器残差不自动成为严格实数误差上界 |
| Q-A6 | 保持具体证明状态和经验范围 | 第66章初始化全分类、参考相关否定论证、Kraus 范数充分界、无限重试的单调收敛解释为书面层；相邻 Lean 通过不改变其层级；成本模型正例不等于新硬件优势数据 |

这些约束已经存在于当前第 66.6—66.16 节。后继规范采用应保存它们；不能因为增加了通用合同入口而扩大领域结论。

## 6. 后续维护的最小完成条件

若未来只做入口或九处导航更正，完成条件是链接准确、声明名保持、中英相应引用一致、版本关系正确。无需为这些文档变更声称新的 Lean 构建。若实际修改书的 Markdown、排印源或 PDF，则由该书的构建流程生成相应新回执，原出版回执保持历史身份。

若未来拟扩大数学域、物理允许动作、观测权限、资源供给或经验结论，这已超出本采用清单：需要登记新增的源或桥、前提和相应证明/验证责任，不能用“采用 successor 1.0”替代。

## 7. English adoption summary

The baseline contains Mathematics **v4.1**, Philosophy **v3.0**, and Physics publication **v3.7** (research **v31.10 / Kernel 1.10**). All three books and their publication artifacts remain unchanged in this upgrade. The independent successor **1.0 candidate** adds reusable contracts; it does not rename the mathematics book, replace frozen Core v3, or announce Core v4.

The mathematics maintenance action is concrete: correct the nine defining-file links listed above while retaining the exact declaration names and P-IDs. Other adoption consists of accurate entry links and preservation of existing scope distinctions: public request policies versus internal inherited execution; `ProbabilityValid` growth versus old `Valid` feedback; finite exponential bounds versus written root-limit consequences; written task representations versus dedicated Lean endpoints.

Philosophical adoption requires an explicit interpretation, not a shared type name. Conditional mechanism results do not establish moral justification, universal purpose, phenomenal consciousness, universal two-dimensional dynamics, or empirical confirmation.

Physics adoption follows the existing C/B/S/P/E/O/X dependency classes. The Choi application requires a finite library of complete instruments, visible outcome blocks, common randomization within each observation fibre, and explicit input restrictions. Nodewise realizability does not establish implementability under hidden information. Generic Core does not select complex quantum theory, establish general quantum Perron results, or supply hardware cost data. Written arguments, finite exact computations, Lean proofs and numerical diagnostics retain their own evidence levels.

This document supplies bounded maintenance actions and conditions. It neither schedules book edits nor starts new mathematical or empirical work.
