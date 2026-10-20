# UEOT Core：原始哲学、数学主文与形式化的反馈 V1

## 0. 本次反馈的结论与证据范围

UEOT 目前最有依据的统一性，是**在同一受控过程、同一观察与行动协议、明确的评价和失效语义下，把预测压缩、控制、生存与统计认证连接成可检查的条件定理**。原始哲学中的“所有存在都是拓扑闭环”“一切演化必沿双驱动趋向唯一最优吸引子”，不能作为这套形式化已经证明的结论。数学主文已经主动修正了其中许多表述；本次应把这些修正反馈到哲学叙述，并用新增的采样—风险连接进一步检验它们。

本文件是新建的版本化研究反馈，不修改原始附件，也不升级任何全局科学闭合状态。它回答三个问题：原始核心主张经过数学化后实际保留了什么；现有 Lean 真正证明了哪些连接与反例；本轮真实采样工作怎样解除一个具体前提，而不把其他前提隐藏起来。

原 PDF 在摘要、p3 的 122–125 行和 p41 的 §5.3 已主动把 UEOT 定位为开放研究计划。这一点应保留。需要修正的是同一文稿中“所有系统”“必然”“唯一”与“已经推导”的具体句子，使它们与数学主文已经采用的条件、反例和经验等级一致，而不是把研究计划本身当作错误。

### 0.1 所用原始来源

| 来源 | 本文引用方式 | 固定身份 |
|---|---|---|
| `01-UEOT_v3_top.pdf`，*A Universal Evolutionary Object Theory (UEOT): A Framework and Research Program for a Unified Science* | `PDF pN` 为 PDF 物理页码，也与所读页底的 `N/43` 一致；附节号及印刷行号 | 43 页；SHA256 `6c2acdf8d8232377066c3363ce3f0b0a14b3b60608c485ce70f2089c8a2263c3` |
| `02-UEOT_Core_Mathematics_v3.0_Complete.md` | `数学 §N` 及该节原有 P/N/H 标识 | 主文 version 3.0，日期 2026-09-05；SHA256 `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303` |
| 本次起点的 canonical Core | 下列链接所指实际源码与完整声明名 | 基线 `0c093e9fae990d6ef8d670163b84ec93bd6fb025`；本文件不是对未读模块的全量证明评级 |
| [Unified Closure Mission V1](UNIFIED_CLOSURE_MISSION_V1.md) | UMC 单一世界、G5 统计有效性、G6 实质连接、G8 语义边界 | 以现有 mission 的科学范围为准；本文不另设状态账本 |

已实读 PDF 的核心论证页 1–11、26–28、38 的 Proposal 1、40–41；其中 p4、p6、p7 另作原页渲染核对，确认公式及页码。引用原始文本是定位待修订的主张，不是承认该主张已经成立。其余领域分支不在本次反馈范围。

### 0.2 状态词的严格含义

| 标签 | 本文含义 |
|---|---|
| `THEOREM` | 已有 Lean 声明证明了其完整类型；量词、定义域和前提都是结论的一部分 |
| `CONDITIONAL` | 把数学定理应用于所研究系统，还需明确的模型匹配、观测、干预、评价或初态条件 |
| `NO_GO` | 已有具体反例否定一个无条件蕴含；不宣称所有增加条件后的版本也不可能 |
| `EMPIRICAL` | 需要采样、独立测量、干预或外部验证；编译本身不能提供这类事实 |
| `OPEN` | 尚未完成所声称的连接，或本次新增源码尚未取得相应实际验证证据 |

这里的分类与数学主文 §0.3 的 D/P/K/H/E/N/O 可对应，但不能把主文的 `P` 自动改记为 Lean `THEOREM`。主文自己已经声明其证明状态与原创性、机器验证状态不同。

### 0.3 本轮新增证明的验证状态

下列五个冻结研究模块已通过正式 Lean 构建；包含它们的完整 `UEOT` 构建为 **9352 jobs PASS**。原生导出与固定验证器随后分别实际运行通过，两次输出的完整 JSON 对象一致。数学主端点、负例和同模型非平凡正例均已作独立语义审查。研究源码随后完成了基于 canonical main `78852812650eff0a4803596bf3379d4d792122d0`（已包含治理 PR #339）的本地整合验证；当时核验的 18 个集成文件在两地逐字节一致。上述结果不提供现实系统的采样、机制或失效标签匹配事实。

FKRG、复用检查与完整 UMC 本地审计已实际通过。[本地审计 receipt](STATISTICAL_RISK_LOCAL_AUDIT_V1.json) 的 SHA256 为 `399f7c4fbe084c4ebd78510a3c772b1de8535ae803b299184d2664fb0a038bb4`：UMC 范围为 47 个模块、266 个公开源码定理候选，原生枚举 471 个定理常量（266 个已确认公开源码候选、22 个私有常量、183 个其他原生公开常量），471/471 的公理闭包均只含标准公理；完整 `UEOT` 构建通过，全局 646 个源码模块全部可达且导入图无环。这是可复核的本地验证检查点；远端研究 PR 的审查、CI 与合入生命周期由关联 Git/PR 记录追踪，不由本文把本地通过改记为远端合入完成。

| 新增模块 | SHA256 | 本稿阶段 |
|---|---|---|
| `StatisticalRiskCalibration.lean` | `20169e48a8561c6de93c6767ade68173cc80e45ffefa06c43b19d5c735cbf1ee` | Lean / native / fixed `PASS` |
| `MicroscopicFailureRisk.lean` | `5736eae5f9939ef0fdb4c7c520c2c0bc5766d85bf863161787568d2042842cfb` | Lean / native / fixed `PASS` |
| `EmpiricalReferenceRisk.lean` | `9b5594629e9e439282134cdece24b22786eff83a392a6a4168cc4249f9e0556d` | Lean / native / fixed `PASS` |
| `StatisticalRiskBoundary.lean` | `a9f2742599f190755548f9739a1c67276f6e72bf1c38769b343710e59999dc4c` | Lean / native / fixed `PASS` |
| `StatisticalRiskWitness.lean` | `9bd381fde5c6db2ae84e02363d33ed68de412b1fd9a2f827a72fe474bf82405e` | Lean / native / fixed `PASS` |

原生枚举按实际来源模块覆盖 126 个定理常量：73 个公开源码定理候选、11 个 private 常量和 42 个其他非 private 常量，后者包含实例及编译器生成的辅助证明，不能统称为手写定理。全部公理集合都是 `propext`、`Classical.choice`、`Quot.sound` 的子集。既定原始编译类型比较得到 282145 次跨表、2628 次内部比较与零碰撞；91 条登记证明边来自实际证明项。零碰撞只描述该比较协议，不代表数学新颖性判定。

结果文件 `STATISTICAL_RISK_NATIVE_V1.json` 的 SHA256 为 `9a87e5f99d48cfc7fa95df595d7884837f0dd24253205858f5c27ae22545a63d`；固定验证器 `VERIFY_STATISTICAL_RISK_OVERLAY_TYPES.lean` 的 SHA256 为 `5615a23f94b3ba53f9faec51b72d021f204e539fc73448f793752cc78727438d`。具体契约、来源映射与阶段证据见 [Statistical Risk Closure V1](STATISTICAL_RISK_CLOSURE_V1.md)。

完整连贯的英文改写另见 [UEOT Core Philosophy Revised V1](UEOT_CORE_PHILOSOPHY_REVISED_V1.md)。该正文可用于回写原论文的 Core 论证；本文件保留中文分析与逐项来源定位。

## 1. 原始哲学经过数学化后的实质改变

### 1.1 “存在就是拓扑”应改为分层的操作性对象证书

**原始位置。** PDF p4，§2.2，147–160 行，将稳定对象、内部自维持反馈、非零第一同调群 $H_1$、状态完整回归和身份保持连接起来；p38，1847–1866 行，进一步把持久同调长条作为自创生系统应当具有的决定性签名。

这些是不同类型的命题。状态空间有洞，轨迹绕成环，机制图含有有向反馈，以及干预后能够重新建立组织，分别涉及空间、轨迹、因果结构与恢复能力。必须先给出连接这些类型的构造，才能相互推导。稳定平衡的轨迹可以收敛到一点；一个被外部周期驱动的观测也可以呈现闭合曲线。因而几何环的检测本身既没有建立内部因果闭合，也没有说明是哪一组机制维持了身份。这里的例子用于说明概念区别，本文不把它们伪装成仓内已经存在的同调形式化。

**数学主文已经作出的修正。** 数学 §0.1 明确把几何环降为特殊模型；§12.1 定义预测、因果、历史、实现分层的证书；§12.2 在冻结的对象判据与毁损操作上定义 $\Omega_T$ 的极小失效集，且 P-OMG-01 需要有限机制域与失败单调性。若删除抑制机制反而恢复功能，原文要求保留完整响应表，不能强套单调超图。这比把所有自维持解释为 $H_1\ne0$ 有更直接的实验内容。[数学 §0.1、§12.1–12.3]

**Lean 边界。** [SemanticBoundaries.lean](../../../../UEOT/V3/Compression/TheoryCompletion/SemanticBoundaries.lean) 的 `UEOT.V3.Compression.TheoryCompletion.formedProvenance_does_not_imply_interactionDelimitation` 给出已形成来源也不足以获得交互区分性的真实反例。[UnifiedCoreClosureCertificate.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/UnifiedCoreClosureCertificate.lean) 则从一个实际有限模型生成最粗稳定商并保持已注册属性；它明确不由一个 state label 推出历史程序来源。二者共同支持“逐层认证对象”的叙述，不支持“一个拓扑签名即全部对象性”。

**建议修订。** 将原始 Postulate 1 分成研究假说和条件实现：研究假说是跨领域持久性可能具有可复用的组织维持机制；已可检验的版本是，在给定协议、时域和干预语义下，候选是否具有非平凡的预测、因果、历史及恢复证书。若要保留拓扑版本，应另声明从机制到空间的映射、相应同调不变量与保持定理，把它作为一个特殊分支。

相同修订也适用于 Type I/II。PDF p5，177–201 行将开放性、内外两环和生命周期阶段联系起来；数学 §0.1、§6、§12.4 已把资源交换、信息接口、外部脚手架依赖和身份失效分开。它们应形成可测的能力剖面，而不能只用一个“开放程度”同时推出适应性、成熟度和寿命。

### 1.2 Π/Φ 的价值在可独立检验的约束，不在任意二分

**原始位置。** PDF p3，79–94 行与 p6，§2.3.1，229–260 行，主张所有动力学都由物理效率与信息驱动共同优化。PDF 摘要与 p3 对 $\Phi$ 使用“信息增进”语言，p6 则将其定义为应降低的信息缺口；这一符号语义需要统一。

**数学主文已经作出的修正。** 数学 §23.1 将 $J=\Pi-\lambda_\Phi\Phi-C$ 作为带单位、符号和测量约定的可用模板。§23.2 的规范变换说明同一行为目标可以有多种轴分解；§23.4 的共同二维瓶颈是独立假设 H-DDH，其秩约束是可否证的必要条件；§23.5 的有效秩认证有阈值与扰动预算，有限样本“不拒绝第三维为零”不等于证明精确二维。

**Lean 已经提供的正反两面。** [DualDriveGaugeCompleteness.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/DualDriveGaugeCompleteness.lean) 的 `same_objective_iff_gauge_related`、`pi_identified_of_phi_anchor`、`phi_identified_of_pi_anchor` 及 `unanchored_drive_is_not_uniquely_identified`，分别给出代数等价、独立锚定后的识别及未锚定反例。[TeleologicalGauge.lean](../../../../UEOT/V3/Compression/TheoryCompletion/TeleologicalGauge.lean) 的 `incomparableBoolContract_has_no_validDualDriveRepresentation` 还表明一般的偏序评价契约甚至不必有这种实值双轴表示。因此“写出两个函数”与“发现两条普遍的自然驱动”之间有实质距离。

[C5DualDriveTest.lean](../../../../UEOT/V3/Compression/TheoryCompletion/ScientificClosure/C5DualDriveTest.lean) 的 `dualDrive_compatible_sound` 只支持声明容差下的相容；[SISCJoint2DRejection.lean](../../../../UEOT/V3/Compression/TheoryCompletion/ScientificClosure/SISCJoint2DRejection.lean) 的 `reject_exact_common_twoD_from_same_jacobian` 从同一个真实 Jacobian 的认证误差拒绝精确共同二维。这里已有可检验内容，不能再用换一套潜变量坐标回避拒绝结果。

**建议修订。** 把“普遍双驱动定律”改为“资源与信息约束的共同接口，以及待独立检验的低维机制假说”。每项实验先规定资源轴、信息轴、单位和干预方式，再检验跨环境共同响应。允许结果要求第三条乃至更多独立维度。新统计风险桥中的 TV 误差是预测误差预算，不会因为冠以 $\Phi$ 就自动成为所有系统的内生信息目标。

PDF p6，237–239 行还将 $\Pi$ 与经典作用量的动能减势能项联系，并由此声称包含经典力学。把一个函数定义成该表达式，没有同时证明相应运动方程或把变分驻点变成资源效率最大值；该特例需要自己的状态、约束与变分推导。它不能由一般双轴表示定理补出。

### 1.3 GOD 应由明确评价下的可实施控制定义

**原始位置。** PDF p3，104–110 行与 p6–7，§2.3.2，271–281 行，把实际瞬时变化方向、局部最陡收益方向、全局最优路径和系统意图联系起来。

**数学主文已经作出的修正。** 数学 §18.1 区分状态可行路径、因果可实施策略和可达路径律；§18.3 的 N-TEL-01 用同一动力学上的相反目标否定“对象存在唯一决定价值”。§19 的 GOD 是给定评价、约束和时域后的最优动作对应，不要求单值。瞬时收益最大、有限时域风险最小与长期折扣最优是不同问题。

**实际形式化。** `SemanticBoundaries.lean` 中的 `bellmanGOD_can_be_nonunique` 给出两种并列最优动作。[ProgramPurposeInformationBoundary.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/ProgramPurposeInformationBoundary.lean) 的 `same_process_opposite_goals` 使用一个受控机制展示不同资源评价下的相反选择。[SafeRewardConflictWitness.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/SafeRewardConflictWitness.lean) 的 `conflict_same_source_reward_and_risk` 和 `conflict_nonzero_reward_safe_bellman_preserves` 把即时奖励与安全冲突、加入安全约束后的非空最优控制放在同一真实随机源中。安全控制与无约束收益贪心因此不能靠命名合并。

**建议修订。** 保留“目的性可研究”的方向，改为识别并检验一个评价机制对未参与拟合的行为与干预响应的预测能力。不得事后把实际策略定义为唯一高分策略，再宣称证明了自然界必然最优。

### 1.4 GOA 应是带条件的长期结构，不是普遍唯一的终点

**原始位置。** PDF p7，282–298 行及 p40，1972–1977 行，把 GOA 定义为唯一渐近最优状态，并由此宣称目的性必然产生。

**数学主文已经作出的修正。** 数学 §21.1–21.5 分别记录极限集、时间平均分布、多复归类、准平稳分布和 Q-process；不把这些对象都等同于有开放吸引域的唯一固定点。P-GOA-02 的唯一性与稳定性需要混合裕量；P-GOA-03 需要扰动保持复归分解；有限时域路径界不提供这些条件。

**实际反例和正例必须同时保留。** `SemanticBoundaries.lean` 中的 `invariantGOA_can_be_nonunique` 已给出非单点不变律集合。[AbsorbingLeakage.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/AbsorbingLeakage.lean) 的 `bounded_row_error_with_asymptotic_failure` 使用真实归一化 PMF：任意固定的小正泄漏仍可导致失败概率趋于一。这禁止从“小行误差”直接宣告永续稳定。

与此同时，不能错误地说仓库从未证明无限时域持续性。[CoreSourceAllTimesAssembly.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreSourceAllTimesAssembly.lean) 的 `single_source_terminal_object_viability_all_times` 已将同源有限核、生存核及真实无限路径律连接；它需要已注册的安全语义和生存核内初始分布。[CoreNonvacuousAllTimesWitness.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreNonvacuousAllTimesWitness.lean) 的 `registered_survival_nonempty_infinite_law` 提供非空实例。缺口是把任意近似、统计学习或自然系统自动放入这些精确条件，而不是没有任何 all-times 定理。

### 1.5 尺度变化、时间演化和物理解释须各有接口

**原始位置。** PDF p6，264–267 行将连续尺度变换和时间步合称 RG 演化流；p9，403–406 行把它并入从存在到目的的必然链条。

数学 §7.4 的 P-DYN-04 以两种尺度共同来自同一个底过程为前提，给出动态推送的误差界。实际 [ObjectScaleCalculus.lean](../../../../UEOT/V3/Compression/TheoryCompletion/ObjectScaleCalculus.lean) 证明了类型化映射及保持证书的复合；`p9_terminal_objectScale_semantic_transport` **需要**身份、目的、GOD、GOA、修复和稳态的分别保持证明。`SemanticBoundaries.lean` 中的 `quotientMap_does_not_imply_dynamicIntertwining` 进一步用两个真实概率核否定“商映射本身推出动力学相容”。

需要精确纠正旧讨论中的一个表述：当前文件的 `wilsonianCouplingFlow_nontrivial_of_twoCouplings` 只证明独立的 coupling-flow 数据类型非平凡。它没有给固定尺度映射的两种兼容物理流，不能被引用成那个更强的非唯一性定理。

因此现阶段应称“同源过程的精确或近似尺度接口”。若再作更强物理解释，必须提供额外模型与相容关系；本次 Core 统计风险研究不承担那项任务。

### 1.6 身份、繁殖与自创生不得以“持久”一个词代替

数学 §11、§25、§26 分开处理历史运输、复制算子、群体均值及个体性转变。[LineageEvolution.lean](../../../../UEOT/V3/Compression/TheoryCompletion/LineageEvolution.lean) 中 `LineageSemantics.OffspringOf` 要求亲缘关系与新身份，`sameObjectRepair_not_offspring` 将修复与后代区分。`lineage_perron_bridge` 消费给定的均值算子证书与谱系相容性；谱增长不自动是单个个体的存活概率。

[AutopoiesisClosure.lean](../../../../UEOT/V3/Compression/TheoryCompletion/AutopoiesisClosure.lean) 的 `p12_terminal_conditional_finite_lifecycle` 是有限、条件性的生命周期接口。其 `no_physicalOnly_synthesizer_for_distinct_sources` 与 [ProgramPurposeInformationBoundary.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/ProgramPurposeInformationBoundary.lean) 的 `perfect_program_decoder_iff_injective_information` 指明：无法区分两份程序的信息不能无损还原它们。补充有效编码确实能解除一个信息障碍，却没有自动实现材料供给、损伤检测与物理制造。

因此“有限风险可控”“历史同一对象”“代际谱系延续”“自主再生产”应分别陈述。新采样证明不能将 P12 的条件范围升级为全自主自创生。

### 1.7 功能与规范的分层，是保留解释力的必要条件

**原始位置。** PDF p26–28，§3.6.5，1256–1360 行，把个人与集体轨迹对齐、价值场谱指标和伦理义务连接起来；p40–41，1991–2008 行进一步把生命、意识和意义描述为闭环与最优轨迹的自然结果。

数学 §27.6 已明确区分功能贡献、意向/表征关系和规范意义；不能从预测压缩、复制优势或梯度公式推出体验、意识或唯一终极价值。§24 也要求层级评价与协调机制，不能把“整体在某个目标下稳定”替换成“每个成员都有服从它的伦理义务”。

**建议修订。** 功能性目的可以定义为某机制在匹配干预下对存续或任务价值的贡献。行为目的解释需要可识别评价机制和留出预测。主观体验需要独立经验研究；规范判断需要明确的价值桥、主体间约束和理由。现有形式化可以表示这些额外条件，但没有证明其普遍真实性。

另有一个具体诊断修订：PDF p10–11 的 $\rho=\|F_\perp\|/\|F\|$ 对正向和反向平行都为零，不能单独表示“目标一致”。数学 §12.4 已用有符号余弦并处理零向量、无最优方向和量纲问题。应将这个修订直接反馈到诊断流程，再对阈值作独立校准。

## 2. 已有的硬连接：从真实源行到有限路径风险

这一部分是原始哲学可据以缩小并强化主张的具体内容。它不只是把若干独立结构装入一个记录。

给定有限状态 $X$、粗状态 $Y$、行动 $A$，真实时间相关转移 $P_t(x,a)\in\operatorname{PMF}(X)$、选择的映射 $q:X\to Y$、宏观参考转移 $Q_t$，以及只读取**同一粗历史和过去行动**的共同因果策略 $\pi$。初态为 $p_0$，参考初态必须为 $q_\#p_0$。若

$$
\forall t<T,\ x,a,\qquad
D_{\rm TV}\!\left(q_\#P_t(x,a),Q_t(q(x),a)\right)\le\epsilon_t,
\quad 0\le\epsilon_t\le1,
$$

则现有 [FiniteHorizonRisk.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteHorizonRisk.lean) 的 `same_policy_projected_path_error` 证明

$$
D_{\rm TV}\!\left(q_{\rm hist\#}\mathbb P_{P,\pi},
                         \mathbb P_{Q,\pi}\right)
\le B_T:=1-\prod_{t=0}^{T-1}(1-\epsilon_t)
\le\sum_{t=0}^{T-1}\epsilon_t.
$$

`q_hist` 保留行动并映射每个状态。实际微观历史律经推送后可依赖整个粗历史；[FinitePMFProjection.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FinitePMFProjection.lean) 的后验/混合构造及 `FiniteHorizonRisk.lean` 中的 `risk_causalLaw_map` 正是为此服务。因此这里没有暗中假设任意所选 $q$ 都是精确 Markov 商。有限历史核界最终调用原有 P-DYN-03 接口，而非改用另一个无关过程。[数学 §7.3，P-DYN-03]

对于可测的粗历史失效事件 $F$，`same_policy_projected_failure_risk` 给出

$$
(q_{\rm hist\#}\mathbb P_{P,\pi})(F)
\le \min\{1,\mathbb P_{Q,\pi}(F)+B_T\}.
$$

这控制的是指定事件在实际推送路径中的概率。若声称微观物理失效 $E$ 也受到控制，还必须说明 $E\subseteq q_{\rm hist}^{-1}(F)$，或更强的精确因子关系。一个只保留预测观测、却丢弃隐藏损伤变量的商，不能凭预测准确自动认证所有物理安全目标。[PredictiveGoalClosureBoundary.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/PredictiveGoalClosureBoundary.lean) 的 `no_macro_reward_for_hidden_memory_goal` 已体现同类目标闭合障碍。

### 2.1 观测校准进入行 TV 的精确方式

[CalibratedRiskRows.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CalibratedRiskRows.lean) 复用既有 `UEOT.V3.FiniteRecurrentDecompositionStability.pmf_tv_eq_half_sum_abs`，从真实归一化 PMF 的坐标误差得到

$$
|p(c)-q(c)|\le\Gamma(c)
\quad\Longrightarrow\quad
D_{\rm TV}(p,q)\le\min\!\left\{1,\frac12\sum_c\Gamma(c)\right\}.
$$

其 `calibrated_observable_partition_tv_budget` 进一步消费同一个真实转移模型上的实验测试期望：$\delta_t$ 为每个目标类指示函数的统一重构残差，$\eta_t$ 为同纤维两行的实测差，$\rho_t$ 为每行真实测试期望与实测均值的校准半径，$\kappa_t$ 为重构系数的 $\ell^1$ 条件数上界。具有 $m$ 个类时，所生成行预算为

$$
\epsilon_t=
\min\!\left\{1,\frac m2
      \bigl[2\delta_t+(\eta_t+2\rho_t)\kappa_t\bigr]\right\}.
$$

两个 $\rho_t$ 来自被比较的两行，$2\delta_t$ 来自两个状态的类指示函数重构，$m/2$ 来自有限 PMF 的半 $\ell^1$ 公式。它们不能不加说明地都改称“压缩误差”。

`FiniteHorizonRisk.lean` 中的 `calibrated_representative_path_error` 与 `calibrated_representative_failure_risk` 已把该预算接入实际路径，参考行明确为同源代表元模型

$$
Q_t(c,a)=q_\#P_t(r(c),a),\qquad q(r(c))=c.
$$

这是一个有实际数学内容的模型选择。它不等于任意训练得到的 $\widehat Q$。若最终算法使用另一个归一化参考核，必须另给它相对代表元核或真实源行的误差桥，不能把未知模型误差吸收到 $\kappa$ 的名字里。本轮新增的经验参考路线正是针对这个接口提供实际连接，见 §3.6。

## 3. 新统计研究应解除什么前提

### 3.1 现有统计工作应被准确承认

仓库已有 [SISCStatisticalCandidateCalibration.lean](../../../../UEOT/V3/Compression/TheoryCompletion/ScientificClosure/SISCStatisticalCandidateCalibration.lean) 的真实有限样本集中界和错误候选解析界。其 `measure_bad_empirical_calibration_le` 调用既有双侧 Hoeffding，并显式要求 `SampleLossMatchesRegisteredRisk`。文件正确指出

$$
\mathbb E|Y-r|\ne |\mathbb E Y-r|
$$

一般并不相等。因此不能把“没有集中不等式”作为新增工作的理由。本轮工作已在明确的源行采样模型中证明**所采到的量恰好估计下游需要的转移测试期望**，并把同一个随机校准事件接入 §2 的实际源路径风险。

### 3.2 本轮目标的采样契约与概率层级

以下是本轮新增 `StatisticalRiskCalibration.lean` 的实际接口。该冻结源码已通过 §0.3 的构建、原生与固定验证及本轮本地整合审计；它是本轮新增结果，不能混写为起点版本中原有的定理。

固定时域 $T$、有限 $X,A$、有限测试族 $f_{t,i}:X\to[0,1]$。对每个实验行 $(t,a,x)$，从同一个实际源 $P_t(x,a)$ 取得 $N>0$ 个可测、行内相互独立的样本 $Z_{t,a,x,k}$，并明确

$$
\mu\circ Z_{t,a,x,k}^{-1}=P_t(x,a).
$$

这里 $\mu$ 是实验数据概率空间上的概率律。要求每个样本边缘律真实匹配源行；不同实验行之间不需要独立。测试族、$T$、$N$ 及用于集中界的半径先固定。这是可针对每个状态、行动和时间行重复实验的契约，不是从一条观测轨迹自动提取独立样本的定理。如果隐藏状态无法访问、重置或干预，有限 Lean 类型本身不能补足这项实验条件。定义

$$
\widehat m_{t,a,x,i}(\omega)=\frac1N
\sum_{k=1}^{N} f_{t,i}(Z_{t,a,x,k}(\omega)),
$$

以及同时校准事件

$$
G=\left\{\omega:\
\forall t<T,a,x,i,\quad
\left|\mathbb E_{P_t(x,a)}f_{t,i}
      -\widehat m_{t,a,x,i}(\omega)\right|\le\rho_t\right\}.
$$

证明复用 `UEOT.V3.BoundedLossTwoSided.measure_exists_candidate_bad_le` 与有限行并合界得到下面的界。它是 P-STAT-08 所用的既有双侧 Hoeffding 采样核心，并非直接将 ERM excess-risk 定理 `FiniteCandidatePStat08.p_stat_08` 当作行均值校准：

$$
\mu(G^c)\le\alpha_{raw}
=\sum_{t<T}\sum_{a\in A}\sum_{x\in X}
  2|I|\exp(-2N\rho_t^2).
$$

如需报告概率预算，可取 $\alpha=\min\{1,\alpha_{raw}\}$；粗界大于一时不提供有用认证。新增引理 `finiteKernelRowPMF_trueRisk` 已从实际 PMF 的定义推出 `trueRisk = transitionTestExpectation`，而不是再要求一个新的同义匹配字段。

在事件 $G$ 上，只要同一次观测对应的 $\delta,\eta,\kappa$ 检查成立，就可使用 §2 的代表元路径结论。最精确的接口是“存在可测 $G$，$\mu(G^c)\le\alpha$，且对每个 $\omega\in G$，所有通过检查的后续选择都满足风险结论”。它无需先假定所有候选或数据选择映射组成的集合可测。

这是**关于实验数据所得证书的置信保证**。它与实际部署失效概率 $\mathbb P_{P,\pi}(E)$ 位于不同概率层。若要再给训练与部署的联合失效概率，需建立数据依赖部署律的可测核，并正确积分条件风险；不能直接把 $\alpha$ 写成每条部署路径的故障率。

### 3.3 为什么同数据选择有时合法，有时不合法

统一事件 $G$ 同时约束所有注册行与测试，因此在该事件上，可以为每个数据集再选择划分、代表元、重构系数或共同部署策略；证明必须保留“所选择对象通过确定性检查”的前提，并保持下游接口的同源性。这样的选择不一定需要再对所有划分逐个并合。这对应数学 §16.2 的“先认证共同底层响应，再支持多个候选”的思想。

这个结论不允许在看到数据后任意挑一条未纳入统一事件的测试，也不允许任意重复检验并沿用一次固定时刻的置信度。数学 §16.7–16.8 已分别列出重复协议、在线自适应、相关轨迹和模型选择的附加要求。对只有一次访问的连续历史，不能把“条件分布下 N 次独立采样”写成已经获得的事实。

本轮 [StatisticalRiskBoundary.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/StatisticalRiskBoundary.lean) 已给出真实 PMF 负控：两个动作的实际失效率均为 $3/4$；各固定动作的精确失准概率为 $1/4$，但用同一训练数据选择经验上更安全的动作后，失准概率变成 $7/16$。`selected_bad_iff_false_risk_bound` 还证明，在该事件上经验值加 $1/4$ 的上界确实低估所选真实行的风险。`simultaneous_calibration_protects_any_selector` 则说明统一好事件怎样保护后续选择。这是训练后选择的反例，不是在线依赖采样定理，也没有声称单样本 Hoeffding 界在这个半径下有用。

### 3.4 微观失效的保守包络是另一条独立接口

本轮新增 `MicroscopicFailureRisk.lean` 已从实际源历史律证明：若微观失效事件 $E$ 的每条路径都落入某个可测粗失效包络 $F$，则

$$
\mathbb P_{P,\pi}(E)
\le(q_{\rm hist\#}\mathbb P_{P,\pi})(F)
\le\min\{1,\mathbb P_{Q,\pi}(F)+B_T\}.
$$

对逐状态失效，只需 $\mathrm{bad}_X(x)\Rightarrow\mathrm{bad}_Y(q(x))$ 即能构造包含初始状态和 $T$ 次转移内所有状态的事件包络；无需强求隐藏损伤在每条纤维内完全相同。当前实现还直接构造在所有微状态逐点覆盖意义下最小的保守包络

$$
\mathrm{bad}_Y(y)\iff\exists x,\ q(x)=y\ \land\ \mathrm{bad}_X(x).
$$

`risk_failure_envelope_covers`、`risk_failure_envelope_minimal` 和 `same_policy_canonical_exit_risk` 证明覆盖、最小性并消费该构造。因此选择这个包络时不再需要调用者另行假设覆盖关系。不过包络过宽时上界会失去实用性，例如每个粗状态都包含某个坏微状态时只能得到平凡界。**形式上正确的包络与有辨别力的风险认证仍要分开。**

此接口解除的是“粗事件风险与所声称微观风险可能不是同一件事”的断点。它不会证明失效标签就是自然界唯一的身份标准，也不会识别未观测的物理损伤。

### 3.5 可以提出的局部科学闭合主张

上述连接已通过 §0.3 的正式构建、原生与固定验证，并纳入本轮本地整合审计，可以按以下严格范围表述：

> 对有限、可按指定源行重复采样的受控系统，在固定测试族上，实际样本同时校准真实转移期望；通过可检查的类指示函数重构与同纤维测试差，将它转为所选代表元宏观模型的行 TV 预算；以微观初态的推送作为参考初态，并使用同一粗历史因果策略，预算控制真实微观路径的推送误差，并在明确失效包络条件下控制按已声明标签定义的有限时域微观失效。置信度属于实验数据上的证书事件，持续时间属于指定的有限时域。

这是一项有范围的科学连接，仍保留三类不同工作：确认现实采样与真实源的匹配；针对具体应用计算或认证参考模型的失效风险，§3.7 给出一个已完成的数值实例；把结论推广到未覆盖行、漂移环境或无限时域。全局“科学闭合”不能由其中一条成功连接代替。[数学 §16.9、§28.4、§31.1–31.2；UMC Mission G5/G8]

### 3.6 将未知的真实代表元核进一步替换为数据构造的参考核

本轮新增 [EmpiricalReferenceRisk.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/EmpiricalReferenceRisk.lean) 正面处理 §2.1 的一个实用限制：若参考行仍为真实 $P_t(r(c),a)$，数学比较虽已成立，实验者未必掌握该参考模型。本节结果已通过 §0.3 的正式构建、原生与固定验证及本轮本地整合审计。

`empiricalResponsePMF` 将均匀样本索引的真实 PMF 推送到观测值，得到归一化经验行 $\widehat P_{t,x,a}$，重复样本按出现次数计入。固定测试族改为微观有限字母表的**全部事件指示函数**，即 `Finset X`。同一个同时校准事件因此给出

$$
\forall t<T,x,a,\qquad
D_{\rm TV}(P_t(x,a),\widehat P_{t,x,a})\le\rho_t.
$$

这一步的端点为 `calibrated_full_event_row_tv`，样本律和事件均值之间的连接由 `empiricalResponsePMF_toMeasure`、`empiricalResponsePMF_event_mean`、`pmf_event_test_mean` 明确承担。统计预算中的测试数量为 $2^{|X|}$，与数学 §16.1 的有限事件并合口径一致；不能仍以稀疏测试的 $|I|$ 数量报告该保证。

随后选择映射 $q$ 与原型 $r$，从同一批样本构造

$$
\widehat Q_t(c,a)=q_\#\widehat P_{t,r(c),a}.
$$

直接检查数据行对经验参考行的拟合

$$
\forall t<T,x,a,\qquad
D_{\rm TV}\!\left(q_\#\widehat P_{t,x,a},
                    \widehat Q_t(q(x),a)\right)\le\eta_t.
$$

真实到经验的 TV 经过数据处理不增加，再与实测拟合误差相加，`empirical_coarse_row_tv` 的结论为

$$
D_{\rm TV}\!\left(q_\#P_t(x,a),\widehat Q_t(q(x),a)\right)
\le\min\{1,\rho_t+\eta_t\}.
$$

这里只有一个统计误差 $\rho_t$，因为比较终点本来就是经验参考核；与真实代表元路线的 $2\rho_t$ 不能混用。该拟合条件直接针对所选参考行，因此这条路线不要求原型 $r$ 必须满足 $q(r(c))=c$；如果后续赋予它“商截面”的语义，再单独加截面条件。声明风险端点的输入是这些真正通过检查的行，并非无条件保证任意低维选择都有小误差。

总端点 `statistical_empirical_reference_certificate` 提供同一个可测好事件，支持后续所有有限 $q,r$、初态与共同粗历史策略，并输出相对于**数据本身定义的**参考路径的误差与微观失效包络界。两条路线因此互补：

| 路线 | 测试与数据条件 | 参考过程与预算 | 保留的限制 |
|---|---|---|---|
| 稀疏测试及类指示函数重构 | 固定 $I$ 个测试；提供 $\delta,\kappa$ 和同纤维实测差 | 真实源代表元核；$\epsilon_t=\min\{1,\frac m2[2\delta_t+(\eta_t+2\rho_t)\kappa_t]\}$ | 参考核仍含真实未知行；测试重构条件必须验证 |
| 全事件测试及经验参考 | 固定 `Finset X` 测试；全源行实际样本；经验拟合检查 | 归一化经验原型核；$\epsilon_t=\min\{1,\rho_t+\eta_t\}$ | 置信预算含 $2^{\lvert X\rvert}$；未自动取得可重置/可访问实验行 |

构造经验参考核解除的是“比较模型仍完全未知”的障碍。它没有使该模型下选定策略的失效概率无需计算，也没有把训练置信与部署路径风险变成同一个概率。实际数值应用仍应根据已生成的有限参考核、策略和时域计算或认证风险，并保留 §3.4 的微观失效包络条件。

### 3.7 同一非稳定模型中的非平凡有限认证链

[StatisticalRiskWitness.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/StatisticalRiskWitness.lean) 给出四状态模型 $X=\mathrm{Bool}\times\mathrm{Bool}$：第一位为可见状态，第二位为持续隐藏状态 $h$，动作 $a$ 也是布尔值。真实下一步可见失效率为 $1/16+\mathbf1_h/8+\mathbf1_a/8$。丢弃隐藏位的粗映射非单射，隐藏状态与动作都产生非零的 $1/8$ 响应差；`partition_not_stable` 证明所选分区不满足精确稳定性。

实验概率空间直接构造为真实源行 PMF 的有限乘积，样本是其坐标投影；边缘律与行内独立性从构造导出，并实际复用 P-STAT-06 的 `coordinate_iIndep`。取 $T=2$、16 个源行、每行 $N=4096$、两个固定可见类指示测试、$\rho=1/32$、$\delta=0$、$\kappa=1$，则

$$
\mu(G^c)\le64e^{-8}\le\frac14,\qquad
\mu(G)\ge\frac34.
$$

同一 $G$ 上的经验纤维差由证明导出为至多 $3/16$，因此行预算为 $1/4$，两步路径预算为 $7/16$。这已经给出满足各项契约的共同模型及非空好事件，而不再另行传入未经构造的样本律或独立性假设。

数值实例采用真实代表元路线：共同策略固定选择动作 `false`，原型的隐藏位为 `false`，微观初态可见位为 `false`、隐藏位均匀分布。参考每一步仍有 $1/16$ 的失效概率，且允许从失效状态恢复。`boolReference_two_step_failure` 从真实 `causalLaw` 的历史质量和有限求和计算“从初态至第二步曾失效”的概率。P-FAC-01 的 `causalLaw_transport_equiv` 将这个布尔参考计算传到可达商类上的同一参考过程；这只是参考坐标变换，没有把非稳定微观分区变成精确动力学商。随后得到

$$
\mathbb P_{Q,\pi}(F)=\frac{31}{256},\qquad
\mathbb P_{P,\pi}(E)\le\frac{31}{256}+\frac7{16}
=\frac{143}{256}<1.
$$

`joint_statistical_microscopic_risk_witness` 将非稳定性、严格小于一、$\mu(G)\ge3/4$ 和每个好数据集上的真实微观风险界合在一个定理中。它使采样、表示、共同控制和失效定义在同一模型、有限时域内形成可检查的认证链。一般端点支持通过检查的数据后选取；这个具体数值例固定策略，没有证明学习算法的最优性，也没有构造训练与部署的联合失效率。实际系统能否实现这些源行实验、标签是否覆盖目标物理损伤，仍需独立证据。

## 4. 可直接回写原始叙述的替换段落

以下为中文替换草案。它们保留统一研究计划的方向，同时使每段都有可失败的内容。实际论文可再作语言转换；无需为英文原句逐字保留强度。

### 4.1 摘要与总论：替换 PDF p1、p40 的无条件总链

> UEOT 研究不同系统中的对象形成、持续、控制与演化是否能够共享一套操作性数学结构。我们从给定世界过程、观察和干预协议出发，逐层构造预测表示、动力学商、持续性和评价证书，并明确哪些性质可在同一过程的不同描述之间运输。资源与信息约束为跨领域建模提供共同接口，其有效维数、物理解释及目的机制则需要独立识别。现有理论包含有限受控模型中的严格连接，也包含否定无条件目的唯一性、普遍渐近最优与任意粗粒化保持性的反例。UEOT 因而是一项以条件定理和可复核实验持续收敛的统一研究计划。

### 4.2 Ω：替换 PDF p4 §2.2 的 H1 充要式叙述

> 在指定时域与协议下，我们通过预测区分、因果接口、历史延续及恢复能力来认证一个候选对象。Ω 表示该证书所依赖的组织维持结构：对预先定义的机制移除实验，记录哪些最小改变导致证书失败。几何闭环、机制反馈与物理自生产是不同层次；在给定实现模型中可以研究它们的联系，但非零同调或一个周期观测本身不构成普遍对象判据。相应拓扑实验检验的是声明模型中的一个机制假说，而非单独认证所有自维持性。

### 4.3 Π/Φ：替换 PDF p6 §2.3.1

> 我们将资源收益或代价与预测不足或信息成本分开登记，并在明确单位、预算和评价机制后研究其共同作用。一个双轴表示并不自动具有唯一的物理解释；相同目标可具有不同的代数分解。若进一步假设跨环境响应通过共同二维机制产生，则得到可用干预与谱误差界检验的秩约束。该约束被拒绝时，应扩充模型或缩小适用范围。双驱动在这里是具有测量锚点的机制假说，不是任意行为都能被事后满足的命名规则。

### 4.4 GOD/GOA：替换 PDF p6–7 §2.3.2

> 在给定可实施策略、评价主体、资源约束与时域后，GOD 表示最优动作的对应集合。它可以多值，也不必与即时收益梯度或实际漂移相同。由这些策略产生的长期行为，根据模型分别以极限集、不变占据、复归类或条件存活结构描述，统称为类型化的 GOA 家族。唯一性、吸引性与扰动稳定性需要额外条件。系统存在本身不指定唯一目标；目的解释必须由机制或预先约束的评价类支持，并在新环境中接受预测检验。

### 4.5 尺度：替换 PDF p6、p9 的时间/RG 混用

> 微观与宏观描述通过明确的状态和对象映射连接。若两种描述来自同一底层过程，可证明相应动态推送的精确交换或带预算误差的近似交换。控制、身份与恢复属性只有在各自的保持条件下才能跨尺度运输。观察尺度的改变、时间推进和进一步的领域物理解释各有不同参数及相容要求，应分别建立证明。

### 4.6 诊断与实验：替换 PDF p10–11、p38 的过强认证语言

> 每次诊断先固定观察量、行动协议、失效集合、评价目标和时域，再报告模型误差、采样误差与机制不确定性。有限受控模型中，实际转移样本可在声明的独立采样条件下校准测试期望；与指示函数重构和同源控制结合后，可形成有限路径风险证书。方向一致性应区分同向与反向，并为零向量规定未定义状态。所有阈值都应有独立校准，证据不足时允许拒绝或暂不判定。持久同调可以作为特定观测实验的一项特征，但其因果意义须由实现模型与干预另外建立。

### 4.7 意义与价值：替换 PDF p27–28、p40–41 的规范跃迁

> UEOT 可将功能性目的描述为机制对对象持续或任务价值的反事实贡献，并研究内部表征与环境、行动后果之间的关系。主观意义与规范价值涉及另外的经验和评价前提：稳定、复制成功或与集体行为一致，都不能单独推出意识体验或伦理义务。统一框架的作用是使这些接口及其证据变得清楚，而不是用动力学名词取消价值分歧。

## 5. 证据—主张对照与研究优先级

### 5.1 当前可用主张

下表声明名默认前缀为 `UEOT.V3.Compression.TheoryCompletion.`；`UC` 是其 `UnifiedClosure.` 子命名空间，`SC` 是其 `ScientificClosure.` 子命名空间。这里仅作阅读缩写，不创建新的 Lean 名字。

| 主张 | 现有精确端点或来源 | 状态与实际边界 |
|---|---|---|
| 同源有限模型可构造稳定商、控制与生存接口 | `UC.unified_finite_core_control_and_viability` | `THEOREM / CONDITIONAL`；已注册输出和奖励，生存域可为空 |
| 同源精确有限模型存在 all-times 安全路径律 | `UC.single_source_terminal_object_viability_all_times`；非空例 `UC.registered_survival_nonempty_infinite_law` | `THEOREM / CONDITIONAL`；初始 PMF 在生存核内；不是任意近似模型的永续性 |
| 固定有限时域、同一策略下，真实行误差控制真实路径 | `UC.same_policy_projected_path_error` | `THEOREM / CONDITIONAL`；逐行统一误差、相同投影初态及共同粗历史策略 |
| 校准测试可控制同源代表元模型的有限风险 | `UC.calibrated_representative_failure_risk` | `THEOREM / CONDITIONAL`；hcal 仍是确定性前提，参考核按代表元构造 |
| 候选样本损失的统一集中可控制错误解析 | `SC.SISC.measure_bad_empirical_calibration_le` | `THEOREM / CONDITIONAL`；IID、有界损失和显式风险匹配 |
| 所采源行的真实均值校准直接进入上述风险链 | `UC.statistical_representative_risk_certificate`，见本轮 `StatisticalRiskCalibration.lean` | `THEOREM / CONDITIONAL`；§0.3 本地整合验证通过；源行实验、固定测试与共同可测好事件 |
| 样本直接构造参考模型并认证其真实源路径风险 | `UC.statistical_empirical_reference_certificate` | `THEOREM / CONDITIONAL`；全事件测试、经验拟合和共同策略；统计预算含 $2^{\lvert X\rvert}$ |
| 粗风险转为隐藏微观失效风险 | `UC.same_policy_microscopic_failure_risk` | `THEOREM / CONDITIONAL`；必须消费失效包络，而非默认安全目标可由观察恢复 |
| 同一非稳定模型满足实际采样与非平凡微观风险界 | `UC.StatisticalRiskWitness.joint_statistical_microscopic_risk_witness` | `THEOREM / CONDITIONAL`；构造实验中 $\mu(G)\ge3/4$，固定策略下风险至多 $143/256<1$；非经验测得的联合失效率 |
| 固定候选各自覆盖不足以保证选择后覆盖 | `UC.StatisticalRiskBoundary.pointwise_confidence_not_selected_confidence` | `NO_GO`；实际 PMF 的固定失准率 $1/4$ 与选择后 $7/16$；范围是训练后选择 |
| 对象或行为不唯一识别目标与双轴 | `UC.same_process_opposite_goals`；`UC.unanchored_drive_is_not_uniquely_identified` | `NO_GO`；添加独立机制/轴锚可得到受条件限制的正向结果 |
| GOD/GOA 不必唯一 | `bellmanGOD_can_be_nonunique`；`invariantGOA_can_be_nonunique` | `NO_GO`；不否定有唯一性条件的专门模型 |
| 近似有限路径控制不能自动升为全时域存活 | `UC.AbsorbingLeakage.bounded_row_error_with_asymptotic_failure` | `NO_GO`；真实 PMF 正泄漏反例 |
| 一切系统都恰有两条物理/信息驱动 | 数学 H-DDH 与独立实验协议 | `EMPIRICAL / OPEN`；代数表示及秩必要条件不是普遍真实性证明 |
| 稳定/最优/复制优势推出意识与唯一伦理 | PDF p27–28、p40–41；数学 §27.6 已作否定性边界说明 | 不得作为 Core 定理；需明确额外经验与规范桥 |

### 5.2 以解除前提衡量下一步，而不以文件数量衡量

本轮已完成 §3 的三处具体连接：实际样本律与转移均值相同；共同随机好事件支持下游通过检查的划分与策略；粗事件包络覆盖声称的微观失效。§3.7 又以同一非稳定模型、实际乘积采样和严格小于一的数值风险界排除了这些契约只能分别成立的疑虑。选择与泄漏反例继续限制结论范围。本轮本地整合验证见 §0.3；后续科学研究应针对真实应用解除仍未满足的实验前提。

具体模型的参考风险计算已经在 §3.7 完成；面向其他应用的可计算认证、受限源行访问与部署覆盖、相关或自适应采样，以及长期鲁棒性仍各有任务。它们需要相应的数学前提或解除前提的证明。数学 §16.9 给出的覆盖关系，不能在没有密度比或分布差证据时自动套到罕见部署状态。

对“全局优化”的实际反馈是：以 **共享对象、可核查输入、可组合误差、具体反例** 改写理论主线。既保留已经完成的精确同源控制/生存证明，也允许统计与机制证据让某个强哲学主张失败。这样的版本才能让后续研发检验同一理论，而不是不断换一个更容易满足的定义。

## 6. 本文的集成范围与可复核性

本文件属于 Track TC 新增文档，未修改原始附件、现有任务状态、历史凭据、counted Core 或既有研究政策。文中采用现有实际定义；不存在的旧声明名没有被用作证据。新增数学文件的科学状态与实际编译结果须在该研究阶段的证据中登记，不由本文件推断。

新分支 `compression/theory-completion-statistical-risk` 符合 TC 分支模式，其新 Lean 文件及新文档位于已拥有的目录；公共 `TheoryCompletion.lean` 仅可增加导入。基线的旧 `TC-FINITE-HORIZON-RISK-EVIDENCE-2026-10-19` 例外只匹配旧分支，不能沿用为本轮既有文件修改权限。[COMPRESSION_RESEARCH_TRACKS.json](../../COMPRESSION_RESEARCH_TRACKS.json)

本轮研究起点的 mandatory freshness gate 消费 `UMC_GLOBAL_MODULE_DAG_V4.json`，reuse loader 使用显式 overlay/certificate 哈希注册。因而新建一个并行 V5 清单本身不能使既有门验证新源码。本轮本地整合已更新必要的现用证据入口，使运行中的门消费新增数学及其 §0.3 验证证据；相关授权与远端整合生命周期以关联 Git/PR 记录为准。旧快照、旧 overlay 与旧 receipt 保持历史含义，登记不会扩大科学结论。

本稿所识别的必需既有证据入口为当前全局源码 DAG、`knowledge/reuse/fkrg_reuse.py` 和 `knowledge/reuse/test_fkrg_reuse.py`；现行 `audit_umc_local.py` 和 `knowledge/test_fkrg.py` 已能动态消费当前源码，不因模块增加而需要再次修改。入口说明和 clone 扫描器的“live”数字若要更新，应单独列入精确授权范围，不能把文字维护当作修改冻结数学的理由。

本文件的判断以原文、实际类型和当前 mission 为依据。它提供的是可以采纳或被反例纠正的具体反馈，不将任何局部认证等同于“UEOT 的普遍真理已经确立”。
