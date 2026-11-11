## 阅读说明：数学论证与 Lean 接口范围

本说明逐项区分已发布的生产接口，以及已有书面证明但尚无专门形式端点的连接。**当前数学合同采用至 PR #447（2026-11-11）**：Core 定本保持 `CLASSIFIED_CORE_CLOSED`，严格正概率域的增长分类已完成新增 Lean 合同；经验支持仍为 `UNVERIFIED`。调用仍须读取完整定理类型。

当前总入口为[Core 定本](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_theory_closure_v1/README.md)及其后继[增长参数分类](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_growth_classification_v1/README.md)。以下按来源批次保留接口演进：第 1 节的七个扩展模块和 666 模块统计是当时的范围，不是当前全仓统计；第 2 节已按后继证明更正旧书面义务的状态。冻结的 106 个 P-ID 不因这些后继模块重新编号。

### 1. 概率接口的实际范围

| 接口 | 保留的原接口 | 本版扩展及仍保留的条件 |
|---|---|---|
| 支持生存与观察类型 | 正概率历史支持桥与有限时域 Viable 双向定理不要求 Y 有限 | 已证明，不退回待证明；显式 fallback、同一源和正概率条件保留 |
| 一侧有限支撑的 TV 编码 | 原有限观察路径界仍要求有限 Y | FiniteObservationEscapeCheck.tvDist_atomEncode_eq 及跨空间 live 质量比较已编译；Y 可任意，但有可测单点及一侧完整支撑条件。其他参考质量全部保存在独立逃逸点；FiniteObservationEscapeBoundary 已证明无限环境中 5/12、1/4 与编码后零距离的边界 |
| 完整路径与任意 Y 风险 | coverage_same_policy_path_error 及原风险层仍使用有限 Y | PathObservationEscapeCheck.escape_path_tv 与 ArbitraryObservationRiskCheck 的原空间路径及风险端点已编译；保留同一策略、全部实际占据、原 Q(F)，仅需有限 X、A，Y 有可测单点。可测事件 F 是明确的充分前提，不声称它对所有 PMF 模型都不可弱化 |
| 真实逐行样本 | 旧注册风险使用统一 Fin N；已有数值见证取 N=256 | VariableRegisteredSamples 使用 SampleCoordinate N = Σ j, Fin (N j) 及真实产品测度；registered_row_calibration、product_experiment_calibration 已编译。每条实际行 N j>0；注册、N、半径和源在数据前固定。单行校准组合无需有限训练 Ω，也不要求行间独立 |
| 逐行联合风险 | 旧 RegisteredGoodJointCheck 保留其统一样本签名 | VariableRegisteredJointCheck.registered_selected_joint_failure_of_cap_on_good 的当前任意 Y 版本已编译；保留 Ω、X、A 有限、相关可测单点结构和 Good 上选中 F 的可测性 hF。样本类型为 ∀ j, Fin (N j) → Ω → X，候选类型无需有限。半径按时刻 rho n 参数化，不是 Samples 层任意逐行 rho j 的全部范围 |
| 选中事件包络 | 旧通用与 Viable 组合的 henvelope 对所有候选 c 成立 | 新 VariableRegisteredJointCheck 的 hfit、hcap、henvelope、hchecked 只在同一个 RegisteredCalibrationGood 上要求；任意 Y 版本的 hF 也限定于同一个 Good。henvelope 仅涉及该好记录实际选中的候选。共同微观失败事件 E 固定于采样前 |
| 同 Good 消去占据 | 旧 ViableRegisteredJointCheck 已在内部证明同一 viableFamilyPolicy 的零占据 | ViableVariableRegisteredJointCheck.viable_registered_selected_joint_failure_on_good 的当前任意 Y 版本已编译；hinit、hfit、hF、henvelope、hchecked 限定同一个 VariableRegisteredJointCheck.RegisteredCalibrationGood。策略、参考路径、真实部署核和内部零占据使用同一个 viableFamilyPolicy，不另传 hcap |

该接口批次的历史 Core 生产范围为 666 模块（655 维护、11 改编），不代表当前总模块数。原 #354 研究原型与首版有限 Y 的编译记录保留其历史身份，当前接口的源码与证据由文末入口定位。固定采样分配不包括数据后决定 N 的停止规则，也不包括任意相关单轨迹样本。

有限编码目前使用非计算定义与 Classical.choose；证明精确保持的是相对于所给有限载体源的 TV，不是所有外部参考之间的全局等距，也不是新可执行的通用编码算法。它与已经实际执行的有限支持 checker 分别说明。

有限编码的基本 TV 定理允许一般概率测度，包括非原子的参考测度；现有路径与风险源仍是 PMF。即使去掉整体 Y 的有限性，参考路径层也只由 PMF 行生成，不能写成已经涵盖任意非原子连续 Markov 核或所有连续随机过程。

### 2. 同源长期实例的范围

数学书 §21.7 的 Lθ、显式 μθ、killed Qθ、参数边界、曾失败风险，以及受限 R 的值和完整 greedy 不变律族，最初在本说明登记为书面实例；后继 `ConflictParametricSource`、`Control`、`Stationary`、`QSD`、`Path`、`Infinite` 与 `CommonConsumer` 已接通真实源、完整策略路径及同一无限实验，不能继续列为当前未形式化。准确端点、来源绑定和验证见[原书具名来源包](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/conflict_family_book_source_v1/RESULTS_AND_OPEN_OBLIGATIONS.md)及数学书 §39.71。

InvariantLawGOA、CesaroLimitGOA、KilledQSDGOA 的定义描述给定核，本身没有最优性字段；GreedyInvariantGOASet 绑定所给模型的 Bellman-greedy。受限 R 的动作在 K 外不受保持 K 的蕴含约束，所以其完整 greedy 保持可见位，具有两个闭类及其全部混合不变律。仅从指定 K 初始的实际路径与恒定维持策略相同；不能宣称完整受限 greedy 与全空间恒定策略相同或有唯一全局 GOA。

数学书 §35.7 的非零奖励 P-ALG 注册实例、受保护程序表示、实际后验和两组织时钟恢复，已由 `ConflictOrganizationalSource` 的来源等式与实际消费者形式化。§35.4 的 8/5 等待／修复模型则由独立的 `WaitingRepairControl` 形式化，不能与 §21.7 的源混为同一过程。这些后继结果解除相应的旧书面义务；四状态源不展示严格历史记忆增益的边界保持，第 37 章独立后验与死路见证仍需保留。

### 3. 源码入口

- [DeploymentCoverage](../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/DeploymentCoverage.lean)、[RegisteredDeploymentRisk](../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisteredDeploymentRisk.lean)、[ViableRegisteredJoint](../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/ViableRegisteredJoint.lean)：原生产基线。
- [FiniteObservationEscape](../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteObservationEscape.lean)：本批有限编码核心。
- [PathObservationEscape](../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/PathObservationEscape.lean)、[ArbitraryObservationRisk](../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/ArbitraryObservationRisk.lean)、[FiniteObservationEscapeBoundary](../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteObservationEscapeBoundary.lean)：完整路径来源、原空间风险及正逃逸边界。
- [VariableRegisteredSamples](../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/VariableRegisteredSamples.lean)、[VariableRegisteredJoint](../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/VariableRegisteredJoint.lean)、[ViableVariableRegisteredJoint](../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/ViableVariableRegisteredJoint.lean)：本批逐行采样、Good 包络与同策略组合。
- [TheoryCompletion/GOA](../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/GOA.lean)、[PositiveEigenstructure](../formalization/ueot-core/UEOT/V3/Compression/PositiveEigenstructure.lean)、[SameObjectViableGOA](../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/SameObjectViableGOA.lean)：一般长期接口，具体调用仍需其完整来源字段。

本批命题与验收范围的总入口是 [REGISTERED_INTERFACES_CLOSURE_V1](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/REGISTERED_INTERFACES_CLOSURE_V1.md)。以上相对链接按本说明位于 mathematics 目录设置；链接指向本版生产基线中的源码和说明，适用条件仍以完整定理类型为准。

## 2026-11-04 新合同接口：有限钱包全流程联合决策

前文模块数量与阶段表述保留各自历史时点；本增补不重开已完成的原条件数学合同。新增一般有限返回/过滤/支持支付接口与真实 Register 有限人口消费者，完整清单及实编译、源/输出身份见[交付包](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/joint_decision_closure_v1/README.md)。

`RegisterJointDecisionNativeConsumer` 的 `returned_native_value`、`returned_native_payment`、`returned_native_optimal`、`returned_native_population`、`initial_returned_native_value`、`initial_returned_native_boundary` 直接接原 Store 与 THIS 输出。比较类包括只在实际正概率历史合法的任意实数随机完整历史策略。公开目标、正固定收费、一次 θ、允许收据与地址 0/1 为实例范围；一般期限闭式另外要求 B=c 与 p≥S_H。未知程序、额外读取、全人口同时老化和无限内生资源未被覆盖。后验缓存与有限表缓存分别证明整个原后验和整张返回表相等；实测不预先宣称提速。

## 2026-11-06 新合同接口：源导出的决策充分表示

`RegisterDecisionRepresentation` 连接实际收据观察器、计数后验、全动作充分性、共享DAG、原生Store与逐前缀预付，仍比较任意同信息同钱包完整历史实随机可行策略。准确声明与量词见[定理索引](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/decision_representation_closure_v1/THEOREM_INDEX.md)和[API边界](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/decision_representation_closure_v1/API_BOUNDARIES.md)。

`plan`/`returned`是Option；主结论针对通过精确检查器的实际候选，不另外宣称generate对每个合法输入总通过。13个实际实例均被接受。实际数组界为24(H+1)^4，不是有理位长、总内存或一般POMDP时间界。执行直接走共享节点，理论展开只用于证明；没有新增Lean JSON往返定理，导出身份由实际哈希及独立全动作检查绑定。源权限保持公开goal与地址0/1；地址2可达反例证明权限扩展须细化表示。原完整身份/谱系/None继续保留。

## 2026-11-06：允许实验下的机制分辨与最坏决策损失

公共入口 RegisterMechanismDecision 暴露原返回控制器与完整 Store 达到定理；同信息同钱包对手包括仅在正概率历史合法的实概率动作核。精确分辨、连续私种子分类界、一般证书和原生付款的量词见[定理索引](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/mechanism_decision_closure_v1/THEOREM_INDEX.md)。冻结 H2/H3 数值用 native_decide；实际闭合证明的公理依赖见[审计](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/mechanism_decision_closure_v1/checks/AXIOM_AUDIT.json)。

## Core 定本的同源来源消费者（2026-11-06）

公共入口 `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreTheoryClosure` 可经 `UEOT`、`UEOT.V3.Compression` 或 `UEOT.V3.Compression.TheoryCompletion` 导入。`UEOT.V3` 保持原有并行子集的范围，不导出这 13 个新增模块。原 106 个 P-ID 的冻结映射不改。

`CoreRegenerativeSource` 从真实物理码、执行门、预付费用和 36 个局部噪声原子构造完整事件；`CoreRegenerativeRepair`/`Formation` 复用原修复秩与内生形成；`FiniteSourceGrowthControl`/`ControlPopulation` 消费旧 Perron 工厂并从实际人口推导任意允许历史核的有限条件超鞅与最优达到；`SourceCohortFeedback`/`CoreRegenerativeFeedback`/`FeedbackBoundary` 推出同源独立 cohort 的有限概率反馈及精确失效边界；`Population`/`Lineage` 从真实身份、父指针与标记连接有限 many-to-one；`Quotient` 保持完整事务与允许历史。

新定理没有裸给 success、fitness、条件均值或最优性。C1、C5、连续过程与原 Price 源结果继续按原条件复用，不冒称此有限新消费者重新实例化了每条旧定理。本文的有限条件鞅不是新增无限路径 Mathlib Martingale 实例；期望增长、原身份续存、实际份额、加权谱系和规范价值分别定型。具体可检查声明与信任范围以[定理索引](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_theory_closure_v1/THEOREM_INDEX.md)及[公理审计](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_theory_closure_v1/checks/AXIOM_AUDIT.json)为准。


## 2026-11-11：定本书面补充与新增增长分类的不同证明层次

PR #446 的固定内部程序 2／3／4 任务表示分类，以及公开响应 `(s,b,bq)` 的局部秩三边界，已有书面证明和独立精确核对，**尚未新增各自完整的专门 Lean 端点**。它们使用的原事务、后继和矩来源已有形式证明；具体范围见[定本冻结包](review/CORE_DEFINITIVE_FREEZE_2026-11-11/README.md)。不能将固定程序预测等价当作完整外部控制等价。

PR #447 另有三个新增生产模块，由原 `CoreTheoryClosure` 公共入口导出；它们不是上述书面分类的形式化替代。原定本的 13 个模块及原 106 个 P-ID 合同保留。

| 模块 | 已证接口及责任 |
|---|---|
| [CoreRegenerativeGrowthClassification](../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeGrowthClassification.lean) | `ProbabilityValid`；`valid_iff_probability_advantage_supercritical` 保留旧 `Valid` 的精确拆分；`optimalRate_formula` 给出 `max(1, λ₀, λ₁)`；原完整请求菜单的真实行界与所选行等式 |
| [CoreRegenerativeGrowthPopulation](../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeGrowthPopulation.lean) | 原 `Policy`、`State`、人口递归上的 `optimal_population_upper`、`optimal_hasExpectedGrowth`；公开可执行达到策略、实际继承程序桥和受损创始体收费 |
| [CoreRegenerativeGrowthAttainment](../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeGrowthAttainment.lean) | `optimalRate_isLeast_uniform_upper`；两个程序的 `false_program_attains_iff`、`true_program_attains_iff`；同一受损程序的 `same_damaged_program_repairs_and_attains_iff` 及亚临界失败、旧 `Valid` 特例 |

基本域要求原 36 个噪声原子严格为正，不包含零概率端点。对有限非空 canonical 初始人口，一个常数同时覆盖所有原允许历史实随机联合请求策略及全部有限期限；达到者另有正的双边指数常数。`HasExpectedGrowth` 与最小统一底数是已证 Lean 合同；正次根极限、任意策略的 limsup 解释是书面分析推论，没有另称专门的 Lean 极限端点。

两个程序的内部达到解释使用各自的真实受损创始体、`founder_program`、原继承不变式和 `programPolicy_positive_branch_is_internal`。一般 canonical 人口上的 `programPolicy theta` 首先是公开请求规则，不能无条件改称全体成员已带有该内部程序。原 stop、真实拒绝、观察、六单位事务、身份与遗传未改变；旧选择反馈常数和 cohort 合同未扩大。指数最优不等于每个有限期限人数最优，两个固定程序失优不等于所有含真实修复的政策失优。

[实际 Lean 验证](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_growth_classification_v1/LEAN_VALIDATION.json)绑定三个新模块、受影响公共入口和边界消费者的五次成功检查；15 个所列关键端点仅使用 `propext`、`Classical.choice`、`Quot.sound`。未重跑历史全工程，且该端点范围不改写 PR #443 已披露的数值信任。八组有理数源探针是独立交叉核对，不是新的 Lean 原生执行或经验验证。五项出口的实际状态见[最终验证](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_growth_classification_v1/VALIDATION.json)；该研究单元已完成并停止自动扩题。
