## 阅读说明：数学论证与 Lean 接口范围

本说明逐项区分已发布的生产接口，以及已有书面证明但尚无专门形式端点的连接。本版生产接口包含有限观察编码与路径风险、逐行注册采样及共同 Good 组合的七个扩展模块。这里不是完整前提清单，调用仍须读取完整定理类型。

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

本版引用的 Core 生产范围为 666 模块（655 维护、11 改编）。原 #354 研究原型与首版有限 Y 的编译记录保留其历史身份，当前接口的源码与证据由文末入口定位。固定采样分配不包括数据后决定 N 的停止规则，也不包括任意相关单轨迹样本。

有限编码目前使用非计算定义与 Classical.choose；证明精确保持的是相对于所给有限载体源的 TV，不是所有外部参考之间的全局等距，也不是新可执行的通用编码算法。它与已经实际执行的有限支持 checker 分别说明。

有限编码的基本 TV 定理允许一般概率测度，包括非原子的参考测度；现有路径与风险源仍是 PMF。即使去掉整体 Y 的有限性，参考路径层也只由 PMF 行生成，不能写成已经涵盖任意非原子连续 Markov 核或所有连续随机过程。

### 2. 同源长期实例的范围

数学书 §21.7 的 Lθ、显式 μθ、killed Qθ、参数边界、曾失败风险，以及受限 R 的值和完整 greedy 不变律族，给出完整书面推导。源 survivalMicroKernel、conflictRewardControl、真实安全固定点与一般控制/GOA/QSD 接口已经生产成立；这些新的完整参数化实例尚不称为已有专门 Lean 端点。

InvariantLawGOA、CesaroLimitGOA、KilledQSDGOA 的定义描述给定核，本身没有最优性字段；GreedyInvariantGOASet 绑定所给模型的 Bellman-greedy。受限 R 的动作在 K 外不受保持 K 的蕴含约束，所以其完整 greedy 保持可见位，具有两个闭类及其全部混合不变律。仅从指定 K 初始的实际路径与恒定维持策略相同；不能宣称完整受限 greedy 与全空间恒定策略相同或有唯一全局 GOA。

数学书 §35.7 的非零奖励 P-ALG 注册实例、额外程序表示与两个组织时钟的具体适配亦保留书面范围。该四状态源不展示严格历史记忆增益，第 37 章独立后验与死路见证仍需保留。

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
