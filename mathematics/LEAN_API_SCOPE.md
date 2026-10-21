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
