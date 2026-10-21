# UEOT Core：MINCORE → H0 → P-ID → TheoryCompletion 桥接矩阵

日期：2026-10-21。定向源码回顾；未编辑生产、运行 Lean、执行 Git 写入或复做全量审查。读取的本地仓库 HEAD 为 `c30aa219b90173ca15e0eb9878f244de363e1fc3`；它只是本次读取锚点，不代表重新核验了远端 canonical main。当前七模块的集成、构建和发布状态由主智能体的相应收据确定。

## 1. 核心判断与分类口径

统一工作的实质进展，应当是从同一组过程、记录、策略和目标数据推导出下一层对象，并证明有关数据确实相同；随后再说明缺陷、风险、可行性或长期行为怎样传递。生产中已有多条这样的桥，特别包括 **同一有限源的全时域安全** 和 **由历史数据构造同一模型的 GOD/GOA 装配**。不能把本批有限时域支持认证的边界扩写成整个项目尚无无限时域理论，也不能把所有装配都说成并列证书。

本文的标签描述连接在研究中的角色，不更改冻结 P-ID 分类。

| 标签 | 本文含义 |
|---|---|
| THEOREM | 明示输入之下，连接及所强调的来源身份已在现有证明中推出；仍需阅读该行的假设。 |
| CONDITIONAL | 结论已有证明，但突出保留了需独立成立的可观测性、校准、收缩、正特征结构或语义条件。 |
| ADAPTER | 既有领域定理/语义结构的显式适配；不会因此变成四生成元的自动推导。 |
| BOUNDARY | 已证明的反例、不可识别性或不能删除的范围限制。 |

冻结口径维持 **106 项 = 11 generated / 89 adapters / 6 boundaries**。四个计数生成元仍为 M-QD-01、M-TC-01、M-PE-01、M-OI-01。本表的若干 BOUNDARY 行是后续研究成果，不能据此增加或替换冻结的六项。

路径缩写均相对 `/workspace/scratch/9a8d58b21e30/ueot-integration/formalization/ueot-core/`：`V = UEOT/V3/`，`C = V/Compression/`，`TC = C/TheoryCompletion/`，`U = TC/UnifiedClosure/`。表中“文件 : 端点”组合给出可直接定位的 Lean 声明。

## 2. MINCORE、H0 与冻结端点

| 连接 | 分类 | 精确端点与路径 | 假设、真实内容与适用边界 |
|---|---|---|---|
| 精确关系 → 可比较缺陷 | BOUNDARY | `TC/MinCore/RelationDefectNoGo.lean : no_relation_only_quantitative_recovery; relationDefectPresentation_does_not_force_triangle`；`TC/MinCore/CalibratedDefectComparison.lean : same_relation_does_not_transport_unit_budget` | 同一零缺陷关系不能恢复数值缺陷、单位预算或三角结构。此处否定的是“关系本身足够”的推论，不否定额外校准下的定量统一。 |
| 已校准缺陷 → 同一零结构、预算与 M-TC 链 | CONDITIONAL | `TC/MinCore/CalibratedDefectComparison.lean : DefectCalibration.rel_iff; forward_budget; reverse_budget; tendsto_zero_iff; calibrated_weighted_chain_bound`；`TC/MinCore/DefectGaugeCovariance.lean : DefectCalibration.triangle_quasi; calibrated_cross_stage_contraction; rescaled_weighted_chain_bound` | 输入 `a>0, b≥0, a·d≤d′≤b·d`；同一关系由校准推出。预算正向乘 `b`、反向除 `a`；一般校准仅把三角不等式变成因子 `b/a` 的准三角形式。正的逐层标量重标度才保持精确三角型，并把链参数变为 `L′ₙ=(cₙ₊₁/cₙ)Lₙ, ε′ₙ=cₙ₊₁εₙ`。**这条桥已经存在；不要重新创造 CalibratedDefectComparison。** |
| M-QD → H0-PQ → P-PRED-01 | THEOREM | `C/QuotientDescent.lean : countableAEFamily_descend; p_pred_01_via_countableAE_descent` | 可数协议族、可测核及各坐标 a.e. 因子分解，推出一个共同满测集上的联合可测解码器、模零最小性与坐标恢复。一般输入核的存在仍由来源模型提供；此定理没有声称从任意裸载体生出观测实验。 |
| 当前预测坐标 → 下一步 Bayes 响应 | ADAPTER | `V/PredictionUpdate.lean : RecursiveCoordinateClosure; p_pred_03_recursive_update`；`C/RecursiveSufficientState.lean : existsUnique_reachableUpdate; existsUnique_ambientUpdate_of_surjective` | P-PRED-03 显式提供观察边缘与“观察＋延续”联合事件的坐标索引，以及这些坐标确为实际概率的 `hObs/hJoint`；有限动作/观察、可测单点和可数延续坐标用于相应接口。零分母分支是任意数学延拓。可达状态上的唯一更新与整个环境状态上的唯一更新不同，后者还需满射。 |
| M-TC → H0-DYN/HIST → 路径误差与 P-ID | THEOREM | `V/PathError.lean : p_dyn_03_finite_path_error`；`V/TransportDefect.lean : FrozenTransportSystem.p_id_01`；`V/DevelopmentTransport.lean : development_pipeline` | P-DYN-03：同一初始律、有限记录、逐史下一记录 TV≤εₙ∈[0,1]，得路径 TV≤`1−∏(1−εₙ)≤∑εₙ`。P-ID-01：概率核及可测传输满足恒等/组合律，逐邻接 TV 预算累加。P-ID-02：参考递推、实际残差、非负 Lipschitz 常数给出加权链界。**这些身份延续/误差定理没有单独建立祖先谱系、父对象形成或生产来源。** |

H0 的组织作用是显式列出领域结构及其连接。`docs/compression/hierarchy/H0_HIERARCHY_INVENTORY.md` 中 H0-RES 的闭包/Galois/阻断对偶、H0-COMP 的共同联合律与不可分性、H0-SEL 的复制信道与选择结构仍有各自适配或边界。它们不因可用 M-QD/M-TC 语言表述一部分结构，就自动成为全部由四生成元重推导的结果。本次只复用该库存的数学映射，不复用其中旧模块计数。

## 3. 受控动态、实际路径与风险

| 连接 | 分类 | 精确端点与路径 | 来源身份、量词与剩余条件 |
|---|---|---|---|
| 同一随机未来响应 → 精确控制商 | CONDITIONAL | `U/StochasticPredictiveObservabilityBridge.lean : FutureTestsResolvePredictiveClasses; stochastic_future_tests_force_strong_lumpability`；`U/PredictiveOptimalControlLift.lean : predictiveFutureExactControlQuotient; future_observability_yields_micro_optimal_macro_control` | 有限微状态/动作/探针，动作非空；每个可达预测类的指示函数须能由**同一 K/read 的实际未来字词概率**线性重构。由此证明强 lumpability，再构造同源微观/宏观转移与控制商；最优值、Q 值及宏观贪婪策略提升成立，并支配所有因果历史随机微策略。类上有界奖励及 `0<β<1` 明示给定；预测结构本身没有决定奖励。 |
| 同一 P-ALG 表 → 组织商、原微观控制与可行反馈 | THEOREM | `U/UnifiedCoreClosureCertificate.lean : unified_finite_core_control_and_viability; registered_organizational_attributes_preserved`；`U/ViabilityKernelIntertwining.lean : micro_viability_iff_macro_viability` | 从一个归一化有限表 `M` 构造终止稳定划分、SISC 核与精确控制商，**转移、奖励和受保护输出的身份实际推出**。安全条件是输出的注册谓词；微观可行域是宏观域的精确逆像，有限迭代给出固定点及反馈。注册 program/resource 标签只保护当前状态信息，不推出真实历史程序、物质自生产或祖先来源。 |
| 上述同源有限表 → 真正无限路径上的全时域安全 | THEOREM | `U/CoreInfinitePathClosure.lean : micro_pmf_viability_fixed_of_macro_real_fixed; exists_source_micro_all_times_viable_path_law`；`U/CoreSourceAllTimesAssembly.lean : single_source_terminal_object_viability_all_times` | 实际证明实数权重可行固定点也是原微观 PMF 删除算子的固定点，再复用 `V/ViabilityTrajectory.lean : exists_stationary_policy_all_times_of_fixed`。对**每个支撑在所算固定点内的初始 PMF**，存在由该源支持导出的确定性平稳反馈，使真实 `stationaryTrajMeasure` 对“所有自然数时刻均安全”赋概率 1。可行域可能为空；不能省初始支撑条件，也没有认定该反馈等于无约束 Bellman 贪婪策略。 |
| 支持递推 → 实际后验 → 有限认证策略 | THEOREM | `U/FiniteSupportViability.lean : SupportViabilityClosure.traceSupport_eq_fiberTerminalPosterior_support; zero_uncovered_iff_support_certified; initial_viability_iff_exists_zero_uncovered_policy` | 有限 X/A，Y 可任意；后验等式只在该**实际策略的正概率完整观察/动作历史**上成立。零未认证占据恰为实际支持上所有正概率受选动作均认证。所有非空初始观察纤维的有限可行性，等价于存在**同一个完整因果策略**在每个 `n<T` 零占据；完整 fallback 显式提供。这是过渡行认证，未设置终端安全约束，不能直接等同物理存活。 |
| 实际受选行 → 同策略完整路径 → 微观风险事件 | THEOREM | `U/DeploymentCoverage.lean : coverageDeploymentRowLaw; coverage_same_policy_certified_path_error; coverage_same_policy_microscopic_failure_risk`；`U/FiniteHorizonRisk.lean : risk_causalLaw_map; risk_event_transfer`；`U/MicroscopicFailureRisk.lean : risk_microscopic_event_le_envelope` | 占据律由同一初始律、微观转移与观察历史策略生成，记录包含动作。行预算经真实占据权重成为路径预算，再由 `E⊆projection⁻¹(F)` 转为微观失败概率界；F 的可测性及行 TV 预算不可删除。成熟旧接口使用有限观察 Y；本轮有限像/任意观察候选的发布状态另按主智能体收据判断。`ε+(1−ε)u` 中把 u 换成上界还需要 `ε≤1`。 |
| 有限可行策略 → 同一注册训练/部署联合实验 | THEOREM | `U/RegisteredDeploymentRisk.lean : RegisteredGoodJointCheck.registered_selected_joint_failure_of_cap_on_good`；`U/ViableRegisteredJoint.lean : ViableRegisteredJointCheck.viableFamilyPolicy; viable_registered_selected_joint_failure_on_good` | 每条注册行的样本可测、行内独立且律**等于同一 P 的该行**；不需另加跨行独立。数据依赖 select 与同一个 Good 事件参与拟合、占据/初始可行性和预算检查。组合端点内部证明**自己使用的 viableFamilyPolicy**零占据，得 `min(1,α+(1−α)β)`，坏训练事件只算一次。β∈[0,1]；本成熟版本统一 `Fin N`，包络对所有候选成立。新逐行 N/Good 包络接口不因本表采用旧端点而被重新列作“从未实现”。 |
| 好策略存在 → 任意先前认证前缀可延拓 | BOUNDARY | `U/ControlCoverageWitness.lean : viable_source_with_a_covered_deadend; checking_one_representative_does_not_bound_actual_coverage; whole_current_fiber_has_no_common_action` | 实际反例分别阻断：把存在好策略升级成每条认证前缀可延拓；把一个代表点的认证当成整纤维/真实占据认证；把当前观察纤维当成每条历史的后验支持。应在实际支持上量化，不删除正概率历史条件。 |

## 4. GOA、存活与目的适配

| 连接 | 分类 | 精确端点与路径 | 已证身份及仍然独立的条件 |
|---|---|---|---|
| 可行核 → 同一源上的安全最优控制 | THEOREM | `U/SafeOptimalControlFromViability.lean : viableRestrictedModel; viable_restricted_greedy_preserves_source_kernel; viable_restricted_optimal_dominates_all_causal_policies` | 由实际 PMF 可行固定点 `viabilityStep P K=K` 推出可行行动非空；限制模型逐项使用原转移和奖励。其贪婪反馈保持 K，并对所有遵守相同行动限制的历史随机策略最优。域外限制为空真；结论是安全约束下最优。`U/SafeRewardConflictWitness.lean : conflict_same_source_reward_and_risk` 已给出同一源上即时高奖励与离开安全域的冲突，当前该见证没有自行分类全部最优 GOA。 |
| 有限长期占据 → 不变律 | THEOREM | `V/FiniteCesaroInvariant.lean : p_goa_01`；`C/OccupationLimitInvariance.lean : p_goa_01_via_occupationLimit`；`TC/GOA.lean : cesaroLimitGOA_is_invariant; greedyInvariantGOASet_nonempty` | 给定一个有限行随机核和初始概率律，Cesaro 子列极限存在并为同核不变律。贪婪闭环的不变 GOA 非空直接使用该闭环的实际矩阵。基础存在性不要求 Dobrushin，也不推出唯一性、所有初值同极限或逐时分布收敛。 |
| 原历史响应 → 同一有效模型 → GOD/唯一稳定 GOA | THEOREM | `C/AgencyGodGoaAssembly.lean : HistoryControlSpec.stateResponse_spec; agency_god_goa_from_history` | `C:H→S` 满射，有限非空 S/Act，有界奖励、`0<β<1`；**联合的奖励/下一状态响应**对 C 纤维兼容。控制模型 `D.toModel` 由这份历史数据构造，源码证明其奖励/转移在 C 上的原值身份，并给出 Bellman 最优、所有因果随机策略的价值上界。唯一且几何吸引的 GOA 还用该实际贪婪矩阵的严格 Dobrushin 条件 `α<1`。这已是真正同源装配，不能归为仅把独立证书放在一起。 |
| 同一 Objecthood 父对象 → 目的控制与可存活 GOA | ADAPTER / CONDITIONAL | `TC/SameObjectEffectiveState.lean : existsUnique_parentDynamics_effectiveResponse`；`TC/SameObjectObjecthoodAnchor.lean : ObjecthoodTeleologicalControlSpec.toControlModel_transition_selectedParent`；`TC/SameObjectViableGOA.lean : ObjecthoodTeleologicalControlSpec.persistenceSupportedGreedyGOASet_nonempty; existsUnique_stable_persistenceSupportedGreedyGOA` | 父对象 token、其 own history 和选定父对象实际动力学的身份固定；不能替换为另一个 parent。输入强 Objecthood 证书及明确的 teleological contract/actionFuture/数值表示与有界性。存在持久域支持的 GOA 需 **该贪婪动作保持该证书的同一 persistence.K**；初始种子来自 Objecthood 证书。唯一全局吸引还需严格 Dobrushin。对象存在、某个存活控制器存在、任意目的的无约束贪婪控制安全是三个不同命题。 |
| 正 Perron 数据 → QSD、存活幂与 Doob 核 | CONDITIONAL | `C/PositiveEigenstructure.lean : p_qsd_02_via_positiveEigenstructure; p_qsd_02_killed_via_positiveEigenstructure`；`V/QSDPerron.lean : qsd_survival_mass_pow; qsd_all_steps`；`TC/GOA.lean : killedQSDGOA_all_steps; killedQSDGOA_rho_le_one` | 正 scale/right vector 与规范化左右特征结构、非负/次随机条件按接口输入。QSD 初始律 r 满足 `rQ=ρr` 时得到 r 的存活幂与归一化不变性；并未仅从“有有限控制模型”推出正 QSD。若自由给定 Q 与另一风险模型，现有两个结果的并列不能自动证明 Q 是其实际安全限制；需要下节的构造性来源桥。 |
| 机制/载体 → 目的语义 | BOUNDARY / CONDITIONAL | `TC/Purpose.lean : positiveAffineEquivalent_to_policyOrderingEquivalent; carrier_does_not_determine_choiceRepresentationClass`；`TC/PurposeIdentifiability.lean : purpose_not_identified_of_valid_counterexample; unconstrained_objectEvidence_projection_not_purposeIdentifying`；`TC/ScientificClosure/C6PurposeMechanism.lean : mechanismObservation_identifies_teleologicalClass; mechanismTeleologicalFaithfulness_not_automatic` | 正仿射表示保持弱序，弱序保持最大化集合；这些层次不可倒置。机制观察识别目的类需 `MechanismTeleologicalFaithfulness`。裸载体/无约束扩展的反例只证明相应接口不可识别；若要宣布“完整有效 Objecthood 模型的证据不能识别目的”，还必须给出同一有效性谓词下的两个真实模型。目的类识别也没有推出数值代表唯一。 |

## 5. 私有 SourcePolicyPathBridge 的准确增量

已存在的 `V/CoreOperationalAssembly.lean` 定义了随机平稳策略的 `policyTransitionPMF`、纯状态记录的 `policyPathKernel` 以及同源 `policyMatrix`，且已有 `same_policy_path_error` 与 `same_policy_goa02`。`CoreInfinitePathClosure` 已连接所合成确定性反馈的原源 PMF 与无限轨迹安全。上述已有连接均应直接复用。

私有候选 `/workspace/scratch/9a8d58b21e30/tmp/finite-encoding-20261021/resume-source-bridge/SourcePolicyPathBridge.lean` 的两个目标是：

1. `actual_next_state_eq_stationary_row`：以 `sigma : Y → PMF A` 构造真实观察策略 `πₙ(h)=sigma(last(h))`，并从同一个 M 定义源 `Pₙ=M.transitionPMF`。将风险接口 `riskMicroControlKernel` 的 `(action,nextState)` 记录经 `Prod.snd` 推前，证明其等于既有 `policyTransitionPMF M` 的行；不把二者相等当输入。
2. `actual_state_path_eq_stationary_path`：对每个初始 PMF p₀、每个 n，把整条实际动作/状态历史擦除动作后，证明得到 `causalLaw p₀ (policyPathKernel M liftedPolicy) n`。擦除保留所有微观状态，不仅保留终点。

这里是一个新的**接口来源身份**：将原风险实验的动作记录语义接到既有随机平稳状态路径/矩阵语义。定向符号搜索中，生产 `riskMicroControlKernel` 与 `policyPathKernel/policyTransitionPMF/policyMatrix` 没有同文件交叉使用；未找到该直接端点。这个搜索只支持“当前直接端点未找到”，不声称所有通用推前引理均不能推出它。候选本身已复用 `Model.transitionPMF_apply_toReal`、`policyTransitionPMF_apply_toReal`、`risk_last_project`、`risk_map_extend_right` 与 `coverage_map_extend_reference`，不重建已有随机过程。

准确范围：有限 X/A、非空 A、任意观察类型 Y；σ 在每个时刻与每条历史都只依赖当前观察，且不依赖时间。观察过程 Y 不需要自身 Markov、lumpable 或有限。任意历史依赖策略通常只能得到历史核；若引入有限记忆扩充状态，必须证明该记忆更新的实际来源。时间依赖 σₙ 通常得到非齐次状态核，不能直接套一个齐次 `policyMatrix` 的 QSD。擦除动作的推前直接传递**状态路径事件的逆像**；含动作的任意失败事件 E 仍须保留原记录律，或另证它可经纯状态路径因子化。当前私有候选的实际编译状态由主智能体的聚焦收据确定，本矩阵不将其新增为已集成生产定理。

## 6. 由事实导出的下一批最小任务

**第一优先：在完成当前七模块发布闭环后，接上实际风险路径与同一矩阵的存活事件。** 私有路径桥若经编译和审查通过，就以它为唯一来源入口。对实际闭环矩阵 L、注册安全域 K，直接定义 `Q(u,v)=L(u.val,v.val)`，而不是输入一个自由 Q 再假设相等。对实际初始律 p₀，定义 `η₀(u)=p₀(u.val)`；允许 p₀ 在 K 外有质量，因此 η₀ 可为次概率。应证明

\[
\Pr(X_0,\ldots,X_n\in K,\ X_n=v)=(\eta_0Q^n)(v),\qquad
\Pr(X_0,\ldots,X_n\in K)=\eta_0Q^n\mathbf1.
\]

这一步的增量是实际联合事件身份，无需任何 QSD 假设。条件终端律仅在该存活质量正时归一化。精确合同及五类边界已在 `resume-source-bridge/CONTRACT_KILLED.md` 修订 2 中独审 CLEAR，状态仍为数学合同，未形式化；没有必要再起一份并列证书。

**第二优先：将现有 M-OI / M-PE 后果绑定这一个源。** Cesaro 对同一 L 使用既有端点即可；QSD 则按已给出的左特征关系选择实际初始律，再由上式推出实际存活 `ρⁿ`。不能用全支撑左 QSD 推出每个初态在每个时域均有正存活；一般需要严格正右特征向量等额外条件。有限时域条件生存核由 `g_r=Q^r1` 导出；它和固定 Doob 核的相等需要额外条件。条件于生存会改变动作分布以及初始律，原风险/注册策略的身份不能在此步骤悄悄沿用。

**第三优先：只补真实的对象—目标适配条件。** 保留生产已证的同源历史模型、受限 Bellman 与全时域安全；在具体非空实例上证明其 greedy 安全条件、奖励表示与目标序关系，然后复用 SameObject/GOA 端点。若模型未具备机制到目的的 faithfulness，就把它列为该模型的待证条件或给出有效模型反例，不能把希望得到的目的结论写入新的装配假设再宣称闭合。

对两部著作的反馈应据此区分：数学书写出实际构造、假设及策略/实验身份；哲学书讨论“在何种可检验关系下，多个描述属于同一对象”“目的表示何以多样而选择语义可保持”“持续性为什么不等于最优性”。这些成熟结果支持有条件的统一结构，不支持从 Lean 推出经验世界、意识、伦理或完整自然理论已获证明。

## 7. 主智能体追加的执行状态（2026-10-21）

以上独立矩阵原始 SHA256 为 `1fe4acdf1da97e88b12aeb2ed706f28a69ee594a72b286b29f0957655da9d9d7`。本归档仅将“实时权重”的笔误修正为“实数权重”；其余矩阵正文保留。本段单独补充随后实际执行的状态。

SourcePolicyPathBridge 源 SHA256 `108500fc13229b8faffc9829d886313167142075112bc3f6c023a086c074ae91` 已实际聚焦编译 PASS，Lean exit 0，35.495 秒；两个端点的实际 `#print axioms` 仅为 propext、Classical.choice、Quot.sound。源码和证明体未改，原首次包根目录错误保留。该结果仍是私有候选，不属于七模块生产候选、native census 或 canonical main。

killed 合同仍为已审数学合同；后续私有形式化工作另以实际收据为准，不由上述两个端点的通过自动升级。详细任务次序见 [下一阶段研究计划](../derivations/UEOT_CORE_UNIFICATION_NEXT_2026-10-21.md)。
