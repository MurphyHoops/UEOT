# UEOT 规范阅读导航：44 个入口与假设边界

这份导航把现有数学库整理为一条可审查的阅读路线。44 是入口文件数；所有既有导入和传递依赖继续保留。没有新增或宣称编译过 `UEOT/Canonical.lean` 之类的 facade，也不按阅读数删除 V1/V2/V3 的源定理。

本轮源清单为 **641 个随包 Lean 模块 = 630 个 UEOT 维护模块 + 11 个改编上游模块**。实时源路径和内容以 [现有源 DAG](../unified_closure/UMC_GLOBAL_MODULE_DAG_V4.json)、[复用导航器](reuse/README.md) 的逐文件 SHA 校验为准；这里是阅读索引，不是另一份 counted ledger。106 个 P-ID 的证明状态与 11 generated / 89 adapter / 6 boundary 的压缩分类继续使用既有账本。

## 先核对的问题

每次把两个端点接起来，先比较：是否为同一个源模型、同一状态/动作域、同一观测时序、同一初始律和策略；目的、身份、安全、谱系或尺度保持条件是否已经给出。下面的顺序是教学顺序，不是声称每一相邻文件都直接调用前一个文件的证明。编译器证明项中的实际直接依赖另由复用证据记录。

## 基础：载体、预测、概率核与分辨率

| # | 现有 Lean 文件 / 优先端点 | 阅读问题与前提边界 |
|---|---|---|
| 1 | [Blocker.lean](../../../../UEOT/Core/Blocker.lean) — `blocker_involution` | 最小失效集合怎样与最小充分载体形成 blocker 对偶？ 前提：有限底集，载体族为 clutter（包含反链）；消除集合按击中关系定义。 边界：这是有限组合结构；不能把任意实体的物理自维持性从对偶本身推出。 |
| 2 | [Access.lean](../../../../UEOT/Core/Access.lean) — `sufficient_iff_factors_range` | ‘可访问’和‘足够表达目标’在什么意义下能由 decoder 因子化刻画？ 前提：给定read与target，有限坐标子集；decoder限制在实际实现的readout范围。 边界：充分性相对已指定target；不是从数据发现target或对象本体。 |
| 3 | [PredictionDependent.lean](../../../../UEOT/V3/PredictionDependent.lean) — `canonical_ae_minimal` | 各协议有不同未来输出空间时，如何构造同一规范预测状态和最小性？ 前提：协议族可数；各response kernels已经给出并可测；共同零测集来自可数性。 边界：不自动构造未知response kernels，不把不可数协议的零测例外合并。 |
| 4 | [PredictionUpdate.lean](../../../../UEOT/V3/PredictionUpdate.lean) — `p_pred_03_recursive_update` | 观测更新如何真正通过当前预测状态闭合，零概率分支如何处理？ 前提：RecursiveCoordinateClosure、action/observation response坐标闭合与可测性；Bayes有效分支满足正分母。 边界：零分母分支是约定扩张，不是经验认证；这里不是全套主动推断模型。 |
| 5 | [DynamicsKernel.lean](../../../../UEOT/V3/DynamicsKernel.lean) — `strongLumpability_iff_pathLaw_of_surjective` | 精确 lumpability 何时等价于宏观路径律，而不只是一步图交换？ 前提：Markov kernel、可测粗映射、相应可测/轨迹结构；唯一性或反向识别使用满射条件。 边界：不能把任意coarse map视为Markov quotient；文件头残留‘path bridge待做’已经被后面的endpoint超越。 |
| 6 | [InformationPacking.lean](../../../../UEOT/V3/InformationPacking.lean) — `common_decoder_half_distance` | 同一表示把两个真实预测律合并时，最少会损失多少TV预测精度？ 前提：真实概率律的TV分离、共同decoder、所声明精度界；packing注入性需要分离裕量。 边界：证明预测表示下界；不能直接把TV等同于UEOT Φ或物理信息成本。 |
| 7 | [Resolution.lean](../../../../UEOT/V3/Resolution.lean) — `pushFamily_realization_interval` | 同一宏观载体族允许哪些微观实现，何时实现唯一？ 前提：粗映射、向上闭族/有限clutter与active-fibre条件。 边界：H0-RES保留其Galois/实现结构；不等于普通quotient descent或Wilsonian RG。 |

## 压缩：四个生成元与定量校准边界

| # | 现有 Lean 文件 / 优先端点 | 阅读问题与前提边界 |
|---|---|---|
| 8 | [QuotientDescent.lean](../../../../UEOT/V3/Compression/QuotientDescent.lean) — `fiberCompatible_iff_existsUnique_descend` | 纤维相容性究竟生成哪些商下降结论，哪些可测性仍要外供？ 前提：set-level下降需纤维常值及满射；a.e.版本另需可数协议和坐标可测。 边界：M-QD counted有明确mapping范围；set-level law不会自动成为measurable Markov kernel。 |
| 9 | [TransportCertificate.lean](../../../../UEOT/V3/Compression/TransportCertificate.lean) — `weighted_chain_bound` | 局部缺陷经过可控传输后，如何累计成有限链误差证书？ 前提：三角/transport不等式、非负Lipschitz系数与局部误差；概率实例需匹配原source kernels。 边界：独立generic-to-source证据不可改回source endpoint的alias；有限链界不自动给无限时间稳态。 |
| 10 | [PositiveEigenstructure.lean](../../../../UEOT/V3/Compression/PositiveEigenstructure.lean) — `qsdDoob_bundle` | 同一个正特征结构如何桥接QSD/Doob与演化鞅？ 前提：有限正算子与供给的正左右特征数据、归一化；鞅还需条件均值与可积条件。 边界：不在本生成元里证明Perron存在性、primitive渐近或连续谱隙。 |
| 11 | [OccupationLimitInvariance.lean](../../../../UEOT/V3/Compression/OccupationLimitInvariance.lean) — `p_goa_01_via_occupationLimit` | 趋零的占据残差为何让极限成为不变测度？ 前提：适当observable极限、残差趋零；紧性/紧致性、Feller连续性、support继承由adapter提供。 边界：不是无条件极限存在定理；文件头Experimental为历史措辞，当前M-OI counted以ledger为准。 |
| 12 | [RelationDefectNoGo.lean](../../../../UEOT/V3/Compression/TheoryCompletion/MinCore/RelationDefectNoGo.lean) — `no_relation_only_quantitative_recovery` | 仅知道精确关系或零缺陷集合，能否重建所有定量误差尺度？ 前提：非负defect与zero-set关系一致；正缩放及有限反例构造。 边界：结论是否定relation-only定量恢复，不是证明所有未来压缩方案不可能。 |
| 13 | [CalibratedDefectComparison.lean](../../../../UEOT/V3/Compression/TheoryCompletion/MinCore/CalibratedDefectComparison.lean) — `calibrated_weighted_chain_bound` | 补上双边校准后，哪些M-TC预算和渐近性质能跨表示传输？ 前提：a*d ≤ d′ ≤ b*d，a>0，b≥0；原transport chain假设明确保留。 边界：精确关系不自行给出校准，单位三角常数也不自动保持；后续 DefectGaugeCovariance 给出显式变换预算。 |
| 14 | [DefectGaugeCovariance.lean](../../../../UEOT/V3/Compression/TheoryCompletion/MinCore/DefectGaugeCovariance.lean) — `rescaled_weighted_chain_bound` | 改变缺陷刻度后，准三角、收缩系数和链预算如何同步变换？ 前提：双边校准参数及原来的三角/传输不等式均显式给出。 边界：正缩放与双边比较有不同假设；没有从精确关系单独恢复度量。 |

## 同源控制与生存：真实桥接、策略与非空性

| # | 现有 Lean 文件 / 优先端点 | 阅读问题与前提边界 |
|---|---|---|
| 15 | [PathError.lean](../../../../UEOT/V3/PathError.lean) — `p_dyn_03_finite_path_error` | 一步TV差异怎样得到真正有限因果路径律的乘积误差上界？ 前提：有限PMF路径/因果法则、每步TV误差在[0,1]及共同源构造。 边界：端点已含随机路径桥；文件头关于仅代数部分的描述过期。路径误差小不等于对象身份相同。 |
| 16 | [FiniteDiscountedCausalInfinite.lean](../../../../UEOT/V3/FiniteDiscountedCausalInfinite.lean) — `infiniteValue_le_optimal` | 最优性有没有覆盖历史依赖、随机化的全部因果策略？ 前提：有限state和state-dependent action集合、非空动作、bounded reward、discount在(0,1)。 边界：这是真正因果策略上界，但目标reward已经指定；不等于内生目的或无限持续性。 |
| 17 | [ViabilitySource.lean](../../../../UEOT/V3/ViabilitySource.lean) — `p_per_03` | 生存核的删除算法、策略语义和真实无限路径见证怎样合一？ 前提：有限X/A，PMF动力学、safe集合、可测单点；初始律支持在稳定生存核。 边界：有限随机生存核，不应误称任意连续Aubin控制系统；生存核可以为空。 |
| 18 | [DeterministicDiracPredictiveBridge.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/DeterministicDiracPredictiveBridge.lean) — `canonical_future_dirac_strong_lumpability` | 怎样从同一个确定性step构造随机核并导出预测商，避免两套源模型？ 前提：有限确定性controlled process、完整未来响应等价、同一step的Dirac核。 边界：一般随机过程仍可能不lumpable；确定性正例不证明一般随机预测商闭合。 |
| 19 | [PredictiveOptimalControlLift.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/PredictiveOptimalControlLift.lean) — `future_observability_yields_micro_optimal_macro_control` | 同一随机源的未来可观测性怎样接入既有P-QUO-01最优控制？ 前提：有限共享动作；FutureTestsResolvePredictiveClasses的线性可分辨证书；bounded宏观reward及discount(0,1)。 边界：证明调用既有P-QUO端点而非重写Bellman；reward/完整可观测性仍为显式输入。 |
| 20 | [PredictiveViabilityTransport.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/PredictiveViabilityTransport.lean) — `macro_support_viability_lifts_to_micro` | 宏观可生存集合通过真实预测商怎样保持微观路径安全？ 前提：ExactControlQuotient；安全集是宏观predicate的饱和拉回；动作正support保持条件。 边界：主要是有条件有限路径不变性；安全集、保留性以及生物对象解释不从预测充分性自动产生。 |
| 21 | [SafeOptimalControlFromViability.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/SafeOptimalControlFromViability.lean) — `viable_restricted_greedy_preserves_source_kernel` | 如何由原源的生存核导出允许动作，并在允许因果策略中做最优控制？ 前提：同一有限source model、已证明viability固定点；按真实PMF支持限制state-dependent action。 边界：constrained optimality；不保证无约束最优策略安全，核外动作限制为空泛条件。 |
| 22 | [UnifiedCoreClosureCertificate.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/UnifiedCoreClosureCertificate.lean) — `unified_finite_core_control_and_viability` | 有没有真正把稳定分区、源核一致性、控制和生存接成同源构造链？ 前提：一个有限controlled Model；bounded reward/discount；安全谓词由受保护output标签决定。 边界：生存集合可为空；标签为注册输入，不能由此宣称物理自生产、谱系和内生程序。 |
| 23 | [SISCApproximateLumpability.lean](../../../../UEOT/V3/Compression/TheoryCompletion/ScientificClosure/SISCApproximateLumpability.lean) — `robust_class_mass_from_approx_observable_tests` | 近似类指标重构如何把观测测试误差传到每一类的转移质量？ 前提：对所有目标类和状态的重构残差 δ；所有相关行的测试差界；系数 L1 范数。 边界：测试和选定分区 S 都是输入，统计覆盖概率尚需外部证据。 |
| 24 | [StochasticPredictiveRobustObservability.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/StochasticPredictiveRobustObservability.lean) — `quantitative_future_probe_mass_defect` | 规范未来测试的有限误差怎样控制规范预测类质量？ 前提：精确的未来类指标展开、同一源核、当前读出相等，以及完整延伸词的真实误差界。 边界：这里的类是指定 K/read 的规范未来类，不能直接改称任意选定商。 |
| 25 | [FiniteHorizonPathAdapter.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteHorizonPathAdapter.lean) — `finite_horizon_path_error` | 既有 P-DYN 路径定理如何只要求 n<T 的行条件？ 前提：同一初始律、因果 PMF 核、区间 [0,1] 内的有限时段误差。 边界：适配保留真实路径律；没有把有限时段假设提升为无限时间控制。 |
| 26 | [FinitePMFProjection.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FinitePMFProjection.lean) — `risk_conditionedRow_tv_le` | 不假设精确 lumpability 时，真实投影路径怎样通过纤维后验条件核递推？ 前提：有限 PMF、具体投影、同权混合；TV 条件在后验的实际支持上成立。 边界：零质量纤维的总化选择不改变联合律；不存在默认的无记忆宏观核。 |
| 27 | [CalibratedRiskRows.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CalibratedRiskRows.lean) — `calibrated_observable_partition_tv_budget` | 归一化 PMF 的坐标误差及实验校准怎样给出真正的 TV 行预算？ 前提：实际 PMF；坐标界，或给定 δ/η/ρ/κ 的全域测试重构与校准假设。 边界：复用既有 half-L1 定理。实测数组可不归一化，但不把它们当成真实 PMF。 |
| 28 | [FiniteHorizonRisk.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteHorizonRisk.lean) — `calibrated_representative_failure_risk` | 同一宏观历史策略下，真实微观投影路径的失败风险怎样受控？ 前提：相同投影初始律；同一策略 π；所有动作的有限时段行界；指定可测失败事件。代表元校准前端还要求 r 为截面。 边界：代表元宏观核由真实源行构造。任意独立学习 Q 仍需要额外实际行校准；不能得出对象永生。 |
| 29 | [AbsorbingLeakage.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/AbsorbingLeakage.lean) — `bounded_row_error_with_asymptotic_failure` | 很小的每步模型误差为什么仍可导致长期失败概率趋于 1？ 前提：明确归一化的两状态吸收模型，固定正泄漏率 ε∈(0,1]。 边界：这是严格反例，隔离有限风险控制与无限持续性所需条件。 |

## Objecthood / Theory Completion：程序、目的、谱系、生命周期

| # | 现有 Lean 文件 / 优先端点 | 阅读问题与前提边界 |
|---|---|---|
| 30 | [JointRecovery.lean](../../../../UEOT/V3/Compression/Objecthood/RepairLawSelfReconstruction/JointRecovery.lean) — `jointRecoveryBasin_recovers` | 修复程序与控制器本身受损时，联合自主核恢复的是什么？ 前提：TrustedRepairSubstrate、程序validity、纠错/单副本损坏模型、起点在JointRecoveryBasin；恢复顺序restore→execute。 边界：可信substrate/codec及允许故障范围未被自我生成；并非对任意程序破坏普遍恢复。 |
| 31 | [OperationalObject.lean](../../../../UEOT/V3/Compression/TheoryCompletion/OperationalObject.lean) — `operationalParent_constituents` | 预测身份、构成性持续和物理可恢复性是否被清楚区分？ 前提：已注册response family与representation；独立parent形成、constitutive persistence和repair certificates。 边界：不是把Object定义成所有结论的打包；也不能从PredictiveIdentity一个谓词直接得到Objecthood。 |
| 32 | [TeleologicalGauge.lean](../../../../UEOT/V3/Compression/TheoryCompletion/TeleologicalGauge.lean) — `gaugeTransform_preserves_validRepresentation` | Π/Φ代数分解何时是同一个目的contract的合法表示？ 前提：TeleologicalContract、order representation、domain-supplied dual-axis admissibility；合法gauge还要保持该admissibility。 边界：不能把任意两个实函数称为Φ/Π；排序等价不自动等于同一代数gauge轨道，也不保证标量表示存在。 |
| 33 | [SameObjectEndogenousAgencyClosure.lean](../../../../UEOT/V3/Compression/TheoryCompletion/SameObjectEndogenousAgencyClosure.lean) — `endogenous_sameObject_agency_god_goa` | 在同一对象上，Agency、GOD与支持于生存核的GOA能否真正同时成立？ 前提：Bellman teleological faithfulness、greedy preservation of canonical persistence kernel；因果contract结论需要相应更强faithfulness。 边界：不隐含GOA唯一性/混合、RLSR恢复或不经语义gate的内生目的。 |
| 34 | [AutopoiesisClosure.lean](../../../../UEOT/V3/Compression/TheoryCompletion/AutopoiesisClosure.lean) — `p12_terminal_conditional_finite_lifecycle` | P12终端究竟统一了什么，又明确保留了什么自创生缺口？ 前提：有限载体、PhysicalRepairCertificate、TrustedRepairSubstrate/Codec、程序source seed、joint homeostasis/resource/lineage/scale桥接。 边界：conditional finite lifecycle；没有从physical seed独自生成程序、codec、fault model、资源模型或谱系语义。 |
| 35 | [LineageEvolution.lean](../../../../UEOT/V3/Compression/TheoryCompletion/LineageEvolution.lean) — `lineage_perron_bridge` | 同一对象修复与产生新后代如何区分，Price/Perron如何合法接入？ 前提：独立LineageSemantics parentOf/identity；compatible reproductive transmission、非负归一化人口动力学及Perron证书。 边界：population mathematics不自动推导parentOf；same-object repair不是offspring。 |
| 36 | [ObjectScaleCalculus.lean](../../../../UEOT/V3/Compression/TheoryCompletion/ObjectScaleCalculus.lean) — `p9_terminal_objectScale_semantic_transport` | 跨尺度哪些对象性质可传输，Wilsonian物理解释实际欠哪些数据？ 前提：ObjectScaleMap和显式property/identity/purpose/GOD/GOA/repair/homeostasis preservation谓词。 边界：当前Wilsonian端点仅证明独立coupling-flow数据类型非平凡，明确不声称与特定ObjectScaleMap相容；不是已证Wilsonian RG推导。 |
| 37 | [TerminalClosure.lean](../../../../UEOT/V3/Compression/Objecthood/JointHomeostasis/TerminalClosure.lean) — `p5_terminal_sameParent_joint_homeostasis` | 反复故障下的平均稳态损伤界怎样绑定到同一个已认证parent？ 前提：有限joint repair carrier、mixed drift、recurrent faults、已认证semantic/self-repairing parent与projection桥。 边界：均值占据/Cesaro界，不是pathwise永恒合法性；不包括任意程序损坏或资源自闭合。 |

## Scientific Closure：实验可辨识性、反例与证据分类

| # | 现有 Lean 文件 / 优先端点 | 阅读问题与前提边界 |
|---|---|---|
| 38 | [SISCFiniteFutureProbes.lean](../../../../UEOT/V3/Compression/TheoryCompletion/ScientificClosure/SISCFiniteFutureProbes.lean) — `finite_probes_identify_canonical_future_classes` | 完整未来响应是否存在有限实验见证，数量界到底约束什么？ 前提：注册的有限确定性state system；对不同响应state pair选取分离word。 边界：测试数≤\|X\|²；选词noncomputable，不是word长度界、运行复杂度界或连续状态算法。 |
| 39 | [SISCFormationIdentityBridge.lean](../../../../UEOT/V3/Compression/TheoryCompletion/ScientificClosure/SISCFormationIdentityBridge.lean) — `finite_mechanism_unique_formed_successor` | 由形成证书走向唯一operational successor，究竟补上了哪种可辨识性？ 前提：归一化有限response channel、world/parent残差；独立causal edge；目标对其他候选的response gap>2τ。 边界：唯一性相对已声明candidate space；零formation error不保证唯一父对象或真实谱系。 |
| 40 | [SISCEmissionTiming.lean](../../../../UEOT/V3/Compression/TheoryCompletion/ScientificClosure/SISCEmissionTiming.lean) — `pre_and_post_emission_are_not_interchangeable` | 观测是在动作前还是动作后，预测轨迹和Bayes模型是否同一时间约定？ 前提：明确的finite controlled kernel与readout；分别定义pre-transition trace和post-transition Bayes observation。 边界：这一步给出不相容反例；真实互换还要额外time-shift/observation-order bridge。 |
| 41 | [C5DualDriveTest.lean](../../../../UEOT/V3/Compression/TheoryCompletion/ScientificClosure/C5DualDriveTest.lean) — `dualDrive_rejected_sound` | 共用二维驱动在实验上怎样被拒绝、暂时相容或判模糊？ 前提：真实operator-norm估计误差界、估计第三奇异值、预注册practical-zero tolerance；共同二维bottleneck假设。 边界：低秩兼容仅通过必要条件，不识别Π/Φ，不提供二驱动充分性。 |
| 42 | [SISCKernelLineageBridge.lean](../../../../UEOT/V3/Compression/TheoryCompletion/ScientificClosure/SISCKernelLineageBridge.lean) — `support_admitted_unique_operational_successor` | 真实转移正概率能替代多少手工causal-admissibility输入？ 前提：candidate是micro next-state；K(source,action,c)>0；已注册protocol/separation；谱系解读另需CompatibleTransmission。 边界：positive support推出operational reachability，不能单独推出genealogical parent。 |
| 43 | [SISCCausalLineageNoGo.lean](../../../../UEOT/V3/Compression/TheoryCompletion/ScientificClosure/SISCCausalLineageNoGo.lean) — `full_microstate_process_does_not_fix_parent_semantics` | 即使完全知道微观随机核和当前state，能唯一恢复谱系吗？ 前提：固定同一已知normalized kernel及injective readout，允许两个独立admissible lineage interpretations。 边界：否定由这些描述性输入唯一解码parentOf；不是宣称自然界真实亲代任意。 |
| 44 | [C7EvidenceGovernance.lean](../../../../UEOT/V3/Compression/TheoryCompletion/ScientificClosure/C7EvidenceGovernance.lean) — `requiresCoreReview_iff_mathMismatch` | 实验证据失败时，应重审数学、测量假设、领域桥还是覆盖度？ 前提：FailureClass分类和RequiresCoreTheoremReview为显式治理定义。 边界：这是治理规则的形式化一致性，不是经验分类器，也没有证明任何现实实验成功。 |

## 新的定量贯通：从校准到真实有限路径风险

主路径端点是 `same_policy_projected_path_error` 与 `same_policy_projected_failure_risk`。给定真实微观 PMF 行 `P n x a`、归一化宏观行 `Q n y a`、投影 `q`，同一个宏观历史策略 `π` 驱动两侧。微观侧以投影后的历史调用这个策略，宏观初始律明确等于 `p₀.map q`。若所有 `n<T`、`x`、`a` 满足

$$\operatorname{TV}\!\left(q_*P_n(x,a),Q_n(q(x),a)\right)\le\varepsilon_n,\qquad 0\le\varepsilon_n\le1,$$

则实际微观路径的投影律与宏观路径律满足

$$\operatorname{TV}\!\left(q_*\mathbb P^{\pi}_{0:T},\mathbb Q^{\pi}_{0:T}\right)\le B_T:=1-\prod_{n<T}(1-\varepsilon_n)\le\sum_{n<T}\varepsilon_n.$$

任一声明的可测宏观路径失败事件 `F` 因而满足

$$q_*\mathbb P^{\pi}_{0:T}(F)\le\min\{1,\mathbb Q^{\pi}_{0:T}(F)+B_T\}.$$

此处 `q_*` 还保留动作并逐步投影状态；源码中的 `riskHistoryMap` 给出确切映射。路径证明使用真实纤维后验条件核和同权 PMF 混合，不要求投影过程本身预先满足精确 lumpability，也没有增添“各时刻误差独立”的假设。

坐标前端复用现有 `FiniteRecurrentDecompositionStability.pmf_tv_eq_half_sum_abs`，把真实 PMF 的逐坐标界 `|p(c)-q(c)|≤Γ(c)` 变成 `TV≤min(1,(1/2)∑c Γ(c))`。`same_policy_coordinate_path_error` / `same_policy_coordinate_failure_risk` 消费的就是这些真实行界。

实验前端 `calibrated_representative_path_error` / `calibrated_representative_failure_risk` 更具体：选定分区 `S` 和满足 `q(r(c))=c` 的代表元，宏观行定义为 `Q_n(c,a)=q_*P_n(r(c),a)`。若每类指标重构残差为 δ、同类实测测试差为 η、每个真实测试期望的校准半径为 ρ、系数 L1 范数不超过 κ，则 N 个可达类的行预算为

$$\varepsilon_n=\min\!\left\{1,\frac{N}{2}\bigl(2\delta_n+(\eta_n+2\rho_n)\kappa_n\bigr)\right\}.$$

所有界都在声明的状态、动作、测试和有限时段上统一成立。ρ 的统计覆盖概率需要实验或统计定理提供。这个代表元结果不声称估计了一个独立学习的 `Q̂`；后者需要额外真实行校准。κ 是重构系数条件数，也不是 `Q̂` 的模型估计误差。

`AbsorbingLeakage` 给出配套限制：固定正泄漏率的两状态模型有一步误差 ε，但失败概率恰为 `1-(1-ε)^T` 并趋于 1。有限风险边界因此不能用于宣称无限时间生存、自创生、谱系唯一性或科学全闭合。

## 阅读与验证的职责

先用 FKRG 搜索候选与位置，再检查真实类型。第 4 个复用 overlay 将新增源候选同其编译器 `source_module` 对齐，原生导出实际类型显示、直接证明常量和注册公共定理子图；全模块公理审计独立覆盖 private 与 generated theorem constants。它不从名称前缀推断源模块。

类型比较继承历史证书的 raw stored type `Meta.isDefEq` 协议：每一对使用新的 `liftTermElabM` 状态，宇宙参数保留已存名称。零匹配仅表示此精确定义的比较通过，不是穷尽宇宙重命名、逻辑等价、可实例化复用或科学独立性。`ppExpr` 是便于阅读的类型显示，不是无损表达式序列化。

默认 UMC 审计打印当前结果；完整审计先构建 `UEOT`，再以真实编译源模块枚举定理并通过 `Lean.collectAxioms` 拒绝非标准公理。仅显式 `--output` 可写一份新的完整 receipt，既有历史 receipt 保留原字节。快速 receipt 测试只检查写入边界，独立 freshness 测试仍验证实际当前 DAG 及新增/删除/哈希漂移/图不闭合等负控。

正式门的当前运行结果请读对应 overlay、CI 与新 receipt；本导航本身不改 P-ID、生成元计数、七阶段 open ports 或 `NOT_ESTABLISHED` 的科学结论。
