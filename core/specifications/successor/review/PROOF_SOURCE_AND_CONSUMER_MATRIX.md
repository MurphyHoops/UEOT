# 证明来源、输入责任与实际消费者矩阵

原生独立审查者 B。日期：2026-11-11。源码基线：`16a89154183c22030d4526413167d095d94e6890`；tree：`839321b98ddcf368d0673484f7239733b53a5180`。

## 1. 如何阅读此矩阵

同一个数学结论可以有“抽象条件定理”“标准来源证书”“实际来源构造”“旧定理消费者”和“有限数值实例”几个不同层次。以下把输入与推导结果分开登记，避免从结构字段的存在跳到来源定理已经得到证明，也避免把后来已完成的来源构造继续当作债务。

这里的公共入口统一为 `import UEOT`。下表的简写 `UC.` 表示完整 namespace `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.`；文件仅给 basename 时，其前缀是 `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/`。**namespace 与文件不按名称推断**：例如 `UC.CoreRegenerativeSource.damaged_repairRank_one` 实际定义于 `CoreRegenerativeRepair.lean`。

完整可机检路径、声明、SHA、导入路线、旧 P-ID 和关系类型位于 [V3_PROPOSITION_INTERFACE_MAP.json](../V3_PROPOSITION_INTERFACE_MAP.json)。该文件的 27 个关系组有 104 个公开端点；旧命题区覆盖全部 106 P-ID／163 个唯一声明。关系不要求一对一，60 项明确没有登记直接后继关系。

本轮对既有证明凭据作静态源字节绑定，没有新 Lean 编译。本矩阵的“证明”指当前仓库已保留且范围明确的形式结果；“书面”与“有限精确检查”另标。更详细的兼容性判断、9 处旧导航修复和编译凭据边界见 [形式兼容性审计](FORMAL_SPEC_COMPATIBILITY_AUDIT.md)。

## 2. 原理、预测与风险来源

| 合同／旧关联 | 允许输入；不能偷换为结论的前提 | 已证明的输出与实际消费者 | 精确来源；保留边界 |
|---|---|---|---|
| 四生成器；11 项已计数重导出 | 固定 registered theorem-surface DAG、各源领域 adapter；删去某生成器时不得合成替代宏定理 | M-QD、M-TC、M-PE、M-OI 的已计数 wrappers；新索引直接复用 `COMPRESSION_LEDGER.yaml` 的 counted mappings | `QuotientDescent.lean`、`TransportCertificate.lean`、`PositiveEigenstructure.lean`、`OccupationLimitInvariance.lean` 均在上一级 `Compression/`。独立性是声明系统内的不可替代性；不是所有数学公理系统中的绝对独立性。M-BU 是历史 candidate，不是第五个生成器 |
| 关系与数值缺陷校准；P-MET-01／DYN-03／ID-01／API-01 | 同一零关系不决定数值尺度；`DefectCalibration` 明示正下界 a 和非负上界 b | `MinCore.DefectCalibration.zero_defect_iff`、`forward_budget`、`reverse_budget`、`MinCore.calibrated_weighted_chain_bound` 推出零集及有系数预算运输 | `TheoryCompletion/MinCore/RelationDefectNoGo.lean`、`CalibratedDefectComparison.lean`。反例 `exists_same_relation_different_defect` 保留，不能把校准常数写成仅从等价关系推得 |
| C1 实际响应递归；P-PRED-01／02／03、P-REF-02 | 同一 primitive P/O 核、可测历史策略；标准 Borel 潜态、相应输出正则性和可数行动／测试条件 | `UC.MeasurablePredictiveResponseRecursion.actual_C1_response_kernel_factor` 构造实际响应递归核；不是输入一个已满足递归的宏核 | `MeasurablePredictiveResponseRecursion.lean`。不假设响应像 Borel 或可测 section。零概率观察只按 a.e. 共同版本解释 |
| 实际过去—未来规范性；P-PROC-01／P-PRED-01／P-REF-02 | 任意原可测全历史过去控制器；未来控制器是否保留过去记忆必须明示 | `actual_prefix_latent_consistency`、`actual_past_future_factorization` 连接实际潜态、后验和路径；`actual_response_adaptive_ae_minimal` 对 fresh adaptive future 给出最小性；`futureKernel_response_memory_factor` 对 retained memory 保留响应与记忆二者 | 均在 `MeasurablePredictiveHistoryCanonical.lean`。fresh future 最小性不能用于任意不同 retained memory 的识别；不要把有限字母递归的旧 P-PRED-03 与此源级扩展写成相同量词 |
| 有限控制器记忆；P-PROC-01／P-PER-03／P-REF-01／02 | 有限 memory update／action source；可时变原 source。全时零 uncovered 的 support-memory 构造另要求相应支持与认证齐次 | `UC.FiniteMemoryRealization.actual_augmented_history_law` 和 `actual_augmented_prefix_eq` 证明实际增广状态—记忆前缀；`UC.FiniteMemorySeparation.stationary_feedback_cannot_certify_two_rows` 给出具体严格分离；`UC.FiniteMemoryPhysicalSafety.controller_all_times_physical_safe` 消费全时认证与物理不变前提 | `FiniteMemoryRealization.lean`、`FiniteMemorySeparation.lean`、`FiniteMemoryPhysicalSafety.lean`。动作在该 state-memory projection 中已被抹去；动作事件需要另一个保留动作的 map。分离仅排除齐次当前观察反馈，不能排除外部时钟策略 |
| 支持可行性与有限检查；P-PER-03／P-ALG-01／P-CORE-01 | 同一实际 source support、初始 posterior support、认证行、有限动作与显式 fallback | `UC.SupportViabilityClosure.initial_viability_iff_exists_zero_uncovered_policy` 给出有限 iff；`initial_infiniteViability_iff_exists_all_times_zero_uncovered_policy` 给出全时版本；`finiteRelationViabilityCheck_correct` 给出 executable finite checker 对应性。现行 R1 `UC.ExecutableSupportSynthesis.synthesize_isSome_iff_exists_all_times_policy`、`synthesize_some_zero_uncovered` 和 `synthesize_some_all_times_physical_safe` 进一步证明实际可执行返回 Program 的合同 | 前三项分别在 `FiniteSupportViability.lean`、`InfiniteSupportViability.lean`、`FiniteSupportViabilityCheck.lean`，R1 位于 `ExecutableSupportController.lean`。零步 terminal=True 不是“末态物理安全”。R1 保留确切初态／支持／认证对应、行动列表覆盖及独立物理安全前提；它已完成实际行动选取，不能把旧 Classical.choose 选择重新列作当前缺口 |
| 同来源 viability 最优控制；P-PER-03／P-CTL-01／P-QUO-01 | 对原 action 施加 viable restriction，保留原转移核和目标，满足原折扣控制条件 | `UC.viable_restricted_greedy_preserves_source_kernel` 和 `UC.viable_restricted_optimal_dominates_all_causal_policies` | `SafeOptimalControlFromViability.lean`。竞争类是这个受限折扣模型中的因果策略；不能换模型后仍称同来源最优 |
| 后验覆盖与全路径 TV；P-DYN-03／P-STAT-09／P-REF-02／P-API-01 | 同一策略与 source；只在实际正概率历史上定义归一化 fiber posterior，显式 reference 和 escape 编码 | `UC.PosteriorSupportCoverageCheck.posterior_supported_actions_bound_actual_coverage`；`UC.same_policy_projected_path_error`；`UC.PathObservationEscapeCheck.escape_path_tv` | `PosteriorSupportCoverage.lean`、`FiniteHorizonRisk.lean`、`PathObservationEscape.lean`。后验支持来自实际历史，不能用静态全纤维代替；全路径事件不能只凭终端 marginal 界覆盖 |
| Good-only 的实际联合风险；P-STAT-01／03／08、P-CORE-01 | 固定 registered calibration event、真实抽样分布；Good 上 fit、参考风险预算和选中策略实际占据 cap；同一个候选、策略及联合 law | `UC.RegisteredGoodJointCheck.registered_selected_joint_failure_of_cap_on_good` 仅对 Good 要求检查，坏训练概率收费一次；`UC.ViableRegisteredJointCheck.viable_registered_selected_joint_failure_on_good` 从初始 viability 推出同策略零 uncertified occupancy | `RegisteredDeploymentRisk.lean`、`ViableRegisteredJoint.lean`。viable consumer 消除了 hcap 输入，但保留参考风险 envelope／预算；不是删除一切风险前提。联合失败概率不等于给定 Accept 后的条件失败概率 |
| C5 rank／gauge／锚；P-DDH-01／04／05 | 有限维实线性空间、rank 条件；唯一性需要非退化 rank two，尺度识别需要已注册单位锚 | `UC.finite_rank_le_two_iff_linear_factorization`、`rank_two_factorizations_unique_gauge`、`rank_two_registered_units_identify` | `DualDriveFiniteRankFactorization.lean`。rank≤2 的线性 iff、GL(2) 自由度及定标分别陈述；微分 rank 必要性不等于一般非线性全局分解 |

## 3. 连续来源、Perron 与谱证书

| 冻结接口 | 旧接口允许假设什么 | 后继来源真实推导什么 | 直接消费者与剩余输入 |
|---|---|---|---|
| P-REC-02／P-CTL-03／P-KL-05 的实际随机来源底座 | 指定原 Brownian 源及原滤过；完整可预测 L² 输入；确定 vanishing-mesh 分割；drift Itô 另有实际全局有界强可预测 β、C² φ 的原生导数／Hessian 全局界；换测度另需原标量控制有界 | `UC.BrownianProjectiveSource.source_isPreBrownian`、`BrownianContinuousSource.process_isBrownian`；`BrownianVectorPredictableDensity.integralDomain_eq_fullPredictableL2`；`BrownianVectorPartitionQV.fullInput_partition_QV`；`BrownianFiniteStateDriftItoSource.actual_drift_state_ito_integral`；`BrownianOwnQPredictableDensity.integralDomain_eq_fullPredictableL2Q` 与 `BrownianOwnQFullIntegralSource` 的真鞅／能量消费者 | 各同名文件。P 连续版本与原积分是逐固定时刻 AE；固定 Q_A 积分窗 U 可大于 A，完整 Q 过程未被宣布一般连续。`BrownianBoundedGirsanovSource.full_future_indep_original_past` 的未来是 `(W_{s+t}−W_s)_{t≥0}` 增量过程，不能写成未平移未来坐标与过去独立 |
| P-REC-02，`RecoveryDynkin` | 停时／Dynkin／积分及恢复条件 | 在声明的 OU quadratic 实际源中构造物理 recovery contract | `UC.OUPhysicalRecoverySource.physical_source_p_rec_02`，文件 `OUPhysicalRecoverySource.lean`。仍需所列源类、测度和可积性条件；不能泛化为所有扩散 |
| P-CTL-03，`DiffusionHJBVerification.Model.ItoRun` | 有限时间 Itô 期望恒等、占据／终端概率与积分性、无限 reward 收敛；不是最优性结论 | `UC.BrownianControlledDynkinSource.actual_controlled_dynkin` 和 `UC.BrownianControlledItoRunSource.actualItoRun` 提供同实际 Brownian 路径的前提；HJB source 消费它们 | `UC.BrownianControlledHJBSource.actual_p_ctl_03`，分别在三个同名 `.lean` 文件。固定 `2+sin x` 值函数及有界 full-predictable 控制族；完整可预测对象、时间区间与导数界按 Lean 类型保留 |
| P-KL-05，路径控制能量接口 | 变化测度、终端指数密度、熵／积分条件，观察数据处理 | `UC.BrownianBoundedTerminalKLSource.actualTerminalData` 从实际有界 predictable integrand 构造数据并证明所需关系 | 同文件 `actual_p_kl_05`。能量／完整路径熵与观察熵不等号方向不同，不把观察 KL 一概写成能量等式 |
| P-EVO-03，`EvolutionPerronGrowth.KPF01Certificate` | 原证书明确含 primitive、左右正 eigen 数据、幂极限、唯一性和严格谱支配；这是标准来源输入 | `UC.PrimitivePerronClosure.certificateOfPrimitive` 从同一个 primitive M 构造这些字段；`actual_power_limit` 推得幂极限，`actual_root_simple` 推得代数单重 | 同文件 `actual_p_evo_03` 直接消费旧 P-ID，`actual_lineage_perron` 还要求实际 lineage transmission；不凭均值矩阵凭空生成血缘 |
| P-QSD-04，`ReversibleKilledSpectralQSD.SpectralData` | 原证书接收谱展开、L² residual 界等标准谱来源结论，并据此证明归一化吸引／存活渐近 | `CompactSpectralSemigroupSource.ResolventOrbit` 只输入同一 S 的 resolvent-range 导数恒等与零时恒等；紧自伴谱全备和模态 ODE 导出 actual expansion。`CompactKilledSpectralBinding.ofActualSource` 构造旧 certificate 全部相关字段 | `UC.CompactKilledSpectralBinding.actual_p_qsd_04` 和 `conditioned_eq_actual` 绑定同一 killed law。compact、对称、主模态、正 gap、正 initial density、收缩、source realization 等输入保留；一般绑定是给定 g 的实际演化 |

Perron 与 compact 的 source bridge 不是本轮新证明任务；[已公开来源验证](../../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/general_perron_compact_spectral_source_v1/SOURCE_VALIDATION.json) 所绑定的 10 个文件均与当前字节一致。该事实不要求复跑这些证明，也不能把未覆盖的其他 SDE／PDE／非 primitive 情形写成完成。

## 4. 实际执行、决策与数量表示

| 合同 | 源与竞争类 | 推导与实际消费者 | 边界／证据等级 |
|---|---|---|---|
| literal lifecycle、资源、Price | literal register instructions、实际 population step、明确 owner／lineage、目标与外部 tail supply | 已有 whole-theory 与原 Core source receipts 保留；后继规格应沿每条原 native consumer 登记执行→付费→结果链，不再用仅存在抽象结构替代实际来源 | 目标／规范选择和外部资金供应是明确输入；不会从执行语义中“证明”目标正确或凭空供应资源。相关 source family 并非对所有程序、所有机制的完备求解 |
| PR441 联合有限决策 | 固定 family、θ 开始只抽一次、实际 posterior＋wallet、所有正概率历史上的允许 real full-history competitors、完整费用 | `UC.RegisterJointDecisionNativeConsumer.returned_native_value`、`returned_native_payment`、`returned_native_optimal` 将 solver 输出绑定 literal native register execution | `RegisterJointDecisionNativeConsumer.lean`；[PR441 验收](../../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/joint_decision_closure_v1/FINAL_ACCEPTANCE.md)。同源 closed form 另有 B=c p≥S_H 条件；有限截止日目标不与任意 infinite discounted GOD 自动等同 |
| PR442 可执行共享图 | 每次 public input 用 fresh memo；候选经 all-action Bellman checks、root 绑定及 source-specific bounds 检查 | `UC.RegisterDecisionRepresentation.returned : Option Result`；`result_native_value`、`result_native_optimal`、`result_node_bound` 对接受结果成立 | `RegisterDecisionRepresentation.lean`。24(H+1)^4 是节点数；已接受有限实例与 source-specific array certificate 可复用，不是所有输入生成成功，不是 bit/RAM 或 generic POMDP bound |
| PR443 机制不可识别与 regret | 固定两机制；精确任务 H=3、r=1/2、B=2、c=1、λ=1/4、d=1；同一 raw 历史策略同时映到二机制；private seed 开始抽一次 | `UC.RegisterMechanismDecision.returned_contract`；`RegisterMechanismDecisionRealization.returned_beats_every_raw_regret`；`RegisterMechanismDecisionRegret.private_randomization_strict_gain` | 固定 H3 的 deterministic 1/32、mixed 3/128；H≤2 另有共同最优，不能赋予相同正 regret。exact numerical tables 使用 `native_decide`，`Lean.ofReduceBool` 依赖保留在局部 axiom audit |
| 未来任务决定的 2／3／4 类及 `(s,b,bq)` 秩三 | 明示任务读出、干预／目标族和原参数域 | 当前数学书与 source supplement 给出书面分类及精确有限核查；可登记为 source-relative structural result | 此类条目没有因“旁边 Lean 模块已编译”就得到专属 Lean 证明。不得伪造端点；后续完整形式化是新任务，不影响冻结106或既有分类完成状态 |

## 5. 同源再生、人口控制、反馈与谱系

| 合同 | 实际来源与允许输入 | 从来源推导的消费者 | 必须保留的非结论 |
|---|---|---|---|
| 付费再生 | `Body` 含两行三位重复码、gate、bootstrap、tag；多数信息未被抹去，可信 bootstrap，可支付资金；先修复再读取执行 | `UC.CoreRegenerativeSource.damaged_repairRank_one`、`same_program_restores_then_reads` 位于 `CoreRegenerativeRepair.lean` | 不恢复已全失的信息；`bootstrap_cut_not_repairable`、`underfunded_not_repairable` 是实际源反例。成功修复后仍有正死亡概率 |
| 物理形成与能力边界 | 同一 source response、实际 physicalCell／readout、合法候选族与干预族 | `UC.CoreRegenerativeSource.actual_formed_candidate_family_nonempty`、`bootstrap_cut_changes_future` 位于 `CoreRegenerativeFormation.lean` | 具体源具毁损见证，不意味着一般非恒定 q 必有毁损集。q(x,u)=x 且仅可干预 u 的书面反例保留；Ω 相对于能力与允许干预族 |
| 旧 Valid 域全策略人口控制 | canonical finite population，任意联合随机 public-history request policy，先请求后世界噪声；每个旧成员本代执行一次，新生下一代入 census | `UC.CoreRegenerativeControlPopulation.actual_supermartingale`、`actual_population_bounds`；`bestPolicy_positive_branch_is_internal` 将达到策略桥接同程序继承执行 | 有限历史条件均值公式不是直接给出无限路径 Mathlib Martingale。内部继承程序需要 founder/reachable invariants；不能对混合程序初态仅从公共 request rule 宣称同一内部程序 |
| 严格正域全分类 PR447 | `ProbabilityValid`：0<δ<s<1、b>0、γ>0、b+γ<1、0<q<1；原36 noise atoms全正；非空初始人口用于正双侧常数 | `UC.CoreRegenerativeGrowthAttainment.optimalRate_isLeast_uniform_upper`；rho_star=optimalRate=max(1,kc,(1−q)kb+qkc)；单一 C 先于 ∀Policy ∀n | 不假设每个 policy 有指数极限。`HasExpectedGrowth` 是全 n 的双侧正倍数界；ρ*不可误写成Lean局部mu。q=0/1 等边界、有限截止日最优性和a.s.存活不在结论中 |
| 同一受损程序达到 iff | 同一 damaged founder、paidRepair 后余3单位、每个 noise 分支实际支付3修复费、同程序路径；仍用原 action/noise/source | `UC.CoreRegenerativeGrowthAttainment.same_damaged_program_repairs_and_attains_iff`；false 区域 γ≤δ且1≤kc，true 区域δ≤γ且1≤growthRate true | 全策略 scale 1 来自真实 D/bloom rejection identity；两个已有程序均次临界时二者都不达到。这里是继承程序各自的 iff，不能把最优 public policy 偷换成内生程序 |
| 有限 cohort 反馈 | 旧 `Valid` 域、独立 actual source cohorts；先选 T 使均值份额分离，再选 n 控制风险，显式 work/resource 预算 | `UC.CoreRegenerativeFeedback.exists_finite_cohort_selection`、`actual_sample_resource_bound` | 不随 PR447 扩至全部 ProbabilityValid；不推出固定有限群体最终 a.s. 选优。高增长早灭且低增长非零的事件概率243/2048仍为正 |
| 比例与随机灭绝边界 | 固定原 source 和同一 finite event | `UC.CoreRegenerativeFeedbackBoundary.concrete_expected_ratio_zero_extension`、`concrete_expected_ratio_given_nonzero`、`concrete_ratio_expected_counts` 及 `expected_ratio_ne_ratio_expected_counts` | 2095/4096、2095/4006、10/19 是不同随机量；不能在统计推理中互换。定理名、来源字节及精确数值验证按该模块凭据理解 |
| 标记谱系与繁殖价值 | 原实际 retained/newborn marks、严格身份边、source expected offspring 和正特征数据 | `UC.CoreRegenerativeLineage.retained_is_same_object`、`newborn_is_strict_offspring`、`actual_marked_many_to_one` | retained不是严格后代；均值组成2/3、1/3与繁殖价值加权lineage20/29、9/29不同；Doob核正规化不自动等于允许物理策略 |
| 合法 silent-tag 商 | 保留 H/D、gate、bootstrap、完整公共收据与执行结果，只擦除无关 tag | `UC.CoreRegenerativeQuotient.step_joint_record_commutes`、`history_kernel_two_way`；`UC.CoreRegenerativeControlPopulation.protected_test_expectation_eq` | `dropping_diagnostic_is_not_lawful`、`code_only_prediction_loses_execution` 阻止过度压缩；扩展tag矩阵可约，positive eigen lift不等于全矩阵唯一射线 |

上述再生／形成／控制／反馈／谱系／商的 11 个原执行源 SHA 与 PR447 的 `SOURCE_BINDING.json` 完全一致。增长分类三个新模块、更新的 CoreTheoryClosure 与 check 文件的五份已有编译凭据另作绑定；身份一致与编译成功是两类证据，不能互换。

## 6. 消费者、计数与下游采纳规则

旧106项的 source-level consumer 是数学书相应稳定锚和旧源码合同，逐项在 JSON 的 `consumers` 保留。后继消费者按上述原定理、实际源、实际执行和具体任务区分，不能仅以“这个文件 import 了那个文件”就声称定理已用于输出。

Perron `actual_p_evo_03`、compact `actual_p_qsd_04`、Brownian `actual_p_ctl_03`／`actual_p_kl_05`、OU `physical_source_p_rec_02` 是明确的旧合同消费者。其余如有限终端决策、源再生、有限人口增长，是新任务类与旧原则的关系；不是旧106的逐字一对一重证明。JSON 为每类注明 `relation_type` 与 `scope`。

建议下游数学书后续采纳三种信息：准确的实际定义文件；新来源构造及其精确前提；已 proved／written／exact-check／native trust 的证据等级。本轮不编辑书籍。九个旧文件链接修复应单列为导航维护，不能宣称需要改变数学定理或重新编号。

当前 source receipt 绑定的完整清单与 SHA 留在 JSON；历史 `SOURCE_VALIDATION` 里的 `/tmp` 或 Mac 路径只是原收据的 provenance，不作为用户现在可打开的源码路径。实际 public consumer 均指向本 checkout 的版本化 Lean 文件。

## 7. 最终候选稿复核记录

基线源码、106 项映射、来源构造／消费者责任与现有证据等级已完成审计。已对实际生成的双语 30 卡候选稿完成接口与责任复核；[CLAIM_INDEX](../CLAIM_INDEX.json) 的 163 个端点引用全部解析到真实公共声明，27 个后继关系组全部登记到有效 CSX 合同。静态校验 8 组均通过，没有据此宣称本轮 Lean 编译。

非作者独立签收覆盖 A 提供的 CSX-04、CSX-07、CSX-29：分别为 5／6／13 个源文件、13／13／32 个端点、3／4／6 份证据。实际双语正文已经保留有限非空动作的齐次数值分支、Boolean `isSome = true`、R1 返回程序自身的保证，以及固定 Q_A 下每个 s 的未来**增量**过程独立于原 F_s。P 连续版本的固定时刻 AE 身份与 Q 完整域的一般连续版本非主张已明确分开。

还已核对 CSX-20 一般 primitive 选择器工厂与实际 stop／refusal 菜单的不同输入责任，以及 CSX-21 非空初态下正统一常数的等价解释。原证书字段、后来实际构造、书面结果和 native 数值实例没有被并为一种证据。

**最终签收：通过，无本角色剩余语义阻塞项。** 最终文字身份为中文 `9e0837d1210d0d091bfd6e74b10960a34ae175c1daad53ecce909a5dd1a628b5`（157131 字节／3140 行），英文 `5f63dafe8e68cc6e339cbdfab19d516c39270a9ca622634e5961db53c4599bca`（178228 字节／3140 行）。已将最后 CSX-03／08／17／23／24 与初审快照逐字段比较：Borel／动作正则条件、Good 的五项数学条件和真实逐行 confidenceBudget、H3 固定后悔参数、较优 θ₁ 的比例反例、同参数的加权谱系例均已明确，且与真实来源相符。来源端点及原 106 映射没有变化。

详细分工、实质修正与最终字节记录见[兼容性审计第 10 节](FORMAL_SPEC_COMPATIBILITY_AUDIT.md#10-交付与实际候选稿复核)。签收范围是当前文稿的数学接口和来源责任；本角色未运行 Lean，也不以签收替代远端集成事实。
