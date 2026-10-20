# Native v2：私有辅助与同源主证明的独立窄审阅

结论：CLEAR。本审阅限于三项新私有计算辅助、实际支持／可行性／联合风险主链。17 组词法提示的完整 typed review 由 deployment_coverage 另行完成；本记录核验冻结工作树源与原生类型／证明证据，不是提交后 Git 对象或远端 CI 验证。

## 核验对象

- SUPPORT_VIABILITY_NATIVE_V1.json：34376e2c8564d148e5dcd4452ab0dddeb9aa20bbb1b9d0f7c88c194b9b82baca。
- SUPPORT_VIABILITY_REUSE_OVERLAY_V1.json：2af284000d6a6c25f67e9356a236817b22334dbfba777ca2eaf37e8060a3a45e。
- VERIFY_SUPPORT_VIABILITY_OVERLAY_TYPES.lean：26fd18e77dd6b7db550c6c5e1105376ef7f494db03bbab646e8d8fa42313a118。
- 三项原始字节的 SHA 与 finalization_summary 一致；9 个 added_modules 的 content_sha256 与实际 ueot-support-viability 文件逐项一致。
- V3 原始源码清单 PRODUCTION_SOURCE_MANIFEST_V3.json：SHA-256 为 993bd1a5c32b9872212282fba38411caf683c088f374b4d3c178fd79cc8c923e；root 原件与原始传回 build-v3 副本全字节相同，且与 native_execution.source_manifest_sha256 相符。清单 10 文件（9 模块与 TheoryCompletion 入口）均逐字节核对实际工作树；不是只比较候选摘要。
- 全部 219 个原生 theorem constants 名称唯一；102 个 public source、22 个 private、95 个 other native public；219 项 axiom 集合均包含于 propext / Classical.choice / Quot.sound。

## 三项私有辅助确实保留

### initial_checker_pass

原生完整名：_private.UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ControlCoverageWitness.0.UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.SafePrefixDeadend.initial_checker_pass

真实 owner：UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ControlCoverageWitness。is_private=true；不存在同名 public source row。

实际 direct_theorem_constants 消费者：UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.SafePrefixDeadend.a_complete_zero_uncovered_policy_exists。

其类型仍是原有闭合布尔计算等式，声明未从完整 native census 中删除。

### good_successor_checker_pass

原生完整名：_private.UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ControlCoverageWitness.0.UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.SafePrefixDeadend.good_successor_checker_pass

真实 owner：UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ControlCoverageWitness。is_private=true；不存在同名 public source row。

实际 direct_theorem_constants 消费者：无。

其类型仍是原有闭合布尔计算等式，声明未从完整 native census 中删除。

### allTrue_selects_true

原生完整名：_private.UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredDeploymentRiskWitness.0.UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredSelectionWitness.allTrue_selects_true

真实 owner：UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredDeploymentRiskWitness。is_private=true；不存在同名 public source row。

实际 direct_theorem_constants 消费者：UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredSelectionWitness.allTrue_checkedBudget。

其类型仍是原有闭合布尔计算等式，声明未从完整 native census 中删除。

## 原始碰撞失败仍保留

原 native-observed-v1/native_export.log 为 791076 字节，SHA-256 为 d406b3185d8f75be4eac8a80f1ce0621c14353e5cc0700e0261e757e68f0990b。其完整原生 JSON 实际有 105 个 public source 候选和 9 个闭合 Bool 类型碰撞，日志尾仍是 SUPPORT_VIABILITY_OVERLAY_TYPE_COLLISION；对应 pipeline status 保留 state=fail、native_export returncode=1，日志哈希一致。新 v2 不修改或重新标记该失败。三项辅助转为 private 仅缩小公开 theorem 表面；它们仍被完整原生 census 与公理检查覆盖，实际数学终端及其证明消费未被删除。

## 类型与实际证明边

已读取编译器导出的实际类型，确认 mem_traceSupport_iff_realized 和 traceSupport_eq_fiberTerminalPosterior_support 只识别正粗历史；mem_coarseLaw_succ_support_iff 的旧粗历史和所用 π 动作支持同时保留。trace support 本身没有 π 参数，不被误称完整后验概率。

实际证明常量链包括：

- mem_traceSupport_iff_realized → 私有 coarse successor raw support / mem_microLaw_succ_support_iff。
- traceSupport_eq_fiberTerminalPosterior_support → mem_traceSupport_iff_realized / 既有 mem_fiberTerminalPosterior_support_iff。
- mem_deploymentRowLaw_support_iff → 私有 pmfExtend support / mem_traceSupport_iff_realized。
- zero_uncovered_iff_support_certified → zero_uncertified_mass_iff_support / mem_deploymentRowLaw_support_iff。
- viablePolicy_zero_uncovered → zero_uncovered_iff_support_certified / viablePolicy_supported_histories_viable / viablePolicy_support_step。
- initial_viability_iff_exists_zero_uncovered_policy → viablePolicy_zero_uncovered / mem_coarseLaw_zero_support_iff / supported_viable_of_zero_uncovered。
- finiteRelationViabilityCheck_correct → finiteRelationViabilityCheck_eq / finiteViabilityCheck_correct。
- registered_selected_joint_failure_of_cap_on_good → registered_calibration_good_bad_le / 既有 selectedTrainingDeployment_failure_le / coverage_empirical_registered_microscopic_failure_risk / deployment_coverage_budget_le_of_actual_occupancy_cap。
- viable_registered_selected_joint_failure_on_good → registered_selected_joint_failure_of_cap_on_good / viablePolicy_zero_uncovered。
- actual_joint_failure_exact → 既有 selectedTrainingDeployment_failure_tower / actual_failure / coverage_expectation_map / selectedAction_pmf / actualRow_mass。

这些连接从 direct_theorem_constants 读取，未以 direct_constants 中出现在类型里的符号冒充证明调用。

有限关系正确性仍明确要求 R 与实际 P.support 的等价及相关 Decidable 实例；主策略 iff 本身不要求用户提供支持匹配证明。Good-only 端点真实类型保留 hN、逐注册行同源 marginal 与行内独立性、rho 非负、同一选择后的源/策略，以及共同微观失败事件；拟合、实际覆盖与预算只在 Good 上要求。薄桥从初始可行性推导同一个 viablePolicy 的实际零 ν，未把所需结论重新放入输入。

联合见证公开终端同一 trainingLaw.toPMF / id / actualDeployment 上给 17/32 上界、9/64 等式、7/8 与 1/8 选择质量、不同实际部署以及全一记录正概率和非全记录预算。数值上界与精确值没有混为同一量。

本审阅未编译新源、未写生产、未改书稿、未改变任何旧失败记录。
