# UEOT 数学著作：完整来源索引

本索引随 [完整数学著作](UEOT_MATHEMATICS.md) 使用。书的正文与附录 B 完整保留 106 个稳定 P-ID 的陈述、证明及依赖；本索引额外给出同一底本的全部登记 Lean 源端点，不以名称索引替代类型或假设审阅。

**当前数学内容采用至 PR #447（2026-11-11）**：原 106 项稳定表面、全 Core 条件合同与同源定本保留；后继严格正概率域增长分类的三个生产模块已由 `CoreTheoryClosure` 导出。当前主文为核心定本及增长分类增补，不再以本索引早期的 3.1 版号判断现行内容。整体内容状态为 `CLASSIFIED_CORE_CLOSED`，经验状态为 `UNVERIFIED`；当前端点、证明层次及历史来源的读取规则见下文末两节与 [Lean 接口范围](LEAN_API_SCOPE.md)。

## 1. 不可变底本与索引来源

- [原始 v3.0 完整数学主文](source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md)：183440 字节；SHA-256 为 ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303。
- [压缩账本](../formalization/ueot-core/docs/compression/COMPRESSION_LEDGER.yaml)：登记更新时间 2026-09-29；其 baseline.source_sha256 与上述上传底本相同。
- [冻结 106 结果章节索引](../formalization/ueot-core/docs/CORE_COMPRESSION_THEOREM_INDEX.csv)：SHA-256 为 8ff2a25512e0e99524fb5afc2b90bf628f9e931b590131354d0d1a0232372032。
- 本次逐项读取 final_dispositions 和 audit_records，实际 106 条为 11 个生成端点、89 个领域适配、6 个保留边界；下表含 163 个互不重复的登记源端点。
- 每条 source-facing 端点只承担其真实 Lean 类型中的命题。连续时间 HJB 的 ItoRun、谱证书、可测选择、实际源与采样等条件不能因状态写为 completed 就被删除。

## 2. 106 个稳定结果的全部登记源端点

下表保持冻结章节索引顺序。链接指向实际 Lean 源文件，标签是完整命名空间。处分描述压缩角色，不是现实世界验证等级。

| P-ID | 主文 | 压缩角色 | 登记 Lean 全限定名与源文件 |
|---|---|---|---|
| P-MET-01 | [第 1 章](UEOT_MATHEMATICS.md#ch-1) | 领域适配 | [UEOT.V3.TotalVariation.tvDist_map_le](../formalization/ueot-core/UEOT/V3/TotalVariation.lean)；[UEOT.V3.TVKernel.tvDist_comp_le](../formalization/ueot-core/UEOT/V3/TVKernel.lean)；[UEOT.V3.TotalVariation.tvDist_map_measurableEquiv](../formalization/ueot-core/UEOT/V3/TotalVariation.lean) |
| P-MET-02 | [第 1 章](UEOT_MATHEMATICS.md#ch-1) | 领域适配 | [UEOT.V3.TVSpan.abs_integral_sub_le_span](../formalization/ueot-core/UEOT/V3/TVSpan.lean) |
| P-PROC-01 | [第 2 章](UEOT_MATHEMATICS.md#ch-2) | 领域适配 | [UEOT.V3.ConcreteHistoryMarkovization.p_proc_01_history_markovization](../formalization/ueot-core/UEOT/V3/ConcreteHistoryMarkovization.lean) |
| P-FAC-01 | [第 3 章](UEOT_MATHEMATICS.md#ch-3) | 领域适配 | [UEOT.V3.RepresentationCovariance.p_fac_01_covariance_bundle](../formalization/ueot-core/UEOT/V3/RepresentationCovariance.lean)；[UEOT.V3.RepresentationCovariance.homTrajMeasure_transport_covariance](../formalization/ueot-core/UEOT/V3/RepresentationCovariance.lean)；[UEOT.V3.RepresentationCovariance.causalLaw_transport_equiv](../formalization/ueot-core/UEOT/V3/RepresentationCovariance.lean)；[UEOT.V3.RepresentationCovariance.causalPolicyValue_transport_bundle](../formalization/ueot-core/UEOT/V3/RepresentationCovariance.lean) |
| P-PRED-01 | [第 4 章](UEOT_MATHEMATICS.md#ch-4) | 生成端点 | [UEOT.V3.PredictionDependent.canonical_ae_minimal](../formalization/ueot-core/UEOT/V3/PredictionDependent.lean)；[UEOT.V3.PredictionDependent.canonical_ae_sigma_minimal](../formalization/ueot-core/UEOT/V3/PredictionDependent.lean)；[UEOT.V3.PredictionDependent.canonical_kernel_sufficient](../formalization/ueot-core/UEOT/V3/PredictionDependent.lean) |
| P-PRED-02 | [第 4 章](UEOT_MATHEMATICS.md#ch-4) | 领域适配 | [UEOT.V3.PredictionRefinement.pushTargetDependent_apply](../formalization/ueot-core/UEOT/V3/PredictionRefinement.lean)；[UEOT.V3.PredictionRefinement.protocol_refinement_sigma_le_dependent](../formalization/ueot-core/UEOT/V3/PredictionRefinement.lean)；[UEOT.V3.PredictionRefinement.sigmaCanonicalDependent_iUnion_of_monotone](../formalization/ueot-core/UEOT/V3/PredictionRefinement.lean) |
| P-PRED-03 | [第 4 章](UEOT_MATHEMATICS.md#ch-4) | 领域适配 | [UEOT.V3.PredictionUpdate.p_pred_03_recursive_update](../formalization/ueot-core/UEOT/V3/PredictionUpdate.lean) |
| P-INFO-01 | [第 5 章](UEOT_MATHEMATICS.md#ch-5) | 领域适配 | [UEOT.V3.InformationStatistic.mutualInfo_eq_statistic_add_conditional](../formalization/ueot-core/UEOT/V3/InformationStatistic.lean)；[UEOT.V3.InformationStatistic.mutualInfo_statistic_ge_sub_of_conditional_le](../formalization/ueot-core/UEOT/V3/InformationStatistic.lean)；[UEOT.V3.InformationMemoryBound.p_info_01_discrete_entropy](../formalization/ueot-core/UEOT/V3/InformationMemoryBound.lean) |
| P-INFO-02 | [第 5 章](UEOT_MATHEMATICS.md#ch-5) | 领域适配 | [UEOT.V3.InformationPInfo02.p_info_02_finite](../formalization/ueot-core/UEOT/V3/InformationPInfo02.lean)；[UEOT.V3.InformationPInfo02.p_info_02_ennreal](../formalization/ueot-core/UEOT/V3/InformationPInfo02.lean) |
| P-INFO-03 | [第 5 章](UEOT_MATHEMATICS.md#ch-5) | 领域适配 | [UEOT.V3.InformationPredictiveRateZero.predictiveObjectRateZero_eq_sourceEntropy](../formalization/ueot-core/UEOT/V3/InformationPredictiveRateZero.lean) |
| P-INFO-04 | [第 5 章](UEOT_MATHEMATICS.md#ch-5) | 领域适配 | [UEOT.V3.InformationPInfo04.p_info_04](../formalization/ueot-core/UEOT/V3/InformationPInfo04.lean)；[UEOT.V3.InformationConditionalBinaryMutualEntropy.p_info_04_conditional_binary](../formalization/ueot-core/UEOT/V3/InformationConditionalBinaryMutualEntropy.lean) |
| P-INFO-05 | [第 5 章](UEOT_MATHEMATICS.md#ch-5) | 保留边界 | [UEOT.V3.InformationPacking.merged_histories_decoder_lower_bound](../formalization/ueot-core/UEOT/V3/InformationPacking.lean)；[UEOT.V3.InformationPacking.packing_ncard_image](../formalization/ueot-core/UEOT/V3/InformationPacking.lean)；[UEOT.V3.InformationEntropy.p_info_05_uniform_entropy](../formalization/ueot-core/UEOT/V3/InformationEntropy.lean) |
| P-INT-01 | [第 6 章](UEOT_MATHEMATICS.md#ch-6) | 领域适配 | [UEOT.V3.InformationPInt01Common.p_int_01](../formalization/ueot-core/UEOT/V3/InformationPInt01Common.lean)；[UEOT.V3.InformationPInt01Common.p_int_01_common_decoder](../formalization/ueot-core/UEOT/V3/InformationPInt01Common.lean) |
| P-INT-02 | [第 6 章](UEOT_MATHEMATICS.md#ch-6) | 生成端点 | [UEOT.V3.StructuredQuotient.p_int_02](../formalization/ueot-core/UEOT/V3/StructuredQuotient.lean) |
| P-INT-03 | [第 6 章](UEOT_MATHEMATICS.md#ch-6) | 领域适配 | [UEOT.V3.MarkovBoundary.p_int_03_boundary_unique](../formalization/ueot-core/UEOT/V3/MarkovBoundary.lean) |
| P-DYN-01 | [第 7 章](UEOT_MATHEMATICS.md#ch-7) | 领域适配 | [UEOT.V3.DynamicsKernel.strongLumpability_iff_pathLaw_of_surjective](../formalization/ueot-core/UEOT/V3/DynamicsKernel.lean) |
| P-DYN-02 | [第 7 章](UEOT_MATHEMATICS.md#ch-7) | 领域适配 | [UEOT.V3.CTMCSemigroupNonnegative.p_dyn_02_nonnegative_semigroup_iff_blockSum](../formalization/ueot-core/UEOT/V3/CTMCSemigroupNonnegative.lean)；[UEOT.V3.CTMCSemigroupNonnegative.exists_macro_ctmc_semigroup_of_blockSum_constant](../formalization/ueot-core/UEOT/V3/CTMCSemigroupNonnegative.lean) |
| P-DYN-03 | [第 7 章](UEOT_MATHEMATICS.md#ch-7) | 生成端点 | [UEOT.V3.PathError.p_dyn_03_finite_path_error](../formalization/ueot-core/UEOT/V3/PathError.lean) |
| P-DYN-04 | [第 7 章](UEOT_MATHEMATICS.md#ch-7) | 生成端点 | [UEOT.V3.DynamicsCrossScale.p_dyn_04_cross_scale_tv](../formalization/ueot-core/UEOT/V3/DynamicsCrossScale.lean)；[UEOT.V3.DynamicsCrossScale.p_dyn_04_exact_intertwining](../formalization/ueot-core/UEOT/V3/DynamicsCrossScale.lean) |
| P-PER-01 | [第 8 章](UEOT_MATHEMATICS.md#ch-8) | 领域适配 | [UEOT.V3.PersistenceOmega.p_per_01](../formalization/ueot-core/UEOT/V3/PersistenceOmega.lean) |
| P-PER-02 | [第 8 章](UEOT_MATHEMATICS.md#ch-8) | 生成端点 | [UEOT.V3.PersistenceOccupation.FellerOccupationSystem.p_per_02](../formalization/ueot-core/UEOT/V3/PersistenceOccupation.lean) |
| P-PER-03 | [第 8 章](UEOT_MATHEMATICS.md#ch-8) | 领域适配 | [UEOT.V3.ViabilitySource.p_per_03](../formalization/ueot-core/UEOT/V3/ViabilitySource.lean) |
| P-PER-04 | [第 8 章](UEOT_MATHEMATICS.md#ch-8) | 领域适配 | [UEOT.V3.ViabilityTangency.p_per_04](../formalization/ueot-core/UEOT/V3/ViabilityTangency.lean) |
| P-REC-01 | [第 9 章](UEOT_MATHEMATICS.md#ch-9) | 领域适配 | [UEOT.V3.RecoveryProbability.p_rec_01_mean_bound](../formalization/ueot-core/UEOT/V3/RecoveryProbability.lean)；[UEOT.V3.RecoveryProbability.p_rec_01_tail_bound](../formalization/ueot-core/UEOT/V3/RecoveryProbability.lean) |
| P-REC-02 | [第 9 章](UEOT_MATHEMATICS.md#ch-9) | 领域适配 | [UEOT.V3.RecoveryDynkin.p_rec_02](../formalization/ueot-core/UEOT/V3/RecoveryDynkin.lean) |
| P-REC-03 | [第 9 章](UEOT_MATHEMATICS.md#ch-9) | 领域适配 | [UEOT.V3.RecoveryHittingPoisson.p_rec_03](../formalization/ueot-core/UEOT/V3/RecoveryHittingPoisson.lean) |
| P-REC-04 | [第 9 章](UEOT_MATHEMATICS.md#ch-9) | 领域适配 | [UEOT.V3.RecoveryHittingBound.p_rec_04_hitting_time_bound](../formalization/ueot-core/UEOT/V3/RecoveryHittingBound.lean) |
| P-QSD-01 | [第 10 章](UEOT_MATHEMATICS.md#ch-10) | 领域适配 | [UEOT.V3.QSDTVLimit.p_qsd_01](../formalization/ueot-core/UEOT/V3/QSDTVLimit.lean) |
| P-QSD-02 | [第 10 章](UEOT_MATHEMATICS.md#ch-10) | 生成端点 | [UEOT.V3.QSDPerron.p_qsd_02](../formalization/ueot-core/UEOT/V3/QSDPerron.lean)；[UEOT.V3.QSDPerron.p_qsd_02_killed](../formalization/ueot-core/UEOT/V3/QSDPerron.lean) |
| P-QSD-03 | [第 10 章](UEOT_MATHEMATICS.md#ch-10) | 领域适配 | [UEOT.V3.QSDDurationWindow.p_qsd_03](../formalization/ueot-core/UEOT/V3/QSDDurationWindow.lean)；[UEOT.V3.QSDDurationWindow.window_nonempty_iff](../formalization/ueot-core/UEOT/V3/QSDDurationWindow.lean) |
| P-QSD-04 | [第 10 章](UEOT_MATHEMATICS.md#ch-10) | 领域适配 | [UEOT.V3.ReversibleKilledSpectralQSD.SpectralData.p_qsd_04](../formalization/ueot-core/UEOT/V3/ReversibleKilledSpectralQSD.lean) |
| P-ID-01 | [第 11 章](UEOT_MATHEMATICS.md#ch-11) | 生成端点 | [UEOT.V3.TransportDefect.FrozenTransportSystem.p_id_01](../formalization/ueot-core/UEOT/V3/TransportDefect.lean) |
| P-ID-02 | [第 11 章](UEOT_MATHEMATICS.md#ch-11) | 生成端点 | [UEOT.V3.DevelopmentTransport.development_pipeline](../formalization/ueot-core/UEOT/V3/DevelopmentTransport.lean) |
| P-OMG-01 | [第 12 章](UEOT_MATHEMATICS.md#ch-12) | 领域适配 | [UEOT.V3.OmegaMinimalFailure.p_omg_01](../formalization/ueot-core/UEOT/V3/OmegaMinimalFailure.lean) |
| P-OMG-02 | [第 12 章](UEOT_MATHEMATICS.md#ch-12) | 领域适配 | [UEOT.V3.OmegaIntegrityMargin.p_omg_02](../formalization/ueot-core/UEOT/V3/OmegaIntegrityMargin.lean) |
| P-CAR-01 | [第 13 章](UEOT_MATHEMATICS.md#ch-13) | 领域适配 | [UEOT.V3.Access.sufficient_mono](../formalization/ueot-core/UEOT/V3/Access.lean)；[UEOT.V3.Access.contains_minimal](../formalization/ueot-core/UEOT/V3/Access.lean) |
| P-CAR-02 | [第 13 章](UEOT_MATHEMATICS.md#ch-13) | 领域适配 | [UEOT.V3.Access.erasure_survives](../formalization/ueot-core/UEOT/V3/Access.lean)；[UEOT.V3.Access.erasure_failure](../formalization/ueot-core/UEOT/V3/Access.lean)；[UEOT.V3.Access.minimal_erasure](../formalization/ueot-core/UEOT/V3/Access.lean) |
| P-CAR-03 | [第 13 章](UEOT_MATHEMATICS.md#ch-13) | 领域适配 | [UEOT.Blocker.blocker_involution](../formalization/ueot-core/UEOT/Core/Blocker.lean)；[UEOT.Blocker.blocker_empty](../formalization/ueot-core/UEOT/Core/Blocker.lean)；[UEOT.Blocker.blocker_singleton_empty](../formalization/ueot-core/UEOT/Core/Blocker.lean) |
| P-CAR-04 | [第 13 章](UEOT_MATHEMATICS.md#ch-13) | 领域适配 | [UEOT.V3.DecoderRadius.decoder_radius_bounds](../formalization/ueot-core/UEOT/V3/DecoderRadius.lean) |
| P-RES-01 | [第 14 章](UEOT_MATHEMATICS.md#ch-14) | 领域适配 | [UEOT.V3.ClosureResolution.minimal_property_coarse_graining](../formalization/ueot-core/UEOT/V3/ClosureResolution.lean) |
| P-RES-02 | [第 14 章](UEOT_MATHEMATICS.md#ch-14) | 领域适配 | [UEOT.V3.ClosureResolution.closure_comp_of_nested](../formalization/ueot-core/UEOT/V3/ClosureResolution.lean)；[UEOT.V3.ClosureResolution.resolutionMap_comp](../formalization/ueot-core/UEOT/V3/ClosureResolution.lean) |
| P-RES-03 | [第 14 章](UEOT_MATHEMATICS.md#ch-14) | 领域适配 | [UEOT.V3.BlockerNaturality.blocker_naturality](../formalization/ueot-core/UEOT/V3/BlockerNaturality.lean) |
| P-RES-04 | [第 14 章](UEOT_MATHEMATICS.md#ch-14) | 领域适配 | [UEOT.Resolution.lower_adjunction](../formalization/ueot-core/UEOT/Core/Resolution.lean)；[UEOT.Resolution.upper_adjunction](../formalization/ueot-core/UEOT/Core/Resolution.lean) |
| P-RES-05 | [第 14 章](UEOT_MATHEMATICS.md#ch-14) | 领域适配 | [UEOT.V3.Resolution.pushFamily_realization_interval](../formalization/ueot-core/UEOT/V3/Resolution.lean) |
| P-RES-06 | [第 14 章](UEOT_MATHEMATICS.md#ch-14) | 领域适配 | [UEOT.V3.Resolution.endpoint_equality_iff_unique_active_fibers](../formalization/ueot-core/UEOT/V3/Resolution.lean) |
| P-COMP-01 | [第 15 章](UEOT_MATHEMATICS.md#ch-15) | 领域适配 | [UEOT.V3.CompositionPathSource.p_comp_01](../formalization/ueot-core/UEOT/V3/CompositionPathSource.lean) |
| P-COMP-02 | [第 15 章](UEOT_MATHEMATICS.md#ch-15) | 领域适配 | [UEOT.V3.CompositionInterventionJS.jsDiv_mem_Icc_logTwo](../formalization/ueot-core/UEOT/V3/CompositionInterventionJS.lean)；[UEOT.V3.CompositionInterventionJS.jsDiv_eq_zero_iff](../formalization/ueot-core/UEOT/V3/CompositionInterventionJS.lean)；[UEOT.V3.CompositionInterventionJS.cutJSMargin_pos_iff](../formalization/ueot-core/UEOT/V3/CompositionInterventionJS.lean) |
| P-COMP-03 | [第 15 章](UEOT_MATHEMATICS.md#ch-15) | 领域适配 | [UEOT.V3.CompositionMargin.p_comp_03](../formalization/ueot-core/UEOT/V3/CompositionMargin.lean) |
| P-COMP-04 | [第 15 章](UEOT_MATHEMATICS.md#ch-15) | 领域适配 | [UEOT.V3.CompositionParentInformation.p_comp_04](../formalization/ueot-core/UEOT/V3/CompositionParentInformation.lean) |
| P-COMP-05 | [第 15 章](UEOT_MATHEMATICS.md#ch-15) | 领域适配 | [UEOT.V3.CompositionBooleanAtoms.p_comp_05](../formalization/ueot-core/UEOT/V3/CompositionBooleanAtoms.lean) |
| P-COMP-06 | [第 15 章](UEOT_MATHEMATICS.md#ch-15) | 领域适配 | [UEOT.V3.CompositionCarrierLift.p_comp_06](../formalization/ueot-core/UEOT/V3/CompositionCarrierLift.lean) |
| P-COMP-07 | [第 15 章](UEOT_MATHEMATICS.md#ch-15) | 领域适配 | [UEOT.V3.CompositionWindow.p_comp_07](../formalization/ueot-core/UEOT/V3/CompositionWindow.lean) |
| P-STAT-01 | [第 16 章](UEOT_MATHEMATICS.md#ch-16) | 领域适配 | [UEOT.V3.FiniteAlphabetPStat01.p_stat_01_tail](../formalization/ueot-core/UEOT/V3/FiniteAlphabetPStat01.lean)；[UEOT.V3.FiniteAlphabetPStat01Radius.p_stat_01_radius](../formalization/ueot-core/UEOT/V3/FiniteAlphabetPStat01Radius.lean) |
| P-STAT-02 | [第 16 章](UEOT_MATHEMATICS.md#ch-16) | 领域适配 | [UEOT.V3.StatisticalDefect.p_stat_02](../formalization/ueot-core/UEOT/V3/StatisticalDefect.lean) |
| P-STAT-03 | [第 16 章](UEOT_MATHEMATICS.md#ch-16) | 领域适配 | [UEOT.V3.Threshold.approximate_family](../formalization/ueot-core/UEOT/V3/Threshold.lean) |
| P-STAT-04 | [第 16 章](UEOT_MATHEMATICS.md#ch-16) | 领域适配 | [UEOT.V3.Threshold.exact_family](../formalization/ueot-core/UEOT/V3/Threshold.lean) |
| P-STAT-05 | [第 16 章](UEOT_MATHEMATICS.md#ch-16) | 领域适配 | [UEOT.V3.PredictiveClassRecovery.p_stat_05](../formalization/ueot-core/UEOT/V3/PredictiveClassRecovery.lean) |
| P-STAT-06 | [第 16 章](UEOT_MATHEMATICS.md#ch-16) | 领域适配 | [UEOT.V3.HilbertMeanSourceRadius.source_meanError_tail_exact_radius](../formalization/ueot-core/UEOT/V3/HilbertMeanSourceRadius.lean)；[UEOT.V3.HilbertMeanSourceSimultaneous.source_simultaneous_exact_radius](../formalization/ueot-core/UEOT/V3/HilbertMeanSourceSimultaneous.lean) |
| P-STAT-07 | [第 16 章](UEOT_MATHEMATICS.md#ch-16) | 领域适配 | [UEOT.V3.MMDTransportSource.p_stat_07_source](../formalization/ueot-core/UEOT/V3/MMDTransportSource.lean)；[UEOT.V3.MMDTransport.p_stat_07](../formalization/ueot-core/UEOT/V3/MMDTransport.lean) |
| P-STAT-08 | [第 16 章](UEOT_MATHEMATICS.md#ch-16) | 领域适配 | [UEOT.V3.FiniteCandidatePStat08.p_stat_08](../formalization/ueot-core/UEOT/V3/FiniteCandidatePStat08.lean) |
| P-STAT-09 | [第 16 章](UEOT_MATHEMATICS.md#ch-16) | 领域适配 | [UEOT.V3.AverageErrorTransport.p_stat_09](../formalization/ueot-core/UEOT/V3/AverageErrorTransport.lean) |
| P-INV-01 | [第 17 章](UEOT_MATHEMATICS.md#ch-17) | 保留边界 | [UEOT.V3.BinaryTesting.p_inv_01](../formalization/ueot-core/UEOT/V3/BinaryTesting.lean) |
| P-INV-02 | [第 17 章](UEOT_MATHEMATICS.md#ch-17) | 保留边界 | [UEOT.V3.FisherGauge.p_inv_02](../formalization/ueot-core/UEOT/V3/FisherGauge.lean) |
| P-INV-03 | [第 17 章](UEOT_MATHEMATICS.md#ch-17) | 领域适配 | [UEOT.V3.FisherIntersection.p_inv_03](../formalization/ueot-core/UEOT/V3/FisherIntersection.lean) |
| P-INV-04 | [第 17 章](UEOT_MATHEMATICS.md#ch-17) | 领域适配 | [UEOT.V3.DesignIdentifiability.p_inv_04](../formalization/ueot-core/UEOT/V3/DesignIdentifiability.lean) |
| P-INV-05 | [第 17 章](UEOT_MATHEMATICS.md#ch-17) | 领域适配 | [UEOT.V3.PredictableOLSSourceConfidence.measure_source_goodGram_and_euclidean_error_gt_le_alpha](../formalization/ueot-core/UEOT/V3/PredictableOLSSourceConfidence.lean) |
| P-TEL-01 | [第 18 章](UEOT_MATHEMATICS.md#ch-18) | 领域适配 | [UEOT.V3.RewardInfinite.shaping_limit_value](../formalization/ueot-core/UEOT/V3/RewardInfinite.lean)；[UEOT.V3.RewardInfinite.policy_values_affine_from_bounded_state_potential](../formalization/ueot-core/UEOT/V3/RewardInfinite.lean) |
| P-CTL-01 | [第 19 章](UEOT_MATHEMATICS.md#ch-19) | 领域适配 | [UEOT.V3.FiniteDiscountedControl.p_ctl_01_causal_optimality](../formalization/ueot-core/UEOT/V3/FiniteDiscountedControl.lean)；[UEOT.V3.FiniteDiscountedControl.Model.fixedPoint_unique](../formalization/ueot-core/UEOT/V3/FiniteDiscountedControl.lean)；[UEOT.V3.FiniteDiscountedControl.Model.valueIteration_tendsto](../formalization/ueot-core/UEOT/V3/FiniteDiscountedControl.lean)；[UEOT.V3.FiniteDiscountedControl.Model.valueError_le_residual](../formalization/ueot-core/UEOT/V3/FiniteDiscountedControl.lean)；[UEOT.V3.FiniteDiscountedControl.CausalPolicy.infiniteValue_le_optimal](../formalization/ueot-core/UEOT/V3/FiniteDiscountedControl.lean)；[UEOT.V3.FiniteDiscountedControl.greedy_infiniteValue_eq_optimal](../formalization/ueot-core/UEOT/V3/FiniteDiscountedControl.lean) |
| P-CTL-02 | [第 19 章](UEOT_MATHEMATICS.md#ch-19) | 领域适配 | [UEOT.V3.CompactFellerControl.Model.p_ctl_02](../formalization/ueot-core/UEOT/V3/CompactFellerControl.lean) |
| P-CTL-03 | [第 19 章](UEOT_MATHEMATICS.md#ch-19) | 领域适配 | [UEOT.V3.DiffusionHJBVerification.p_ctl_03](../formalization/ueot-core/UEOT/V3/DiffusionHJBVerification.lean) |
| P-QUO-01 | [第 20 章](UEOT_MATHEMATICS.md#ch-20) | 领域适配 | [UEOT.V3.FiniteDiscountedControl.ExactControlQuotient.p_quo_01](../formalization/ueot-core/UEOT/V3/FiniteDiscountedControl.lean) |
| P-QUO-02 | [第 20 章](UEOT_MATHEMATICS.md#ch-20) | 领域适配 | [UEOT.V3.FiniteDiscountedControl.ApproxControlQuotient.p_quo_02](../formalization/ueot-core/UEOT/V3/FiniteDiscountedControl.lean) |
| P-QUO-03 | [第 20 章](UEOT_MATHEMATICS.md#ch-20) | 领域适配 | [UEOT.V3.CoreOperationalAssembly.macro_gap_certifies_micro_action](../formalization/ueot-core/UEOT/V3/CoreOperationalAssembly.lean) |
| P-QUO-04 | [第 20 章](UEOT_MATHEMATICS.md#ch-20) | 领域适配 | [UEOT.V3.FiniteDiscountedControl.Model.p_quo_04](../formalization/ueot-core/UEOT/V3/FiniteDiscountedControl.lean) |
| P-QUO-05 | [第 20 章](UEOT_MATHEMATICS.md#ch-20) | 领域适配 | [UEOT.V3.FiniteDiscountedControl.LocalApproxControlQuotient.p_quo_05](../formalization/ueot-core/UEOT/V3/FiniteDiscountedControl.lean) |
| P-GOA-01 | [第 21 章](UEOT_MATHEMATICS.md#ch-21) | 生成端点 | [UEOT.V3.FiniteCesaroInvariant.p_goa_01](../formalization/ueot-core/UEOT/V3/FiniteCesaroInvariant.lean) |
| P-GOA-02 | [第 21 章](UEOT_MATHEMATICS.md#ch-21) | 领域适配 | [UEOT.V3.FiniteDobrushin.p_goa_02](../formalization/ueot-core/UEOT/V3/FiniteDobrushin.lean)；[UEOT.V3.FiniteDobrushin.tv_step_le_dobrushin](../formalization/ueot-core/UEOT/V3/FiniteDobrushin.lean) |
| P-GOA-03 | [第 21 章](UEOT_MATHEMATICS.md#ch-21) | 领域适配 | [UEOT.V3.FiniteRecurrentDecompositionStability.p_goa_03](../formalization/ueot-core/UEOT/V3/FiniteRecurrentDecompositionStability.lean) |
| P-GOA-04 | [第 21 章](UEOT_MATHEMATICS.md#ch-21) | 领域适配 | [UEOT.V3.SymmetricKilledSpectralStability.p_goa_04](../formalization/ueot-core/UEOT/V3/SymmetricKilledSpectralStability.lean) |
| P-KL-01 | [第 22 章](UEOT_MATHEMATICS.md#ch-22) | 领域适配 | [UEOT.V3.PathEventKL.p_kl_01](../formalization/ueot-core/UEOT/V3/PathEventKL.lean) |
| P-KL-02 | [第 22 章](UEOT_MATHEMATICS.md#ch-22) | 领域适配 | [UEOT.V3.PathEventIProjection.p_kl_02](../formalization/ueot-core/UEOT/V3/PathEventIProjection.lean) |
| P-KL-03 | [第 22 章](UEOT_MATHEMATICS.md#ch-22) | 领域适配 | [UEOT.V3.PathKLChain.p_kl_03](../formalization/ueot-core/UEOT/V3/PathKLChain.lean)；[UEOT.V3.PathKLChain.p_kl_03_general](../formalization/ueot-core/UEOT/V3/PathKLChain.lean) |
| P-KL-04 | [第 22 章](UEOT_MATHEMATICS.md#ch-22) | 领域适配 | [UEOT.V3.FiniteCTMCPathKL.p_kl_04_holding](../formalization/ueot-core/UEOT/V3/FiniteCTMCPathKL.lean)；[UEOT.V3.FiniteCTMCPathKL.p_kl_04_clock](../formalization/ueot-core/UEOT/V3/FiniteCTMCPathKL.lean)；[UEOT.V3.FiniteCTMCPathKL.p_kl_04](../formalization/ueot-core/UEOT/V3/FiniteCTMCPathKL.lean) |
| P-KL-05 | [第 22 章](UEOT_MATHEMATICS.md#ch-22) | 领域适配 | [UEOT.V3.GirsanovPathKL.TerminalGirsanovData.p_kl_05](../formalization/ueot-core/UEOT/V3/GirsanovPathKL.lean) |
| P-DDH-01 | [第 23 章](UEOT_MATHEMATICS.md#ch-23) | 保留边界 | [UEOT.V3.DualDriveGauge.p_ddh_01](../formalization/ueot-core/UEOT/V3/DualDriveGauge.lean) |
| P-DDH-02 | [第 23 章](UEOT_MATHEMATICS.md#ch-23) | 领域适配 | [UEOT.V3.ExponentialFamilyCalculus.p_ddh_02](../formalization/ueot-core/UEOT/V3/ExponentialFamilyCalculus.lean) |
| P-DDH-03 | [第 23 章](UEOT_MATHEMATICS.md#ch-23) | 领域适配 | [UEOT.V3.ExponentialFamilyIProjection.p_ddh_03](../formalization/ueot-core/UEOT/V3/ExponentialFamilyIProjection.lean) |
| P-DDH-04 | [第 23 章](UEOT_MATHEMATICS.md#ch-23) | 领域适配 | [UEOT.V3.CommonBottleneckRank.p_ddh_04](../formalization/ueot-core/UEOT/V3/CommonBottleneckRank.lean) |
| P-DDH-05 | [第 23 章](UEOT_MATHEMATICS.md#ch-23) | 领域适配 | [UEOT.V3.SingularValueEffectiveDimension.p_ddh_05](../formalization/ueot-core/UEOT/V3/SingularValueEffectiveDimension.lean) |
| P-ALI-01 | [第 24 章](UEOT_MATHEMATICS.md#ch-24) | 领域适配 | [UEOT.V3.AlignmentGlobalExactness.p_ali_01](../formalization/ueot-core/UEOT/V3/AlignmentGlobalExactness.lean) |
| P-ALI-02 | [第 24 章](UEOT_MATHEMATICS.md#ch-24) | 领域适配 | [UEOT.V3.AlignmentParentValue.p_ali_02](../formalization/ueot-core/UEOT/V3/AlignmentParentValue.lean) |
| P-ALI-03 | [第 24 章](UEOT_MATHEMATICS.md#ch-24) | 领域适配 | [UEOT.V3.AlignmentThreshold.p_ali_03](../formalization/ueot-core/UEOT/V3/AlignmentThreshold.lean) |
| P-EVO-01 | [第 25 章](UEOT_MATHEMATICS.md#ch-25) | 领域适配 | [UEOT.V3.EvolutionPrice.p_evo_01](../formalization/ueot-core/UEOT/V3/EvolutionPrice.lean) |
| P-EVO-02 | [第 25 章](UEOT_MATHEMATICS.md#ch-25) | 保留边界 | [UEOT.V3.EvolutionSharedLabel.p_evo_02](../formalization/ueot-core/UEOT/V3/EvolutionSharedLabel.lean) |
| P-EVO-03 | [第 25 章](UEOT_MATHEMATICS.md#ch-25) | 领域适配 | [UEOT.V3.EvolutionPerronGrowth.p_evo_03](../formalization/ueot-core/UEOT/V3/EvolutionPerronGrowth.lean) |
| P-EVO-04 | [第 25 章](UEOT_MATHEMATICS.md#ch-25) | 生成端点 | [UEOT.V3.EvolutionReproductiveMartingale.p_evo_04](../formalization/ueot-core/UEOT/V3/EvolutionReproductiveMartingale.lean) |
| P-BRG-01 | [第 26 章](UEOT_MATHEMATICS.md#ch-26) | 领域适配 | [UEOT.V3.FixedFitnessRecurrenceUniqueness.p_brg_01_closedForm_of_recurrence](../formalization/ueot-core/UEOT/V3/FixedFitnessRecurrenceUniqueness.lean)；[UEOT.V3.FixedFitnessConcentration.p_brg_01](../formalization/ueot-core/UEOT/V3/FixedFitnessConcentration.lean) |
| P-BRG-02 | [第 26 章](UEOT_MATHEMATICS.md#ch-26) | 保留边界 | [UEOT.V3.SelectionBridge.ReplicationBridge.behavior_equiv_fitness_eq](../formalization/ueot-core/UEOT/V3/SelectionBridge.lean)；[UEOT.V3.SelectionBridge.ReplicationBridge.behavior_equiv_same_multiplier](../formalization/ueot-core/UEOT/V3/SelectionBridge.lean)；[UEOT.V3.SelectionBridge.ReplicationBridge.behavior_equiv_positive_ratio_preserved](../formalization/ueot-core/UEOT/V3/SelectionBridge.lean) |
| P-REF-01 | [第 27 章](UEOT_MATHEMATICS.md#ch-27) | 领域适配 | [UEOT.V3.ReflexivePRef01.p_ref_01](../formalization/ueot-core/UEOT/V3/ReflexivePRef01.lean)；[UEOT.V3.ReflexivePRef01.p_ref_01_structureModification](../formalization/ueot-core/UEOT/V3/ReflexivePRef01.lean)；[UEOT.V3.ReflexivePRef01.p_ref_01_compression_closure_iff_kernel](../formalization/ueot-core/UEOT/V3/ReflexivePRef01.lean)；[UEOT.V3.ReflexivePRef01.p_ref_01_compression_closure_iff_pathLaw](../formalization/ueot-core/UEOT/V3/ReflexivePRef01.lean) |
| P-REF-02 | [第 27 章](UEOT_MATHEMATICS.md#ch-27) | 领域适配 | [UEOT.V3.PRef02.p_ref_02_general_joint](../formalization/ueot-core/UEOT/V3/PRef02.lean)；[UEOT.V3.PRef02.p_ref_02_general_update](../formalization/ueot-core/UEOT/V3/PRef02.lean)；[UEOT.V3.PRef02.p_ref_02_discrete_observation](../formalization/ueot-core/UEOT/V3/PRef02.lean)；[UEOT.V3.PRef02.p_ref_02_discrete_posterior](../formalization/ueot-core/UEOT/V3/PRef02.lean)；[UEOT.V3.PRef02.p_ref_02_discrete_modelConflict](../formalization/ueot-core/UEOT/V3/PRef02.lean)；[UEOT.V3.PRef02.p_ref_02_discounted_step](../formalization/ueot-core/UEOT/V3/PRef02.lean) |
| P-REF-03 | [第 27 章](UEOT_MATHEMATICS.md#ch-27) | 领域适配 | [UEOT.V3.FreeInformationValue.p_ref_03](../formalization/ueot-core/UEOT/V3/FreeInformationValue.lean) |
| P-REF-04 | [第 27 章](UEOT_MATHEMATICS.md#ch-27) | 领域适配 | [UEOT.V3.Decision.goal_regret](../formalization/ueot-core/UEOT/V3/Decision.lean) |
| P-REF-05 | [第 27 章](UEOT_MATHEMATICS.md#ch-27) | 领域适配 | [UEOT.V3.Agency.feasibleValue_mono](../formalization/ueot-core/UEOT/V3/Agency.lean)；[UEOT.V3.Agency.feasibleValueReal_mono](../formalization/ueot-core/UEOT/V3/Agency.lean)；[UEOT.V3.Agency.extension_optimalValue_mono](../formalization/ueot-core/UEOT/V3/Agency.lean) |
| P-API-01 | [第 28 章](UEOT_MATHEMATICS.md#ch-28) | 生成端点 | [UEOT.V3.ProcessInterface.p_api_01_exact](../formalization/ueot-core/UEOT/V3/ProcessInterface.lean)；[UEOT.V3.ProcessInterface.p_api_01_approx](../formalization/ueot-core/UEOT/V3/ProcessInterface.lean) |
| P-ALG-01 | [第 28 章](UEOT_MATHEMATICS.md#ch-28) | 领域适配 | [UEOT.V3.PAlg01.p_alg_01](../formalization/ueot-core/UEOT/V3/PAlg01.lean) |
| P-CORE-01 | [第 31 章](UEOT_MATHEMATICS.md#ch-31) | 领域适配 | [UEOT.V3.CoreOperationalAssembly.p_core_01](../formalization/ueot-core/UEOT/V3/CoreOperationalAssembly.lean) |

## 3. 新增连接与边界的对应

第 32–38 章的 M 编号不改变上述 106 条。全部新连接端点及命名空间前缀见 [附录 F.3](UEOT_MATHEMATICS.md#appendix-f)。其阅读层次如下：

| 章节 | 可直接审阅的数学问题 | 阅读入口 |
|---|---|---|
| 32 | 八类层级、集合／可测降落、误差传输、不变性、正谱数据与相对压缩最小性 | [第 32 章](UEOT_MATHEMATICS.md#ch-32) |
| 33 | 同零关系的定量 no-go、双边校准、三角与收缩标度、Π/Φ 规范等价 | [第 33 章](UEOT_MATHEMATICS.md#ch-33) |
| 34 | 六种对象角色、条件 FBT、P12 程序来源、P9 RG 相容缺口、C1–C7 科学接口 | [第 34 章](UEOT_MATHEMATICS.md#ch-34) |
| 35 | 同一源上的组织商、真实无限安全路径、约束最优、程序恢复一致性 | [第 35 章](UEOT_MATHEMATICS.md#ch-35) |
| 36 | 实际纤维后验、共同前缀 TV、实际部署占据、认证行覆盖与失败风险 | [第 36 章](UEOT_MATHEMATICS.md#ch-36) |
| 37 | trace support 与实际后验支持、策略存在 iff、确切支持关系检验、后验严格放松与死路 | [第 37 章](UEOT_MATHEMATICS.md#ch-37) |
| 38 | 注册 Good-only 校准、实际训练部署 joint、viability 薄桥、17/32 与 9/64 的不同作用 | [第 38 章](UEOT_MATHEMATICS.md#ch-38) |

## 4. 原始代码与历史运行

原书附录 D 的完整 Python 数值程序在维护版中按原文保留；其标记的 SHA-256 为 4d4072377cbae485f595eddc239ea6962a7bdc5cf7ad400e8d75086ce485c5f7。原有 JSON 输出及 2371 项检查属于 v3.0 历史运行，本轮未重新执行这份大数值程序。

本轮有限关系检验的 true、false、true 来自真实 Lean #eval；它与旧 NumPy 检查是两个独立证据集合。支持桥、薄联合桥和 512 坐标真实采样见证的实际 assembled-source 编译身份见 [附录 F.4](UEOT_MATHEMATICS.md#appendix-f)。未通过的第一稿和混合批次不追溯改为成功。

## 5. 解释责任

数学正文给出条件、陈述、关键证明与必要性反例；源码提供形式实现；编译和公理检查提供该实现的核验记录；真实实验检验世界模型。原哲学论文在概念和问题来源上有独立作用，但不作为无条件数学命题的证明。两部书的互相修订应经过这些明确接口，而不把文本完整、内核检查、发布完成与现实真理混为同一状态。

## 6. 条件持续与接口扩展的本次正文增量

第 21.7、35.7 节从同一 conflictRewardControl.micro 与真实 transitionPMF 推导对象划分、恒定历史随机策略的闭环、显式不变律、killed QSD、曾失败风险以及安全受限最优。新实例的数值和完整 greedy 不变律族为书面证明；一般源、控制、M-OI、M-PE 与 GOA 接口已生产。受限模型在 K 外的动作域保留原定义，因此完整 greedy 不变律并非唯一。这一具体边界不能由恒定策略的值等式替代。

第 36.8 节吸收 [有限观察像与 escape 研究](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/interface_research_v1/FINITE_OBSERVATION_ESCAPE.md) 的完整事件证明和 live 历史递推。FiniteObservationEscape、PathObservationEscape、ArbitraryObservationRisk、FiniteObservationEscapeBoundary 已作为本版生产接口实现：保持原 Q、原策略、原实际占据与可测粗事件，并证明无限观察环境中 5/12、1/4 及编码后零距离的联合边界。

第 38.10 节的实际不等 N j 采样、共同 Good 选中包络与同策略零占据消去，分别对应本批 VariableRegisteredSamples、VariableRegisteredJoint、ViableVariableRegisteredJoint；三个接口均已纳入本版生产范围。Joint/Viable 允许任意 Y，明示同一 Good 上选中 F 的可测性，保留有限 Ω/X/A 与时间半径。首版有限 Y 的通过记录保留为历史；Samples 一般采样层与 Joint 的条件不混同。

本版引用上述七个生产模块。声明、完整源树身份与验收入口见 [REGISTERED_INTERFACES_CLOSURE_V1](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/REGISTERED_INTERFACES_CLOSURE_V1.md)；接口范围见 [LEAN_API_SCOPE](LEAN_API_SCOPE.md) 与附录 F.3.1。

哲学反馈进入配套书关于对象、修复、学习、稳态与意义的独立论证。其规范理由不从本数学模型自动推出；原论文第 6–7、40–41 页提出的 GOA、目的与意义问题继续作为思想来源，而非新数学命题的证明。既有 P-ID 源映射、原附件、历史代码与历史输出未因本次增补重写。


## 7. 同源程序、预测与连续来源的历史演进

以下按第 39 章各批次顺序保留来源定位。阶段中的未覆盖事项只描述当时边界，不取代第 8、9 节以及后续已采用合同的结论；是否仍属当前义务须按对应后继消费者判断。

第 39 章与附录 F.5 对应实际修复程序、故障和资源、同一无限记录、时戳出生身份、一般有限动作词响应、实际最小预测来源、完整历史策略以及实际连续 Brownian/OU 来源。直接入口为 [第 39 章](UEOT_MATHEMATICS.md#ch-39)；该阶段登记的精确模型条件、公开端点与义务见[连续源与历史控制差额](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/continuous_history_source_v1/RESULTS_AND_OPEN_OBLIGATIONS.md)。新增来源不改变冻结 106 条的历史索引。第 39.12 节已在声明协议与源类中给出真实任意历史过去的 fresh adaptive 最小性；第 39.15—39.16 节给真正 predictable 终点积分与有限目的证书的实际无限消费者。第 39.17—39.19 节又给原自然过滤上的实际连续积分、真实时间能量和平方补偿鞅，以及 Brownian 原分割极限；第 39.20—39.21 节接实际人口父身份和经验子代 Price。第 39.22—39.25 节进一步给同一完整标量输入的确定性分割 QV 与实际加权表、联合历史向量积分的原生闭包、完整新训练协议账本及共同群体／读出源的实际亲本风险。第 39.26—39.29 节继续给同源标量 Itô／Dynkin、完整向量可预测域／条件过程／均方连续、原 OU 条件核、常控制 Girsanov／KL 及同数据 C5 带噪风险；第 39.30—39.33 节又给实际过去反馈表的完整换测度路径、同一向量积分的连续版本、保留执行的尺度、真实持续人口账本及精确统一供给边界与原校准的有用接受。一般 SDE／全部可预测控制及未覆盖源类没有因这些有限消费者被无条件覆盖；该阶段对内生资源和整体闭环的未完成记录，须结合后继实际来源及第 8、9 节读取。

这一阶段新增连接的直接入口见数学书第 4.6、22.6、39.12—39.16 节及附录 F.5；对应来源和原生接口范围见[最新来源差额](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/predictable_finite_purpose_v1/RESULTS_AND_OPEN_OBLIGATIONS.md)。有限目的判定保持全部原采样数据，仅增加形式协议与确定性 fixtures；原采样协议的 source-level UNKNOWN 与负界保留；新训练资助须按另登记完整协议判断。

此阶段新增直接入口为第 39.17—39.21 节及附录 F.5；当时登记的精确条件与义务见[连续积分／反馈资源](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/continuous_resource_source_v1/RESULTS_AND_OPEN_OBLIGATIONS.md)和[实际补偿／人口来源](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/compensator_population_source_v1/RESULTS_AND_OPEN_OBLIGATIONS.md)。这一段记录第 39.17—39.21 节的来源；后继已集成差额现见第 39.22—39.25 节。

后续直接入口补至第 39.22—39.25 节，分别接[完整 QV／训练／发现](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/full_qv_vector_training_source_v1/RESULTS_AND_OPEN_OBLIGATIONS.md)与[向量表示／实际加权表／共同群体源](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/vector_weighted_population_source_v1/RESULTS_AND_OPEN_OBLIGATIONS.md)。该段记录 #409/#410 的来源；随后补至第 39.26—39.29 节与[同输入演算／完整向量域／同数据校准](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/ito_vector_calibration_source_v1/RESULTS_AND_OPEN_OBLIGATIONS.md)，采用已集成 #412。该包使用实际原 Dynkin／TerminalGirsanovData／action-gap 消费者，C5 全部128形式读出逐项绑定原 sourceData；联合风险不是条件或逐样本保证。第 39.30—39.33 节现采用 #414/#415，直接对应[过去反馈／尺度／接受](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/past_feedback_scale_source_v1/RESULTS_AND_OPEN_OBLIGATIONS.md)及[实际表路径／连续向量／持续资金](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/table_continuous_funding_source_v1/RESULTS_AND_OPEN_OBLIGATIONS.md)。有限表 KL 使用最终 Q 能量，向量连续性不等于状态 Itô，供给 iff 是有实际初始占用时所有登记计划各自 AE 的统一保证；非每个计划的必要条件。第 39.34—39.38 节现采用 #417/#418，进一步接入[有界控制／实际读数／载体来源](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/bounded_control_carrier_source_v1/RESULTS_AND_OPEN_OBLIGATIONS.md)和[实际 Q 积分／固定输入 QV／程序实现](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/q_integral_vector_qv_program_source_v1/RESULTS_AND_OPEN_OBLIGATIONS.md)。Q 积分域保持显式闭包，QV 输出是多维噪声的标量积分，程序 Valid 是目标保持；第 39.39—39.44 节现采用 #420/#421，接[实际原控制／状态权重／持续程序](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/fixed_q_run_stateweighted_source_v1/RESULTS_AND_OPEN_OBLIGATIONS.md)及[状态演算／Q 鞅／真实恢复](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/state_ito_q_martingale_recovery_source_v1/RESULTS_AND_OPEN_OBLIGATIONS.md)。有限状态 Itô 保留全局导数界与零初态积分状态，Q 域保留显式闭包，恢复检查不取消故障。第 39.45—39.48 节再接物理时钟 OU／真实漂移／实际程序长期与目的／完整原可预测 Q 域，见[新来源差额](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/drift_ou_instruction_qfull_source_v1/RESULTS_AND_OPEN_OBLIGATIONS.md)。第 39.49—39.54 节采用 #425/#426 的[实际时变身体／子对象／全价格目的](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/rotating_body_dynamic_price_source_v1/RESULTS_AND_OPEN_OBLIGATIONS.md)与[有限资源／有限块／原数据动态选择](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/resource_block_dynamic_data_source_v1/RESULTS_AND_OPEN_OBLIGATIONS.md)。第 39.55—39.57 节进一步采用[同源资金／可数块／实际轮末命中](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/funded_countable_block_source_v1/RESULTS_AND_OPEN_OBLIGATIONS.md)。第 39.58—39.60 节采用[实际父对象／原生完整程序生活律／有限线性rank因子存在](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/native_lifecycle_rank_source_v1/RESULTS_AND_OPEN_OBLIGATIONS.md)；第 39.61—39.64 节采用[实际六性质／有限后代 Price／同 tick 组织来源](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/p9_lineage_organization_source_v1/RESULTS_AND_OPEN_OBLIGATIONS.md)；第 39.65—39.67 节采用[实际登记／出生父标记／有限资金来源](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/owner_discovery_resource_source_v1/RESULTS_AND_OPEN_OBLIGATIONS.md)；第 39.68—39.69 节采用[同钱包共同角色／实际规范预测来源](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/finite_predictive_source_v1/RESULTS_AND_OPEN_OBLIGATIONS.md)；该阶段尚未纳入的实际末亲本带资续行与同源 Price 共同角色，后继状态见第 8 节及原完整来源合同；不能仅据此历史段落继续报告未完成。冻结历史索引与原数据不改。

## 8. 原全 Core 条件数学验收与后继入口

第 39.68—39.74 节与 F.5 的最新状态覆盖同一钱包、真实首出生父、实际 Register 规范预测及真实末亲本续行，并接原 P5 均值／有限时域占据和原 P6 期望实际费用。当前完整范围、量词、前提分类、严格反例与实际发行条件见[全理论验收表](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/whole_theory_formal_closure_v1/FINAL_ACCEPTANCE.md)；三源及独立公共消费者见[来源核验](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/finite_predictive_source_v1/SOURCE_VALIDATION.json)。前述各差额段落是历史来源定位，未覆盖的一般 SDE、任意非线性理论等不自动成为当前合同承诺。冻结原书与旧裁决不重写；原第 21.7、35.4 和35.7节的具名书面义务现已由[同源参数族／独立8/5／组织来源包](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/conflict_family_book_source_v1/RESULTS_AND_OPEN_OBLIGATIONS.md)给出实际证明与公共消费者；一般来源与原范围逐项科学结算进一步见第9节；本节合同与发行身份按对应包的最终回执读取；后继 Core 定本和 PR #447 增长分类另按本文末节及各自验收读取。经验支持 UNVERIFIED。


## 9. 原一般来源的实际构造

第25.4节 K-PF-01／P-EVO-03 由 UC.PrimitivePerronClosure.certificateOfPrimitive 从任意非空有限本原 M 构造原完整证书，实际增长与谱系条件消费者、实复代数单重均有端点。第10.4节由 UC.CompactSpectralSemigroupSource 和 CompactKilledSpectralBinding 从同一实际生成关系构造展开、余项及原 killed 条件律结论；非零余项实例另证完整算子与实际核一致。准确来源、合法条件、独审及原合同结算见[一般来源包](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/general_perron_compact_spectral_source_v1/RESULTS_AND_OPEN_OBLIGATIONS.md)。旧标准接口与旧负向审查保留；本段不把标准旁引或现实经验重标为已执行的 UEOT 证明。

## 2026-11-04：有限钱包下的全流程联合决策

数学书 §39.75—39.81 的新来源，不改变冻结的 106 个 P-ID 或原全 Core 完成裁决。源目录统一为 `UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/`。

| 主文 | Lean 来源与关键端点 |
|---|---|
| §39.75—76 同一源/信息/费用 | FiniteJointDecisionBelief、FiniteJointDecisionFilteredModel、RegisterJointDecisionSource、Execution、NativeLaw；联合质量/后验与原 Store 交易投影 |
| §39.77 实际返回/完整比较类 | FiniteJointDecisionSolver、SolverExecution、SupportedPolicy；solve、rows_exact、supported_actual_causal_le_returned；FiniteJointDecisionFastSolver.fastSolve_eq |
| §39.76—78 原生消费者 | [RegisterJointDecisionNativeConsumer](../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterJointDecisionNativeConsumer.lean)：returned_native_value/payment/optimal/population、initial_returned_native_value/boundary |
| §39.78 一般期限边界 | [RegisterJointDecisionOptimality](../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterJointDecisionOptimality.lean)：optimal_initial_value、positive_price_boundary、insufficient_wallet_optimal_zero；FreeTail与ExpectedBounds提供源上界/达到 |
| §39.79—80 参数/后验/对照 | [RegisterJointDecisionBoundary](../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterJointDecisionBoundary.lean)、RegisterJointDecisionFixedTail：持久矩、真实故障后验与严格性条件、同菜单固定流程及状态反馈差 |

实际输入、THIS 表、原四步成功运行、完整有理重放、编译失败与缓存尝试、非作者审查均见[联合决策交付包](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/joint_decision_closure_v1/README.md)。本地检查不写成已禁用的云 CI 通过；形式结论不增加经验支持。

## 2026-11-06：许可历史到实际紧凑控制器

数学书 §39.82—39.88 / 附录F 的13个新增模块、关键定理与源SHA统一见[精确定理索引](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/decision_representation_closure_v1/THEOREM_INDEX.md)。Observer/ObserverSource从原primitive导出收据更新；CountPosterior/CountHistory覆盖零先验、端点率和任意实随机完整历史；RepresentationModel与Refinement接原Belief全动作联合律。DAG/Generator、Native/Payment、Bounds与Witnesses分别提供可信全动作认证、原生执行/付款、实际Array四次界和可达正反见证。公开入口为RegisterDecisionRepresentation，经既有TheoryCompletion导入。源码、实际产物和消费者身份见[交付清单](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/decision_representation_closure_v1/DELIVERY.json)。冻结106项不变，旧完成合同不重开。

## 2026-11-06：允许实验下的机制分辨与最坏决策损失

§39.89—39.95 / 附录 F：从固定两个故障机制的真实源到可实现分辨和决策损失。[公共接口与精确端点](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/mechanism_decision_closure_v1/THEOREM_INDEX.md)、[发行身份](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/mechanism_decision_closure_v1/DELIVERY.json)和[实际原生核对](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/mechanism_decision_closure_v1/actual-execution/THIS_EXACT_CHECK.json)。旧源及冻结的 106 项不变。

## Core 定本的同源来源消费者（2026-11-06）

公共入口 `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreTheoryClosure` 可经 `UEOT`、`UEOT.V3.Compression` 或 `UEOT.V3.Compression.TheoryCompletion` 导入。`UEOT.V3` 保持原有并行子集范围，不导出这组定本模块。原定本 13 个模块及原 106 个 P-ID 的冻结映射不改。

`CoreRegenerativeSource` 从真实物理码、执行门、预付费用和 36 个局部噪声原子构造完整事件；`CoreRegenerativeRepair`/`Formation` 复用原修复秩与内生形成；`FiniteSourceGrowthControl`/`ControlPopulation` 消费旧 Perron 工厂并从实际人口推导任意允许历史核的有限条件超鞅与最优达到；`SourceCohortFeedback`/`CoreRegenerativeFeedback`/`FeedbackBoundary` 推出同源独立 cohort 的有限概率反馈及精确失效边界；`Population`/`Lineage` 从真实身份、父指针与标记连接有限 many-to-one；`Quotient` 保持完整事务与允许历史。

新定理没有裸给 success、fitness、条件均值或最优性。C1、C5、连续过程与原 Price 源结果继续按原条件复用，不冒称此有限新消费者重新实例化了每条旧定理。本文的有限条件鞅不是新增无限路径 Mathlib Martingale 实例；期望增长、原身份续存、实际份额、加权谱系和规范价值分别定型。具体可检查声明与信任范围以[定理索引](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_theory_closure_v1/THEOREM_INDEX.md)及[公理审计](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_theory_closure_v1/checks/AXIOM_AUDIT.json)为准。


## 2026-11-11：有限定本加固的书面数学来源（PR #446）

定本核心总论第三部分的 2／3／4 分类，固定同一内部程序、原资源与严格新生计数任务；从首期真实后继槽的同噪声耦合推到每个有限期限的联合记录。第 23.4 节用原公开收据得到 `(s,b,bq)` 与非零 Jacobian 行列式，限制共同光滑二维因子。两项均为书面证明和精确有限核对，未新增完整分类的专门 Lean 端点。原事务、身体后继、均值及公开观察端点仍为已证明的来源基础。

对应[冻结包](review/CORE_DEFINITIVE_FREEZE_2026-11-11/README.md)保留其实际文本指纹、独立读者及原 PDF 导航验收；它绑定 PR #446 的产物，不用后继两书字节回写该历史清单。

## 2026-11-11：严格正概率域增长分类（PR #447）

数学定本核心总论第四部分“严格正概率域上的精确增长与内部达到”消费以下三个新生产模块，公共入口仍为 `CoreTheoryClosure`。

| 来源模块 | 关键已证端点 | 责任 |
|---|---|---|
| [CoreRegenerativeGrowthClassification](../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeGrowthClassification.lean) | `valid_iff_probability_advantage_supercritical`、`optimalRate_formula`、`actual_one_step_value_le`、`actual_selected_one_step_value_eq` | 严格正概率基本域、旧 `Valid` 条件拆分、真实全菜单与最优率 `max(1, λ₀, λ₁)` |
| [CoreRegenerativeGrowthPopulation](../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeGrowthPopulation.lean) | `optimal_population_upper`、`optimal_hasExpectedGrowth`、`programPolicy_positive_branch_is_internal`、`damaged_founder_paid_repair` | 复用原完整历史实随机 Policy 和实际人口递归；共同上界、可执行达到、忠实程序执行与首期付款 |
| [CoreRegenerativeGrowthAttainment](../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeGrowthAttainment.lean) | `optimalRate_isLeast_uniform_upper`、`false_program_attains_iff`、`true_program_attains_iff`、`same_damaged_program_repairs_and_attains_iff` | 最小共同正指数底数、两个内部程序的准确达到域、各自同一受损创始体的修复与增长绑定 |

令 `k_c=s+b`、`k_b=s−δ+b+γ`，则 `λ₀=k_c`、`λ₁=(1−q)k_b+q k_c`。两个内部程序分别达到，当且仅当 `γ≤δ 且 k_c≥1`、`γ≥δ 且 λ₁≥1`；平手和临界等号保留。形式合同是全部有限期限的正双边指数界，以及覆盖全部原允许策略的共同上界最小底数。正次根／limsup 叙述为书面分析推论；两期人数反例、临界 11/12 及先付费恢复一次的策略也按书面和精确计算层次登记。它们未被一并称为专门 Lean 极限或有限期最优端点。

[来源绑定](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_growth_classification_v1/SOURCE_BINDING.json)记录原 11 个执行来源文件、旧 `Valid`、依赖及工具链均未修改；[Lean 验证](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_growth_classification_v1/LEAN_VALIDATION.json)记录三个新模块、公共入口及边界消费者的成功检查和 15 个所列端点的标准公理；[最终验证](../formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_growth_classification_v1/VALIDATION.json)记录五项出口完成、八组精确探针、两书读者与 PDF 选页验收。

这次增长范围扩大没有扩大第五部分的原选择反馈合同，没有加入未知机制学习、新程序、共享钱包、几乎处处增长或无限谱系存活。PR #447 是已采用的有限扩展，不再列作下一步候选；完整经验支持仍为 `UNVERIFIED`。
