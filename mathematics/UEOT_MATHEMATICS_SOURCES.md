# UEOT 数学著作 3.1：完整来源索引

本索引随 [完整数学著作](UEOT_MATHEMATICS.md) 使用。书的正文与附录 B 完整保留 106 个稳定 P-ID 的陈述、证明及依赖；本索引额外给出同一底本的全部登记 Lean 源端点，不以名称索引替代类型或假设审阅。

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
