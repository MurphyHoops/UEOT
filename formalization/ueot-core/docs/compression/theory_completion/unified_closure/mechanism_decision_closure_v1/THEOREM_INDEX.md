# 定理索引：固定故障结构、允许实验与最坏后悔

下列名称均以 `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure` 为公共命名空间前缀。每一行的模块名也是其内部命名空间名。读者不必分别导入所有文件：

```lean
import UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

#check RegisterMechanismDecision.returned
#check RegisterMechanismExperimentSharp.H3_experiment_sharp
#check RegisterMechanismDecision.returned_contract
#check RegisterMechanismDecisionNativeConsumer.returned_native_payment
```

[公共汇合入口][public]中的 `returned` 是 `RegisterMechanismDecisionConsumer.returned` 的定义别名，其输入为独立的 `Fin 4` 私种子。此接口不新建控制器，也不把机制、真实噪声或完整 Store 加入动作选择。要看返回值背后的全竞争类下界，读下表中的 `all_native_regret_lower` 和 `every_raw_has_shared_realization`；要看数值是否真能取得，读 `returned_native_values` 和 `returned_native_payment`。

## 1. 真实事务、联合信息和可达的迁移反例

| 模块 | 声明 | 解决的问题 |
|---|---|---|
| [RegisterMechanismDecisionSource][src] | `step`, `observe`, `initialWorld`, `step_S`, `step_normal`, `step_G_fault`, `theta_preserved`, `stopped_step`, `step_length` | 固定 S/G；唯一坏 root 初始化；S 原事务、G 仅故障后追加全体共同损坏；每个 tick 的停止状态和新增槽。允许收据保持原定义。 |
| [RegisterMechanismDecisionNative][nat] | `nativeStep`, `nativeTransaction`, `nativeExecute_S`, `native_G_missing_fault`, `damageOrganism_other_bit`, `nativeStep_metadata`, `native_fault_no_child`, `native_new_slot_is_actual_child` | 完整原生 Store；S 运行保守延伸；缺失地址的 G 故障仍生效；其他物理位与事务后的程序、身份、谱系、时钟保留；出生来自原交易。 |
| [RegisterMechanismDecisionNative][nat] | `nativeExecute_project`, `nativeExecute_length`, `prefix_cost_eq`, `table_payoff_eq`, `rawNativeCausalValue_eq_packed` | 每个对齐起点、有限完整表和噪声带的实际记录投影；原生费用/净收益；任意历史实随机核的原生值桥。完整身份留在原生侧。 |
| [RegisterMechanismDecisionSource][src] | `initialBelief`, `historyInfo`, `walletContract`, `supported_charge_le_cap`, `value_eq_source`, `all_actual_causal_le_returned` | 新源使用原联合 belief/钱包/菜单；在正支持行检查预付，实际费用与收据一致，并复用既有完整历史最优性。 |
| [RegisterMechanismDecisionInformation][info] | `history_disintegration`, `rawHistory_factor`, `raw_joint_history_identity`, `real_policy_joint_posterior` | 以已请求动作及允许收据累积联合质量；任意实概率动作核的动作因子只依允许历史。实际质量为正时可除，零质量不伪造条件事件。 |
| [RegisterMechanismDecisionInformation][info] | `ambiguous_actual`, `ambiguous_likelihood`, `ambiguous_joint_posterior`, `old_observer_migration_failure`, `ambiguous_next_receipts` | 11/00 前缀在两机制各有 $r(1-r)$ 质量。任意归一化机制权重（含零权重）、$0<r<1$ 时具有不同的机制—身体联合状态；G 不能沿用旧 S observer。 |

## 2. 所有允许实验的边界与实际达到者

| 模块 | 声明 | 解决的问题 |
|---|---|---|
| [RegisterMechanismExperimentRate][rate] | `PhysicalExperiment`, `primitiveLaw_real`, `primitiveLaw_ofParameters` | 实验率可为任意登记的实数 $r\in[0,1]$；原 mode 与独立公平 label 的每个原子质量为 $r/2$ 或 $(1-r)/2$。在有理规划参数上与同一原噪声律一致。 |
| [RegisterMechanismTableLaw][table] | `sampleTable`, `sampleTable_supported`, `sampled_table_historyLaw_eq_raw`, `rawHistoryLaw_eq_seed_tape` | 对原实随机历史核预抽完整有限响应树，不读任何世界字段；同一树律在每个既定世界实现原允许历史律。正质量树保留原“仅在源支持上合法”的要求。 |
| [RegisterMechanismExperimentPaths][paths] | `first_receipt_eq`, `second_receipt_eq`, `third_receipt_eq_unless_NFN`, `history_three_eq_unless_NFN`, `separationTable`, `separation_event_S`, `separation_event_G` | 从真实 primitive 穷尽所有可能的当步请求得到前三个收据的路径约束；上界不限于最后部署的行动。正常—故障—正常（NFN）是 H3 唯一可能出现差异的 mode 词。 |
| [RegisterMechanismExperimentZero][zero]、[RegisterMechanismExperimentLaw][law] | `root_history_same`, `insufficient_wallet_zero_history`；`seeded_root_history_eq`, `seeded_short_eq`, `seeded_insufficient_wallet_eq`, `endpoint_TV_zero` | 任意有限 H 的实际 root-only、$H\le2$ 的全菜单、唯一坏 founder 且 $B<c$，以及 $r=0,1$ 的零界。低钱包依赖请求前 cap；root-only 可只限制实际正支持派发。 |
| [RegisterMechanismExperimentLaw][law] | `seeded_H3_TV_upper`, `raw_H3_TV_upper`, `separation_TV_exact` | 真实源公共噪声和独立私随机耦合给全动作实验 TV 上界；分离表中的排他收据事件给相同下界。 |
| [RegisterMechanismExperimentSharp][sharp] | `separation_prepaid`, `H3_experiment_sharp` | 当 $B\ge c>0$，两种机制下每一条完整噪声带均可执行“正确写根 / 根 idle / child1 idle”，达到 $\Delta_{3,B}=r^2(1-r)$。 |
| [RegisterMechanismExperimentLaw][law] | `classification_finite_lower`, `classification_finite_positive`, `H3_half_classification_lower`, `separation_test_exact` | 所有有限视界的等权分类错误界 $(1-r)^H/2$；H3、$r=1/2$、可预付分离实验时最小错误 $7/16$。终端事件可作用于“私种子、允许历史”。 |
| [RegisterMechanismDecisionShort][short]、[RegisterMechanismDecisionConsumer][cons]、[RegisterMechanismDecisionRegret][reg] | `short_common_optimal`, `short_common_dominates_raw`；`short_common_values`；`nonzero_common_optimum` | 任意登记规划参数与同一钱包的 $H\le2$ 共同返回表；H2 具体例中两个机制的同一合法最优值是 $13/16$。 |

终端可保留比动作树更多的私随机信息。对任意事先独立的私种子和任何可测二元终端检验，冻结种子得到“完整动作树，针对每条可能终端历史的 Bool 判决表”。有限时限、有限动作和有限收据使该签名有限；逐机制推前后保留同一行动、收据和判决的联合律。对每个检验分别使用这一归约即可得到原私种子情况下的风险/TV 界，不对原随机律作有理性限制；这一步的数学说明见 [README](README.md)。形式化的 `seededLaw`、`rawHistoryLaw` 分别处理保留有限种子的输出与原始实概率核的允许历史。

## 3. 后悔证书、完整比较类与冻结决策

| 模块 | 声明 | 解决的问题 |
|---|---|---|
| [FiniteMechanismRegretCertificate][cert] | `lower_bound`, `certificate`, `matched_certificate`, `worst_zero_iff` | 任意非空有限机制族及同一共享策略类：由任意概率权重的已证全策略上界和一个实际候选给 $L\le R^*\le U$。当上下界相等时认证指定候选；零后悔 iff 对所有机制同时最优仅对**给定策略**表述。 |
| [RegisterMechanismDecisionConsumer][cons] | `cachedAt_eq`, `returnedS_eq_solve`, `returnedG_eq_solve`, `knownS_all_policy_upper`, `knownG_all_policy_upper`, `dual_value`, `returned_matrix` | 同一旧缓存求解器返回完整表；已知 S/G 的比较者仍仅凭收据行动，源导出的 oracle 值为 41/32、40/32，见证 $w=(3/4,1/4)$ 的全菜单值为 5/4。 |
| [RegisterMechanismDecisionConsumer][cons] | `raw_mixture_identity`, `all_shared_weighted_upper`, `all_shared_regret_lower`, `seed_noise_independent`, `returned_randomized_values` | 任意合法实随机原历史核的双机制加权值至多 5/4；实际四点私种子同真实机制和世界噪声独立。部署两个机制的 J 是 161/128、157/128。 |
| [RegisterMechanismDecisionRegret][reg] | `ambiguous_mass_and_wallet`, `ambiguous_last_values`, `minimax_regret_exact`, `rho_worst` | 同一已发生前缀，余一个 tick、余额 1；备份 idle 在 S/G 值为 1/2、0，根正确写均值 3/8。独立混合的同一返回达到全策略最坏后悔 3/128。 |
| [RegisterMechanismDecisionRealization][real] | `sampled_source_value`, `every_raw_has_shared_realization`, `returned_beats_every_raw_regret` | 原任意记忆、实动作概率控制器中的**每个**合法竞争者可由同一个有限树律实现，两个机制的实际 $J_m$ 分别保持，并非只保持加权平均。 |
| [RegisterMechanismDecisionRegret][reg] | `deterministic_J_lattice`, `deterministic_regret_lattice`, `deterministic_lower_exact`, `returnedG_worst`, `deterministic_minimax_exact` | 冻结消费者所有确定性策略的 $1/32$ 格点；严格正下界排除零，$\pi_G$ 真实达到确定性最优 1/32。此格点依赖冻结参数。 |

## 4. THIS 输出与完整原生支付

| 模块 | 声明 | 解决的问题 |
|---|---|---|
| [RegisterMechanismDecisionNativeConsumer][nc] | `nativeJ`, `returned_nativeJ`, `returned_native_values`, `returned_native_regret`, `returned_native_population` | 同一 `returned seed` 的原生原事务折扣净值与生产源表值一致；混合的原生 J 和后悔；每条原生三步路径有三条记录、三条允许历史、四个最终槽；无出生时真实 None 原位保留。 |
| [RegisterMechanismDecisionNativeConsumer][nc] | `NativePrepaid`, `returned_native_payment`, `nativeRawJ_eq_actualJ`, `all_native_regret_lower` | 每个 seed、固定机制及完整噪声带：执行前允许支付 cap；每个前缀余额等于 2 减真实累计费用且非负。真实完整 Store 上原实随机竞争者的最坏后悔下界也是 3/128。 |
| [RegisterMechanismDecision][public] | `returned`, `returned_contract` | 将已证的随机化最优、实际原生返回值及确定性最优交给同一公共入口。 |

**证据边界。** 512 条实际原生路径与 1,536 个实际非空支付前缀检验的是同一个返回物及执行接线，不代替上述全策略定理。闭合 H2/H3 数值求值 `exact_two_data`、`exact_cached_data` 使用 `native_decide`；其依赖须与原生计算正确性一同解释。公共消费文件以 `#check` 和 `#print axioms` 暴露主要端点和实际信任依赖。自然系统的经验适用性仍为 UNVERIFIED；本索引也不认定任何尚未发生的发布或 GI 事务。

[src]: ../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterMechanismDecisionSource.lean
[nat]: ../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterMechanismDecisionNative.lean
[info]: ../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterMechanismDecisionInformation.lean
[rate]: ../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterMechanismExperimentRate.lean
[table]: ../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterMechanismTableLaw.lean
[paths]: ../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterMechanismExperimentPaths.lean
[zero]: ../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterMechanismExperimentZero.lean
[law]: ../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterMechanismExperimentLaw.lean
[sharp]: ../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterMechanismExperimentSharp.lean
[short]: ../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterMechanismDecisionShort.lean
[cert]: ../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteMechanismRegretCertificate.lean
[cons]: ../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterMechanismDecisionConsumer.lean
[reg]: ../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterMechanismDecisionRegret.lean
[real]: ../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterMechanismDecisionRealization.lean
[nc]: ../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterMechanismDecisionNativeConsumer.lean
[public]: ../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterMechanismDecision.lean

实际可预付实验的最大值与上确界：RegisterMechanismExperimentSharp.H3_distance_greatest、H3_distance_supremum。任意独立私随机概率空间（含非原子）的终端分类：arbitrary_private_H3_error、arbitrary_private_finite_error；允许终端检验随整个私种子变化。
