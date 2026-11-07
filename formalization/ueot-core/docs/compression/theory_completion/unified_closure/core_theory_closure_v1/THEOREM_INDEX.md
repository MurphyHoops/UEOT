# UEOT 核心理论定本：定理与来源索引

**定理与实际来源索引。** 本文按《UEOT_CORE_THEORY_CLOSURE_MASTER_PLAN_2026-11-06.md》的 S0—S6 与第 12.1 节七项出口，索引已经存在的声明及其实际消费者。它不以文件数或定理数表示理论完成度，也不代替本包最终的源码 manifest、编译日志、逐端点公理打印、发行回执或原 GI 接续回执。

本次核对的正式模块位于仓库目录：

`formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/`。

以下书面缩写只用于缩短索引；例如 `S.step_budget` 的完整声明名为 `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeSource.step_budget`。这些缩写不声称仓库另有同名 Lean alias。

| 书面前缀 | 完整命名空间后缀（前接 `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.`） | 源文件 |
|---|---|---|
| S | CoreRegenerativeSource | CoreRegenerativeSource.lean、CoreRegenerativeRepair.lean、CoreRegenerativeFormation.lean、CoreRegenerativeOneStep.lean |
| G | FiniteSourceGrowthControl | FiniteSourceGrowthControl.lean |
| GS | FiniteSourceGrowthControl.SourceConsumer | FiniteSourceGrowthControl.lean |
| P | CoreRegenerativePopulation | CoreRegenerativePopulation.lean |
| C | CoreRegenerativeControlPopulation | CoreRegenerativeControlPopulation.lean |
| L | CoreRegenerativeLineage | CoreRegenerativeLineage.lean |
| Prob | SourceCohortFeedback | SourceCohortFeedback.lean |
| F | CoreRegenerativeFeedback | CoreRegenerativeFeedback.lean |
| B | CoreRegenerativeFeedbackBoundary | CoreRegenerativeFeedbackBoundary.lean |
| Q | CoreRegenerativeQuotient | CoreRegenerativeQuotient.lean |
| T | CoreTheoryClosure | CoreTheoryClosure.lean |

这张表登记十三个正式模块的责任与命名空间。`CoreTheoryClosure` 是同一来源的共同消费者，未增加第二个世界源。原生导出程序 `NativeSourceRun.lean` 是执行证据入口，不以另一个文件计作新增数学贡献。

## 一、S0：声明类、原始量与公开修订

| 合同内容 | 可核查入口 | 结论及边界 |
|---|---|---|
| 唯一新源的原始数据 | `S.Triple`、`S.Body`、`S.Parameters`、`S.Noise`、`S.Action` | 身体含真实码位、执行门、bootstrap 和静默标签；源参数只有原始噪声参数。没有 success、fitness、条件均值或最优性字段。 |
| 非空参数化正类 | `S.Valid`、`S.concreteParameters_valid` | 正类为 \(0<\delta<s<1,\ 0<b,\ b+\gamma<1,\ \delta<\gamma,\ 0<q<1,\ s+b>1\)。具体有理点证明非空；后续主要结论对整个声明类成立。 |
| 概率确实来自源 | `S.noiseWeight_sum`、`S.noiseWeight_pos` | 36 个原子的权重由两个三值类别及两个损伤位生成；合法参数给正权和归一。仅有归一代数式不能替代非负性。 |
| 原强版的修订 | `S0_FREEZE.md`、两书核心总论及原稿修订表 | 普遍自创生、唯一自然边界、无条件进步、增长推出规范价值等不由本模块包证明。原全 Core 条件合同与 PR441—443 的完成状态保持。 |

S0 是来源和主张的冻结。最后一行属于书稿与声明状态审计，不伪装成一个 Lean 定理。

## 二、S1：物理程序、资源、真实后继与来源矩

### 2.1 同一实际程序与公共请求端口

| 已证内容 | 声明 |
|---|---|
| 多数恢复保留这两个程序的可解码内容 | `S.decode_programBody`、`S.restore_programBody`、`S.repairCost_programBody` |
| 程序确实读取恢复后的活动位 | `S.actual_program_reads_restored_code`、`S.rawExecute_restore`、`S.programStep_eq_step`、`S.program_step_executes` |
| 所称代码和门不是无效标签 | `S.active_code_is_causal`、`S.main_gate_is_causal` |
| 允许程序在原钱包中可支付 | `S.program_request_affordable`、`S.requestCap_program_care`、`S.requestCap_program_bloom`、`S.damaged_bloom_rejected` |
| 所有请求的实际账本 | `S.step_budget`、`S.outputCapital_le_two`、`S.stop_is_zero`、`S.rejection_retains_without_free_newborn` |
| 恢复原码的实际复制，而非裸给 faithfulness | `S.copied_code_faithful`、`S.copied_decode_faithful`、`S.executed_retained_faithful`、`S.executed_newborn_faithful` |

`programStep` 的运行项先检查预付上限，恢复后调用 `rawExecute`，再执行读到的动作。`programAction` 是其行为的数学描述，不是控制器读取隐藏 θ 的运行通道。

### 2.2 实际名单、身份、时钟与付款

| 已证内容 | 声明 |
|---|---|
| 续存保持旧身份、父指针、出生时刻 | `P.retained_identity` |
| 新生有实际父体、不同身份、出生时刻和年龄零 | `P.newborn_actual_parent`、`P.childIdentity_ne` |
| 在声明的合法身份时钟下，新生身份相对旧人口新鲜 | `P.childIdentity_fresh`、`P.valid_childIdentity`、`P.newborn_fresh_from_old_population` |
| 局部后继名单与付款相符 | `P.liftResult_length`、`P.actualStep_length_le_two`、`P.actualStep_budget` |
| 真实记录列表与反馈使用的计数是同一个对象 | `P.descendants_length` |
| 每条新增谱系边来自实际旧体 | `P.actual_edge_provenance` |
| 全部旧体逐一处理，输出等到下一次普查 | `P.descendants`、`C.generation`、`C.next` 的实际递归定义 |
| 整次普查使用每旧体唯一的一份六单位余额 | `C.generation_budget` |

身份新鲜性保留其 `ValidIdentity` 假设；不能把任意伪造初始身份列表也称为合法世界。期望计数定理可对更宽的列表成立，不会因此赋予非法身份列表物理解释。

### 2.3 从真实 retained/newborn 事件到 L、B、M

| 来源箭头 | 声明 |
|---|---|
| 原子上的 retained 与 newborn 分开计数 | `S.retainedCount`、`S.newbornCount`、`S.eventCount` |
| 实际输出 Body 的计数等于事件计数 | `S.executedResult_count` |
| 被接受继续事务的真实均值 | `S.retainedMean_eq`、`S.newbornMean_eq`、`S.eventMean_eq_row` |
| 全请求菜单，包括拒绝与 stop 的真正均值 | `S.step_resultCount`、`S.realizedMean_eq`、`S.program_realizedMean` |

令 \(\nu=(1-q,q)\)，继续动作给
\[
L_a(i,j)=s_a\nu_j,\quad B_a(i,j)=b_a\nu_j,\quad M_a(i,j)=(s_a+b_a)\nu_j.
\]
但 D/bloom 的实际事务为拒绝，其行是 \(e_D\)，不能用未经 cap 检查的 `eventMean` 替代。后续完整策略上界使用 `realizedRow`。

## 三、S2：付费再生、实际形成与不可恢复边界

### 3.1 原 repair rank 的实际源消费者

| 已证内容 | 声明 | 采用的原工具 |
|---|---|---|
| 修复读取真实 Body 与有限余额 | `S.paidRepair`、`S.paidRepair_start`、`S.paidRepair_start_account` | 本轮物理阶段定义 |
| 实际损坏体支付三单位，余额三单位可支付 care 与两个输出 | `S.paidRepair_damaged_costs_three`、`S.restored_remainder_funds_care_and_two_outputs` | 原钱包同一账本 |
| 该恢复阶段正是实际程序使用的阶段 | `S.paidRepair_body_is_source_restore`、`S.programStep_uses_paid_repair` | `S.programStep` |
| 两程序 H/D 源态有非空恢复域；健康 rank 0，损坏 rank 1 | `S.source_strongRepairable`、`S.healthy_repairRank_zero`、`S.damaged_repairRank_one` | `UEOT.V3.Compression.Objecthood.StrongRepairable`、`repairRank`、`repairRank_le_of_mem`、`repairRank_eq_zero_iff_mem` |
| 同一程序、损坏初态和六单位资源恢复后执行原诊断行 | `S.same_program_restores_then_reads` | 实际码读取与阶段账户 |

rank 的对象是**当前已获资源、尚未读取存活/出生噪声的恢复阶段**，不是全人口永存核。

### 3.2 形成由实际读取及未来响应产生

| 已证内容 | 声明 |
|---|---|
| 实际六码、门与 bootstrap 的完整物理读取识别声明初态 | `S.physicalReadout_full_injective` |
| 真实有限噪声通过 `programStep` 产生概率响应 | `S.sourceNoisePMF`、`S.sourceResponse_probability`、`S.sourceResponse_true` |
| 两个物理程序的真实新生未来不同 | `S.sourceResponse_nontrivial` |
| 零缺陷种子与真实部件 cover 均由源证明 | `S.full_physical_seed_zero_defect`、`S.physical_children_cover_seed` |
| 生成非空形成候选族 | `S.actual_formed_candidate_family_nonempty` |
| 空物理载体确实丢失未来信息；生成父候选不能为空 | `S.empty_physical_defect_pos`、`S.actual_formed_candidate_nonempty` |
| bootstrap 切断实际改变未来新生律 | `S.cut_bootstrap_programStep`、`S.cut_bootstrap_newbornResponse_true`、`S.bootstrap_cut_changes_future` |

直接消费的既有入口是
`UEOT.V3.Compression.CrossTrack.responseFormedCandidateFamily_nonempty_of_zeroDefectSeed`。
其中 seed、zero defect、cover 现在由同一源提供；没有输入 formed-parent 证书。

该形成消费者的 `SourceHistory` 是两个程序 × H/D 的四个真实初态，tag 固定为 false；响应是实际下一次新生事件。它不是对任意严重损坏 Body、所有未来实验或唯一自然对象边界的定理。

### 3.3 保留的失败和不可识别结论

| 边界 | 声明 |
|---|---|
| 切断 bootstrap 的损坏状态不能在该恢复核中自行恢复 | `S.bootstrap_cut_blocks_recovery`、`S.bootstrap_cut_not_repairable` |
| 固定余额不足且阶段内不加供给 | `S.underfunded_not_repairable`、`S.damaged_care_needs_full_supply` |
| 全擦除把不同原程序变成同一物理态 | `S.erased_programs_indistinguishable`、`S.erased_bloom_cannot_be_restored`、`S.no_decoder_recovers_both_erased` |

这些端点没有撤回有限可信基元，也没有声称所有执行路径与信息全毁后仍可恢复。

## 四、S3：机制生成排序、完整允许控制与真实谱系

### 4.1 一般有限行优化与实际可编译行

| 内容 | 声明 |
|---|---|
| 对同一选中矩阵调用旧 Perron 工厂 | `G.selectedPerron` |
| 有严格改进坐标时的谱根比较与单行替换 | `G.root_lt_of_subsolution`、`G.maximal_selector_row_bound` |
| 有限最大谱根选择器及 Bellman 上界 | `G.exists_optimal_selector`、`G.optimalSelector_row_bound`、`G.optimalSelector_row_isGreatest` |
| 任意实概率混合及可支配额外行 | `G.optimalSelector_mixed_row_bound`、`G.dominated_extra_row_bound` |
| 每个继续选择器由本源真实两行码实现 | `GS.selector_program`、`GS.selector_actual_raw_execution`、`GS.selector_same_wallet_affordable`、`GS.selectedMatrix_is_actual_program` |
| 本原性来自实际事件行的正性 | `GS.sourceRows_pos`、`GS.source_primitive` |
| 实际源存在有限最优者；显式 θ1 达到 | `GS.source_finite_optimizer_exists`、`GS.source_best_maximal`、`GS.source_best_bellman` |
| 可计算向量与旧工厂的同矩阵 Perron 向量同射线 | `GS.sourceValue_eigen`、`GS.sourceValue_actual_perron` |

旧工厂的完整入口是
`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PrimitivePerronClosure.certificateOfPrimitive`。
本轮先证明其本原性输入，没有把谱极限或成功控制作为工厂前提。一般 `G.optimalSelector` 是数学选择；实际运行达到者是物理编码 θ1，不宣称执行了 `Classical.choose`。

### 4.2 所有请求与同一实际人口历史

| 内容 | 声明 |
|---|---|
| stop 与拒绝均在完整请求上界中 | `GS.actual_row_bound`、`GS.actual_one_step_value_le`、`GS.actual_mixed_request_value_le` |
| 最优请求与真实内部程序达到一步等式 | `GS.actual_best_request_one_step_value_eq`、`GS.actual_program_one_step_value_eq` |
| 每个实际父体到整次人口的条件矩 | `C.member_expected_bound`、`C.member_expected_eq`、`C.generation_expected_bound`、`C.generation_expected_eq` |
| 允许历史行为核、请求先于世界噪声 | `C.Policy`、`C.branchWeight`、`C.branchWeight_nonneg`、`C.branchWeight_total` |
| 源事实满足通用有限历史定理的一步前提 | `C.next_expected_bound`、`C.next_expected_eq` |
| 有限条件核意义的非负超鞅与达到鞅 | `C.actual_supermartingale`、`C.actual_martingale` |
| 全历史允许策略的期望人口上界及最优双边界 | `C.actual_population_upper`、`C.actual_population_bounds`、`C.actual_growth_constants` |
| 同一遗传程序贯穿允许请求与可达状态 | `C.generation_program`、`C.reachable_program` |
| 外部最优请求等于真实 θ1 内部程序 | `C.best_step_is_programStep`、`C.attaining_generation_is_internal`、`C.bestPolicy_positive_branch_is_internal` |
| 一个真实损坏 θ1 创始体达到增长双边界 | `C.damaged_true_founder_growth` |

增长上界是期望人口的指数尺度。`C.actual_supermartingale` 和 `C.actual_martingale` 是每个有限历史节点的实际条件核陈述，没有在本消费者中另造共同无限路径空间的 Mathlib `Martingale` 实例。

### 4.3 原身份续存与增长不是同一目的

`S.healthy_retainedProbability` 从同一健康 Body 的真实 retained 记录得到 care 的 \(s\) 与 bloom 的 \(s-\delta\)。
`S.growth_choice_not_identity_survival_maximal` 因此给出同源、同初态、同钱包下的严格区别。这不是无限期谱系生存概率的排序。

`GS.rejection_subcritical_counterexample` 保留亚临界拒绝单位行可胜过继续增长潜势的反例；`source-prototype.json` 另保留冻结时的有理短反例。两个例子不得互换参数或数值。

### 4.4 由真实父指针导出的带标记谱系

| 内容 | 声明 |
|---|---|
| 旧 P8 身份/父子语义的实际实例 | `L.actualLineageSemantics`、`L.retained_is_same_object`、`L.newborn_is_strict_offspring` |
| 每次实际 retained/newborn 对 ancestry 追加相应标记 | `L.retained_markedPath`、`L.newborn_markedPath` |
| 递归值就是实际后继记录列表的加权和 | `L.pathValue_eq_actual_descendants`、`L.pathMean_eq_actual_descendants` |
| 同一噪声树及分开的 L/B 条件矩 | `L.pathMean_succ`、`L.noise_expected_retained`、`L.noise_expected_newborn`、`L.noise_expected_marked` |
| 实际后继路径的期望等于源生成的路径递推 | `L.pathMean_program_eq_lineageMass` |
| 本源证明旧正特征结构所需全部字段 | `L.actualRightEigenData` |
| 标记核正且总质量一；遗忘标记恰得旧 Doob | `L.markedKernel_pos`、`L.markedKernel_total`、`L.markedKernel_unmarked` |
| 实际有限 marked-path many-to-one | `L.actual_marked_many_to_one` |

最后的 F 读取实际 ancestry 的 retained/newborn 标记和目标身体类型；该端点针对共同达到者 θ1。它不是从人口均值递推直接猜祖先律，也不是普通活体均匀抽样或一个已获原动作实现证书的控制核。

## 五、S4：实际继承反馈与有限时域概率

### 5.1 通用有限概率引理由实际计数消费者履行前提

| 通用工具 | 本轮实际源履行处 |
|---|---|
| `Prob.product_expect_add`、`Prob.product_centeredSecond_of_means` | 实际 `F.NoiseTree`、`F.treeWeight` 和两个真实后继槽 |
| `Prob.centeredSecond_le_bound_sq` | `F.treeCount_le`、`F.cohort_count_bounds`、`F.cohort_variances_bounded` |
| `Prob.iid_expect_sum`、`Prob.iid_centeredSecond_sum` | 整个真实 cohort 的 `F.cohortWeight` 及 `Prob.iidWeight` |
| `Prob.iid_badRatio_mass_le` | `F.actual_cohort_feedback`，其所有均值、正性、归一、计数与矩条件均从源证明 |

这些通用引理保留显式概率和均值前提是正常的代数分层。最终源消费者不能再次把未证明的 hmean 当作输入：`F.treeMean_program_succ`、`F.cohortLower_mean`、`F.cohortTotal_mean`、`F.totalMean_pos` 等实际履行它们。

### 5.2 源端点

| 已证内容 | 声明 |
|---|---|
| 有限真实树概率与后继/工作量界 | `F.treeWeight_pos`、`F.treeWeight_total`、`F.treeCount_le`、`F.treeWork_le` |
| 真实逐代均值递推与闭式 | `F.treeMean_program_recurrence`、`F.treeMean_program_succ` |
| 本源两程序谱根严格排序及归一化均值集中 | `F.growthRate_order`、`F.lower_upper_ratio`、`F.lower_mean_share_tendsto_zero` |
| 真实比例的 Chebyshev 界，零人口明确计为失败 | `F.actual_cohort_feedback`、`F.actual_cohort_feedback_bounded` |
| 先选有限 T，再选独立且真实付费的 n 个 cohort | `F.exists_horizon_mean_share`、`F.actual_selection_failure_bound`、`F.exists_finite_cohort_selection` |
| 增加 cohort 的真实资源上界 | `F.cohort_resource_bound`、`F.actual_sample_resource_bound` |

这里的实际 cohort 是一健康 θ0 创始体加一健康 θ1 创始体。没有将其推广为新证的任意程序族、并列谱根的任意初始混合，或固定有限群体无限期必然选优。

### 5.3 同源的精确反例和数值见证

| 内容 | 声明 |
|---|---|
| 实际程序输出数量与事件数一致 | `S.programStep_total`、`S.actualCountProbability_eq` |
| care/bloom 的参数化 0、1、2 后继概率 | `S.care_count_zero`、`S.care_count_one`、`S.care_count_two`、`S.bloom_count_zero`、`S.bloom_count_one`、`S.bloom_count_two` |
| 健康 θ1 创始体立即完全灭绝的概率严格正 | `S.actual_best_extinction_pos` |
| 有理点的实际单体分布 | `S.concrete_care_count_law`、`S.concrete_bloom_count_law` |
| 两个实际独立创始体的九类计数推前 | `B.concrete_twoFounderMean` |
| 共同零人口 \(45/2048\) | `B.concrete_zero_population` |
| 高程序灭绝而低程序仍非零 \(243/2048\) | `B.concrete_best_extinct_inferior_nonzero` |
| 期望比例、条件非零比例与期望之比各不相同 | `B.concrete_expected_ratio_zero_extension`、`B.concrete_expected_ratio_given_nonzero`、`B.concrete_ratio_expected_counts`、`B.expected_ratio_ne_ratio_expected_counts` |

具体比例分别为 \(2095/4096,\ 2095/4006,\ 10/19\)。最佳健康创始体的单体灭绝概率为 \(9/64\)；不能把该数误套到共同见证的损坏初态，后者当次执行 care。

## 六、S5：合法表示与共同装配

### 6.1 已核实的局部和人口公共记录端点

| 已证内容 | 声明 |
|---|---|
| 删除静默标签保留观察、诊断、费用与请求 | `Q.observe_eraseTag`、`Q.diagnostic_eraseTag`、`Q.repairCost_eraseTag`、`Q.requestOf_eraseTag` |
| 同一个原子上的完整事务联合记录交换 | `Q.step_joint_record_commutes`、`Q.programStep_joint_record_commutes` |
| 商确实非单射且满射 | `Q.quotient_is_noninjective`、`Q.quotient_surjective` |
| 同一可观察历史行为核双向使用 | `Q.observed_history_descends`、`Q.history_kernel_two_way` |
| 完整投影收据的任意实值测试保持 | `Q.joint_law_test` |
| L、B、M 分别交换 | `Q.source_L_B_M_intertwining` |
| 抹标签保持实际身份、父指针、年龄、时戳和 ancestry | `C.eraseMember_keeps_identity` |
| 实际政策收据与整个人口观察保持 | `C.publicReceipt_eraseMember`、`C.population_observations_eraseMember` |
| 不能删掉真实权限/执行区别 | `Q.dropping_diagnostic_is_not_lawful`、`Q.code_only_prediction_loses_execution` |

`expanded` 的静默标签被忠实携带。因此完整标签展开矩阵有两个可约块，不能冒称其本原，也不能把商块的唯一 Perron 射线推广到整个展开矩阵。

### 6.2 完整有限历史的实际 State／Branch 运输

这些声明均位于当前 `CoreRegenerativeControlPopulation.lean`，不是计划中的同名接口。源中的实际状态包含人口、公开历史及合法身体不变量；每步分支包含同一请求字和同一原始噪声字。

| 已证内容 | 声明 | 保持的对象与量词 |
|---|---|---|
| 实际 retained/newborn 与完整名单交换 | `C.eraseMember_retained`、`C.eraseMember_newborn`、`C.liftResult_eraseMember`、`C.actualStep_eraseMember`、`C.generation_eraseMember` | 同一旧成员、动作和噪声；身份、父指针、执行年龄、出生时刻和 ancestry 保持。 |
| 公开收据与观察逐项保持 | `C.receipts_eraseMember`、`C.observations_eraseMember` | 包括实际费用、退款、所请求动作及分别标记的两个输出槽。 |
| 同一允许核在两表示间使用 | `C.policy_kernel_eraseMember` | 对全部 `Policy` 成立；不只保留一个最佳控制器。 |
| 状态投影与真实分支一一对应 | `C.eraseState`、`C.eraseState_idempotent`、`C.eraseBranchEquiv`、`C.eraseBranchEquiv_apply` | 分支只按人口长度相等重索引，不改变请求或世界噪声。 |
| 分支权和下一状态交换 | `C.branchWeight_eraseState`、`C.next_eraseState`、`C.next_expectation_eraseState` | 同一 `State`、`Branch`、`branchWeight`、`next` 的实际有限转移。 |
| 任意有限时域、任意终态审计测试的推前 | `C.populationExpectation_eraseState` | `F : State → ℝ`；左侧商初态执行 F，右侧原过程执行 `F ∘ eraseState`。若无合法概率条件，等式仅是实数加权代数式。 |
| 标签不变测试的值及全部可达值集合相同 | `C.protected_test_expectation_eq`、`C.attainable_test_values_eraseState` | 要求 `F (eraseState s) = F s`，比较完整相同的 `Policy` 集合。 |
| 人口计数、零人口、二阶等计数测试保持 | `C.census_test_expectation_eq`、`C.population_size_expectation_eq` | 任意有限时域、任意当前类型计数测试；概率解释使用同一合法源条件。 |
| 完整公开历史的任意测试保持 | `C.public_history_test_expectation_eq` | 允许历史中的请求、实际修复/操作费、退款和两个标记输出槽。 |

这条证明以完整局部联合记录为起点，逐步构造实际状态与法则的推前，不是从 $MH=H\bar M$ 单独推出全路径或方差结论。隐藏标签自身的数值不属于标签不变测试；删去 H/D、主门、费用或真实身份也不是这个合法商。

### 6.3 同一实际程序的共同消费者与正向量提升

| 共同结论 | 正式声明 | 来源身份与边界 |
|---|---|---|
| 同一损坏 θ1 创始体与六单位账本 | `T.commonFounder`、`T.common_founder_is_actual` | 人口是同一个 `founder index true true tag`；不是两份不同初态的证书拼接。 |
| 付费修复、恢复后真实读取与期望增长达到 | `T.same_program_regenerates_and_attains` | 对 `S.Valid p` 的开放类；恢复支付三单位、余额三单位、当次执行 care，任意有限普查的人口期望有正指数双边界。 |
| 正类实际非空 | `T.positive_source_class_nonempty` | 使用源码中的具体合法参数；一般主张并不限于该有理点。 |
| 静默标签展开的正生殖价值 | `T.liftedSourceValue`、`T.lifted_source_value_pos`、`T.expanded_source_eigen` | 从同一 `programRow p true` 和实际 `sourceValue` 提升；展开矩阵有两个忠实标签块，不主张本原、根简单或唯一正射线。 |

共同消费者的内部执行解释由 `C.best_step_is_programStep`、`C.attaining_generation_is_internal`、`C.reachable_program` 和 `C.bestPolicy_positive_branch_is_internal` 支撑。有限增长界不是无限存活或样本路径必然增长。

公共读者通过 `import UEOT` 获得这一主线。唯一新增生产导入边是 `UEOT.V3.Compression.TheoryCompletion → CoreTheoryClosure`；已有 `UEOT.V3` 与 `UEOT.V3.Compression` 是由 `UEOT` 分别导入的层级，不能把 `import UEOT.V3` 单独解释为导出整个 Compression 分支。最新依赖链构建与只用公共入口的消费者回执见 [VALIDATION.md](VALIDATION.md)。本索引只说明准确声明，不把静态存在冒称新编译。

## 七、原合同的直接复用与保留范围

| 原成果 | 本轮关系 | 不作的新声称 |
|---|---|---|
| `PrimitivePerronClosure.certificateOfPrimitive` 与旧 K-PF-01 / P-EVO-03 对象 | `G.selectedPerron` 直接调用；本源 `GS.source_primitive` 提供条件；`GS.sourceValue_actual_perron` 对齐同一正向量。 | 未重建 PF；未把多遗传程序或多静默标签的全矩阵当本原。 |
| `EndogenousRepairRank` 中 StrongRepairable / repairRank 工具 | `S` 的真实收费相位核、非空域、rank 0/1 与失败自环直接消费。 | 未将局部相位 rank 变成全人口无灭绝保证。 |
| `EndogenousCandidateFormation` 与 child-cover 有限最小化 | `S.actual_formed_candidate_family_nonempty` 直接消费，zero defect 与 cover 由真实响应证明。 | 未裸给 formed parent；未宣称唯一自然边界。 |
| `PositiveEigenstructure.RightEigenData`、`hTransform`、`hTransform_row_sum` | `L.actualRightEigenData`、`L.markedKernel_unmarked`、`L.markedKernel_total` 直接消费。 | 未把 Q 自动提升为允许控制或普通活体抽样。 |
| 旧 `LineageEvolution.LineageSemantics` / P8 区分 | `L.actualLineageSemantics` 实例化实际身份和父关系。 | L 的续存边不是严格 OffspringOf；M=L+B 的全部边不得都叫新生边。 |
| C1 / 完整历史预测 | 原 `C1ParametricBelief`、`MeasurablePredictiveHistoryCanonical` 等已闭合条件结果保持；本轮政策明确只读取允许观察和公开过去。 | 十三新模块没有新增 C1 实例或扩展标准 Borel、可数生成、记忆/fresh-future 的旧量词。 |
| C5 / 共同双驱动秩与规范 | 原 `C5DualDriveTest` 及相应条件结果保持。 | 本轮没有从两身体类型证明自然界存在共同二维驱动；兼容不是唯一识别。 |
| 原实际 Price 与固定 fitness 结果 | 原 `RegisterPopulationTypePrice.actual_program_type_price`、`EvolutionPrice.p_evo_01` 等来源结论保持。新 S4 从真实 treeCount 另证均值和有限 cohort 概率，不重复空 fitness 循环。 | 不声称十三新模块已另行实例化新 census Price；不以 Price 恒等式推出适应或必然选优。 |
| 已声明连续来源与旧全 Core 条件合同 | 保留现有完成状态、原假设和原验证身份。 | 不将本轮有限核论证改称新增一般 SDE、Itô/Girsanov 或无限路径构造。 |

保留的旧源码定位分别为 `ScientificClosure/C1ParametricBelief.lean`、`ScientificClosure/C5DualDriveTest.lean`、`UnifiedClosure/MeasurablePredictiveHistoryCanonical.lean` 和 `UnifiedClosure/RegisterPopulationTypePrice.lean`。旧入口的完整索引继续由原发布包承担；本文不制造同名替代接口。

## 八、S6 与 master 七项出口的证据连接

| master 第 12.1 节出口 | 本索引中的数学/来源证据 | 必须另核的交付事实 |
|---|---|---|
| 1. 保留主张有明确状态、原强版修订可见 | S0 声明类、原合同保留表和各边界 | 两书核心总论、独立哲学论证、原稿修订表；不能只看 Lean 成功。 |
| 2. 非退化真实再生，兼得须同见证 | S1、S2；`T.same_program_regenerates_and_attains` 与真实内部程序桥 | 最终依赖链、共同消费者与同一实际执行产物的身份核对。 |
| 3. 同源矩、允许策略增长和准确谱系 | S1.3、S3 全部源桥、条件核与 actual many-to-one | 原生记录绑定到该源码；不得把矩阵幂单独当父指针证明。 |
| 4. 实际含噪声继承反馈及边界 | S4 参数化源计数、真实比例界、独立 n-cohort 和精确灭绝例 | 独立精确检查及真实资源账本，不能以固定 fitness 输入替代来源。 |
| 5. 同源表示与防偷换反例 | S5 局部完整记录、完整 State/Branch 交换、任意有限期望与可达值集合 | 最新整体历史商与公共消费者的实际编译身份。 |
| 6. 公共入口、必要构建、公理、真实运行和两书相符 | 各正式模块和运行入口 | 实际编译日志、逐端点 `#print axioms`、manifest、原生导出、独立检查、两书构建与版面核验。不得以静态扫描称全仓重编译。 |
| 7. 发行/工作树/GI/唯一 CONTINUE 事实准确 | 无 Lean 定理能代替此出口 | root 以真实 HEAD、工作树、PR/发行身份、原 GI 实时 CURRENT 的 CAS、独立完整 recall 与唯一 CONTINUE 更新完成。本文不预写这些状态。 |

当前读到的独立执行回执 `native_source_check.json` 为 PASS：864 个公共端口原子、288 个内部程序原子、5508 个付款前缀，最低余额为零；身份、父指针、ancestry、两轮新生延迟和真实切断也在核对范围中。其精确 SHA、字节数和生产路径以最终 manifest 为准。`source-feedback-probe.json` 为独立有理数检查，不能代替参数化 Lean 证明。

经验支持始终是 **UNVERIFIED**。本索引不单独宣告七出口全部完成；实际结题状态、验证与发行身份分别见 [FINAL_ACCEPTANCE.md](FINAL_ACCEPTANCE.md)、[VALIDATION.md](VALIDATION.md) 和 [DELIVERY.json](DELIVERY.json)。
