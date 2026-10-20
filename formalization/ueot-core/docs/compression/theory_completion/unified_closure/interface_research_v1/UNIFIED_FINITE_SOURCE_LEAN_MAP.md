# 统一有限实例：逐箭头 Lean 来源与待补义务

## 范围

本表服务于 [数学草稿](UNIFIED_FINITE_SOURCE_EXAMPLE.md) 和 [哲学草稿](UNIFIED_FINITE_SOURCE_PHILOSOPHY.md)。只读审查依据为 Core 提交 3869d166a6bd7f6eda9ea7a9aa6878fb7a3b7a7b。本文没有增加生产模块、运行新 Lean 构建、改变既有声明的证明状态或修改出版候选。

“已有具体见证”指当前文件里确实存在该实例及命题；“已有通用接口”只说明它可在所列前提下调用；“新书面证明”没有专门的新 Lean 声明。只有类型相同不足以把三个状态混为一谈。

下文 UC 缩写为命名空间 UEOT.V3.Compression.TheoryCompletion.UnifiedClosure；SV 缩写为 UC.SupportViabilityClosure；RLSR 缩写为 UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction。

## 1. 唯一底座与允许的表示转换

固定 M = UC.conflictRewardControl.micro；风险层 P n x a = M.transitionPMF x a；注册观察 q(b,h)=b；初态 p₀=δ(1,0)。真实转移、奖励、策略、初态和事件在每条概率结论中都显式记录。

| 连接 | 来源身份 | 当前已经证明的部分 | 尚须补的部分 |
|---|---|---|---|
| survivalMicroKernel → M | M 由 exactControlFromStochasticQuotient 直接以此核构造 | 转移字段取该核的 mass；非零奖励闭合；discount=1/2 | 无须制造第二核；具体 PMF 行式通过既有转换定理写出 |
| M 实数质量 → 风险 PMF | P 明确定义为 M.transitionPMF | M.transitionPMF_apply_toReal 以及 S12 的支持/零质量桥 | 本例 1/2、0 数值与 map q=δa 的专门适配声明 |
| registeredSurvivalModel → 本稿注册模型 | 共享 survivalMicroKernel，但已有模型奖励为零 | 已有零奖励 P-ALG 稳定/终端见证 | 不能声称完整记录相同；明确增加奖励 1−a 的模型并证明划分仍为 q 的核 |
| conflictRewardControl 宏观态 → Bool | 原类型是 ReachableState q，q 满射 | 精确控制商与宏观最优提升的现成接口 | 明确该子类型与 Bool 的等价，证明相应行与奖励的运输 |
| Bellman 策略 → full-history PMF 策略 | 动作概率和 P 必须一致 | 前者有记忆/动作记录，后者有实际 PMF 递推 | 常值策略的具体表示转换与路径律适配尚未写成声明 |
| RLSR 执行段 → 原始受控源 | jointRepairKernel 用同一 M.transitionPMF | 恢复后的执行核正好是原 P 经 restoredJointState 的 pushforward | Bool 程序实例要补有效性；完整联合时钟另需停顿步和事件时间适配 |

## 2. 数学主线的逐箭头审查

| 箭头 | 精确结论或条件 | 当前源码依据 | 本稿状态 |
|---|---|---|---|
| 登记属性 → 两类终端分割 | 保护 b；不保护 h；现有零奖励模型初始已稳定 | S2：registered_survival_initial_stable、registered_survival_terminal_eq_initial、registered_survival_two_hidden_states_merge、registered_survival_visible_states_remain_distinct | 已有具体见证；加非零奖励后的 P-ALG 包装待补 |
| 同一核 → 精确控制商 | 对每个 x,a，q 推送行只依赖 q(x),a；奖励同样闭合 | S1：survivalRead_strongLumpable；S3：conflictRewardControl；S4：exactControlFromStochasticQuotient | 非零奖励商已存在；手写 δa 的具体 PMF 等式待补 |
| 同一核 → K 固定点 | K={b=true}，对每个 x∈K 存在原 P 的保全动作 | S3：conflict_region_is_actual_pmf_viability_fixed | 已有具体见证 |
| 固定点 → 可用安全动作 | viableSourceAction M K x 的蕴涵限制；K 外任意动作 | S5：exists_viable_source_action、viableRestrictedModel | 已有通用接口；本例“在 K 内恰为 true”待具体声明 |
| 同源安全动作 → 全因果受限最优 | 原奖励/转移限制在安全动作子类型；有限且非空动作；0<γ<1 | S5：viable_restricted_optimal_dominates_all_causal_policies；S6：safe_causal_history_optimality_and_path_invariance | 已有通用接口和本例保全见证；完整值 0/2 是新书面证明 |
| 可用安全动作 → 全时刻安全 | 初态支撑于 K；同一个保全策略及真实原核路径 | S6 的正概率历史归纳；CoreNonvacuousAllTimesWitness 有同一转移源的具体无限律 | 本稿显式 πkeep 的数学归纳成立；不冒充旧存在策略与新策略定义相同 |
| 源、初态、历史 → 真实后验支持 | 只对该策略真实 coarseLaw 中的正概率历史；相同 P,p₀,q | S7：traceSupport_eq_fiberTerminalPosterior_support | 已有通用定理；两位核的具体公式（10）、（11）待 Lean |
| 支持可行 → 同一策略零占据 | 所有非空初始纤维同时有限可行；完整 fallback 输入；所有 n<T | S7：initial_viability_iff_exists_zero_uncovered_policy、viablePolicy_zero_uncovered | 已有通用定理；本稿 πkeep 直接证明 cap=0，不借用选择所得策略的证明 |
| 实际策略 → 实际占据 θ | 每个真实前缀上 πθ(false)=θ；νₙ 由同一 P,p₀,q,πθ 生成 | S8：coverageDeploymentRowLaw、coverage_rowLaw_expectation、coverage_uncovered_indicator_expectation | 期望求和的新书面实例证明；非独立拟定占据律 |
| 实际策略 → 精确失败风险 | E_T 为第 1 至 T 步曾有 b=0；b₀=1；同一完整 πθ | S8 所用实际 causalLaw 框架 | 新书面证明 1−(1−θ)^T；15/64 尚无专门 Lean 数值端点 |
| 比较核与认证 → 风险上界 | Qkeep=δtrue；仅认证 true；行误差 ε=0；实际未覆盖 θ；参考风险 0；同一 πθ；真实 E=Φ⁻¹F | S8：coverage_same_policy_microscopic_failure_risk | 通用定理已有；实例得 min(1,Tθ)，2 步为 1/4 |
| 精确核与全行认证 → 实际正风险 | Qexact=δa；全行认证；ε=0、cap=0；参考风险自身为 1−(1−θ)^T | 同一个 S8 端点 | 新实例反例：cap=0 与真实风险 15/64 并存 |
| 原动作 true → 一步物理恢复 | 对每个 x，supp P(x,true)=K；比只在 K 内保全更强 | S1、S3 的源公式；S12 支持接口 | 新书面具体推导；不推出 K 外受限 Bellman 必定修复 |
| 有效修复程序 → 同源安全动作 | T、程序 r、RepairProgramValid T P K r 显式给出 | S11：recoveredProgramSourceSafeAction、reconstructed_program_preserves_source_viability | 通用桥已证明；Program=Bool、execute(c,x)=c、r=true 的实例待补 |
| 单副本损坏 → 重构 → 同源执行 | 同一 P；三副本的指定故障形态；restore 先于 execute；可信解释器 | S10：jointRepairKernel_singleReplica_restore、jointRepairKernel_restored、jointRepairKernel_staysIn_recoveredTarget | 通用有序机制已证明；本例两组织步恢复的完整实例待补 |
| 组织恢复时钟 → 全历史风险 | restore 步不动 x；execute 步才执行 P | S10 明确区分两个模式 | 尚未连接；不能将一次 restore 当一次原 P 执行或直接复用式（16）的 T |

## 3. 需要保留的量词与同一性

### 3.1 支持递推与策略概率不同

SV.traceSupport 由 p₀、P、q 和记录的动作/观察递推，不输入 π。它可以在某个策略概率为零的动作历史上非空。

对任意 θ∈[0,1]、任意 n、任意 g，只有 g 属于该 πθ 的真实 coarseLaw 支持时，才调用后验支持等式。θ=0 时历史 (1,0,0) 的递推支持非空，实际概率却为零；这是本例中保留该条件的直接理由。

### 3.2 两类“允许”不能全状态混同

在 K 内，安全动作子类型只允许 true，恰与 C(n,x,a)⇔a=true 相符。在 K 外，现行安全动作子类型允许任意动作，而 C 仍只认证 true。统一论证须通过实际可达支持上的相符或直接检查，不得声称这两个谓词全局相等。

### 3.3 采用具体策略，或采用存在性所得策略

πkeep 明确在全部历史上给 true 质量 1。SV.viablePolicy 由有限可行性和 fallback 构造；它在实际所需范围内有零占据，但没有现成定理说它在一切历史上等于 πkeep。

本稿的风险与占据计算都直接定义并使用 πθ。θ=0 时再直接得到 πkeep 的零占据；不需要策略全局相等假设，也没有把另一个好策略的 hcap 用于 θ>0。

### 3.4 两个参考不能拼接证明

第一次参考的零事件风险对应 Qkeep；其认证谓词只保护 true，真实 cap=θ。

第二次参考的零 cap 对应 Qexact 与全行认证；其事件风险是 1−(1−θ)^T。

真实实验虽然一样，两个参考证明包中的 Q、认证和参考事件概率不同。不能从前者抽“参考风险零”，再从后者抽“cap 零”，得到错误的真实风险零。

### 3.5 程序有效、安全最优、主动恢复各有命题

RepairProgramValid 的核心是：从 K 内执行该程序会留在 K。它不是最优性证明，也不独自要求 K 外最终恢复。新增 Program 及三副本存储属于联合状态；它们不等于原微观状态中的隐藏位 h，后者仍按原 P 更新。

本稿程序 true 从任意状态一步进入 K，是源公式另行给出的更强实例事实。从 K 内，它也是这里的唯一安全动作，故恰好达到本例受限最优值；从 K 外，它却不是现行受限奖励问题的最优策略。任何“恢复程序最优”的陈述必须带上状态域和评价。

## 4. 可直接形式化的最小命题包

下列是拟议数学命题，名称只是研究占位；不是已添加声明。

| 顺序 | 建议命题 | 完整数学范围 | 证明路线 |
|---|---|---|---|
| 1 | 同源 PMF 与可见推送 | ∀ n x a，Pₙ(x,a) 由 M.transitionPMF 定义，质量为式（1），map q=δa | M 的字段展开、transitionPMF_apply_toReal、有限 Bool 求和 |
| 2 | 显式策略的未认证占据 | ∀ θ∈[0,1]，∀ n，coverageDeploymentRowLaw(p₀,q,P,πθ,n)(Cᶜ)=θ | 实际 rowLaw 期望展开，πθ 常值，真实前缀质量归一 |
| 3 | 全时域精确失败公式 | ∀ θ∈[0,1]，∀ T∈ℕ，actualLaw(E_T)=1−(1−θ)^T | 用真实 causalLaw 递推“全程动作 true”事件，不另给独立实验 |
| 4 | 同源两个参考的比较 | 同一 θ、T、P、p₀、q、πθ、E_T；分别明示 Q 与 C | 证明投影事件相等、两种行 TV、参考事件概率，调用现成 coverage 端点 |
| 5 | 两步具体正风险见证 | θ=1/8、T=2，实际 15/64≤1/4；全行认证后 cap=0 且实际 15/64>0 | 第 2–4 项专门化并作有理数计算 |
| 6 | 非零奖励受限/无约束值 | ∀ x，无约束 2；受限值在 K 为 0、K 外为 2 | 具体 Bellman 固定点或回报上界与达到策略 |
| 后续 | 非零奖励注册分割、Bool 修复程序 | 每一附加结构由原 P 明确定义；各自具体来源条件 | 复用现有稳定分割与 RLSR 通用定理，补实例证明 |

第 1–5 项最直接地把旧同源控制见证接上本轮支持/风险接口，且有一个明确区分模型认证与运行安全的真实正风险结果。第 6 项可补强同源目标比较。不得只把这些结论写为新假设后宣称桥接完成。

## 5. 与整体统一研究的关系

本例可具体展示商的降落与误差沿同一过程的传输，因而能帮助读者理解 M-QD、M-TC 的作用。它没有实例化 M-OI 的长期占据结论或 M-PE 的正特征归一化。

在 H0 的阅读框架里，它主要涉及预测/动态描述和价值控制。所用“概率历史”是风险事件与后验的载体；这本身不构成历史个体同一的 HIST 端点。程序修复带来了一个已有机制接口，也不自动补齐所有对象形成、资源、繁殖或目的来源的桥。

因此，此例是成熟 Core 结果之间的一段真实连接，而不是新的全部推导链。冻结 106 P-ID 的 11 generated / 89 adapters / 6 boundaries 分类没有因本稿而改变；生产 659 个模块的计数也没有变化。若以后新增实例适配，应按其真实作用登记，不能把实例的可读性当作额外生成端点的证据。

## 6. 不得借用的其他实例

| 看起来相近的材料 | 与本稿不同之处 | 正确使用方式 |
|---|---|---|
| 现行数学 §35.4 | 等待时以 3/4 保持，奖励 s−a；值 8/5 | 作为另一个书面模型；不可把 8/5 带入本稿的 M |
| ActiveHiddenOptimalControl 的隐藏状态例 | 3/4–1/4 响应或隐藏位保持等结构不同 | 用于它自己的主动信息/控制问题，不接本稿的精确路径概率 |
| RegisteredDeploymentRiskWitness | 两个真实注册行、训练后选择、实际联合风险 9/64 | 保留其独立实验；本稿 15/64 不继承其训练校准和 Good |
| 严格后验支持缩小的见证 | 需要历史真正改变可行动作集合的另一源 | 本稿只展示初始支持与纤维不同、正概率条件和显式支持公式 |
| 认证前缀死路见证 | 某些认证前缀到达不可延拓支持 | 本稿每个状态均可 true 恢复，不能冒充这一反例 |
| RLSR 已有有限数值基准 | 联合状态、故障模型与概率实验有其自己的参数 | 只复用一般机制定理；先明示本稿实例，再产生自己的数值 |

## 7. 直接读取的源码索引

下面链接指向本轮实际只读源。所有“现有定理”的名字均出自这些文件；一般数学计算仍需按上表补具体实例。

| 编号 | 文件 | 关键声明 |
|---|---|---|
| S1 | [ViabilityNonvacuityWitness.lean](../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/ViabilityNonvacuityWitness.lean) | UC.survivalMicroKernel；survivalRead_strongLumpable；survivalExactControl；survival_true_nonempty_all_horizons |
| S2 | [OrganizationalSufficiencyWitness.lean](../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/OrganizationalSufficiencyWitness.lean) | UC.registeredSurvivalModel；registered_survival_terminal_eq_initial；hiddenProgramProtectedModel；protected_hidden_program_prevents_merge |
| S3 | [SafeRewardConflictWitness.lean](../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/SafeRewardConflictWitness.lean) | UC.conflictRewardControl；conflict_same_source_reward_and_risk；conflict_region_is_actual_pmf_viability_fixed；conflict_nonzero_reward_safe_bellman_preserves |
| S4 | [PredictiveOptimalControlLift.lean](../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/PredictiveOptimalControlLift.lean) | UC.exactControlFromStochasticQuotient |
| S5 | [SafeOptimalControlFromViability.lean](../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/SafeOptimalControlFromViability.lean) | UC.viableSourceAction；exists_viable_source_action；viableRestrictedModel；viable_restricted_optimal_dominates_all_causal_policies |
| S6 | [SafeCausalHistoryTransport.lean](../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/SafeCausalHistoryTransport.lean)；[CoreNonvacuousAllTimesWitness.lean](../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreNonvacuousAllTimesWitness.lean) | UC.all_positive_causal_histories_preserve_viability；safe_causal_history_optimality_and_path_invariance；registered_survival_nonempty_infinite_law |
| S7 | [FiniteSupportViability.lean](../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteSupportViability.lean) | SV.traceSupport；traceSupport_eq_fiberTerminalPosterior_support；zero_uncovered_iff_support_certified；viablePolicy_zero_uncovered；initial_viability_iff_exists_zero_uncovered_policy |
| S8 | [DeploymentCoverage.lean](../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/DeploymentCoverage.lean) | UC.coverageDeploymentRowLaw；coverage_rowLaw_expectation；coverage_uncovered_indicator_expectation；coverage_same_policy_microscopic_failure_risk |
| S9 | [TrustedSubstrate.lean](../../../../../UEOT/V3/Compression/Objecthood/RepairLawSelfReconstruction/TrustedSubstrate.lean)；[ProgramSemantics.lean](../../../../../UEOT/V3/Compression/Objecthood/RepairLawSelfReconstruction/ProgramSemantics.lean) | RLSR.TrustedRepairSubstrate；RepairProgramValid |
| S10 | [JointRecovery.lean](../../../../../UEOT/V3/Compression/Objecthood/RepairLawSelfReconstruction/JointRecovery.lean) | RLSR.jointRepairKernel；jointRepairKernel_singleReplica_restore；jointRepairKernel_restored；jointRepairKernel_staysIn_recoveredTarget；jointRecoveryBasin_recovers |
| S11 | [RepairProgramSafeControlBridge.lean](../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RepairProgramSafeControlBridge.lean) | UC.recoveredProgramSourceSafeAction；reconstructed_program_source_kernel_agrees_with_safe_action；reconstructed_program_preserves_source_viability；reconstructed_program_joint_and_source_safety |
| S12 | [CorePMFViabilityReconciliation.lean](../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CorePMFViabilityReconciliation.lean) | UC.frozen_pmf_staysIn_iff_real_zero_outside；macro_viability_iff_frozen_pmf_iteration；micro_viability_equals_frozen_history_strategy_winning_set |

## 8. 本次交付的实际状态

三个研究文件已写入指定临时目录；没有改动候选、源码或原始附件。新增数学结果的依据是上文完整的有限书面证明，当前没有新 Lean 编译收据。现有源码事实按具体定义和 theorem 类型逐项核对；既有全书版面验证、Core 构建及独立审查继续保留原来的身份，不因本稿而获得新的覆盖范围。
