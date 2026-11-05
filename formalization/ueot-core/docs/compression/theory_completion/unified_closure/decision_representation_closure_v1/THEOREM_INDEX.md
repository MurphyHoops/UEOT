# 决策充分表示与紧凑策略：定理和依赖索引

本索引按任务书六项验收的 **1–4 项**组织本轮 **13 个新增 Lean 模块**。声明名、直接 import 和 SHA 均取自本次实际源码；完整限定名、全部公开 theorem 名称、关键声明及依赖边见同目录 `representation_theorem_index.json`。本索引没有新增证明、运行或验收结论；第 5 项实际运行和第 6 项发行/GI 由各自回执承担。

所有下文 `模块.声明` 的完整命名空间前缀是 `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.`。代码位于仓库相对目录 `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/`。

## 先看最终消费者接口

公开返回入口是 `RegisterDecisionRepresentation.returned`，类型为 `Option (Result P prior hn ht initial H)`。`Result.control` 含同一实际图、有效根、`Good`、根状态和期限绑定；`Result.bounds` 含该同一数组的 `boundCheck H = true`。

| 要调用的结论 | 实际公共声明 | 准确范围 |
|---|---|---|
| THIS 返回图的真实期望 J | `RegisterDecisionRepresentation.result_native_value` | 初始损坏 founder、一次抽取 θ 的有限先验、原生完整记录；报告值等于实际 J。 |
| 全历史实随机竞争者上界 | `RegisterDecisionRepresentation.result_native_optimal` | 原 belief 模型上的 `RawCausalPolicy`，初始信息与钱包绑定，且满足 `SupportedAdmissible`；不是只比较摘要策略。 |
| 每个实际前缀预付与费用账本 | `RegisterDecisionRepresentationPayment.initial_graph_native_payment` | 对所返回 graph/root 直接实例化；任何正先验 θ 与正 primitive tape 都满足逐前缀约束。该定理甚至不要求图最优。 |
| 返回数组的节点数界 | `RegisterDecisionRepresentation.result_node_bound` | 整个实际数组，包括为替代动作提供上界的节点，大小不超过 `24*(H+1)^4`。 |

**认证边界是 accepted candidate。** `certify`/`accept` 接受任意候选时给出该对象的证明，`none` 不携带最优性结论。没有声明或证明通用 `generate` 对任意输入必通过认证。原观察枚举只控制候选构造；检查器独立覆盖原 `Fintype O` 的全部正概率分支。13 个具体实例的实际接受属于运行回执，不能替代一个不存在的全域接受定理。

## 出口 1：许可历史产生可执行表示

### 1. `RegisterDecisionObserver`

文件：`formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterDecisionObserver.lean`

可执行声明为 `Local`、`Stat`、`initialStat`、`update`、`updateStat`、`summarizeFrom`、`summarize`。输入只有公开 goal、既有摘要、自身请求和交付收据。它们不调用世界投影。

- `first_append_decides_child`、`missing_child_stays_missing`：区分首 tick 分配 child1 与之后永久的 None；不是由尾部新增槽重新填补旧地址。
- `update_stopped`、`update_fresh`：公开 stopped 和首次分配相位的准确更新。
- `informative_selected`、`uninformative_receipt`、`uninformative_increments`、`informative_receipt_identifies_mode`：刻画哪些收据真正识别 mode；损坏槽 idle 与 None 请求的零收据不记一次故障。
- `likelihood_counts`：原两 mode 边际似然等于兼容性指示乘 `r^Δs*(1-r)^Δf`，保留端点及 `0^0=1`；`likelihood_nonneg`、`likelihood_total` 给出核的合法性。

### 2. `RegisterDecisionObserverSource`

文件：`formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterDecisionObserverSource.lean`

`Rooted`、`projectLocal`、`projectNative` 是证明侧定义，不是控制器传感器。实际源的连接由以下定理承担：

- `observe_project`、`update_project`：逐 primitive 的许可观察和观察器更新与原 packed 源相容，覆盖每个请求、mode 和隐藏 label；`rooted_step` 保持 root 存在。
- `initial_project`、`initial_rooted`：实际初始损坏 founder 满足连接前提。
- `primitive_likelihood`：对原四分支 primitive 求和得到观察器似然；`primitive_joint` 保持收据与下一 Local 的任意有理联合测试，不只保持均值。
- `native_observe`、`native_update`、`native_rooted_step`：经已有原生 Store 桥得到原交易上的同一结论；假设为原生程序对齐与 root 存在。
- `packed_summary`：任意有限自适应 Table、任意实际噪声词下，仅折叠执行 history 就重建最终 Local。

### 3. `RegisterDecisionCountPosterior`

文件：`formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterDecisionCountPosterior.lean`

可计算的 `countWeight`、`normalizer`、`posteriorWeight`、`observationMass`、`countBelief` 给出有限 θ 上的计数过滤。零分母使用原先验作为总函数默认值。

- `posterior_nonneg`、`posterior_total`、`posterior_zero_zero`、`prior_zero_remains_zero`：归一化、初态和零先验边界。
- `countWeight_update`、`normalizer_update`、`observationMass_ratio`：一次许可收据的精确似然更新。
- `positive_update`：从旧分母正与实际收据质量正推出兼容性及新分母严格正，不要求所有先验正或 `0<r<1`。
- `posterior_update`、`posterior_joint_identity`、`posterior_test_identity`：支持上 Bayes 更新及任意 θ 测试函数的联合恒等式。

### 4. `RegisterDecisionCountHistory`

文件：`formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterDecisionCountHistory.lean`

这是 **raw、实数随机、可用完整许可历史记忆** 的后验入口，不把新摘要策略类作为假设。

- `worldLikelihood_eq_local`、`initial_likelihood_counts`：把原 primitive 的完整历史似然接到 observer 计数。
- `rawWorldLikelihood_factor`：对任意 `RawCausalPolicy`、固定初始 policy memory 和同一动作/收据历史，真实源历史权重分解为共同 `actionFactor` 乘固定 θ 的源似然。policy 不接收世界或 θ。
- `rawPriorMass_eq`：先验混合质量等于共同动作因子乘计数 normalizer。
- `positive_history`：实际历史质量正推出兼容、动作因子正及计数分母正。
- `conditional_count_posterior`：任意上述实随机历史核的实际条件 θ 分布，逐 θ 等于 `posteriorWeight`；动作随机化因子被消去，没有重抽 θ 或增加隐藏样本。

这里的代数后验定理不需要额外的可行动作限制；最终优化比较类再由原 `SupportedAdmissible` 施加实际支持前缀的合法性。

## 出口 2：表示保持完整决策语义

### 5. `FiniteJointDecisionRefinement`

文件：`formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteJointDecisionRefinement.lean`

`StepRefinement` 是对既有有限模型定理的薄适配：同 actions/prob/reward/discount，仅在正概率后继要求关系继续成立。它自身的前提不是源充分性证明；下一模块从实际源构造其具体实例。

- `supported_feasible_transfer`：按支持可行性在同一有限 Table 上迁移。
- `value_transfer`：任意支持可行自适应 Table 的完整有限值相等。
- `tapeWeight_transfer`：任意该类 Table 和完整有限收据 tape 的质量相等。这个声明的参数是 Table，不是 RawCausalPolicy；raw 实随机比较类由出口 1 和出口 3 的明确接口接入。
- `optimalValue_transfer`：全部合法动作的有限最优值相等；每个合法替代动作都进入归纳。

### 6. `RegisterDecisionRepresentationModel`

文件：`formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterDecisionRepresentationModel.lean`

`model` 的状态为 Stat；`wallet` 为 `max 0 (B₀-k*c)`；actions 直接使用原 `menu`，保持原请求 cap，不能因 stopped 而降低写请求预付门槛。`BeliefMatches` 和 `Rel` 仅是证明侧关系。

- `joint_theta`、`mass_eq`：从原 belief/primitive 得到 θ 与收据联合律及精确收据核。
- `belief_next`、`rel_next`：在正收据支持上传播世界侧关系、实际计数后验和正分母；`wallet_next` 对总函数离轨分支也成立。
- `refinement`：实际构造前述 `StepRefinement`，全部字段由源定理、相同原菜单和钱包更新证明。
- `initial_relation`：对登记初态直接证明 Rel，消除“把摘要充分性设为输入”的风险。
- `joint_observable_law`：对任意联合测试 `Obs → Stat → ℚ → ℚ → ℚ → ℚ`，保持收据、下一摘要、出生、实际收费和更新余额的联合分布。支持上余额等于字面扣账另由 Payment 定理保证。
- `optimalValue_initial`：任意有限 H、登记先验和钱包下，原 belief 模型与摘要模型的全动作 optimum 相等。
- `feasible_transfer_wallet`：仅凭公开余额对应，把摘要 Table 的全局合法性迁移到旧模型，包含零质量分支；它供原支付桥使用。

## 出口 3：共享紧凑返回、原生执行和全比较类最优性

### 7. `FiniteJointDecisionDAG`

文件：`formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteJointDecisionDAG.lean`

`Node`、`Graph`、`EdgeValid`、`NodeValid`、`Good`、`check` 定义实际数组及精确证书。`NodeValid` 同时检查全部合法动作和每个严格正概率收据；`EdgeValid` 检查真实后继状态、有效索引及 remaining 少 1。`Good` 还要求实际数组键唯一。

- `check_sound`、`good_of_check`：可执行 Bool 检查与 Good 的证明连接。
- `score_eq_qValue`、`node_value_eq_optimal`：认证图的每一个节点值等于原有限求解器 optimum，包括仅供替代动作上界使用的节点。
- `node_choice_eq_chosen`：非终端认证行保持原动作顺序与最先平局选择。
- `controllerAction_mem`：任意图、摘要、时刻和游标的直接请求均在当前合法菜单中；`denote_feasible` 将这一全局安全性递推到所有分支。
- `denote_value_eq_node`、`denote_optimal`：被选边的策略达到同一节点的认证值。`denote` 仅用于证明解释，不在生成、直接执行或序列化入口求值。
- `rawValue_le_node`：摘要模型上的任意支持合法 raw 实随机策略不超过节点值。原完整 belief/原生竞争者的范围由下述 `checked_native_optimal` 继续保证，不能只引用本条就声称已完成原生比较。

### 8. `FiniteJointDecisionDAGGenerator`

文件：`formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteJointDecisionDAGGenerator.lean`

`build`、`generate` 以 `(remaining,state)` 为 memo 键，共享数组索引；`edgeLookup` 只保存已完成的有限边表。`generate` 每次从 `emptyState` 开始。`Candidate` 是无信任候选；`Certified` 绑定 M、H、initial、实际图和根。

- `certify`、`plan`：执行检查并显式返回 Option；不接受错误根或缺失正概率替代边。
- `certified_value`：任意 Certified 的根报告值等于 `optimalValue M H initial`。
- `certified_policy_value`、`certified_policy_feasible`：同图控制策略达到该值且全局合法。
- `certified_randomized_upper`：任意支持合法的 raw 实随机策略受同根值约束。

这些定理量化 **Certified**，没有通用 `generate_always_accepts`、`plan_ne_none` 或等价声明。公共返回接口不隐藏这个边界。

### 9. `RegisterDecisionRepresentationNative`

文件：`formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterDecisionRepresentationNative.lean`

`packedRun` 是可执行的逐节点解释器。`nativeRun` 在原完整 Store/ClockedRecord 类型上给出同一逐节点语义；它因继承原实数原生接口而声明为 noncomputable，不能把它称作另一个已编译运行的原生程序。实际 driver 使用 `packedRun`；以下定理连接完整原生世界。

- `packedRun_eq`、`nativeRun_eq`：直接游标解释器与旧解释器作用于证明用 denote 的完整执行相等；不是只比较期望。
- `nativeRun_project`：原生执行的允许投影等于直接 packedRun，原生记录继续保存身份、程序、谱系、时钟和 None。
- `sourceTapeWeight_eq`：原政策依赖形式的 source tape 权重等于固定 θ 全程不变的 `primitiveTapeWeight`。
- `nativeGraphJ_eq`、`expectedGraphJ_eq`：同图实际 native J 接回已有 source/value 接口。
- `checked_native_value`：给定 Good、根期限和已证 Rel，真实 `expectedGraphJ` 等于该根行的报告值。
- `checked_native_optimal`：对原 `RegisterJointDecisionConsumer.model` 上任意 `RawCausalPolicy` 及 `SupportedAdmissible`，真实 `expectedRawNativeJ` 不超过该图。复用旧原生全历史定理，经源 refinement 转移到图的值。
- `initial_checked_native_value`：登记损坏 founder、原有限先验一次 θ 初始化，直接得到实际根值等式。
- `nativeRun_population`：任意噪声词，记录与历史长度均为 H，原生 Store 长度增 H；包括 stop 后 tick 与 None append。

### 10. `RegisterDecisionRepresentationPayment`

文件：`formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterDecisionRepresentationPayment.lean`

- `GraphPrepaid` 在结果发生前检查原请求 cap，随后扣实际 `nativeFee`；`graphPrepaid_eq` 接回原 NativePrepaid。
- `packed_summary_wallet`、`native_summary_wallet`：任意前缀自身请求/收据摘要给出的余额，与旧过滤器的公开余额相同。
- `graph_native_payment`：不要求 Good 的直接图控制器，在实际正先验原子和正 primitive 路径上逐前缀预付；累计真实费用非负且不超过初始余额，摘要余额等于初始余额减真实费用。
- `initial_graph_native_payment`：把上述结论直接实例化到登记损坏 founder；其图参数可取 `result.control.graph`、游标取认证根。

这里不存在另一个名为 `result_native_payment` 的新包装定理；实际公共支付入口就是上列声明。

### 11. `RegisterDecisionRepresentation`

文件：`formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterDecisionRepresentation.lean`

`Result`、`accept`、`returned` 汇总认证、根绑定和源节点界。三个公共结论为 `result_native_value`、`result_native_optimal`、`result_node_bound`，准确范围见本索引首表。它还 import CountHistory、Payment、Witnesses，使历史后验、支付及边界接口可从同一入口取得。

## 出口 4：实际节点界与必要正反见证

### 12. `RegisterDecisionRepresentationBounds`

文件：`formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterDecisionRepresentationBounds.lean`

- `initial_count_bound`、`update_count_bound`、`summarize_count_bound`：由观察器证明 `s+f≤elapsed`、`paidCount≤elapsed`；`summarize_elapsed` 证明 elapsed 为历史长度。
- `initial_in_horizon`、`update_in_horizon`、`history_in_horizon`：保持 `remaining+elapsed=H`，避免把 remaining 误作第五个独立坐标。
- `local_card`：Local 的保守基数为 24；`code_card`、`encode_injective` 把实际键编码到四个 `Fin(H+1)` 与 Local。
- `boundCheck_sound`：对实际数组每一行执行的 Bool 检查给出域约束。
- `actual_graph_node_bound`：由 **实际行键单射** 和 **同数组 boundCheck=true** 得到 `G.size≤24*(H+1)^4`；`result_node_bound` 自动供应这两个前提。

该界是数组节点数界，覆盖证明图而非只选中执行子图；不宣称表示最小，也不宣称有理数位长、总内存、生成时间或认证时间有相同界。

### 13. `RegisterDecisionRepresentationWitnesses`

文件：`formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterDecisionRepresentationWitnesses.lean`

- `insufficient_histories_actual`、`insufficient_same_time_wallet_body`、`insufficient_likelihoods`、`insufficient_joint_next_birth`：同源、同时间、同钱包和当前体态的两条实际历史，信息计数仍可不同。
- `body_wallet_time_is_insufficient`：两历史质量分别 `3/32`、`3/16`，低 r 后验分别 `1/4`、`1/2`，下一 child1 idle 出生率分别 `5/8`、`1/2`。这否定仅保留体态/钱包/时间的过度压缩。
- `native_history_integral_eq`：反例似然和未来出生积分确实来自原生 Store 的实际收据，不是另造核。
- `merge_histories_actual`、`merge_same_complete_summary`、`merge_both_positive_same_posterior`：两条不同原菜单历史真实可达，完整摘要及后验相同。
- `merge_different_actual_tails`、`native_merge_keeps_distinct_records`：两世界的尾部 None/个体排列和具体原生 identity 记录不同，摘要合并不重造身份。
- `merge_old_menu_receipt`、`merge_old_menu_joint_summary`：原每个动作逐噪声具有相同下一许可收据及摘要；未来有限决策语义再由源充分性和 refinement 接续。
- `dispatch2_breaks_merge`、`dispatch2_birth_laws`、`native_dispatch2_boundary`：只在单列扩权协议中允许地址 2 时，原两可达世界的出生率变成 0 与 r；主求解菜单没有增加地址 2。

## 直接模块依赖

表内短名均位于上述统一命名空间。标“旧”的模块是 PR441 基线复用，未算入 13 个新增模块；精确 repo path 和 full import 名在 JSON 中逐项列出。

| 新模块 | 源码直接 import |
|---|---|
| RegisterDecisionObserver | 旧 RegisterJointDecisionSource |
| RegisterDecisionObserverSource | RegisterDecisionObserver；旧 RegisterJointDecisionExecution |
| RegisterDecisionCountPosterior | RegisterDecisionObserver；旧 FiniteJointDecisionBelief |
| RegisterDecisionCountHistory | RegisterDecisionCountPosterior；RegisterDecisionObserverSource；旧 FiniteJointDecisionSupportedPolicy |
| FiniteJointDecisionRefinement | 旧 FiniteJointDecisionSupportedPolicy |
| RegisterDecisionRepresentationModel | RegisterDecisionObserverSource；RegisterDecisionCountPosterior；旧 RegisterJointDecisionConsumer；FiniteJointDecisionRefinement |
| FiniteJointDecisionDAG | 旧 FiniteJointDecisionSupportedPolicy |
| FiniteJointDecisionDAGGenerator | FiniteJointDecisionDAG |
| RegisterDecisionRepresentationNative | RegisterDecisionRepresentationModel；FiniteJointDecisionDAG；旧 RegisterJointDecisionNativeConsumer |
| RegisterDecisionRepresentationPayment | RegisterDecisionRepresentationNative |
| RegisterDecisionRepresentationBounds | RegisterDecisionObserver；FiniteJointDecisionDAG |
| RegisterDecisionRepresentationWitnesses | RegisterDecisionObserver；旧 RegisterJointDecisionNativeLaw |
| RegisterDecisionRepresentation | RegisterDecisionCountHistory；RegisterDecisionRepresentationPayment；RegisterDecisionRepresentationBounds；RegisterDecisionRepresentationWitnesses；FiniteJointDecisionDAGGenerator |

关键依赖链应按以下方式读取：

1. 原 primitive → `observe_project/update_project/primitive_likelihood` → 真实历史似然与计数等式 → `rawWorldLikelihood_factor` 的共同动作因子消去 → `conditional_count_posterior`。
2. `joint_theta/mass_eq`、`belief_next/rel_next`、`wallet_next` → 具体 `refinement` 和 `initial_relation` → 任意 Table 的完整 receipt tape 法则及全动作最优值迁移。
3. 全动作 `NodeValid` + 实际键唯一 → `check_sound` → `node_value_eq_optimal` → `certified_value`；直接控制器达到同值后，经 refinement 和旧原生桥得到 `checked_native_value/checked_native_optimal`。
4. 直接控制器的全局菜单合法性 + `feasible_transfer_wallet` → 原生逐前缀预付/真实费用结论；它不以最优性为资金前提。
5. 实际键唯一 + 每行 InHorizon → `actual_graph_node_bound`；固定源的历史反例和原生身份见证限定该表示在原权限内的适用范围。

## 实际返回制品的入口路径

driver 的仓库相对路径为 `formalization/ueot-core/docs/compression/theory_completion/unified_closure/decision_representation_closure_v1/native_protocol/RETURN_REPRESENTATION_DAG.lean`，冻结 SHA 为 `4b3537ff018ff234760dd1833ccacb7d0a0ccea392833b59730bf338e6d5763a`。driver 直接执行 `generate → certify → boundCheck`，再对同一图/root 调用 `packedRun` 和序列化；不能把它描述为调用旧树求解器，或声称它实际调用了 `returned` 包装函数。

本索引不添加 JSON 解码器或往返定理，不把导出文件本身当成 Lean proof object。实际字节与 THIS 已认证对象的绑定由原 driver 记录、SHA、独立制品核对承担；具体输出、成本、主例和边界运行仍归第 5 项证据。
