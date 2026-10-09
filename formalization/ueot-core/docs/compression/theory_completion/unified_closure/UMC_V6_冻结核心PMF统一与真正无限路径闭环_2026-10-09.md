# UEOT–UMC V6：冻结 Core 真正 PMF 统一、无限路径闭环与不可消除的理论边界

- 日期：2026-10-09
- 跟踪：既有 Issue #302 / Track TC；**只在本地研究分支**。
- 历史冻结：Core 106/106、Compression 四 counted generators；Theory Completion P0–P12 程序已完成，但 **P12 仍 PARTIAL / EXPLICIT BOUNDARY**。
- 结论状态：**有限随机—组织表示—控制—存续子核心 SOURCE-COHERENT CONDITIONAL PROVED**；**UEOT 全理论（Ω 自创生、Π/Φ 普遍物理机制、内生目的、真实历史谱系）FULL MATHEMATICAL CLOSURE NOT ESTABLISHED**。
- 科学范围：形式化数学；没有外部实验证据，没有物理规律必然性或独立科学认证。

## 1. 从“更多数学模块”转到“同一数学对象的真实组织闭合”

复核真正的 Lean 定理，而不是用同名概念强行缝合，揭示了冻结主干的四套已有结果：

1. **P-ALG-01**：`UEOT/V3/FiniteStablePartition*.lean`、`PAlg01.lean` 已经给出受控马尔可夫状态的初始观测/全行动奖励等价、有限稳定精化、最粗稳定分割与输出词概率保留。不能重做通用 bisimulation 算法。
2. **SISC**：`ScientificClosure/SISCModelKernelReconciliation.lean` 已证明该分割模型与源归一随机核的 strong lumpability 等价，二者的类转移质量是同一有限求和。
3. **P-QUO-01 / P-CTL-01**：`FiniteDiscountedExactQuotient.lean`、`FiniteDiscountedControl.lean` 已有精确 Bellman 最优值、宏观策略微观提升及对完整因果历史随机策略的优越性；无需复制 Bellman 证明。
4. **P-PER-03**：`ViabilityKernel.lean`、`ViabilityStrategy.lean`、`ViabilityTrajectory.lean` 已证明 PMF 存续固定点、历史依赖胜出集合，以及在真实 Ionescu–Tulcea 路径测度中全离散时间概率一存续。**V4 原本用实数矩阵独立重写有限存续递推，却没有证明两种对象语义一致。** 本轮优先消除这条重复与断裂。

## 2. 本轮完成的五个真实数学桥（完整 Lean elaboration）

在 `UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/` 新增：

### 2.1 `CorePMFViabilityReconciliation.lean`

- `frozen_pmf_staysIn_iff_real_zero_outside`：复用冻结 P-QUO-02 的 `FiniteProbabilityRow.ofRealRow` / `transitionPMF`；严格证明 `PMF.support ⊆ K` 当且仅当原始实数转移表对所有补集状态为零，不另设独立 PMF。
- `macro_viability_iff_frozen_pmf_iteration`：对**每一个**时间范围 n，V4 `macroViable` 与冻结 P-PER `viabilityIter` 等价。需注意 V4 n+1 显式要求安全，而 P-PER n+1 要求仍属于上轮区域，证明不是简单定义同一，而使用 V4 下降链消除差异。
- `micro_viability_equals_frozen_history_strategy_winning_set`：由 V4 微观精确前像、上一定理和冻结 `ViabilityStrategy.exists_stabilized_eq_winningSet` 得到相同的全历史控制胜出语义。**这是跨文件证明的实质性连接，不是再写一种胜出集合算法。**

### 2.2 `CoreInfinitePathClosure.lean`

- `micro_pmf_viability_fixed_of_macro_real_fixed`：V4 宏观有限可行集不动点 → 真实微观转移 PMF 的**同一个存续集**是冻结 P-PER 的固定点；微观动力学严格来自 Q.micro，而 Q 与真实源 K 相连。
- `exists_source_micro_all_times_viable_path_law`：调用冻结 `ViabilityTrajectory.exists_stationary_policy_all_times_of_fixed`，获得真实轨迹律
  \[
  \exists\pi:\quad
  \Pr_{P,\pi,\mu}\!\left[\forall t\in\mathbb N,\;
  X_t\in q^{-1}(V_*)\right]=1,
  \]
  对 **支持在 V* 的合法初始 PMF μ** 成立。没有另行假设路径概率论或独立安全控制器。

### 2.3 `CoreSourceAllTimesAssembly.lean`

- `single_source_terminal_object_viability_all_times`：从原始 P-ALG 受控有限马尔可夫 `M`，经**最粗稳定组织分割、SISC 一致性、P-QUO-01 Bellman 保真、P-PER-03 PMF 存续**产生单一证明链。
- 同时证明模型 `Q.micro.transition x a z = M.transition a x z`；一旦初始 PMF 支持在可维持核，微观无限轨迹概率一保持 `M.output` 上注册的安全条件。
- 奖励是已给定的并保真；**未证明存续动作恰是 Bellman greedy，也未推出环境中真实内生目标。**

### 2.4 `CoreNonvacuousAllTimesWitness.lean`

- **同一个既有** `survivalMicroKernel`：四个微观状态（显式可见/隐藏位）、两个控制动作、非 Dirac 随机性。
- `registered_survival_viable_all_horizons`：经真正 P-ALG→SISC→P-QUO 构造出的终端控制商，使初始可见位为 true 的每个微观状态均在所有有限步维持核内；不是“取 V* 非空为前提”。
- `registered_survival_nonempty_infinite_law`：以明确合法初始分布 `PMF.pure (true,false)`，**真正构造存在的微观策略及全离散时间可见安全事件概率一**。避免空核导致的形式真值假突破。
- 保护当前隐藏程序位时，同一源不能再将这些状态并类，见 V5 `OrganizationalSufficiencyWitness.lean`；这不是历史来源已被观测的证明。

### 2.5 新的 106 个正式定理的真实 elaborated 常量依赖审计

- 原有 `UMC_CORE_106_ELABORATION_AUDIT_V1.json`：106/106 被引用 Lean 符号 #check 和 #print axioms 均成功，106 个不同符号，0 自定义公理依赖；这不是自然语言源语义重新证明。
- 新增 `audit_core_106_elaborated_dependencies.py`、`UMC_CORE_106_ELABORATED_DECL_DAG_V1.json`。
- 审计读取 Lean Environment 的 theorem value 和 type 中的 **实际 one-hop 第一方声明引用**，不是引用文本或 module import。
- 106 个正式 P-ID 定理符号之间只有 **3 条直接引用边**，无有向环；多数依赖通过 first-party 中间定义、桥引理、Mathlib 等路径传递。这只能说明**直接 P-ID 子图稀疏**，不得推断 106 条定理数学上互不相干。未来必须做经辅助定理的传递闭包和来源假设剖面。

## 3. 数学严谨性边界

- **有限**状态/行动、真实行归一随机核、已选共同动作、已注册观测/组织状态/奖励/安全、0<β<1 与奖励界。输出标签自身不能证明其客观性。
- `terminalSetoid` 的最粗性是**相对初始受保护签名及精确 strong lumpability** 的最粗性，不是物理宇宙中绝对最小对象或唯一跨尺度自然表示。
- 折扣最优与存续控制是两个不同的目标。冻结 `SameObjectViability.lean` 已证明 Bellman-optimal 动作可能破坏存续域；除非建立 `GreedyPreservesObjectPersistence` 或真正约束最优策略，不能合并为无条件 GOA。
- 非空实例在一个有限 toy kernel 上建立，既非现实设备证据，也不能推出任意核有非空存续集。
- 路径律的全时刻性是**可数离散时间**的 Ionescu–Tulcea 语义，不是连续时间无界动力学自动成立。
- `registered program` 当前为**状态依赖的保护标签**，绝不等于物质性的程序重构、内生执行、真实来源证明。
- `AutopoiesisClosure.lean` 的 `no_physicalOnly_synthesizer_for_samePhysical_distinctSeeds` 明确反对从同一物理状态凭空恢复不同来源程序；P12 仍为 PARTIAL。
- `DualDriveGaugeCompleteness.lean` 证明 Π/Φ 只有组合目标时存在未锚定 gauge 不可识别性；不能拿抽象 Π−λΦ 数学表达冒充真实两种独立物理驱动已得到确认。
- 现有 P2 同对象、GOD/GOA、修复和 P12 条件式生命周期**不能仅凭 Q.micro transition 自动实例化**，其组织来源、内生目标、物理修复/材料/程序条件属于独立科学前提。

## 4. 外部先例定位：严禁重复发明标准数学

- Dean & Givan, *Model Minimization in Markov Decision Processes*, AAAI 1997，提出 coarsest homogeneous refinement / MDP reduction（https://mlanthology.org/aaai/1997/dean1997aaai-model/）。UEOT 的通用稳定分割不是此方向的新发现。
- Doyen & De Lara, *Stochastic viability and dynamic programming*, Systems & Control Letters 59 (2010), DOI 10.1016/j.sysconle.2010.07.008。随机可行性动态规划不是 UEOT 独创。
- *Formalizing autopoiesis: Toward a Categorical-Thermodynamic Calculus of Closure*, BioSystems 268 (Oct 2026), DOI 10.1016/j.biosystems.2026.105918，特别区分严格组织自生产与形式表示、随机动力学之间的开放问题。
- 因此本轮贡献是**把冻结 formalization 中彼此独立类型的证明转成同源 Lean 互操作与非空边界实例**，不是宣称新发现了最粗分割、Bellman 或存续动态规划的原理。研究独创性仍需独立比较和新物理可检验机制。

## 5. 全局剩余门槛，按优先顺序

| 门槛 | 核心问题 | 验收条件 |
|---|---|---|
| G-SEM | 106 个被引 Lean 定理的 source contract 条件是否真的匹配原稿？ | 逐条 theorem type/前提、source chapter、隐含约束和负控复核；one-hop/DAG 不替代语义审计 |
| G-ORG | P-ALG 最粗稳定组织态与真实物质/能量/程序历史是否可接？ | 明确历史增强或 source-certified functional adapter；有正例及不可能性定理 |
| G-PI-PHI | Π/Φ 是否是可识别、具有来源的双驱动且构成同一作用动力学？ | 解除 gauge 或给出不可识别条件；不得从变分形式直接推出 |
| G-GOD-GOA | 目标是内生还是外加？最优控制是否维持同一对象？ | 从 P2 真实语义合同推导忠实性+维持兼容；或保留边界 |
| G-OMEGA | 维持安全集合如何提升为资源—物质—程序再生产？ | 同源 P5/P6/P7 修复生成与 P12 物理/程序载体桥，实例不是仅仅安全集 |
| G-LINEAGE | 何时跨代成为同一谱系而非观测别名？ | 对 P8/P12 的 parent/offspring 来源真实性做成可否证桥 |
| G-SCALE | 多级最小表示和 P9 尺度是否符合物理 transport？ | typed 同中间模型连接、不可压缩负控，不能冒充 RG |
| G-FINAL | UEOT 原始完整核心是否从尽可能少的必要前提推出？ | 一个源对象、非空联合实例、完整 Lean 根编译、语义来源、独立前提标注、否定控和科学证据门全通过 |

## 6. 当前验收与发布约束

- 新 Lean 证明无 `sorry`/`admit`/`axiom`/`opaque`/`native_decide` 等占位。
- Lean axiom audit：七个代表性桥/终端符号仅依赖 `propext, Classical.choice, Quot.sound`。
- 完整 `lake build UEOT`：**9334 jobs 成功**（以本地构建记录为准）。
- UMC 9 个冻结治理门通过；12/12 个变异负控按预期拒绝。
- 本轮**只允许本地研究提交**；无需推送、改账本、改 P12 结论，也不删除旧分支或任何未跟踪环境文件。
- 全理论数学闭环仍 **NOT ESTABLISHED**；有限源一致的存续子闭环 **PROVED UNDER FINITE REGISTERED PREMISES**。
