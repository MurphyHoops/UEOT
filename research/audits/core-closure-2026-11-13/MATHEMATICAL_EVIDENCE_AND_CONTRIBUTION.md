# 数学证据、证明可信边界与贡献定位

日期：2026-11-13。本文是本轮有限整改的数学记录，不替代已有定理合同，不增加生产 Lean 定理。

**结论：修正一处来源矩阵的折扣条件，保留已核实的条件数学结果，明确历史编译与独立新执行的区别，并以成熟先行理论为基础限定贡献表述。未发现要求重构基础公理或重开既有 K1/K2 合同的数学反证。**

## 1. 固定版本与证据等级

本记录复核的源基准为 [UEOT `cb17211653fde30aa50e0e9848798a6a5b3b3f12`][base]，Git tree 为 `921f87cbbdcd11d1c2fa79cc9424aa095e3c6914`。有限整改前 main 与原独立审计基准相同。本文引述的当前源、历史回执均指这个版本；本记录随后的文档提交不改动该生产数学源。

| 等级 | 本文含义 | 不包含的保证 |
|---|---|---|
| E1 | 当前固定源、精确类型/假设的读审、文件哈希核对、独立数学推导或精确算术 | 不自动等于本环境重新经过 Lean 内核 |
| E1-L | 实际读取的一手文献，按下表注明摘要或相关全文章节 | 不等于完成全领域优先权检索 |
| E2 | 与当前源字节绑定的历史编译、公理检查及执行日志 | 不等于今天独立重建或跨平台复现 |
| E3 | 项目登记、作者解释或尚未独立证实的原创性判断 | 不由登记状态升级为证明 |
| E4 | 此次未查明的外部问题或未执行的检验 | 既非已通过，也不自动成为核心数学缺口 |

项目入口是 `formalization/ueot-core` 的 `UEOT.lean`，package 为 `ueot_core` v0.2.1。[工具链][toolchain]锁定 `leanprover/lean4:v4.33.1`；[Lake 配置][lakefile]和[依赖锁文件][manifest]共同固定 Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`。历史增长检查记录的运行时为 Lean 4.33.1、`arm64-apple-darwin24.6.0`、Lean commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`。[E1/E2]

**本次审计和本轮有限整改都没有重新执行 Lean。独立新执行（D3）状态为“未执行”，不是 PASS。** 当前可用环境没有所需可执行工具链，本地 Mac 离线；这限制新复现证据，不撤销准确匹配的既有证明记录。本轮没有升级工具链、安装替代版本、修改生产 Lean 或要求无差别全库重建。[E1/E4]

## 2. P-CTL-01 的精确勘误

[来源矩阵][matrix]的 P-CTL-01 一行原写 `0≤β<1`，改为 `0<β<1`。这是该行唯一变动。[有限折扣 Model][discount-model] 的字段是：

```lean
discount_pos : 0 < discount
discount_lt_one : discount < 1
```

当前中文[数学著作][math-book] §19.1 与冻结 [Core v3.0 原文][frozen] §19.1 都采用严格正折扣。因此错误发生在矩阵，不能称为正文主定理的假覆盖，也不需要补造 β=0 端点。P-ID、冻结原文、类型、证明及中英文正文均不因该勘误改变。[E1]

勘误前矩阵 Git blob 为 `73ee4e6f97b0f38b93bb72c4300ecf72bf3e670f`；仅此替换后的 Git blob 为 `fe5bd83ef692c068a825bb0dbfd45db11fcec485`。验证是逐字差异和准确字段核对，未运行 Lean。[E1]

## 3. 可复用证明证据及其真实范围

### 3.1 已完成审计与此次复核分别做了什么

此前的独立审计对该固定基准的 1,051 个生产 Lean 模块作了去注释/字符串的语法扫描和内部导入图检查：未发现 `sorry`、`admit`、`sorryAx` 或显式自定义 `axiom`，发现并定位了两个 `native_decide`；106 个冻结 P-ID 对应的 163 个登记声明作了静态定位和类型头核对。这是覆盖信息，不是成熟度评分，也不代表所有传递依赖均于本环境重新 elaboration。详情保留于[原综合报告][prior-review]第六章及原交付包。[E1]

此次有限整改没有重复全工程扫描。从固定 SHA 重新读取并逐 Git blob 核对了 19 个必要文件：工具链与锁文件、折扣 Model、增长三模块、受影响公共入口、边界消费者、五份逐文件编译回执、三个汇总构建/公理记录、增长汇总记录及原生归约源。增长五个源文件的 SHA-256 与逐文件回执和汇总记录再次逐项匹配；退出码 0 是历史记录中的退出码。[E1/E2]

### 3.2 历史执行怎样覆盖当前源

原同源 Core 包的 [PUBLIC_SOURCE_AUDIT.v2.json][public-audit] 登记 1,048 个生产文件；原独立审计核对当前字节时，1,047 个不变，唯一变化是 `CoreTheoryClosure.lean`。后续增长分类增加三个生产模块，并为该公共入口提供新的准确回执。因此“旧包不能覆盖改变后的入口”已经通过后续回执接续，不是仍待修补的证明空白。[E1/E2]

[原同源 INTEGRATION_BUILD.json][integration] 记载历史 `lake build UEOT` 退出码 0，采用已有 `.lake` 缓存，`clean_full_rebuild=false`。原独立审计还核对了其实际日志哈希；不能将它改称此次干净全库重建。[E2]

最新 [LEAN_VALIDATION.json][growth-validation] 与其 `checks/` 下五份回执给出下列源绑定，本轮已重新计算并匹配：[E1/E2]

| 源文件 | 当前 SHA-256 | 回执作用 |
|---|---|---|
| `CoreRegenerativeGrowthClassification.lean` | `ce5f6f1119a3a1c209148280200fed532377ba4b28a6745813ab3dcae0bd7dcb` | 严格正参数域、真实逐行上界与达到条件 |
| `CoreRegenerativeGrowthPopulation.lean` | `e69d2ef25be8a7ea0a74bc6e8c7d24580cd1d614691c5e38d9c5292848864b54` | 完整允许历史策略的人口期望界和内部程序桥 |
| `CoreRegenerativeGrowthAttainment.lean` | `952740533202112b37765f3a887dbe1e65dbee1864f386abb7b3abf759529edd` | 最小统一指数底数及两程序达到区域 |
| `CoreTheoryClosure.lean` | `c14befb44ce0d87a7db3d044671c1f88ca9415a822597c1bca0eedd9eaec50ac` | 受影响公共入口 |
| `GrowthClassificationCheck.lean` | `80e83ae1a7b6b774e605bf7d7d2b55a75419ad45b96fd99c50460db2e9e6dfec` | 扩大域和亚临界具体消费者 |

五项均记录历史编译退出码 0；汇总明确 `full_historical_build_rerun=false`。所列 15 个公理检查端点仅出现 `propext`、`Classical.choice`、`Quot.sound`。原同源包的 [AXIOM_AUDIT.json][core-axioms] 对其 59 个指定端点也只列这些标准逻辑公理或其子集。原独立审计另核对过后继登记的 26 组源/回执绑定；此次没有将那次检查冒称为又执行一遍。[E1/E2]

回执是项目保存的历史执行材料，不是第三方签名证明，也不保证任何未来环境自动重现。源哈希绑定消除了把旧结果配给不同源字节的歧义；执行独立性仍应按“历史记录复用”表述。[E2]

### 3.3 两个原生归约端点

[RegisterMechanismDecisionConsumer.lean][native-source] 中 `exact_cached_data` 与 `exact_two_data` 使用 `native_decide`，分别承担 H3/H2 的有限精确数值检查。[原生归约公理记录][native-axioms] 的状态明确是 `PASS_DISCLOSED_NATIVE_REDUCTION`。其部分下游精确数值端点依赖：

```text
RegisterMechanismDecisionConsumer.exact_cached_data._native.native_decide.ax_1_1
RegisterMechanismDecisionConsumer.exact_two_data._native.native_decide.ax_1_1
```

这是特定原生计算的额外信任边界，不是 `sorry`，也不能归为普通三公理内核归约。依赖必须逐声明检查，不能因模块导入而断言其全部定理都使用这些项。通用机制后悔证书等部分端点不依赖该原生求值。[E1/E2]

Lean 官方[证明验证说明][lean-validation]区分定理类型的意义、证明被接受、公理闭包和额外核验；其“Printing Axioms”及原生计算说明与这里的区别一致。该网页用于解释验证层次，项目版本事实仍由上述固定工具链和具体回执给出。只有下游确实要求取消原生求值信任时，才值得定点替换这两个有限计算；目前不据此重做 Core。[E1-L/P2 按需]

### 3.4 发布证据义务与重新执行的触发条件

本轮对外应同时给出：固定源版本、工具链及锁依赖、具体命题及前提、对应历史回执、实际公理边界、未执行的新验证项目。这组透明、可追溯的材料满足本次文档整改的证据说明义务；**它不把 D3 改成成功，也不认证经验真实性或数学原创性。**

只有出现源/依赖哈希变化、回执不能绑定、具体消费者类型不匹配、反例指向现行精确结论、复现失败，或明确的外部评审复现要求，才启动针对性新执行。复现者使用固定 Lean/Mathlib，先验证受影响模块及消费者，再按失败范围扩大；`#check` 和 `#print axioms` 的实际输出、命令、退出码和日志应随源哈希保存。Mac 离线、定理数量增长意愿或旧任务书的 OPEN 字样均不是重新立项理由。

## 4. 最重要的数学主张怎样表述

以下 K 分级是审计的理论作用判断，不改变原 P-ID、源码或注册合同，也不表示学术原创性等级。

| 对象 | 保留的理论作用 | 必须保留的限制 |
|---|---|---|
| `CoreOperationalAssembly.p_core_01` | K2 接口装配；外层合取包装可评为 K3。内部 `optimal_qValue_macro_error_le_D`、`macro_gap_certifies_micro_action` 具有实际误差传递内容 | 预测类型 H/I/Y、控制 X/M 和失败域 Obj 彼此独立；共同好事件不证明同一身体。不得称为 K1“共同本体源存在定理” |
| `CoreTheoryClosure.same_program_regenerates_and_attains` | K2：在同一已定义源上把付费修复、程序执行、人口与增长结果接合 | 外层合取不是全部子结果的新证明；这个参数类的共同见证不统一所有 Core 分支 |
| 增长分类的真实逐行上界、全允许策略统一上界和达到分类 | 在这一同源模型的主张内承担 K1 作用 | 量化的是指定 `Policy`、开放供给规则和期望人口指数；不包括无条件存续、有限期限最优、未知参数学习或规范价值 |
| 标准控制/概率工具及简单包装 | 按实际用途分为 K2/K3；纯重复包装和无消费者的补证属 K5 | 使用标准定理和完成 Lean 工程可以有价值，但不能据 K 等级主张首次发现 |

准确源见 [CoreOperationalAssembly][assembly]、[同源公共入口][closure]及[增长分类][growth-classification]、[人口桥][growth-population]、[达到分类][growth-attainment]。[E1/E2]

### 4.1 成功是否被预写进假设

增长扩展的 `ProbabilityValid` 只要求原始概率域

\[
0<\delta<s<1,\qquad b>0,\quad\gamma>0,\quad b+\gamma<1,\quad0<q<1.
\]

`valid_iff_probability_advantage_supercritical` 明确旧 `Valid` 恰好再加 `δ<γ` 和 `1<s+b`。因此旧类是充分类；当前分类不能再被批评为所有结果都预设超临界成功。[E1]

令 `kc=s+b`、`kb=s−δ+b+γ`、`λ1=(1−q)kb+q kc`。当前实际全菜单的最小统一期望指数底数为 `ρ*=max(1,kc,λ1)`；保留真实拒绝行，亚临界时仍可取 1。`optimalRate_isLeast_uniform_upper` 对非空初态证明最小性；`false_program_attains_iff` 与 `true_program_attains_iff` 给既有两程序的精确达到区域，而非先假设它们最优。修复本身在概率域内成立，修复后程序是否达到最优需另满足相应区域。真实动作、损伤、付款、出生和继承规则由模型明确给定；这不推出这些程序为什么在自然界出现，也不推出应当以期望人口为唯一评价。[E1/E2]

### 4.2 身份和形成的输入/输出

[CoreRegenerativePopulation][population-source] 预给 `Identity` 编码和亲本/出生记录规则。`retained_identity` 等端点的一部分是定义展开；实际 `Source.step`、记录提升、后代人口及反馈计数的共同来源具有实质桥接作用。`newborn_fresh_from_old_population` 需要旧人口满足 `ValidIdentity t`；[ControlPopulation.State][control-population] 本身不包含全局 `NoDup` 或所有时间合法身份。因此不能宣称任意输入人口天然具有全局唯一且无碰撞的实际身份。[E1]

内部程序解释另有独立前提：初始人口须满足 `ProgramPopulation θ`，即每个成员的身体携带同一程序 θ；`CoreRegenerativeControlPopulation.step_outputs_program` 与 `reachable_program` 保持其继承不变式。[增长人口桥][growth-population]的 `programPolicy_positive_branch_is_internal` 在当前人口满足这一不变式、且实际分支权重为正时，才把 `programPolicy θ` 的后继人口识别为 `internalGeneration`；`founder_program` 为所用 founder 正例履行初始责任。因此，一般 `State` 上的外部 `programPolicy θ`，以及全策略期望增长上界，都不能自动被读作任意身体内部同一个程序的执行。[E1/E2]

[CoreRegenerativeFormation][formation-source] 形成的是给定物理响应源中的决定载体候选，使用 `Finset PhysicalCell` / `SourceHistory`；它不是从无组织材料生成任意身体，也不是永久 `Identity` 的同一个类型。修复保留 boot、编码冗余及资金条件；模型内部实际生成的亲本关系不自动认证现实个体的本体身份。这个边界已在数学总论和后继角色区分中保留，无需制造一个普遍身份互推定理。[E1]

## 5. 与先行理论的关系及可保留贡献

比较区分“在 UEOT 内确实实现了什么”与“是否首次提出”。下列文献均为真实一手来源；只读取摘要的项目不被描述为完成全文定理等价检验。[E1-L]

| 主题 | 已核实先行内容及阅读范围 | UEOT 的准确定位与边界 |
|---|---|---|
| 信息与意义 | Shannon (1948)，引言及统计信息设定：通信量的数学处理与语义问题分开。读取原文相关部分。[R1] | P-INFO 使用概率、统计量与信息工具；信息数值不自动给出语义、意图或价值。KL 链式、Pinsker、Fano 等应按实际来源归属，不能统归 Shannon 该篇或宣传为 UEOT 原创 |
| 最小预测状态 | Shalizi–Crutchfield (2001)，§V、Theorems 1–3 与相关引理：因果状态的预测充分性、最小性和相应唯一性。读取作者全文的这些段落。[R2] | P-PRED-01 的可数协议、依赖目标、可测核与 a.e. 共同因子化应与此精确对照。最小预测状态这个基本思想已有明确先行结果；现有代码实现和接口整合不自动证明一个全新的普遍表示定理 |
| 折扣控制与控制商 | Givan–Dean–Greig (2003)，§2.1.3 的 Bellman 背景、§3.3 定义及 Theorems 5、7：奖励/转移保持与最优策略提升。读取相关全文。[R3] | P-CTL-01 的经典优化骨架、P-QUO-01 的精确商不是 UEOT 首创。UEOT 对观察、合法动作、资源和共同误差消费者的组合需按额外接口逐项评估，不能因更换术语宣称新控制论 |
| 受控多型分枝 | Pliska (1976)，原刊摘要：受控多型分枝的期望奖励优化转为广义非负矩阵 MDP，可包括移民。[R4] | “分枝人口可以控制优化”属于成熟方向。UEOT 的真实执行、费用、损伤修复和身份记录到该数学层的连接是需要展示的工作；尚未建立与该文全部假设/策略类完全等价 |
| 分枝增长最优性 | Rothblum–Whittle (1982)，原刊摘要：有限独立选行非负矩阵族，固定矩阵重复使用可达到矩阵序列中的最佳几何增长及其后的代数增长。[R5] | “增长优化存在固定最优选择”不能作为 UEOT 一般原创性。当前有价值的具体工作是把真实请求/拒绝规则接到全允许历史策略界，并给指定严格正参数域的精确分类；未由摘要证明前文覆盖 UEOT 的全部联合历史策略、账本或代码继承语义 |
| 组织与自维持 | 哲学比较另见本次范围协调和原综合报告的过程哲学/控制论/自创生分析 | 本数学记录只确认模型中的付费恢复、因果门、继承与反馈连接，不把有限冗余码修复直接等同一般生命自生产，也不声称已完成组织论的全面原创性证明 |

**本轮允许的贡献表述：** UEOT 提供按来源、任务、观察、合法动作、资源和失效边界组织的条件数学框架；在一个明确参数类内，把实际程序读出、付费修复、身份与出生记录、随机人口和全允许策略增长界贯通，并公开不能保持任务的商、修复失败与目标分离反例。这些实现与桥接可以具有独立的组织、形式化和具体数学价值。[E1/E2]

**仍需保留的学术不确定性：** 上述具体组合、精确参数分类或反例是否具有全球优先权，尚未通过系统全文比较确定。当前可称“本项目构造并验证的结果”或“待同行比较的贡献”，不能称首创统一理论、全新增长优化原理、最小预测状态的首次发现，或既有理论均无法表达的普遍本体论。[E3/E4]

## 6. 原数学发现的逐项处置

“保留边界/关闭重复任务”意味着准确的现行条件结论未被推翻，不意味着过强命题获得证明。宪章旧强义与当前合同的正式协调由本次治理文件处理；本记录不独自宣告治理修改已获通过。

| 原发现 | 实质边界与证据入口 | 本轮处置 / 是否还需 Core Lean |
|---|---|---|
| B-M01 折扣矩阵 | `FiniteDiscountedControl.Model.discount_pos` 与正文严格正 | 矩阵唯一字符勘误；不增加 β=0 接口。原 P2 文档修正已给出 |
| C01 空 Ω | `OmegaMinimalFailure.p_omg_01` 保留有限性、向上单调；失败族可空 | 保留条件定理和空族反例，协调旧强义；P5，不证明普遍非空 |
| C02 退化静态模型 | Unit 自环与零奖励满足基础接口 | 广泛语言不保证有意义的发展；P5，不为名称添加非退化公理 |
| C03 预测不等于控制/身份 | `CoreRegenerativeQuotient` 的静默标签商合法；删除诊断/执行门失败 | 保留任务、动作、费用与联合记录责任；P5，无普遍互推补证 |
| C04 全码擦除 | `CoreRegenerativeSource.no_decoder_recovers_both_erased`；同输入不能恢复两个不同答案 | 保留信息条件和不可能性；P5 |
| C05 增长与个体续存 | `growth_choice_not_identity_survival_maximal` | 明确目标分别量化；P5，不用“唯一目的”覆盖差异 |
| C06 指数与有限期最优 | 原数学总论及原审计的有限两期/临界反例 | 保留最小指数结论，不升级为逐时最优；P5 |
| C07 亚临界真实拒绝 | 最新增长 `optimalRate`、`subcritical_existing_programs_do_not_attain` | 已由增长分类处理；P5，不按旧 Valid 重开 |
| C08 三种选择陈述 | `CoreRegenerativeFeedbackBoundary.expected_ratio_ne_ratio_expected_counts`；灭绝反例 | 区分均值比例、随机比例与几乎必然选择；有限 T / cohort 浓缩仍有效；P5 |
| C09 局部组合与共享资源 | 两个费用 1 的同时任务不能由共享钱包 1 实现 | 共同来源、联合动作与预算由调用者给出；P3 应用义务，不另造无条件组合定理 |
| C10 共同二维 | `CommonBottleneckRank.p_ddh_04` 输入在考察点可微的共同二维因子；响应 `(s,b,bq)` 可有秩三 | 保留反例并协调定性/定量读法；P5，不新增普遍二维公理 |
| C11 GOA 与收敛 | `FiniteCesaroInvariant.p_goa_01` 不等于唯一不变律或原时刻收敛；混合另有条件 | 保留长期对象分型；P5 |
| C12 泛型装配非同一身体 | P-CORE 各状态类型独立，具体同源模型另给共同见证 | 校准为 K2 接口/K3 包装；P5，无需宇宙总定理 |
| 身份合法输入 | `newborn_fresh_from_old_population` 的 `ValidIdentity`；State 不含任意全局唯一性 | 如实保留输入责任；不把一个 `rfl` 端点当存在论证明；P5 |
| 内部程序解释 | `ProgramPopulation θ` 初态、`step_outputs_program` / `reachable_program` 继承不变式及实际正分支 | 补明现有桥的前提；一般 State 的外部 policy 不自动变成体内执行，不需新证明；P5 |
| 成功写进假设的疑问 | `ProbabilityValid`、旧 Valid 等价分解、全策略达到 iff | 最新分类已包括失败区；P5，不重复研究已完成的扩大域 |
| 四生成器与 106 P-ID 的覆盖 | 原压缩账本只登记 11 个 generated、89 个 retained_adapter、6 个 retained_boundary | 保留具体处分；106 项登记完成不改写为全由四公理推出，后继同源结果也不覆盖每个原端点；P5 |
| 两个 `native_decide` | 明确端点及 `PASS_DISCLOSED_NATIVE_REDUCTION` | 接受公开边界；取消该信任仅属真实消费者有要求时的 P2 |
| 未执行独立新 Lean | D3 未执行，E2 当前字节绑定可复用 | 关闭本轮证据表述义务，保留复现状态；不虚标 PASS，不重开数学合同 |
| 2/3/4 任务分割、秩三、正次根/limsup | [LEAN_API_SCOPE][api-scope] 明确书面推论与专门端点的区别 | 有证明但无专门机器消费者的补证暂属 P4；真实机器接口需要时才转 P2 |
| 零概率端点、更多程序/损伤族 | 超出现行严格正参数类 | P2/P3 新合同；不阻止现行有限范围冻结 |
| 未知参数学习、自发身体生成、一般连续过程 | 当前没有主张这些问题已由同源有限模型解决 | P3 或另立有边界研究；不伪装现行 Core 的必补证明 |
| 原创性未定 | 本节已标成熟先行结果和摘要/全文读取范围 | 以准确归属关闭夸大风险；系统优先权检索可后续开展，不把未定改成首次 |

依据为[来源矩阵][matrix]、[数学 API 范围][api-scope]、[当前数学著作][math-book]、上述准确源及[原综合报告][prior-review]第五至十一章。原审计的精确反模型复算没有重跑为新增生产证明。[E1/E2]

## 7. 完成判准与后续投入

本轮数学整改完成判准是：矩阵前提与实际类型一致；读者能从固定版本复核证据；历史执行、标准公理、原生归约和未执行项目不被混写；现有数学成果与先行结果的关系可查；所有原数学问题均有修正、保留边界、已有解决或明确非核心的处置。

按这一判准，Core 数学不需要通过增加证明数量才能冻结。继续投入优先面向具体外部评审、存在明确风险的独立复现和有经验输入的应用建模；只有新反证、实际消费者失败或另行确定的新目标才重开相应数学合同。不能把无条件的存在、唯一目的、所有现实对象或完整自发组织生成偷偷恢复为已证明主张。

## 参考文献与读取限度

- **[R1]** C. E. Shannon. “A Mathematical Theory of Communication.” *Bell System Technical Journal* 27 (1948): 379–423, 623–656。[原文重印 PDF](https://people.math.harvard.edu/~ctm/home/text/others/shannon/entropy/entropy.pdf)。本轮核对引言及统计设定；不以此文代替后来的全部信息不等式来源。
- **[R2]** C. R. Shalizi and J. P. Crutchfield. “Computational Mechanics: Pattern and Prediction, Structure and Simplicity.” *Journal of Statistical Physics* 104 (2001): 817–879。[作者 PDF](https://csc.ucdavis.edu/~cmg/papers/cmppss.pdf)。本轮读取 §V 相关定义、引理与 Theorems 1–3；PDF 是作者版，页码与期刊版不同。
- **[R3]** R. Givan, T. Dean and M. Greig. “Equivalence Notions and Model Minimization in Markov Decision Processes.” *Artificial Intelligence* 147 (2003): 163–223。DOI [10.1016/S0004-3702(02)00376-4](https://doi.org/10.1016/S0004-3702(02)00376-4)，[作者 PDF](https://cs.brown.edu/people/tdean/publications/archive/GivanetalAIJ-03.pdf)。本轮读取 §2.1.3、§3.3 的定义及 Theorems 5、7；没有声称逐一重证全篇。
- **[R4]** S. R. Pliska. “Optimization of Multitype Branching Processes.” *Management Science* 23(2) (1976): 117–124。DOI [10.1287/mnsc.23.2.117](https://pubsonline.informs.org/doi/abs/10.1287/mnsc.23.2.117)。本轮核查原刊摘要和书目信息，未获得全文定理比较。
- **[R5]** U. G. Rothblum and P. Whittle. “Growth Optimality for Branching Markov Decision Chains.” *Mathematics of Operations Research* 7(4) (1982): 582–601。DOI [10.1287/moor.7.4.582](https://pubsonline.informs.org/doi/abs/10.1287/moor.7.4.582)。本轮核查原刊摘要和书目信息，未完成全文假设/策略类等价检验。

[base]: https://github.com/MurphyHoops/UEOT/tree/cb17211653fde30aa50e0e9848798a6a5b3b3f12
[toolchain]: ../../../formalization/ueot-core/lean-toolchain
[lakefile]: ../../../formalization/ueot-core/lakefile.lean
[manifest]: ../../../formalization/ueot-core/lake-manifest.json
[matrix]: ../../../mathematics/THEOREM_SOURCE_MATRIX.md
[discount-model]: ../../../formalization/ueot-core/UEOT/V3/FiniteDiscountedControl.lean
[math-book]: ../../../mathematics/UEOT_MATHEMATICS.md
[frozen]: ../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md
[prior-review]: prior-review/UEOT_CORE_COMPREHENSIVE_THEORY_AUDIT_2026-11-13.md
[public-audit]: ../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_theory_closure_v1/checks/PUBLIC_SOURCE_AUDIT.v2.json
[integration]: ../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_theory_closure_v1/checks/INTEGRATION_BUILD.json
[growth-validation]: ../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_growth_classification_v1/LEAN_VALIDATION.json
[core-axioms]: ../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_theory_closure_v1/checks/AXIOM_AUDIT.json
[native-source]: ../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterMechanismDecisionConsumer.lean
[native-axioms]: ../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/mechanism_decision_closure_v1/checks/AXIOM_AUDIT.json
[lean-validation]: https://lean-lang.org/doc/reference/latest/ValidatingProofs/
[assembly]: ../../../formalization/ueot-core/UEOT/V3/CoreOperationalAssembly.lean
[closure]: ../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreTheoryClosure.lean
[growth-classification]: ../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeGrowthClassification.lean
[growth-population]: ../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeGrowthPopulation.lean
[growth-attainment]: ../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeGrowthAttainment.lean
[population-source]: ../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativePopulation.lean
[control-population]: ../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeControlPopulation.lean
[formation-source]: ../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeFormation.lean
[api-scope]: ../../../mathematics/LEAN_API_SCOPE.md
