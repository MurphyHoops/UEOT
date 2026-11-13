# B：D3 定向 Lean 复现的数学读回审查

## 1. 裁定

**支持关闭原 D3 的定向复现事项。** 该结论限于既定的 15 个源文件实际重编译、44 条实际类型查询与对应传递公理报告、12 项关键定义/结构查询，以及本轮证据链的来源与完整性。没有发现需要改变数学定义、增加定理或重做全库构建的新问题。

本轮证据补齐了此前未实际执行的关键检查；它不把完整 UEOT、全部依赖、两个缓存 native 数值计算或所有自然语言主张升级为重新验证。现有关于有限模型、参数范围、内部程序、身份、期望增长和同源解释的限定继续有效。

本报告由 B 读取主审取回的实际原始日志、回执和精确源码后形成。B 未操作 Mac，未另行运行 Lean，未修改原执行回执。C 对解析器及证据链进行的独立检查另有记录。

## 2. 实际执行与证据边界

固定提交为 `6dd6a3bc13e26f41eddc10ee4d2f39fa1c8ab3d4`；实际编译器为 Lean 4.33.1，commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`，`arm64-apple-darwin24.6.0`，Lake 5.0.0-src+819816b。源、锁和依赖版本按原计划检查，没有升级。证据见 `evidence/run-20261113T0932Z/D3_RECEIPT.json` 的 `compiler`、`source_identity`、`dependency_sources`。

| 阶段 | 实际观察 | 本次如何使用 |
|---|---|---|
| v1，09:20 run | 首个依赖命令退出 0，但稀疏 overlay 中的依赖文件不存在；生产源尚未编译 | 保留 `FAILED_OR_BLOCKED`，仅定位搜索根故障 |
| v2，09:32 run | 15/15 选定源编译退出 0；30 个新 `.olean/.ilean` 产物；最终原 probe 因未知显示选项 `pp.width` 退出 1 | 复用这 15 个已经完成的新编译，不伪造整个 wrapper 通过 |
| 修正 probe continuation | 仅删除该一行显示选项；实际 `--deps` 与 Lean probe 命令均退出 0，后者 09:39:30.87—09:39:57.24 UTC | 使用真实成功查询输出，不重复编译 15 个源 |
| continuation 的 Python 后处理 | 将 `Classical.choice.{u}`、`Quot.sound.{u}` 误当额外公理而失败 | 原 `FAILED_OR_BLOCKED` 保留；另作严格解析，不改写失败历史 |
| 09:41:17 UTC 只读终核 | 主审在 Mac 再核源/配置 1055 文件、15 模块的 30 新产物、63 个旧目标产物及日志哈希，均未变 | `FINAL_SOURCE_ARTIFACT_CHECK.json` 补足前一 wrapper 中尚未执行的末尾核验 |

实际源编译与查询证据属于本轮 E1；复用依赖仍保留原有来源绑定的 E2 边界。准确说法是“15 个选定源实际重编译，并对 44 个端点完成实际类型和公理查询”。其中 37 个端点来自本轮新编译模块，7 个来自复用 `.olean`；后者包括 5 个保留边界和 2 个已披露 native 端点。

**二进制读回边界：** 30 个源模块二进制产物没有随证据 ZIP 复制到云端。B 在云端独立核对的是主审在 Mac 实际读取的 SHA256/大小记录与编译回执、continuation 绑定和最终读回记录的一致性，以及取回的每份原始日志字节；不能声称 B 或 C 在云端重新哈希了这些二进制。原 native 数值端点没有重新求值。

关键绑定值：

- v2 原回执 SHA256：`aabc33bd9e5928a94cf0036ee2772de26eb082db7e976f65fee1b594fbb6dec1`。
- continuation 原回执 SHA256：`663eddf04eef161971e5d95760a36a0ff40ab6d33fd10bb795f197c81ab342a4`。
- 最终原始日志 SHA256：`21dd301ebaa030f559bad47140b27d87760489fb3fb2c4c16a418b24d55cb65b`。
- 原计划 SHA256：`70b15301958a5c078167f929865c469b3b6fda925db7c0cfa1572e03f54ee29d`。
- 修正 probe SHA256：`28c731287dc45ad7f7f6cbbdd67e011ef493614989da1462bf7f3135ed9bcb8c`。

## 3. 严格公理解析结果

`parse_observed_axioms.py` 只读取证据，不运行 Lean，也不改写回执。它逐条完整消费原公理列表，保留 `raw_token`、完整 `constant_name`、`universe_suffix` 和宇宙参数，不采用任意字符串删除。标准常量只允许原计划中的 `propext`、`Classical.choice`、`Quot.sound`。实际出现的 `.{u}` 是标准公理的宇宙实例；解析器检查完整尾缀和正确元数。当前解析器刻意只接受本批所需的简单宇宙参数/整数格式，遇到陌生复杂语法会停止，不自动宽放。

结果为 **44/44**：35 条依赖三个标准公理，4 条仅 `propext` 与 `Quot.sound`，3 条仅 `propext`；余下 2 条在三个标准公理之外分别依赖以下完整常量：

```text
UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionConsumer.exact_cached_data._native.native_decide.ax_1_1
UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionConsumer.exact_two_data._native.native_decide.ax_1_1
```

这两个完整名字与原计划已披露项精确对应；没有使用宽泛 native 名字匹配。42 个非 native 查询未发现额外公理；44 项均未出现 `sorryAx`。15 个源的实际编译日志中没有未完成证明警告；现有警告属于 `simp` 建议、未使用 section 参数或未显式引用变量等，不据此推导哲学充分性，也没有为了消除这些警告修改生产源。

机器可读结果为 `D3_OBSERVED_AXIOMS_AND_TYPES.json`，保留全部原名、原始类型输出、原始公理文本、行号、来源模式和逐项判定。解析器的 14 个反向检查只测试解析边界，不是新增 Lean 证明。

## 4. 逐项数学类型读回

下表的 **P** 为实际原始日志 `evidence/probe-continuation-20261113T0940Z/D3ProbeFinal.log`，行号从 1 起。完整声明名与原始类型均保存在机器结果中；下表使用末段名便于阅读。前 37 项为新编译源的查询，后 7 项为缓存依赖的查询。所有结论均按实际类型保留前提。

| # | 端点末段 | P 行 | 实际前提、结论及边界 |
|---|---|---|---|
| 1 | `canonical_ae_minimal` | 576–606 | 依赖 Countable I 和给定可测响应核的逐协议 AE 因子化；不是任意不可数协议的一般识别定理。 |
| 2 | `canonical_ae_sigma_minimal` | 607–639 | 同样保留 Countable I；得到 AE 的信息 σ 结构最小性，不是经验可识别性。 |
| 3 | `canonical_kernel_sufficient` | 640–670 | 全响应向量的坐标核给出充分性；不声称有限样本能识别完整机制。 |
| 4 | `fixedPoint_unique` | 671–679 | 有限状态、每态有限非空动作及 Model 的严格折扣条件下，Bellman 固定点唯一。 |
| 5 | `p_ctl_01_causal_optimality` | 680–698 | 对声明的全体 CausalPolicy 给出无限折扣值上界，并由 greedyPolicy 达到；0<β<1。 |
| 6 | `optimal_qValue_macro_error_le_D` | 699–747 | 由同一 ApproxControlQuotient 得到最优微/宏动作值的误差半径 D；源码补核确认并非把目标误差作为额外字段。 |
| 7 | `macro_gap_certifies_micro_action` | 748–867 | 严格宏观 2D gap 是前提，推出对应微观动作的严格最优比较；不包括 gap 消失的情形。 |
| 8 | `p_core_01` | 868–943 | 有限共同好事件的概率下界及条件证书装配；H/I/Y、X/M、Obj 未被识别为同一身体。完整尾部以源码补核。 |
| 9 | `realizedMean_eq` | 944–953 | 实际后代加权计数与 realizedRow 相等；该代数等式本身不把任意参数变成合法概率。 |
| 10 | `programStep_uses_paid_repair` | 954–1018 | 给定 programBody/startState 的程序执行确实使用 paidRepair，并有账目等式；不是程序自发产生定理。 |
| 11 | `source_strongRepairable` | 1019–1028 | 指定 repairKernel、recoveredSet 和 startState 的 StrongRepairable；不包括任意损坏、boot 或资源状态。 |
| 12 | `actual_formed_candidate_family_nonempty` | 1029–1044 | Valid p 下实际响应形成的候选族存在，候选类型为 Finset PhysicalCell；不是无结构材料的身体发生学。 |
| 13 | `actual_formed_candidate_nonempty` | 1045–1067 | 上述候选族内每个候选非空；前提仍是 Valid p 及候选成员关系。 |
| 14 | `newborn_fresh_from_old_population` | 1068–1090 | 旧人口每个成员需 ValidIdentity t 才推出新生身份异于旧身份；任意 State 不自动满足该前提。 |
| 15 | `actualStep_budget` | 1091–1108 | 实际输出数量、修复/操作费用与退款的精确账目，右侧为旧 capital+5；补给属于所给模型。 |
| 16 | `descendants_length` | 1109–1116 | 实际后代列表长度等于该有限 NoiseTree 的 treeCount；不是一般现实谱系识别。 |
| 17 | `step_outputs_program` | 1117–1142 | 从给定 programBody 出发，实际 retained/newborn 的每个输出都携带同一 θ 程序。 |
| 18 | `reachable_program` | 1143–1153 | 初始 ProgramPopulation θ 与 Reachable 前提推出后继人口仍携带同一程序；保留初态不变式。 |
| 19 | `populationExpectation_eraseState` | 1154–1167 | 擦除映射与全人口期望的复合等式；不把可观察等价升级为本体同一。 |
| 20 | `attainable_test_values_eraseState` | 1168–1188 | 仅对满足 F(eraseState s)=F(s) 的测试，擦除前后全策略可达期望值集合相等。 |
| 21 | `valid_iff_probability_advantage_supercritical` | 1189–1198 | 旧 Valid 恰等于 ProbabilityValid 加 careOnly<bloomOnly 与 kc>1；成功区域限制被明确分离。 |
| 22 | `optimalRate_formula` | 1199–1210 | ProbabilityValid 下 optimalRate=max(1,max(growthRate false,growthRate true))；有环境参数条件。 |
| 23 | `actual_one_step_value_le` | 1211–1235 | 对每个实际动作，实际生成后代的加权一步期望≤optimalRate×optimalValue；从 step 生成语义得到。 |
| 24 | `actual_selected_one_step_value_eq` | 1236–1262 | 给定 optimalAction 的同一步加权期望等号；不证明未知参数下自动学习该动作。 |
| 25 | `optimal_population_upper` | 1263–1286 | ProbabilityValid 下对声明的每个 Policy、每个 State 和每个 n 给期望人口上界；不是任意物理策略。 |
| 26 | `optimal_hasExpectedGrowth` | 1287–1299 | 另需初始人口非空，最优策略具有上下常数夹住的期望增长率。 |
| 27 | `programPolicy_positive_branch_is_internal` | 1300–1324 | ProgramPopulation θ 且该 branchWeight>0 才有外部 programPolicy 与 internalGeneration 的人口一致。 |
| 28 | `founder_program` | 1325–1330 | 构造的 founderState 确实满足 ProgramPopulation θ；程序 θ 已由构造给定。 |
| 29 | `optimalRate_isLeast_uniform_upper` | 1331–1345 | 非空初始人口下，optimalRate 是全 Policy、全 n 统一期望指数上界的最小正底数；非有限期逐点最优或几乎必然存续。 |
| 30 | `false_program_attains_iff` | 1346–1364 | false 程序达到 optimalRate，当且仅当 bloomOnly≤careOnly 且 1≤kc；需 ProbabilityValid 和非空初态。 |
| 31 | `true_program_attains_iff` | 1365–1383 | 如前，true 程序达到当且仅当 careOnly≤bloomOnly 且 1≤growthRate true；临界等号保留。 |
| 32 | `same_damaged_program_repairs_and_attains_iff` | 1384–1420 | 受损 founder 的实际付费修复/费用与达到增长最优的合取，等价 programRegion；区域外不等于修复本身必然失败。 |
| 33 | `subcritical_existing_programs_do_not_attain` | 1421–1453 | 两程序自身率均<1时，二者均不达到 optimalRate；不声称全策略都灭绝或每条样本路径都失败。 |
| 34 | `same_program_regenerates_and_attains` | 1454–1538 | Valid p 与同一特定 founder 下连接修复、恢复动作及期望增长；外层为同源桥，不是无条件普遍定理。 |
| 35 | `positive_source_class_nonempty` | 1539–1543 | 存在参数 p 满足 Valid，排除这一正类为空；不证明所有参数或现实对象都属于该类。 |
| 36 | `enlarged_domain_actual_internal` | 1544–1554 | careSubcritical 固定参数实例中 true 程序达到最优，展示扩大域；属有限消费者证据。 |
| 37 | `subcritical_actual_internal_failure` | 1555–1566 | subcritical 固定参数实例中两内置程序都不达到最优；属有限反例消费者。 |
| 38 | `p_omg_01` | 1567–1580 | FailureMonotone 下，每个有限删除集失效等价包含某极小失效集；底层 V 不要求有限，但删除集 D 是 Finset。 |
| 39 | `p_ddh_04` | 1581–1668 | 所有行在同一点 B 经共同可微 ℝ² 瓶颈 z 因子化才得 rank≤2；不从任意系统推出双驱动。 |
| 40 | `p_ctl_03` | 1669–1687 | Model/ControlFamily 中给定 HJB 候选、Itô 期望式、可积/极限与选择器运行条件后验证最优；未新构造一般受控 SDE。 |
| 41 | `behavior_equiv_fitness_eq` | 1688–1695 | fitness 定义为 replicate∘response，故行为等价推出相同乘子；这一桥不证明任意现实 fitness 都只由响应决定。 |
| 42 | `greedyInvariantGOASet_nonempty` | 1696–1704 | 有限非空闭环的 invariant-law GOA 集非空；不含唯一性、混合或单一普适固定点。 |
| 43 | `exact_cached_data` | 1705–1805 | 保留有限数值/策略表实例的实际类型与一个精确 native 公理依赖；本轮未重新运行原数值计算。 |
| 44 | `exact_two_data` | 1806–1852 | 两步有限实例的 13/16 等式类型及一个精确 native 公理依赖；本轮未重新求值。 |

## 5. 省略显示与源码补核

**不能表述为“44 个类型和 12 个定义均已无省略全文打印”。** 实际日志共含 19 处 `⋯`；其中 5 个端点的类型打印含省略，其余省略在结构字段或隐式实例展开中。成功的是 44 条实际类型查询及其公理查询，不是 pretty-printer 输出了全部内核表达式。

原始日志可直接读出：预测最小性使用 `Countable I`；有限状态、各状态有限非空动作和严格 `0 < discount < 1`；`CorePointwiseCertificate` 的预测类型 `H/I/Y`、控制类型 `X/M` 和失效对象类型 `Obj` 互不等同；`ValidIdentity` 的时间限制；`State.good` 和独立的 `ProgramPopulation`；`ProbabilityValid` 不包含旧 `Valid` 的优势与超临界项；全 `Policy`、非空初始人口、期望量及最小统一增长底数。见 P1–575、P576–698、P1068–1453。

含省略的 5 项使用与本轮实际源清单逐 blob 匹配的固定源码补核：

| 查询 | 补核源码与行 | 实际确认 |
|---|---|---|
| `canonical_ae_minimal`、`canonical_ae_sigma_minimal` | `formalization/ueot-core/UEOT/V3/PredictionDependent.lean:28–58` | `Countable I`、逐协议 AE 因子化及可测解码器；未遗漏额外的普遍识别主张 |
| `optimal_qValue_macro_error_le_D` | `formalization/ueot-core/UEOT/V3/CoreOperationalAssembly.lean:201–248` | 同一近似控制商的误差半径，使用既有最优值差界和 `βD + δ = D`；结论不是输入字段 |
| `macro_gap_certifies_micro_action` | 同文件 `253–278` | 宏观严格 `2D` gap，加前项误差界推出微观动作严格比较；gap 是条件 |
| `p_core_01` 与证书字段 | 同文件 `713–863`，完整声明 `769–825` | 共好事件的概率下界；每个好样本上的估计响应、控制、路径及完整性证书；附加长期与历史端口仍有自己的条件 |

其中 `CoreOperationalAssembly.lean` 的 Git blob 为 `c596eddbec8550693b93e4d58ed87f6e400e3c23`，SHA256 为 `1f8c4f5be6d3906cdeaa6d88809cc5e0fa5f601ce8b69b21cef67a16dc7a7384`。`PredictionDependent.lean` 的 Git blob 为 `52d69b1026275f335ecd76fdac9fb3b0e4597db8`。它们同时匹配原计划绑定的源清单与精确提交的 Git 对象；见 `ACTUAL_SOURCE_READBACK_MANIFEST.json`。

P-CORE-01 在 P942 的尾部确实被深度限制省略，因此不能仅凭该打印行声称已看到全部结论。完整源码确认其余前提包括：固定微观源与满射、`FixedSourceApproximation`、非负误差、`0 ≤ εPath n ≤ 1`、同策略逐行路径误差、非空失效集、对象距离误差和严格估计裕量。结论是共好事件概率下界及逐好样本的 `CorePointwiseCertificate`，并未把预测源、控制身体和失效对象在本体上识别为同一物。旧 K2 接口／K3 包装的判断保持，不升格为一个已证明普遍共同身体的 K1 总定理。

结合已实际编译的源码身份、成功查询的精确端点名、公理结果和完整高层声明，没有剩余的显示省略会改变本次数学审查结论。无需为打印深度另跑 Lean。

## 6. 关键语义结论及停止条件

1. **身份没有扩大。** `newborn_fresh_from_old_population` 依赖旧人口中每个身份的 `ValidIdentity t`。`State` 只携带 `GoodPopulation`，不会自动赋予任意状态全局唯一身份或全部历史有效性。日志实际保留这些区别。
2. **体内程序没有被外部策略替换。** `ProgramPopulation θ` 初态、`reachable_program` 保持及正权重分支条件仍是把 `programPolicy θ` 解释为内部执行的必要桥。全策略增长上界本身不提供这一身份。
3. **增长不是在基本概率条件中预设成功。** `ProbabilityValid` 下存在实际逐行上界、选定动作等式、全策略人口上界、最优底数及程序达到的充要分类；失败区域也有实际查询。旧 `Valid` 的优势/超临界限制仍明示。结论针对期望人口，不是几乎必然存续，也不是无需给定程序、环境或评价尺度。
4. **formation 与实际出生分型。** 有响应决定能力的有限 `PhysicalCell` 候选非空，不等于从无结构材料创造身体，也不直接提供永久身份；身体生成、人口与程序继承另由实际模块的声明承接。
5. **保留边界不被本轮通过扩大。** Ω 仍是单调有限删除集合的极小失效见证；双驱动秩界仍以前提中的共同二维可微瓶颈为基础；HJB 仍需过程给出的 Itô/积分条件和选择器运行；复制桥仍以 fitness 经 response 因子化为定义；GOA 非空不含唯一性或普遍收敛。这些源码额外补核与实际查询一致。

因此本轮所需动作是登记一个新的、来源完整的 **D3 定向核验完成结论**，同时保留 v1、v2 与 continuation 的原始失败状态。无需追加全库构建、重新计算两个 K4 native 实例、增加核心公理或再开相同 K1/K2 数学合同。若将来修改这些生产定义、假设或证明，再按变更范围复核；本批没有此类修改。
