# 主张、前提、实际消费者、反例与信任范围

本表与 [CLAIM_STATUS.md](CLAIM_STATUS.md) 的内容终态配套。它检查一条主张到底使用什么原始输入、在哪里履行来源前提、由哪个实际消费者承担，以及哪些反例限制外推。命名空间缩写和完整声明定位见 [THEOREM_INDEX.md](THEOREM_INDEX.md)；这里的 `S`、`C`、`F` 等均是该索引的书面缩写，不是新增 Lean alias。

本表不是新的总证书。每一行的形式、运行、书稿和发行证据分别承担责任；七项出口的实际完成状态由 [FINAL_ACCEPTANCE.md](FINAL_ACCEPTANCE.md) 登记。

## 1. 证据与信任口径

| 记号 | 证据类型与可作的判断 | 不能据此作的判断 |
|---|---|---|
| L | 当前源码中的类型化声明及其实际 Lean 编译；公理依赖以对应端点的 `#print axioms` 和 [VALIDATION.md](VALIDATION.md) 为准。 | 静态声明名核对不等于编译；共享 import 不证明两个定理具有相同公理依赖；旧 PR443 的封闭数值信任不自动扩展到全部新端点。 |
| X | `native_protocol/lean_native_execution.json` 与独立 `native_source_check.json`：实际解释执行、序列化和逐字段核对；保留编译执行器与检查器的实现信任。 | 不代替参数化证明；不代表自然样本；这里的 Lean 原生运行不等于 GI 原生自主完成。 |
| R | `native_protocol/source-feedback-probe.json` 的独立有理数递推及有限数值例。 | 不代表实际展开了所需大规模人口路径，不消除初始材料与供给需求，也不是经验普适支持。 |
| B | 两书正文的数学说明、精确书面反例或独立哲学论证；分别注明其论证层次。 | 不能因写入书稿就升级为 Lean 定理；哲学论证不能由数学库代签，形式证明不能确认自然普适性。 |

所有行的自然经验支持均为 **UNVERIFIED**。L 的最终逐端点信任范围、公共入口构建，及 X/R 的准确源身份采用实际回执；本表不预填公理计数或声称全仓清缓存重编译。

## 2. 同源组织、事件与允许控制

| 保留主张 | 明确的原始前提 | 履行来源前提的实际消费者 | 反例或不外推的范围 | 信任与证据 |
|---|---|---|---|---|
| 程序与主执行门可损坏并恢复；恢复确实影响行为。 | 两行实际六码、允许的活动位损伤、仍保存区别的多数备份、有限可信 bootstrap、当前恢复阶段的足额余额；不是任意毁损。 | `S.programStep` 读取真实多数码，收费恢复后调用 `rawExecute`；`S.active_code_is_causal`、`S.main_gate_is_causal`、`S.same_program_restores_then_reads` 与 `S.programStep_uses_paid_repair` 连接实际运行。 | `S.no_decoder_recovers_both_erased`：相同全擦除态无额外信息不能恢复两个不同原码；切断 bootstrap 和阶段资金不足阻断恢复。 | L：源／Repair 端点；X：活动码、门、bootstrap、擦除四类真实 cut；B：哲学第七章的有限可信底座。 |
| 非空恢复域与真实付费 rank。 | `RepairState` 中的 Body 与有限余额；目标是噪声读取前的恢复阶段。 | `S.source_strongRepairable`、`S.healthy_repairRank_zero`、`S.damaged_repairRank_one` 消费旧 repairRank 工具；损坏态花三单位恢复、余下三单位支持 care 及两个输出资本。 | `S.bootstrap_cut_not_repairable`、`S.underfunded_not_repairable`；局部 rank=1 不证明后续无死亡、永久健康或全人口永存。 | L：真实相位核及旧工具；X：逐付款前缀和退款。 |
| 非平凡物理形成及非空父候选。 | 两程序 × H/D 的四个源初态，tag 固定 false；实际部件读取、36 原子噪声律及下一次新生响应。 | `S.full_physical_seed_zero_defect`、`S.physical_children_cover_seed`、`S.sourceResponse_nontrivial` 供给旧形成工厂；`S.actual_formed_candidate_family_nonempty` 与 `S.actual_formed_candidate_nonempty` 给真实非空结果。 | `S.empty_physical_defect_pos` 排除空载体；不主张任意损坏态、所有未来实验或唯一自然边界。 | L：Formation 与旧 finite cover／形成工具；X：实际新生与 cut；B：对象与组织分层。 |
| 同一真实续存、新生与资源源生成 L/B/M。 | 完整噪声类别、实际 cap、每旧体一单位资本和五单位明确外供；失败、拒绝、stop 都在源中。 | `S.executedResult_count`、`S.retainedMean_eq`、`S.newbornMean_eq` 给被接受继续事件的矩；`S.realizedMean_eq` 与 `C.generation_budget` 回到包括拒绝／stop 的完整事务。 | D/bloom 需要七单位而实际仅六单位，故为保留原体的单位行；不能用其未经 cap 检查的继续行替代。M 不减去 price×cost 后仍称人口均值。 | L：源计数和钱包守恒；X：全部请求与内部程序路径、720 次执行／288 次停止／144 次拒绝、5,508 个付款前缀。 |
| 有限谱优化给实际可实施达到者和完整请求上界。 | 有限逐行动作族、可区分 H/D 的真实观察、各体独立登记的钱包；`S.Valid p` 给真实继续矩阵的正性及拒绝支配条件。 | `GS.selector_actual_raw_execution`、`GS.selector_same_wallet_affordable` 与 `GS.source_primitive` 履行行实现和 PF 输入；`G.exists_optimal_selector` 调用既有 Perron 工厂；`GS.actual_row_bound` 将 stop／拒绝纳入，θ1 实际达到。 | 抽象有限最大根选择不是已运行的 `Classical.choose` 算法；stop 和忠实程序总矩阵不被称作本原；共享总钱包未获相同逐行组合结论；亚临界拒绝优势保留。 | L：有限谱证明及 SourceConsumer；X：θ1 实际两行程序和矩；R：有理点增长率。 |
| 允许完整历史控制下的条件超鞅／鞅与期望人口指数界。 | 全部 `C.Policy` 只读允许公开历史及观察，请求先于独立世界噪声；合法参数与非空初始人口，空人口另处理。 | `C.generation_expected_bound`、`C.next_expected_bound` 从实际分支履行一步矩；`C.actual_supermartingale`、`C.actual_martingale`、`C.actual_population_bounds` 与 `C.actual_growth_constants` 在同一有限法则上结论成立。 | 这是有限历史节点的条件核性质，没有新增共同无限路径空间上的 Mathlib `Martingale`；期望增长不保证单样本增长、无限存活或规范价值。 | L：实际 State／Branch 递推与正势；B：数学总论四对量词和对象的区分。 |
| 再生与增长由同一个实际程序共同见证。 | 同一个受损 θ1 创始体、同一六单位账本及 `S.Valid p`；后继保持真实继承程序。 | `T.common_founder_is_actual`、`T.same_program_regenerates_and_attains`；`C.best_step_is_programStep`、`C.attaining_generation_is_internal`、`C.reachable_program` 与 `C.bestPolicy_positive_branch_is_internal` 连接后续内部执行。 | 不拼接 θ0 的恢复与另一个外部优化器；反馈的两健康创始体是另行声明的同源 cohort，不偷换共同见证的损坏初态。 | L：共同消费者及内部程序桥；X：实际解释器和同钱包；B：数学总论六及哲学附录 C。 |

## 3. 身份、选择、谱系与表示

| 保留主张 | 明确的原始前提 | 履行来源前提的实际消费者 | 反例或不外推的范围 | 信任与证据 |
|---|---|---|---|---|
| 续存与新生有不同身份语义，忠实传递由复制产生。 | 真实 `Member`、当前普查和合法初始身份；当前出生下一 tick 才行动。 | `P.retained_identity`、`P.newborn_actual_parent`、`P.newborn_fresh_from_old_population`；`S.copied_code_faithful`、`C.generation_program` 与 `C.reachable_program` 由实际复制／损伤保证程序支持。 | retained 不是严格 OffspringOf；非法手造身份列表不获全局新鲜性；无变异或迁入不创造初始支持外程序。 | L：人口、来源与旧 P8 实例；X：真实 id／parent／年龄／时戳／ancestry、两轮 2→4→8。 |
| 两个忠实程序的均值排序由真实继承树产生。 | 两个固定物理程序、共同噪声制度和普查时钟、每个真实后继槽的来源律；各身体块本原。 | `F.treeMean_program_recurrence` 与 `F.treeMean_program_succ` 从 `programStep` 输出树求矩；`F.growthRate_order` 和 `F.lower_mean_share_tendsto_zero` 给均值份额集中。 | 整体按程序分块可约；不是任意程序族／任意生态的新定理。归一化期望计数不等于期望随机比例。 | L：源树和反馈；R：65 个有限时域的实际输出矩递推。 |
| 含零人口的实际有限时域选择概率界。 | 每 cohort 各一健康 θ0、θ1 创始体；独立同构且分别供资的 cohort；真实有界后继给有限二阶矩；先固定有限 T，再选 n。 | `F.actual_cohort_feedback` 履行通用 `Prob.iid_badRatio_mass_le` 的全部矩与均值前提；`F.exists_finite_cohort_selection` 在证明内选择 T 和 n；`F.actual_sample_resource_bound` 核算供资。 | 共同噪声破坏 iid 时不能照用；固定有限 n 的无限期必然选优未证明；n 增大不是免费复现实验。 | L：常数 9／36 的源消费者；R：T=31、n=13,338 的精确矩例及资源上界 286,431,368,863,536，未展开该规模完整人口路径。 |
| 最优程序可先灭绝，三种“比例”不同。 | 与正类相同的有理参数点，两个健康独立创始体；零人口比例明确作零扩展或条件非零。 | `S.actual_best_extinction_pos`；`B.concrete_zero_population`、`B.concrete_best_extinct_inferior_nonzero`、三个具体比例与 `B.expected_ratio_ne_ratio_expected_counts`。 | 高增长程序先灭绝而低程序仍非零的 243/2048 不意味低程序永久存活；健康 θ1 的 9/64 不套给损坏共同见证。 | L：同源精确有限定理；X/R：45/2048、243/2048、2095/4096、2095/4006、10/19 的实际输出交叉核验。 |
| 带真实父指针和 retained/newborn 标记的有限 many-to-one。 | θ1 的实际物理程序、同一有限噪声树和 Member 祖先记录；正生殖价值及源 L/B。 | `L.pathMean_eq_actual_descendants`、`L.pathMean_program_eq_lineageMass`、`L.actualRightEigenData`、`L.markedKernel_total` 与 `L.actual_marked_many_to_one` 由实际名单构造标记核。 | 无标记 Q 不能测试出生标记；统计加权谱系不等于普通活体均匀抽样、实际人口比例或原允许动作可实施核；未新增无限路径谱系定理。 | L：实际来源与既有正特征／Doob 工具；X：父指针与标记；R：普通身体组成 2/3、1/3 与谱系 20/29、9/29 的区别。 |
| 合法静默标签商保持完整记录与有限法则。 | 只删除控制器不可见、对实际事务无效的 tag；保留身体码、门、bootstrap、同一动作和噪声；概率解释使用合法源条件。 | `Q.step_joint_record_commutes`；`C.eraseBranchEquiv`、`C.branchWeight_eraseState`、`C.next_eraseState`、`C.populationExpectation_eraseState` 逐步推前实际 State／Branch／next 法则。 | 一阶矩交换本身不够；终态测试先复合 `eraseState`，隐藏 tag 值本身不保持。删 H/D 或主门的映射分别丢失 cap 和执行区别。 | L：局部联合记录及完整有限历史运输；实际编译绑定最终依赖链；B：数学总论六。 |
| 同一全策略集合的受保护测试值等价。 | `F (eraseState s)=F s`；同一完整 `Policy` 比较类与公开历史，未引入额外传感器或修改权限。 | `C.policy_kernel_eraseMember`、`C.protected_test_expectation_eq`、`C.attainable_test_values_eraseState`；计数与收据历史分别由 `census_test_expectation_eq`、`public_history_test_expectation_eq` 实例化。 | 不只验证某一个最优政策；但也不保证任意被隐藏字段依赖的评价保持。标签展开可约，不继承商块的本原性／唯一正射线。 | L：双向可达值集合与具体测试；`T.expanded_source_eigen` 只给同源正向量提升。 |

## 4. 原 Core 保留结果与独立解释责任

| 保留主张 | 明确的前提与范围 | 本轮使用关系／实际消费者 | 反例或不外推的范围 | 信任与证据 |
|---|---|---|---|---|
| 完整历史预测、C1 最小充分性、对象与身份接口。 | 原标准 Borel、可数生成、协议及 fresh-future／继续记忆的不同量词保持。 | 原 `MeasurablePredictiveHistoryCanonical` 等已闭合结果直接保留；新人口区分有限身体类型、永久身份及允许观察，没有伪造新增一般 C1 实例。 | 不保证唯一自然划分；同预测不自动等于同控制记忆、同个体或同组织能力。 | 原已发布 L 证据复用；本轮未将旧模块全量重编译作为新贡献。数学第 0—31 章和 106 个冻结 P-ID 映射不改。 |
| Ω 的操作性失效结构与组织解释。 | 声明能力、允许干预及单调失效结构；非空失效须另有条件。 | 原 `OmegaMinimalFailure.p_omg_01` 保留；新真实恢复、cut 与形成消费者补强组织分支。 | 数学总论中 q(x,u)=x、允许 cut 只改 u 的非退化书面边界，否定“持续必使该操作族 Ω 非空”；该书面例不冒称本轮新增 Lean 端点。 | 原 L、新组织 L/X；B：数学明确反例与哲学第四章的公开修订。 |
| Π／Φ、秩条件、规范与校准。 | 原 C5 的低秩、独立锚定、单位及噪声条件。 | 原逆分类、GL 规范和实际锚定结果保留；本源的两个身体类型不被当作新的自然双驱动证明。 | 秩大于二拒绝二维解释；兼容不等于唯一识别，自然界普遍二维未获支持。 | 原 L 与数学旧章复用；B：哲学第十二、十三章说明评价与锚定责任。 |
| 目的、GOD、GOA、Price 及已声明连续模型。 | 各自评价、过程、稳定性、谱、正则性和资源条件保持。 | 原全 Core 条件合同与 PR441—443 不重开；新源只增加真实增长分支、同源标记谱系和两程序反馈，没有重新证明一般连续过程或新 census Price。 | Price 不等于适应；有限继续增长不代替旧折扣 J、存活、QSD 或普遍唯一吸引子；不可从标准数学换名宣称新自然律。 | 原 L 证据与本包明确的新 L/X/R 分工；旧原生数值信任按原端点保留。 |
| 主体经验、理由、意义与规范。 | 公开概念区分、正面理由、强反对和回应；实际承受者及公共可修订性。 | 哲学六编三十章独立论证；对象—组织—目的的数学约束用于澄清可行联系，不替代理由。 | 增长优势不推出正当性，功能组织不自动证明主观体验，形式核心不宣称绝对伦理或通用意识完备。 | B：独立哲学论证；自然经验仍 UNVERIFIED。 |

## 5. 交付与归因边界

原始总纲、旧成功与失败记录、旧条件合同和本轮参数正类同时保留。`MASTER_PLAN.md` 的历史计划状态不是当前结果状态；同样，内容上采用 `CLASSIFIED_CORE_CLOSED` 不能替代公共构建、真实公理审计、两书产物、独立审查、发行和原 GI 接续。

本包原数学、书稿和 Lean 运行成果保留外部 Core 会话来源。一次 GI Core 工具的控制流程已完成，但其观察为 `REJECTED / EDIT_ROOT_NOT_PUBLICLY_REACHABLE`、无补丁、`claim_consumption=NONE`；后续公共入口修复属于普通外部工程集成。两种来源不相互改记，执行与重放成功不自动变成候选成功。该拒绝不撤销已成立的数学结果，也不授权重跑用完的原请求或增加预算。

最终实际状态使用 [FINAL_ACCEPTANCE.md](FINAL_ACCEPTANCE.md)、[VALIDATION.md](VALIDATION.md) 和 [DELIVERY.json](DELIVERY.json)。如果仍保留的核心正命题在验收中出现实质未决，应明确记录 `UNRESOLVED`；已排除的任意生态、固定有限群体无限期必胜、开放创新、领域应用和普遍自然律不自动成为新的退出条件。
