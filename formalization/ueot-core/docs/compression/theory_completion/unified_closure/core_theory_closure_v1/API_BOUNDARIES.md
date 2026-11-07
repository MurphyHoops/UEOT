# UEOT 核心理论定本：API 合同与适用边界

**实际 API 合同。** 本文约束本包声明的使用方式。正式声明名及命名空间缩写见 `THEOREM_INDEX.md`。准确源码身份、编译与公理范围由最终 manifest 和逐端点审计回执登记；本文不充当第二份发行清单或第二套 GI。

## 1. 原始输入与已经消去的来源前提

本源允许输入物理 Body、初态、原始噪声参数和合法政策。允许政策的非负/归一条件是“它确实是概率行为核”的类型要求，不是成功或最优性的来源假设。

最终消费者不接受未履行的 success、faithfulness、fitness、条件均值、Perron 特征对或最优选择器作为源字段：

| 所需事实 | 本源履行方式 |
|---|---|
| 程序内容与行为 | `Triple/Body` 的实际码位；`programStep` 在恢复后调用 `rawExecute`。 |
| 有限可支付恢复 | 按真实写位/开门计费；`step_budget` 与 `programStep_uses_paid_repair`。 |
| 忠实遗传 | 实际恢复原码复制后施加规定损伤；`copied_code_faithful`。 |
| 合法概率与条件矩 | `noiseWeight_pos/sum`，真实 Option Body 计数及 `realizedMean_eq`。 |
| 继续行可实施、本原、最优 | `selector_actual_raw_execution`、`selector_same_wallet_affordable`、`source_primitive`、旧 PF 工厂和有限单行替换。 |
| 真实人口反馈所需均值/矩 | `treeCount`、`treeMean_program_succ`、实际 cohort 乘积律与局部有界后继。 |
| 形成 seed/cover | 真实八码读取与实际新生响应；零缺陷、非恒响应和非空父候选均有源证明。 |

通用概率与代数引理可以保留显式前提。例如 `Prob.iid_badRatio_mass_le` 接受均值与二阶矩数据；`F.actual_cohort_feedback` 从实际源证明这些条件后消费它。不能把前者单独贴上“真实来源闭合”的标签。

## 2. 正类、物理状态与输入合法性

`S.Valid p` 公开要求
\[
0<\delta<s<1,\quad 0<b,\quad b+\gamma<1,\quad
\delta<\gamma,\quad 0<q<1,\quad s+b>1.
\]

这些是原始噪声参数的严格不等式，构成非空开放类；有理点
\((3/4,1/8,3/8,1/4,1/3)\) 的合法性已经形式证明。后续主要正结果不是仅对此点的计算。

源运行函数 `step` 对更多物理 Body 也有定义，但人口控制正类的 `Canonical` 限定为 `programBody theta kind tag`：两行声明码、允许的一次活动位损伤、主门、可信 bootstrap 和静默 tag。不要把 canonical 正结果延伸到任意多位破坏、任意硬件损坏或任意初始钱包。

若省略 `Valid`，某些和式仍可作实数代数恒等式，不能据此把可能含负权的式子解释为概率。例：`noiseWeight_sum` 的归一恒等式自身不证明非负性。

旧证明中的标准 Borel、可数生成、有限/可数动作和 fresh/记忆协议条件继续保留。本有限源不扩张它们的范围。

## 3. 运行接口、允许信息与私随机

### 3.1 哪些接口是实际事务

完整请求 API 是 `step`，内部程序 API 是 `programStep`。其结果是 `LocalResult`，再由 `Population.liftResult` 生成真实 retained/newborn 名单。

`executedResult` 是已接受非 stop 事务的内部构件；单独调用它没有检查 bootstrap 或预付 cap。尤其不能用 `executedResult x bloom` 绕过 D/bloom 的七单位请求上限。要声称合法执行、付款或全策略结果，必须使用 `step`/`programStep` 及其桥。

`programAction theta kind` 是证明中对行为的描述。真实内部程序的请求来自物理多数码，执行来自恢复后的活动码位；运行项没有读取一个隐藏 θ 标签。

### 3.2 政策可读数据

`C.Policy.kernel` 的数据参数是当前人口长度、完整公开收据历史、当前 `ObservationWord` 和待赋权的请求字。观察包含六码、主门和 bootstrap。审计身份、不可见 tag、未来世界原子不是政策参数。

政策允许对同一人口的请求进行任意实概率联合随机化；没有限制为有理数，也没有假设各个体请求彼此独立。当前世界噪声在请求后取样，`branchWeight` 将请求核与独立原始世界原子相乘。不能把“私随机”解释成读取未来噪声或世界审计字段的许可证。

新端点直接处理上述全允许历史行为核。它不新增任意非可测程序或任意额外隐藏状态控制器的可测实现定理；旧完整历史与私随机实现结果按原合同保留。

### 3.3 外部达到政策与内部达到程序

`bestPolicy` 可对任意 canonical 人口发出 H/bloom、D/care 的公开请求，不会重写亲本的遗传码。若要声称这是**同一个内部程序自主执行**，还必须用 `ProgramPopulation true`、`best_step_is_programStep`、`attaining_generation_is_internal` 或 `bestPolicy_positive_branch_is_internal`。

共同恢复/增长见证由 `CoreTheoryClosure.same_program_regenerates_and_attains` 使用真实损坏 θ1 创始体和同一六单位账本。`bestPolicy_positive_branch_is_internal` 与 `reachable_program` 连接全部实际可达执行。不能拼接 θ0 的恢复、外部优化器的增长与另一初态的钱包。

## 4. 资源、停止与拒绝

每旧体带一单位资本，环境显式流入五单位。恢复一次损坏体花三单位；care 花一、bloom 花二；最多两个后继各需一单位预留。H/care、H/bloom、D/care、D/bloom 的 cap 分别为 3、4、6、7。

- **stop：** 输出空名单，零修复/操作费，退还六单位。
- **拒绝：** 不读取该次世界原子；保留旧 Body 和旧一单位资本，退还五单位环境输入。拒绝不推进本模型的执行年龄。
- **执行：** 从同一余额支付真实修复/操作与实际后继资本，剩余款项归环境；死亡不会把余款变成免费新生资金。

所有这些分支都在 `step_budget` 与 `generation_budget` 中保留。原生核对也检查逐前缀余额，不只核最终净余额。

`row` 与 `eventMean` 描述被接受继续事件的 L/B/M；全菜单必须用 `realizedRow` 与 `realizedMean_eq`。D/bloom 的全菜单行是 \(e_D\)，不是 bloom 的继续行。

条件 \(s+b>1\) 的作用是让拒绝单位行也受同一 \(\lambda_*>1\) 的繁殖值上界支配。亚临界反例保留，不删除拒绝，不将它改成死亡。故不能把增长最优定理移到任意亚临界参数。

各个体的局部账户与每体环境分配是明确的物理规则。两个各自可支付 cap=6 的请求不能据此同时使用唯一共享总钱包 6。逐行可实施结论依赖该真实资源结构。

有限初始 n 体至 T 的环境输入不超过 \(5n(2^T-1)\)，另有 n 初始资本。无限期指数增长依赖持续开放输入。本包不证明封闭有限总资源可以无限增长。

## 5. 恢复核的准确相位与失败边界

`RepairState` 包含真实 Body 和 `Fin 7` 余额。`paidRepair` 是真实程序在读取存活/出生噪声前使用的收费恢复阶段，`programStep_uses_paid_repair` 将该阶段连接到实际输出。

healthy rank=0、damaged rank=1 指这个阶段的 `StrongRepairable/repairRank`。之后的真实生存/出生原子仍可能输出零个后继；rank=1 不等于全人口必然存活、永远健康或概率一最终繁盛。

可信 bootstrap 仅含有限多数/读写/开门基元，不保存正确 θ。允许损伤保留多数信息，恢复依赖这份真实冗余。原始活动码和主门都实际影响执行；不是修复一个无效类型标签。

bootstrap cut 的损坏状态在该恢复核中为目标外自环。余额仅二且当前阶段不追加供给时也无法支付恢复。它们不能被读成“未来获得额外足额资源仍永远不能恢复”。

全码擦除可把两个原程序变成同一物理态。`no_decoder_recovers_both_erased` 排除仅依该态的确定解码器同时还原两个不同原程序。此边界须保留“无额外正确副本或区分历史”的信息条件；不能悄悄给 decoder 一个 θ 或成功标签。

原 `OperationalFormedPersistentParent` 的 sure-persistence 条件保持。没有把带真实死亡的完整人口过程强塞进该旧结构并声称永存。

## 6. 形成与对象解释的范围

形成消费者的 `SourceHistory := Bool × Bool` 是两个程序 × H/D 的四个真实初态，tag 固定 false。`sourceResponse` 是同一 `programStep` 在 36 个原子上的实际下一次新生事件律。

完整物理读取的零缺陷、部件 cover、两程序非恒响应，以及空物理载体的严格正缺陷都由源证明。既有有限最小化生成非空候选族，而且每个生成父候选均非空。

这没有证明：

- 所有任意物理损坏态都有形成候选；
- 该一次新生响应就是所有未来能力的 C1 最小预测状态；
- 形成候选唯一，或与唯一自然/形而上对象边界相同；
- 具有任何存在条件就强制任意允许干预族有非空失效族 Ω。

不可观察或无能力相关性的 cut 可以留下空失效族；两书公开保留这一强版修订。

## 7. 原身份、出生、普查时钟与继承

`Member.identity`、`parent`、`bornAt`、`age`、`ancestry` 与有限身体类型分开。

retained 保持同一身份、原父指针和出生时刻；执行 retained 时增加执行年龄。新生取得新身份，指向实际亲本，出生时刻为下一普查，年龄零。新生进入下一递归轮，不能在出生普查再次执行。

`newborn_fresh_from_old_population` 使用旧身份的 `ValidIdentity` 条件。任意不满足此条件的手造列表不获得“全局新鲜真实人口”的解释。

L 计同体续存，B 计严格新生，M=L+B。旧 P8 的实际实例明确区分两者。不得将 M 的全部正边称为 `OffspringOf`，也不能只用一个无标记 M 恢复出生谱系。

遗传程序保持来自真实码复制。外部 override 请求不把遗传码免费换成最优标签。无变异或迁入时，初始支持外的程序不会出现。

本轮是明确的新人口普查时钟，不冒称旧 Register 串行 dispatch 的保守扩展。PR441—443 的源语义、钱包和已完成合同没有因此被重写。

## 8. Perron、最优性与有限条件鞅

一般 `G.exists_optimal_selector` 要求有限、非空的逐行动作族及每个继续选择器的本原性。这是一般条件定理；本源另证明观察可区分 H/D、每个选择器由实际码实现、在同一钱包可支付以及每个继续矩阵严格正。

继续菜单先取 H 的 care/bloom、D 的 care。完整请求菜单仍含 stop 和 D/bloom 拒绝，通过源证明的行上界扩回；不能说 stop 或所有全菜单矩阵本原。

`certificateOfPrimitive` 构造同一矩阵的既有 Perron 对象。抽象最大根选择器可为非计算数学选择；实际达到者是已编码的 θ1。不能把存在性工厂说成已运行的优化算法。

`actual_supermartingale` / `actual_martingale` 证明每个有限允许历史节点的条件均值不增/取等，且 W 非负。`populationExpectation` 从相同 `State/Branch/next/branchWeight` 递推有限时域期望。它们没有额外宣称共同无限路径空间上的 Mathlib `Martingale` 实例或几乎处处收敛。

最优期望人口有正指数上下界需要非空初始人口；空人口只给零过程。该结论的对象是期望人口增长率，不是实际样本必不灭绝或每个样本都按该指数增长。

同一健康 θ1 身体上，care 的原身份一期续存概率 \(s\) 严格高于最优增长请求 bloom 的 \(s-\delta\)。此反例只比较原身份的一步续存，不把它泛化为 bloom 的一期人口非灭绝率或无限期谱系存活更差。

## 9. 实际标记谱系与 Doob 解释

`actual_marked_many_to_one` 的左端是同一 `NoiseTree` 上 `Population.descendants` 实际返回名单的加权和。测试 F 读取成员 ancestry 的 \((\mathrm{newborn},\mathrm{targetKind})\) 列表；最优程序限定为 θ1，初始 Member 的 body 为对应实际 `programBody true i tag`。

\[
E\!\left[\sum_{u\in\mathcal P_T} r_{i_T(u)}F(\tau_u)\right]
=\lambda_*^T r_{i_0}E^{Q^L,Q^B}_{i_0}[F].
\]

标记核 \(Q^L,Q^B\) 先由实际 L/B 构造，再证明合计质量一；遗忘标记恰为旧 h-transform。固定初始类型可预置到身体路径，有限多创始体按初始繁殖值作线性混合。

这不是：

- 从总均值矩阵递推单独推出父指针；
- 用无标记 Q 计算读取 retained/newborn 标记的 F；
- 普通活体均匀抽样、实际人口比例或原动作可实施核；
- 对无限路径、任意程序族或任意新噪声相关结构的新增定理。

用 \(r=(k_b,k_c)\) 时，\(\nu r=\lambda_*\)，加权谱系平稳分布为 \(\nu_i r_i/\lambda_*\)。只有采用对应配对归一才可简写为 \(l_ir_i\)。本源具体 Q 的身体分布 \((20/29,9/29)\) 不等于普通后继类型分布 \((2/3,1/3)\)。

## 10. 真实选择：两程序、有限 T、付费独立 cohort

本轮新来源选择消费者有两个固定忠实程序，cohort 是一健康 θ0 创始体和一健康 θ1 创始体。程序外部控制的增长比较与固定遗传程序的自主选择反馈分别验收，不把外部 override 等同于基因替换。

`treeMean_program_succ` 从实际继承事件导出均值；`lower_mean_share_tendsto_zero` 是归一化**期望数量**中低程序份额的极限。它不等于期望比例，更不等于每个有限群体的几乎处处无限期选择。

实际比例界基于 n 个独立、同构、分别出资的完整 cohort：
\[
P(\text{零人口或比例偏差}>\varepsilon)
\le
\frac{9\{\mathrm{Var}(X_{\theta,T})+\mathrm{Var}(X_T)\}}
{n\varepsilon^2\mu_T^2}.
\]
该新源端点选取 θ0 的实际计数。结合源均值集中使用常数 36 的选择失败界，量词顺序是**先选有限 T，再选 n**。`exists_finite_cohort_selection` 履行所需均值条件，不将其重新裸给。

单 cohort 两个实际后继槽及整个 cohort 的独立乘积律都明确存在。同父体内部的相关事件没有被删掉；粗二阶矩界由每体至多 \(2^T\) 的实际后继界给出。共同噪声若破坏 cohort 独立性，不能原样使用 iid 界。

n 个 cohort 有 2n 个创始体，其初始资本和至 T 的供给上界为
\[
n[2+10(2^T-1)].
\]
增加 n 不是固定钱包中的免费复现实验。

同源有限反例保留：

| 量 | 在指定健康两创始体有理实例中的值 |
|---|---:|
| θ1 单体一期完全灭绝 | \(9/64\) |
| θ1 灭绝而 θ0 一期仍非零 | \(243/2048\) |
| 两程序共同零人口 | \(45/2048\) |
| 零人口比例扩为零后的期望高程序比例 | \(2095/4096\) |
| 条件非零人口的期望高程序比例 | \(2095/4006\) |
| 归一化期望计数 | \(10/19\) |

不能把“低程序一期仍非零”改成“低程序永久存活”。\(9/64\) 以健康 θ1 起始；共同再生/增长见证从损坏 θ1 起始，当期执行 care，二者不能混用。

## 11. 合法商必须保持联合记录及策略权限

本商只删对事务无影响且控制器不可读的 tag；六码、主门、bootstrap、动作、付款、退款、标记、身份、父指针和历史保持。

`step_joint_record_commutes` 是同一原子上的完整记录等式，强于一阶矩交换。`source_L_B_M_intertwining` 分别保持 L、B、M；不能只用 M 的交换推断方差、灭绝、计数比例或真实谱系分布保持。

原始类型 \((i,\mathrm{tag})\) 的 tag 忠实复制，展开矩阵为两个可约块。商向量可以拉回为一个正特征向量；不能借商块本原性声称整个展开矩阵本原、根简单或唯一正射线。

同一观察历史核在两表示间双向使用。当前源码的 `C.eraseState` 只改变每个 Body 的隐藏 tag，完整公开历史保持；`C.eraseBranchEquiv` 对同一请求字与原始噪声字重索引。`C.branchWeight_eraseState` 与 `C.next_eraseState` 分别证明权重不变和实际下一状态交换。

`C.populationExpectation_eraseState` 对任意有限 n 及任意 `F : State → ℝ` 给准确推前：商初态的 F 期望等于原过程的 `F ∘ eraseState` 期望。它容许测试整个终态审计状态，包括累计公开历史和身份／祖先字段；不主张隐藏标签自身的值不变。`C.protected_test_expectation_eq` 再要求 F 标签不变，由 `C.attainable_test_values_eraseState` 得同一个完整 `Policy` 比较类的可达值集合相等。

`C.census_test_expectation_eq` 与 `C.public_history_test_expectation_eq` 分别给计数、零人口及任意计数测试，以及完整请求／修复费／操作费／退款／标记输出收据历史的保持。因此本条有限记录律结论来自实际 `State/Branch/branchWeight/next` 的递归运输，不只来自矩阵交换。其概率解释仍要求原权重合法；更宽参数上的代数等式不会把负权变成概率。最新依赖链和公共消费者的真实编译与公理身份由 [VALIDATION.md](VALIDATION.md) 绑定。

`CoreTheoryClosure.lifted_source_value_pos` 和 `expanded_source_eigen` 将同一 sourceValue 拉回静默标签展开；它们没有消除展开矩阵的忠实标签块。

删掉 H/D 会丢失 cap 区别；只保留解码内容会丢失执行门区别。这些是本源已有反例，不允许把普通预测等价普遍提升为组织与控制价值等价。

## 12. 原合同、解释责任与可信交付

公共使用入口是 `import UEOT`。本轮最小导入边位于 `UEOT.V3.Compression.TheoryCompletion`，导入 `CoreTheoryClosure` 后传递包含十三个新模块。`UEOT.V3` 本身不导入 Compression；检查四个现有根的编译并不要求改写它们的层级，使每一个根都直接或间接导出所有新模块。

原全 Core 条件合同及 PR441、PR442、PR443 已完成状态保留。C1 的可测/记忆条件、C5 的必要秩及规范条件、一般 Perron、连续来源、实际生命周期及原 Price 结论继续按原来源使用。

十三新模块没有新增 C1/C5 或新 census Price 的直接实例；不要因共享 import 图而登记这些为本轮新结果。直接复用的旧工具是 Perron 工厂、repair rank、formation/cover、P8 身份区分和正特征结构/Doob。Price 恒等式本身也不等于适应或真实必然选优。

增长最优是有来源的一条目的分支，不替代规范价值、主体经验、旧折扣 J、存活或其他允许目标。规范和主体桥接由独立哲学论证承担，不写成 Lean 推论。

合成精确验证不是经验支持。当前实际原生回执覆盖完整局部菜单与程序输出、真实身份/父指针、逐前缀付款、两轮时钟和因果 cut；它不代替参数化证明或自然系统校准。新结果的经验支持是 **UNVERIFIED**。

本包构建报告必须区分：

- 变动模块与必要消费者的实际编译；
- 公共入口导入和逐端点 `#print axioms`；
- 原生程序执行与独立有理数检查；
- 两书文本及 PDF 构建、视觉核验；
- 静态扫描或增量复用。

不得把静态检查叫全仓重编译。旧 PR443 已披露的 native_decide 信任只按原端点的实际依赖登记，不能因一个共享 import 就说所有新端点都依赖它，也不能在未打印前宣称全部消失。

最后的结题状态由 master 七出口的真实证据决定。发行、工作区和原 GI 必须以实时事实为准；原 memory.py、CURRENT 的 CAS、独立完整 recall 和唯一 CONTINUE 接续由协调者完成。本文不写入另一套记忆、不预设发布成功，也不把尚未履行的核心正命题改标为 COMPLETE。若仍保留但未解决，应准确标为 **UNRESOLVED**。
