# 有限支持固定点、完整有限记忆与实际部署：本批结果及边界

状态：**PROOF_AND_LOCAL_PRODUCTION_INTEGRATION_ACCEPTED**。精确 Git 候选、PR 和 resulting-main 的发布记录单独保留。
本文件是本批结果说明；每次实际执行的原始状态、源码和日志另行保留，不能由本文件覆盖。

## 1. 数学责任与原始 Core 的关系

原始 Core §8.5 的 P-PER-03 在有限、完全观察的状态空间上消去不能保持安全域的状态，得到物理安全可行核。本批处理部分观察下的实际认证行占据：同一观察对应的一组可能状态必须共享行动，而且未来每个非空观察分支都要可继续。记忆对象因此是支持集合，停止界计算支持数量。

已合并的 `InfiniteSupportViability.lean` 已证明固定非自治数据下的无限一致策略。本批复用其所在的实际支持、完整历史和部署行律接口，并补上支持齐次时的有限停止界、完整有限记忆实现与有限决策程序。它没有重新声称一般量词交换尚未完成。

## 2. 固定关系上的有限最大固定点

固定有限状态类型 X、观察 q : X → Y、支持关系 R : X → A → X → Prop 和认证 C : X → A → Prop。Y 可以无限。纯关系层不需要 A 有限。

令 Bq 为非空且包含在同一观察纤维内的状态子集族，M = |Bq|。实际后继关系为

\[
U(S,a,y)=\{z:q(z)=y,\ \exists x\in S,\ R(x,a,z)\}.
\]

定义 F(W) 为存在一个行动认证整个 S、并使每个非空 U(S,a,y) 属于 W 的 S ∈ Bq。Lean 证明 F 单调，W₀ = Bq、Wₖ₊₁ = F(Wₖ) 递减，在 M 步时稳定；从此每个 K ≥ M 的迭代都相等。所得 W* 是最大固定点，包含每个后固定集合 W ⊆ F(W)。

有限时域后向可行性与 Wₖ 成员身份等价，因此一个支持在 W* 中，当且仅当它对所有有限剩余时域可行。这里没有把固定点存在或无限可行结论装进结构字段。

主要端点位于 `SupportViabilityClosure`：

- `supportWinning_fixed`
- `supportWinning_greatest_of_postfixed`
- `supportIterate_eq_winning_of_card_le`
- `mem_supportIterate_iff_viableWith`
- `supportWinning_iff_all_horizons`

## 3. 完整控制器及其同源概率结论

以下实际历史律与部署占据端点使用有限 X 与有限 A；实值测度接口还明确要求 X、A 的可测结构及单点可测。Y 仍可任意。纯关系固定点层不要求 A 有限，不能据此省略概率端点的这些假设。

通用控制器只具有初始记忆、当前记忆上的动作 PMF、以及由当前记忆/记录行动/新观察决定的更新。这些函数没有时间或完整历史参数。通用记录本身允许任意记忆类型；本批支持控制器给出有限的具体实例。

支持记忆类型包含 Bq 中的全部支持与空集，包括不可达的支持，且

\[
|\mathrm{SupportMemory}(q)|=M+1\le 2^{|X|}.
\]

给定原始初态 p₀，初始化为 supp(p₀) 与初始观察纤维的交集；更新为 U。winning 支持使用一次固定的认证行动选择，其余支持使用显式固定 fallback PMF。因此整个总策略具有有限记忆，零概率历史也有完整定义。

实际转移 Pₙ 可以在数值上随时间变化。源匹配前提明确为

\[
z\in\operatorname{supp} P_n(x,a)\iff R(x,a,z),\qquad
\mathrm{certified}_n(x,a)\iff C(x,a).
\]

Lean 从这些逐项前提出发，证明控制器沿每一条完整记录计算出的记忆等于原来的 `traceSupport`。随后在这个新控制器自己的 `coarseLaw` 上归纳证明 winning 不变性，并由已有实际行律支持定理得到所有时刻的零未认证占据。

更强的有限判据是：存在任意完整策略在 n < M 的所有行上零未认证占据，当且仅当本批这个具体构造的支持控制器在每个 n 上零未认证占据。右端不是另一个未标明来源的存在策略。

主要端点：

- `supportMemory_card`、`supportArenaCard_add_one_le_pow`
- `supportMemoryController_memory_eq_traceSupport`
- `supportMemoryController_supported_histories_winning`
- `supportMemoryController_zero_uncovered`
- `bounded_horizon_iff_all_times_zero_uncovered`

## 4. 可执行有限判据

`finiteMemoryCheck` 使用有限 X、有限 A，可判定的 X/Y 相等关系，以及可判定的 R 与 C；程序输入包含有限初始支持表与观察。它使用可计算的统一上界 B = 2^|X| − 1，在每个可能初始观察的完整纤维上调用现有 `finiteRelationViabilityCheck`。通过有限初始表的元素枚举观察，不要求枚举整个 Y。同一观察可能重复检查，但不会让该观察下的隐藏状态分别选择行动。

程序不读取未知可行策略，也不调用任意 PMF 的 Classical 支持判定。实际源身份由三个证明前提分别承担：初始表恰等于 supp(p₀)、R 恰等于整条实际转移序列的支持、C 恰等于整条认证序列。

匹配成立时，Boolean 值为 true 与以下三项等价：所有非空实际初始纤维属于 W*；本批支持控制器自己的所有部署行零未认证占据；存在某个完整因果策略满足同一全时间结论。

主要端点：

- `finiteMemoryCheck_iff_initial_winning`
- `finiteMemoryCheck_iff_controller_zero_uncovered`
- `finiteMemoryCheck_iff_exists_all_times_policy`

可执行性在这里指有限精确决策程序。它复用有限时域递归；本批没有实现集合消除式固定点迭代、动态规划或可计算行动表综合，也没有给出多项式时间或 oracle 查询复杂度上界。winning 行动的通用选择仍使用 Classical.choice。

## 5. 记忆分离与计算正反例

两状态来源取 X = A = Bool、p₀ = δfalse、恒定观察、P(x,a) = δ(!x)，认证 a = x。手写的 Boolean 记忆控制器初始记忆 false，按记忆行动，每一步翻转记忆；它没有读取外部时钟。Lean 证明其每条实际部署行均认证。

对任意固定随机当前观察反馈，令 ρ 为恒定动作 PMF。其实际未认证占据满足

\[
U_0=\rho(\mathrm{true}),\qquad U_1=\rho(\mathrm{false}),\qquad U_0+U_1=1.
\]

所以任何此类随机反馈都无法同时认证前两行。概率计算在同一个实际微观历史律与部署行律上进行。

有限检查器另外精确计算两个单点初始表为 true、混合初始表为 false。正例把 δfalse 的实际源匹配接到新构造的支持控制器。负例明确使用均匀初态，其支持为两个状态；它排除的是该不同初始实验下的所有全时间零占据因果策略。手写 Boolean 控制器与通用支持控制器没有被假定为同一函数。

## 6. 保留的边界

1. 支持齐次允许概率数值非自治。固定 killed 矩阵、固定 Doob 过程仍需数值齐次或合法有限相位扩张。
2. 零未认证占据还不是物理安全。要推出物理安全，需要原初态安全与认证行动的真实转移支持保持安全域。
3. 新控制器不被认定为旧 `viablePolicy` 或 `infiniteViablePolicy`。旧策略的精确前缀身份是独立问题。
4. 实际源的零概率历史不控制参考过程的可达历史。本批没有压缩参考 Q 的 fallback 或检查预算。
5. 任意非自治认证序列不保证自主有限记忆；本批明确使用固定支持关系和固定认证谓词。
6. 数学 PMF 见证与可执行有限关系计算不是现实数据实验。C1、C3、C7 的原责任没有因此全部关闭。
7. 冻结的 106 P-ID 仍为 11 generated / 89 adapters / 6 boundaries，四个 counted generators 不变，强全局数学闭合仍为 **NOT_ESTABLISHED**。

## 7. 验收位置

六个模块已经进入生产聚合导入，并实际通过完整 `lake build UEOT`，耗时 38.402 秒。新增 35 个公开源定理声明；编译器在六个模块中检出 82 个所属定理常量，其中 22 个私有、25 个其他生成或原生公开常量。全部公理闭包只含标准三公理。

两轮实际 native 执行均以 0 退出，耗时分别为 59.387 与 57.914 秒，完整导出 JSON 相同。新声明与既有 4,237 个注册声明之间完成 148,295 次原始存储类型比较，新声明之间完成 595 次比较，没有定义相等匹配；该筛查不判定一般逻辑等价或数学新颖性。47 条直接注册证明依赖已从实际证明值导出并固定回放。

[完整构建收据](actual-execution/full-build-01/FULL_BUILD_RECEIPT.json)、[原生执行收据](actual-execution/native-01/STATUS.json)、[独立执行审查](independent/ACTUAL_BUILD_NATIVE_REVIEW.md) 与 [类型复用范围审查](independent/TYPED_REUSE_SCOPE_REVIEW.md) 共同记录以上结论。第十层已完成元数据注册，原始 `PASS_PENDING_INDEPENDENT_REVIEW_AND_REGISTRATION` 与源码预检 `PENDING` 状态保留其执行时含义。

现行十层索引已经安装，覆盖 **684 = 673 个维护模块 + 11 个改编上游模块**，注册证明图为 **4,272 个公开声明 / 5,614 条直接边**。50 项复用测试全部通过，包含对全部当前源码的克隆索引复算；旧 68 行克隆索引逐项不变。完整 30 项 FKRG 测试（包含真实 fast-audit）与 89 项 parser 测试也全部通过。

未修改的 canonical UMC 审查实际执行 `--full`，耗时 81.273 秒。当前 85 个 UMC 模块的 1,155 个编译器所属定理常量全部满足标准公理闭包，其中 599 个是确认的公开源候选、125 个私有、431 个其他原生公开常量；106 个原始 P-ID 均保持来源映射。执行前后的完整源码、运行时、依赖身份均与已接受的完整构建相同。该整组审查输出聚合范围；新增六模块另有完整逐常量导出。

| 实际门槛 | 收据 |
| --- | --- |
| 50 项复用回归，含当前源码克隆复算 | [REUSE_TEST_RECEIPT.json](consumer/actual-tests-01/REUSE_TEST_RECEIPT.json) |
| 完整 30 项 FKRG，含真实 fast-audit | [FKRG_FULL_30.json](local-gates/FKRG_FULL_30.json) |
| 89 项声明 parser 回归 | [PARSER_TEST_RECEIPT.json](local-gates/PARSER_TEST_RECEIPT.json) |
| 全量 canonical UMC 与运行身份 | [EXECUTION.json](actual-execution/umc-full-01/EXECUTION.json)、[UMC_FULL_AUDIT.json](actual-execution/umc-full-01/UMC_FULL_AUDIT.json) |
| 实际消费者安装与测试独审 | [CONSUMER_EXECUTION_REVIEW.json](independent/CONSUMER_EXECUTION_REVIEW.json) |

这些收据确认本批证明及本地生产集成。精确 Git 对象、PR、云端 job 的实际状态、resulting-main 树身份及分支退休是后续发布记录的责任；本文件不把尚未发生的发布动作写成已完成。两部书稿及 QM/physics 未在本批修改，冻结分类与强全局闭合状态保持不变。
