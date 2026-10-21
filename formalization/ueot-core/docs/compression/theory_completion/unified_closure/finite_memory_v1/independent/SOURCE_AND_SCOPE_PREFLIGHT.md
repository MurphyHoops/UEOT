# 有限支持固定点与有限记忆：独立源级预审

状态：**STATIC_PREFLIGHT_CLEAR_WITH_PUBLICATION_OBLIGATIONS**。本文件审查任务定位、已有接口及当前基线权限，不预称新 Lean 实现、编译、native 导出或发布已经通过。审查者：`/root/finite_memory_audit`。基线：`a9109004959975b3d2c5a303741e117f1cd8cb9c`；新科学分支：`compression/theory-completion-finite-memory`。读入文件的 SHA-256 和实际基线权限计算见同目录 `SOURCE_AND_SCOPE_PREFLIGHT.json`。

## 1. 原科学责任与这批工作的增量

用户提供的原数学书 §8.5 / P-PER-03 以真实状态为控制器输入，删除不具备保持行动的物理状态，得到有限状态可行核和保持该核的平稳确定策略。该结果不允许控制器在部分观察下直接读取隐藏状态。

本批将同样的控制责任放到**非空、观察齐次的可能状态集合**上：一个行动必须同时认证当前支持内的所有状态，而且每个非空观察后继支持均保持可行。支持集数量通常大于状态数量，所以严格下降上界是支持集合数 `M`，不能把它写为 `|X|`。已有 `InfiniteSupportViability.lean` 已证明固定整条非自治来源数据下的无限策略存在；本批增加的是支持齐次条件下的有限截止和自主有限记忆表示。

这项增量不改写原 106 个 P-ID 的分类，也不把观察支持控制自动解释成奖励最优、一般预测充分性、物理安全或强全局数学闭合。

## 2. 已有接口的复用核查

| 已有接口 | 可以直接复用 | 不由该接口自动得到 |
|---|---|---|
| `SupportViabilityClosure.initialSupport`、`successorSupport`、`traceSupport` | 同一初态、转移序列、记录动作和观察的来源支持递推 | 零质量记录上的后验唯一性 |
| `mem_coarseLaw_succ_support_iff`、`zero_uncovered_iff_support_certified` | 控制器自己的正历史不变量与实际未认证行占据 | 与另一个 `Classical.choose` 策略相同 |
| `InfiniteViable`、`arbitrarily_long_zero_uncovered_iff_single_all_times_policy` | 任意长有限策略与同一个全时策略的精确存在等价 | 齐次有限记忆或可执行选择算法 |
| `finiteRelationSuccessor`、`finiteRelationViabilityCheck` 及其 correctness 定理 | 明确可判定支持关系输入上的有限 Boolean 检查；真实 PMF 支持的适配责任 | 未经证明的外部支持表正确性或无限截止 |
| `ViabilityKernel.exists_viabilityIter_fixed` | 有限状态删除与不变核的既有数学机制 | 任意关系的观察支持算子、指定 `M` 截止 |
| `UnifiedClosure.exists_finite_viability_fixedpoint` | 已有 `ExactControlQuotient` 上按宏状态数计的严格基数下降证明 | 无数值宏核的观察支持控制算子 |
| `FiniteDiscountedControl.CausalPolicy` | 既有任意时间索引记忆的状态控制语义 | 输入任意观察类型 `Y` 的齐次 PMF 有限记忆记录 |

源码检索没有发现已经提供 `initialize : Y → Mem`、`action : Mem → PMF A`、`update : Mem → A → Y → Mem` 三个齐次映射的通用观察有限记忆记录。因此新表示可增加；它应继续递归生成现有 `CausalHistory` 上的策略并消费现有部署行律，避免另建没有来源身份的概率实验。

FKRG 原始默认临时索引不存在，第一次查询如实返回 `INDEX_MISSING`。在本审查专属 scratch 数据库重建后，第一次基线索引记录 678 模块、6274 个词法声明，完整来源指纹为 `60cd5f8ab161c5b51394463c466947a4c6a6c1742ecdcd9c2bbfc41c0c06bd31`。并行作者新增源码后旧索引按设计拒绝为 `STALE_INDEX`；随后在同一调用中重建并查询成功。查询还包括复用导航器的 `support viable` 和 `fixed`。词法命中后已经打开上述原始源码比较真实假设；这些查询不是 Lean 内核复用验证或语义等价证明。

## 3. 数学与来源验收清单

1. **支持时间结构。** 固定 `R : X → A → X → Prop` 与 `C : X → A → Prop`。实际接口应证明或消费 `R x a z ↔ z ∈ (P n x a).support` 及 `C x a ↔ certified n x a`，允许非零概率随 `n` 改变。不能静默把支持齐次换成数值齐次。
2. **有限支持空间。** `Bq` 包含且仅包含非空且位于同一个观察纤维的支持；非空后继仍在 `Bq`。任意 `Y` 足够，不必枚举整个观察类型。无初态 PMF 的纯关系层允许空 `X`，须保留 `M = 0` 的正确性。
3. **固定点责任。** 算子单调；从 `Bq` 开始的迭代递减；在 `M` 步已经稳定，而不只是某个未经计量的有限步；最大性覆盖每个后固定集合。一步相等后的所有后续相等必须由同一算子推出。
4. **有限时域身份。** 支持成员与原 `viableWith` / `Viable` 的等价须逐步证明，并明确时间索引消除来自来源匹配假设。初始支持在固定点的条件再连接原实际策略存在定理。
5. **整个总控制器。** 初始化、输出和更新无外部时钟或完整历史参数；显式固定 fallback PMF 使零概率和非可行记录也有总定义。实际路径所用的有限记忆要等于原递归支持。空支持可作为额外 memory，界为 `M+1≤2^|X|`；若使用所有 `Set X`，可直接给 `2^|X|` 的完整载体界。
6. **同一个实验。** 证明新控制器自己的 `coarseLaw` 支持不变量，再推出自己的 `coverageDeploymentRowLaw` 零未认证占据。不能把另一有限时域 `viablePolicy` 的占据或策略身份移植过来。
7. **计算边界。** 任意 `Prop` 和 `Classical.choose` 给数学存在构造。可执行检查另需可判定观察等式、支持关系和认证谓词。若只接上现有 Boolean 检查器，则可以宣称有有限准确判据，不能宣称已经给出可执行控制器合成器。
8. **真实两状态分离。** `Bool` 翻转来源、恒定观察与 `a=x` 认证下，齐次 Boolean 记忆可全时认证。任意固定观察随机反馈必须由同一个 PMF 生成两个初始占据，证明 `U₀+U₁=1`，保留随机化量词。
9. **物理安全和无限路径。** 零未认证占据本身只认证行。物理全安全还需初始安全与已认证真实转移的安全支持条件。接入固定 killed 矩阵还需数值齐次源或合法有限相位扩张，以及明确的过程图身份。
10. **参考过程。** 来源支持上的一致性不限制参考 `Q` 能到达的历史；原参考 fallback 和检查预算不能因此删改。若未来减少参考检查，另证参考可达范围的一致性。

## 4. 实际基线治理判定

直接读取基线 Git 对象中的 `COMPRESSION_RESEARCH_TRACKS.json` 与 `validate_compression_research.py`，并验证其字节与当前工作副本一致。调用基线真实 `l2_existing_path_exceptions_for_branch` 得到：

- 新分支 `compression/theory-completion-finite-memory` 的既有路径 L2 授权集合是 **空集**。
- 上轮 `compression/theory-completion-longterm-policy-sisc` 的授权集合是六条已列路径。

新分支符合常规 TC 命名。可以在 TC 的 Lean 与 docs 子树新增文件，并按原规则仅追加 `TheoryCompletion.lean` 的必要公共 imports。`THEORY_COMPLETION_STATUS.json` 是唯一预授权的 TC 可变 live status；这不扩大其他既有文件的权限。

生产集成若更新现行 UMC DAG、复用导航器、回归或导航说明，须先在独立 `ops/compression-*` 治理 PR 中把准确路径和新分支绑定，并合并到科学 PR 的不可变基线。科学候选中的新例外不能授权同一候选的既有文件修改。无需为了开始这些新增数学文件提前修改治理。

发布门槛仍包括实际 full `UEOT` 回归、公共入口、完整源码身份、proof escape 和公理检查、类型复用与实际依赖导出、独立审查、canonical PR 及 resulting-main 核对。云端自动治理成功仍不等于 Lean 构建成功。既有原始失败、PENDING、旧 overlay、冻结台账、QM/physics 与两部书稿均保留。

此预审不阻塞已授权的新证明工作；后续精确源文件与实际编译产物另作独立验收。
