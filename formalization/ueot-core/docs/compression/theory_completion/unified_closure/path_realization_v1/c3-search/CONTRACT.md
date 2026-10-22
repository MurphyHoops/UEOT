# C3：注册嵌套载体族上的可执行最小搜索

初始聚焦检查点：`FOCUSED_LEAN_PASS_NATIVE_INTEGRATION_PENDING`。本模块已在集中
`compile-04` 中实际通过 Lean：exit code `0`，用时 `3.729183458` 秒，日志为空。
对应源码 SHA-256 为
`6a70601f35f12edf0eaf881a39aa36fc8d22d5b42111d0c937fa92948df70abc`，
空日志 SHA-256 为
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`。
协调者的原始收据为
`tmp/core-path-realization-20261022/FOCUS_04_TOOL_OUTPUT.txt`；这里的 PASS
仅指该模块，不能替代同批其他模块、完整构建、native、类型复用或发布验收。

首轮执行的自然数减法查询上界证明失败及原日志继续保留；修正显式保留
`start ≤ i`、`i < start + fuel` 和 `i - start + start = i` 后通过。
独立静态数学/API 审查见
`../independent/C3_AND_DOOB_WITNESS_REVIEW.md`，其审查源码与通过源码相同。

## 1. 本次新增的责任

原始 C3-01/02 要求区分 oracle 查询、候选/输出规模与实际算法。现有
`ScientificClosure/C3NestedSearch.lean` 已给出注册嵌套族中的最小 good index，
但通过非可计算 `goodIndices.min'` 定义，没有实际短路程序或调用计数。

本批新增 `UnifiedClosure/C3ExecutableSearch.lean`：输入一个真正的 Boolean
oracle，按注册顺序查询，首次返回 true 即停；结果包含 `Option Nat` 和查询索引
列表。没有把旧的最小下标、未知真载体或可行性证明作为运行输入。

从这些实际定义证明：成功恰好返回最早 good 下标；失败恰好说明所有注册项为负；
oracle 与声明性质匹配时，输出等于原 `firstGoodIndex`；使用注册族的 nested
条件，返回的集合在该族内没有严格更小的 good 集合。

## 2. 精确输入与语义

设 `F : NestedCandidateFamily V n`，共有 `n + 1` 个注册项。
`candidate : Fin (n+1) → Finset V`，且索引增加时载体包含关系单调。
元素类型 `V` 不必本身有限；实际候选分别为有限集合。

运行输入为 `oracle : Finset V → Bool`。性质 `Good` 及

`∀ i, oracle (F.candidate i) = true ↔ Good (F.candidate i)`

是正确性定理的外部匹配前提。它不由搜索器自动证明，也不把有噪声的观测当成
精确 oracle。`familyOracle` 在表外返回 false，但有范围证明保证搜索从不查询表外。

### 单调性到底用于哪里

线性扫描的第一成功/失败正确性不要求 oracle 或 Good 单调。它查询完整的此前
索引，所以不需要根据未查询点推断正负。注册载体的 nested 条件只在推出链内
严格包含极小时使用。

现有 `firstGoodIndex_chainMinimal` 的注释提到 upward oracle，但其实际定理签名
没有该前提。本批复用实际签名，保留原文件不改。若今后改为二分搜索并跳过某些
索引，就需要另行证明恰当的响应单调性及该算法的正确性；本批不作该推广。

## 3. 可执行定义与查询证书

`scan oracle start fuel` 在 `fuel = 0` 时返回 none/空 trace。
每个非零递归步骤只测试当前 `oracle start`，把该 start 写入 trace；
正则返回，负则递归到 `start + 1`，剩余次数减一。

Lean 证明的通用不变量为：

\[
\mathrm{found}=\mathrm{some}\ i
\iff
\bigl(start\le i<start+fuel\bigr)\land O(i)
\land\forall j\in[start,i),\ \neg O(j).
\]

失败当且仅当区间内每项为负。查询列表中的索引都在该区间内，且无重复。
查询数准确为

\[
N_{\mathrm{query}}=
\begin{cases}
i-start+1,&\mathrm{found}=\mathrm{some}\ i,\\
fuel,&\mathrm{found}=\mathrm{none}.
\end{cases}
\]

在注册族的入口 `start = 0, fuel = n+1` 得到成功时恰 `i+1` 次、
失败时恰 `n+1` 次，以及统一上界 `n+1`。
trace 中无重复的是**注册索引**；族可能含相同载体的多个条目，程序没有自动
对相同集合值做去重或缓存。

这里的 oracle 是纯 Boolean 函数，trace 记录定义中的函数查询；本批没有构造
外部 I/O、硬件测量或样本采集程序。

## 4. 复用与新结论的对应

| 来源 / 接口 | 本批用途 |
|---|---|
| `NestedCandidateFamily` | 保留原注册族和 nested 条件 |
| `goodIndices` / `firstGoodIndex` | 作为已有数学选择对象，未成为程序输入 |
| `firstGoodIndex_chainMinimal` | 通过新 `search_found_iff` 证明程序输出等于旧选择 |
| 新 `scan_found_iff` / `scan_none_iff` | 从递归程序证明准确成功与失败语义 |
| 新 `scan_query_count` / `scan_query_mem` / `scan_queries_nodup` | 证明实际查询列表的数量、合法性和无重复索引 |
| 新 `search_registered_inclusion_minimal` | 用 nested 关系把索引最小推进为注册族内严格包含极小 |

源码检索与 FKRG `search firstGoodIndex` 命中原三个公开端点；本批新增内容是
执行、查询证书与实际输出身份。后续 native proof-value 导出负责实际注册证明边，
本表不替代该导出。

## 5. 非空计算正反例

使用 `V = Nat` 的五个注册前缀载体 `range i`，`i = 0,1,2,3,4`。
族非空，并含非空候选。三个端点均使用 Lean `by decide` 验证精确结果：

| oracle | 实际结果 | 查询 trace |
|---|---|---|
| `2 ≤ card S` | `some 2` | `[0,1,2]` |
| `5 ≤ card S` | `none` | `[0,1,2,3,4]` |
| `card S = 1 ∨ card S = 3` | `some 1` | `[0,1]` |

第三例同时核验索引 1 为正、索引 2 为负，显示 oracle 的 upward 单调性确实不
成立，而本扫描仍准确返回首个正项。它不是物理干预反例；它验证算法假设范围。

## 6. 五类成本和原 C3 的保留责任

| 成本 | 本批范围 |
|---|---|
| Query | 精确 trace 长度与 `≤ n+1` 上界已作为 Lean 目标实现 |
| Sample | 精确 Boolean oracle 未指定样本；不由 query 数推断统计样本预算 |
| Time | 未把每次 oracle 的内部成本、载体构造成本或 Lean 编译时长等同算法总运行时 |
| Memory | 返回 trace 的元素数有同一界；未形式化编译器栈、共享或实际峰值内存 |
| Output | 一个最早 good 索引或 none，外加证据 trace；并非全部极小载体列表 |

该受限族与完整幂集是不同任务。原 C3 的二项式/指数输出下界、全载体发现、
噪声 oracle、未知响应、错误预算分配和物理删除 frame 仍保持独立责任。
访问充分性随信息增加的单调性不会自动证明物理删减操作的单调性；备份激活、
解除抑制等效应仍须由实际模型或实验分析。

本批不修改 106 P-ID 分类、四个 counted generators 或强全局闭合状态。

## 7. 后续实际生产集成检查点

当前执行状态：`FULL_BUILD_NATIVE_REGISTERED_LOCAL_GATES_PASS_PUBLICATION_PENDING`。
上方聚焦收据与初始 pending 状态保留为其原检查点，不被改写成后续执行结果。

本模块仍为上述 `6a70601f…` 源码。整批七模块在正式基线
`d503586107974c56e0773b4ea106b41a7d144b43` 上的最终源码指纹为
`de7c7e287bd1b351ed3f790de58bfd71edf18df4013f7e5aaf2af55a6b3f6379`。
该完整源码的实际 full build 已通过，native02 的初次导出与固定验证器重放
分别以退出码 `0` 完成，完整导出原始字节相同。

本模块的 16 个公开定理已进入本批实际 73 个公开候选的比较与注册范围。
`search_eq_firstGoodIndex` 的实际直接证明依赖为新 `search_found_iff` 和旧
`NestedCandidateFamily.firstGoodIndex_chainMinimal`，没有只按源码名称推定复用。
实际导出完整保留物理模块所有者、公理闭包、类型及私有/生成证明成分。

新增登记的 `PATH_REALIZATION_REUSE_OVERLAY_V1.json` SHA-256 为
`8e72781498acf49496733ace5dfbf80257830ff3a6d85e1b02e66474f936ec3b`；
其实际 [登记收据](../actual-execution/native-02/REGISTRATION_RECEIPT.json)
只增加来源元数据，不改原导出科学内容。

本地十一层消费者的完整 54 项回归、完整 30 项 FKRG（包含真实 fast-audit）
与全部 691 个模块的正常 clone 扫描均首轮通过。后者与原 68 行表逐项相同，
扫描算法未改。既有 89 项 parser 的实际 PASS 因输入不变直接复用，未重跑。
执行命令、输出、耗时、退出码和输入哈希见
[本地门槛总索引](../local-gates/LOCAL_GATE_SUMMARY.json)。

这里记录的是已实际完成的本地集成结果。独立消费者审查、canonical、Git 对象
预检、PR 和 resulting-main 仍各自保留其单独的实际验收；本合同不预填发布成功。
