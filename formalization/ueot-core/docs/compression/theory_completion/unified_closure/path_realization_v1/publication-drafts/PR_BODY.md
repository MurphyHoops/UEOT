<!-- 本地发布草稿，尚未发送；所有待填字段集中在末节 ROOT_TO_FILL。 -->

## 为什么需要这一批

已验收的 [#363](https://github.com/MurphyHoops/UEOT/pull/363) 提供同源长期链、无限一致策略和逐行 SISC，[#365](https://github.com/MurphyHoops/UEOT/pull/365) 提供有限支持记忆控制器与可执行决策。本批接续三个实际责任：这个控制器生成哪一个过程；原存活实验的完整条件路径与 Doob 路径是什么关系；已有注册载体最小下标能否由实际程序返回。

## 新增结果

- **同一有限记忆控制器的实际路径。** 从原初态、观察、行动分布与数值转移序列构造状态—记忆初态及非自治行 $J_n$，证明原微观历史律的完整增广、有限前缀、无限前缀与状态投影身份。状态投影的 Markov 性没有被预设。
- **实际物理安全。** 同一策略的全时零未认证占据，加原初态安全和认证转移的真实支持保持条件，推出其同源无限状态律的概率一全时安全。现有支持固定点控制器直接消费该接口。公开三源合取同时给出安全正例和两个真实 PMF 反例，明确证明反例各自的 `¬hclosed`、`¬hinit`，并保留全部五项坐标/全时质量结论。
- **有限窗与 Doob 的准确联系。** 直接过滤原完整实验，证明条件初态 $\eta_0(i)g_T(i)/s_T$、完整条件路径原子，以及正质量父事件上的下一行比 $Q(i,j)g_{r-1}(j)/g_r(i)$。构造同一 $Q$ 的实际 Doob PMF 路径，得到末端 $h$ 倾斜公式和逐正质量路径的相等判据。三状态原源有真实左 QSD，两条路径的初始边际相同，完整二时刻律的 TV 仍为 $1/4$。
- **C3 可执行搜索。** 对注册嵌套载体族进行实际 Boolean oracle 顺序扫描，返回首个正项及精确调用 trace；证明程序输出等于原 `firstGoodIndex`、查询数上界为注册项数，并得到注册族内的包含极小性。

七个新模块的具体端点、证明路线、非空正反例、原 Core/C1–C7 对应和来源身份见[完整数学报告][report]。五份原始材料的字节绑定和独立审查随本批归档。

## 适用范围

一般记忆实现保留数值非自治与任意观察类型；当前无限物理安全端点使用有限状态、行动与记忆及相应可测性。本批有限窗矩阵路线使用齐次数值源和固定当前观察反馈。`finiteWindowRowPMF` 只构造正分母行；独立的全状态 total 条件核及其整路径生成身份仍待另证。Q-process 极限、谱收敛和一般非自治条件路径没有纳入本批。

C3 的 exact-oracle 匹配是外部前提；查询保证与极小性只覆盖注册族，oracle 内部成本、噪声采样和物理删除 frame 仍需相应证据。来源支持一致性不改变参考过程的完整历史检查预算。

本批属于 **uncounted same-source path realization**。冻结 **106 P-ID = 11 generated / 89 adapters / 6 boundaries**、**4 counted generators** 和全局 **`NOT_ESTABLISHED`** 均保持。现有统计失败预算、领域物理适配及经验验证范围没有扩大。

## 已完成验证

七个最终模块均已实际聚焦 Lean PASS，独立静态数学/API 审查 CLEAR。最终有限窗来源链在 compile-09 顺序执行中全部通过；物理安全见证的三源合取修订在 compile-10 通过，并获独立语义审查 CLEAR。

当前源的实际完整 `lake build UEOT` 已 **PASS，14.23 秒**，覆盖 **691 个模块**。源码指纹为 `de7c7e287bd1b351ed3f790de58bfd71edf18df4013f7e5aaf2af55a6b3f6379`，不可变基线是已验收 operations [#366](https://github.com/MurphyHoops/UEOT/pull/366) 的 resulting main `d503586107974c56e0773b4ea106b41a7d144b43`。

native02 的导出与固定 verifier 均实际 **PASS**（58.451 / 58.297 秒），收据报告本批 **7 模块、73 个公开声明、249 个编译器审计定理常量、114 条注册直接证明边**，两个原日志哈希一致。收据原状态为 `PASS_PENDING_INDEPENDENT_REVIEW_AND_REGISTRATION`；完整执行原档独审、消费者注册、canonical 和发布按下节继续验收。

原 `c344bf66…` 的 full build01 PASS 与 native01 中断 FAIL 均保留。见证修订增加了两条明确的否定前提结论，五个原质量证明作为私有计算完整保留；公开比较域由 77 改为 73，新域按原 native 规则全量执行，私有生成常量继续进入编译器审计。详见完整报告中的修订与执行记录。

## ROOT_TO_FILL：集中待验收与发布字段

**以下 PENDING 项须由各自实际证据验收，不由已有执行 PASS 代填。**

| 项目 | 待填内容 |
|---|---|
| 本批最终 candidate head / tree | `ROOT_TO_FILL_CANDIDATE_IDENTITY` |
| native 两轮完整原档、公理/ownership/raw-type/固定边及对象等同性的独立核对 | `PENDING — ROOT_TO_FILL_NATIVE_REVIEW` |
| 最终注册声明总数、累计证明边与 overlay 数量 | `PENDING — ROOT_TO_FILL_ACCEPTED_REGISTRATION_CENSUS` |
| 消费者、完整 clone、canonical 及必要回归 | `PENDING — ROOT_TO_FILL_INTEGRATION_GATES` |
| 实际执行归档与独立执行审查 | `ROOT_TO_FILL_EXECUTION_ARCHIVE_AND_REVIEW` |
| PR / resulting-main 治理及最终树身份 | `PENDING — ROOT_TO_FILL_RELEASE_GATES` |

Refs #146, #302. 本批不请求关闭长期研究任务 #302。

[report]: ROOT_TO_FILL_REPORT_URL
