# 私有 K1 实现：来源与事件范围独立定向审查

审查者：`/root/books_resume`。结论：**STATIC_K1_SOURCE_EVENT_SCOPE_CLEAR；实际执行状态由另行收据确定**。

审查对象是私有 `SameSourceKilledPath.lean` 的两个最终端点及配套 `INTERFACE_AND_PROOF.md`。本次不重做旧 SourcePolicyPathBridge 全审，不运行 Lean，不修改候选或生产源码。数学工作者正在处理 elaboration；本结论只绑定下面保存的源码快照，不预认其后版本。

## 1. 绑定的版本

- Lean：`383eded19936623d3745d06d0f58e193f4f2682e73123b90a8cbc7733739b7f5`，15286 字节。
- 接口说明：`b8ae2b144b099f350b0396b43dcb39193c407fcebc95001485e6997d6de22b7f`，6969 字节。
- 作为合同使用的 `CONTRACT_KILLED.md` v2：`e0efe3d8405060e1c03ce1d00b3e2810fcebcf4697d23669a289d9590e56283e`。
- 前置来源桥：`108500fc13229b8faffc9829d886313167142075112bc3f6c023a086c074ae91`，复用其独立静态审查及实际编译收据。

实际读取内容已保存在 `input-snapshot-v1/`，两个终点的完整声明头和哈希在 `REVIEW.json`。接口说明与本次源码的数学范围一致。

## 2. 两个终点确实指向原始风险实验

两个左端均直接使用

```lean
causalLaw p0
  (riskMicroControlKernel q (fun _ => M.transitionPMF)
    (observationMarkovPolicy sigma)) n
```

因此测量的是原接口生成的完整动作—微观状态记录律。没有另外给一个 PMF 并假设它等于实际律。

右端使用 `killedMatrix M (liftedStationaryPolicy q sigma) K`，其定义是原 `policyMatrix` 在 K 子类型上的逐项限制。`safeInitialRow p0 K` 直接取同一 p0 的原子质量。调用者没有自由 Q、自由初始行、另一个策略，或核／路径来源等式参数。

两个最终证明内部调用 `actual_state_path_eq_stationary_path M q sigma p0 n`，并证明原始事件是纯状态事件在完整动作擦除映射下的逆像。中间的任意平稳策略定理最终均以同一个 `liftedStationaryPolicy q sigma` 实例化，没有借用另一策略的安全结论。

## 3. 初始时刻、空安全集与先出后回

`stateSurvives K 0 x` 定义为 x∈K。已有 `riskEverFailure bad 0 x` 定义为 bad x；后继才添加下一状态。因此候选的 `¬ riskEverFailure (fun x => x∉K)` 精确检查 0,…,n 的每一个状态，并与 `stateSurvives_erase_iff` 对齐。

- n=0：逐点质量就是 `(p0 v.val).toReal`，Q⁰ 是 K 上单位矩阵；总质量为 p0(K)，不是无条件的一。
- p0 可在 K 外有质量：安全初始行未归一化，前缀事件在初始时刻即排除这部分质量。
- K 可为空：逐点定理的 `v:K` 为空量化；总质量定理仍有内容，右端为空和零，左端在时刻零便无法存活。两条声明均没有 `Nonempty K`。
- 原过程允许离开 K 后返回：递推保留整个前缀的 `stateSurvives`，不会把曾离开的路径重新计入。

这些是全称命题及定义所涵盖的边界；本审查没有另行运行空集或 n=0 的 Lean 实例测试。

## 4. 没有把目标等式放进前提

`stateTerminalMass_succ` 从已有 `policyPathKernel` 的一次真实 PMF extension 展开，终端原子求和选择 v，随后按前缀的最后安全状态分组，给出 κₙ₊₁=κₙQ。分组引理只要求 good 历史的末态在 K；这一性质由本文件的 `stateSurvives_current_mem` 证明。

`state_terminal_mass_eq_killed_pow` 从上述未归一化初始行开始，用 `rowApply_mul` 和 `pow_succ` 归纳。总质量再由存活历史按最后安全状态的有限划分得到。最后通过 PMF 推前和有限事件质量等式回到原风险实验。

这里没有除以历史概率或存活概率，也没有假定目标递推、目标幂公式、初始安全支撑、可行固定点、QSD、正特征向量或不可约性。killed 非负与行和≤1 直接继承原随机行的非负及归一性；没有把安全域假定成闭合域。

有限和写法、子类型有限实例、simp/rewrite 及 definitional equality 是否被 Lean 接受，仍须由实际编译决定。静态审查不把完整候选证明体当成已经通过内核的证据。

## 5. 状态事件作用域准确

擦除映射保留所有微观状态，仅丢弃行动记录。两个事件都是完整状态路径事件：始终在 K，以及始终在 K 且终端等于 v。它们不是“当前观察落在某纤维”的事件，也没有用观察过程自身的 Markov 性。

X、A 有限，A 非空；最终 `toMeasure.real` 接口保留 X、A 的单点可测条件。Y 无需有限或可测。源 M 时间齐次，σ 是固定的当前观察策略；本文件没有把一般历史策略变为平稳策略。依赖行动记录的任意失败事件不在这两条终点的直接结论内。

本次只实现合同 K1 的目标和 killed 核基本性质。K2 条件终端 PMF、K3 从 QSD 初始律出发的实际结论、Doob 倾斜、一般单调性及失败补事件公式不应随之自动标为已形式化。

## 6. 必须保持的修订边界

没有发现需要削弱或改变这两个数学命题的缺口。编译修复可以调整有限子类型实例及证明实现；若出现新的正存活、非空 K、初始安全支撑、外给源等式等前提，或改动 M、p0、σ、事件及时间范围，应重新做定向审查并报告主智能体。

本收据不是编译 PASS、公理闭包、生产导入、native 或 canonical 验收；已成熟的生产所有时刻安全和同源 GOA 保持其原有状态，不由本 K1 的私有草稿状态重新降格。
