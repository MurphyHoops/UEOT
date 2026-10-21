# K2：把 QSD 左特征行绑定到原始风险路径

状态：**静态数学设计与 Lean 证明草稿；未编译，未进入生产，未扩展当前七模块发布范围。**

配套 `SameSourceQSDBinding.lean` 给出完整拟议声明和证明体。这里的 K1 仍是作者维护的私有候选 `SameSourceKilledPath.lean`；本报告不替根智能体宣告它的执行状态。`SourcePolicyPathBridge.lean` 的实际聚焦 PASS 由根智能体报告；本次只复用其源码端点，没有重复执行。

## 1. 最小输入与真正需要绑定的对象

设有限状态 `X`、有限非空行动 `A`、任意观察类型 `Y`，真实模型 `M` 的转移 PMF 为 `M.transitionPMF`。固定观察映射 `q : X → Y` 和时间齐次当前观察策略 `sigma : Y → PMF A`。原风险实验使用 `observationMarkovPolicy sigma`，其诱导状态策略为同源的 `liftedStationaryPolicy q sigma`。

给定安全集 `K : Set X`，矩阵只能取

```lean
Q := killedMatrix M (liftedStationaryPolicy q sigma) K
```

它是原状态转移核在安全子类型上的限制，不是另一份自行选定的矩阵。

核心输入用 `r : PMF K` 表示归一化非负左行，记 `rR v = (r v).toReal`。需要的特征假设只有

```lean
hleft : ∀ v, rowApply rR Q v = rho * (r v).toReal
```

真正部署的初态被构造成

```lean
p0 := r.map Subtype.val
```

草稿先推导

```lean
safeInitialRow (r.map Subtype.val) K = fun v => (r v).toReal
```

从而消去 K1 中的初态限制行。没有把 `eta0 = rR` 当作未经来源说明的额外假设。若上游给的是 `r : K → ℝ`、`hr : ∀ v, 0 ≤ r v`、`hsum : ∑ v, r v = 1`，直接使用既有 `FiniteProbabilityRow.ofRealRow r hr hsum`；草稿末尾给出这一层的质量公式适配。

K2 没有证明 Perron 数据存在，也不要求严格正的每个坐标、不可约性、唯一性或收敛吸引性。这里的行确实归一化且非负；仅有形式左特征等式而没有概率归一化不够。

## 2. 原始路径中的精确结论

令

```lean
nu n := causalLaw (r.map Subtype.val)
  (riskMicroControlKernel q (fun _ => M.transitionPMF)
    (observationMarkovPolicy sigma)) n
S n := {h | ¬ riskEverFailure (fun x => x ∉ K) n h}
```

这里 `S n` 包含初态与时刻 `1,…,n` 全部安全，`n` 计转移数。对每个 `n : ℕ`、`v : K`：

\[
\nu_n(S_n\cap\{X_n=v\})=\rho^n r(v),\qquad
\nu_n(S_n)=\rho^n.
\]

两式都是原始含行动记录的风险 PMF 的事件概率；不是只对杀死矩阵定义出来的新实验成立。

| 草稿端点 | 真实复用路线 | 新增数学工作 |
|---|---|---|
| `safeInitialRow_map_subtype` | `PMF.map_apply`、Subtype.val 单射 | 证明原初态限制行等于 QSD 行 |
| `actual_qsd_survival_terminal_mass` | K1 的 `actual_survival_terminal_mass_eq_killed_pow` → `QSDPerron.leftPerron_pow` | 一次初态行重写 |
| `actual_qsd_survival_mass` | K1 的 `actual_survival_mass_eq_killed_pow_sum` → `QSDPerron.qsd_survival_mass_pow` | 用 `coverage_sum_toReal r` 提供真实归一化 |
| `sameSource_rho_bounds` | `qsd_survival_mass`、K1 非负行、`perron_root_le_one_of_substochastic` | 推出 `0 ≤ rho ∧ rho ≤ 1`，不推出严格正 |
| `sameSource_KilledQSDGOA` | K1 非负/次随机行 + 真实 PMF 归一化 + `hrho` + `hleft` | 直接构造已有 GOA 谓词，无另一个 Q 的适配假设 |
| `actual_qsd_conditioned_terminal_law` | 上述真实事件质量 + `PMF.filter_apply`、`PMF.map_apply`、终态安全 | 把代数条件比值提升为实际条件 PMF 的等式 |

前两条质量公式不需要 `rho > 0`。条件律接口显式增加 `hrho : 0 < rho`，先内部推出 `nu n` 的真实生存事件有正质量，再构造 `PMF.filter` 所需的支持见证。最终精确接口是

```lean
(nu.filter S
  (actual_qsd_survival_support M q sigma K r rho hleft hrho n)).map
    (riskLastState n) = r.map Subtype.val
```

这一步不是将 `qsd_all_steps` 的矩阵比值本身称为真实条件分布。私有通用适配 `filter_map_apply_real` 从 PMF 的 `filter` 与 `map` 定义推导

\[
((p\mid S)\circ f^{-1})(z)
=\frac{p(S\cap\{f=z\})}{p(S)}.
\]

安全集之外的终态质量由真实生存事件蕴含终态安全推出为零；再由所有坐标相等得到整份 PMF 等式。`PMF.filter` 的支持见证不是外加的“另一实验正概率”前提。

## 3. 必须保留的边界

| 情形 | 可得结论 | 不能宣称 |
|---|---|---|
| `rho = 0, n = 0` | 总质量 `0^0 = 1`，终态联合质量为 `r(v)`；初态全在 K | 把所有 n 的条件律接口用于零分母 |
| `rho = 0, n ≥ 1` | 原实验生存质量为零 | 正概率生存条件律；Lean 中实数 `0 / 0 = 0` 不构成条件概率 |
| `0 < rho ≤ 1` | 每个有限 n 的生存事件都有正概率；条件终端律为同一个 r | 无限时域正存活；当 `rho < 1` 时有限窗正概率不产生这一结论 |
| 空安全集 | K1 的任意初态公式仍适用，零时刻也可失败 | 在空 K 上构造 PMF 或总和为 1 的非负行；K2 输入本身已排除此情形，无需给 K1 偷加 `[Nonempty K]` |
| 任意原初态 p0 | K1 给出真实截断行 `safeInitialRow p0 K` 的幂公式 | 用 QSD r 静默替换 p0，再声称原实验满足 `rho^n` |
| 一般历史依赖策略 | 需要额外的状态/历史扩充或新的路径定理 | 直接套用时间齐次当前观察策略的固定 Q |

已审合同的有理反例继续约束这一接口：`Q = [[0,0],[1/2,1/2]]`、`r=(1/2,1/2)`、`rho=1/2` 的左 QSD 具有全支撑，但从第一状态的点质量初态出发一步生存率为零。K2 从实际 `r.map` 初态得出正存活，不向任意初态推广。这里不另行添加数值或 Lean 执行收据。

`KilledQSDGOA` 自身包含严格正的 `rho`，所以零特征值质量结论必须保留在不经过该谓词的接口。GOA 包装不是零特征值情况下的基础接口。Doob 右特征函数、有限窗路径条件化与无限窗问题均未纳入此次最小桥。

## 4. 后续部署接口的来源约束

已读 `VariableRegisteredJoint.lean` 的参数是预先给定的 `initial : C → PMF X`，并非必须对所有候选固定同一个初态。未来可以预先注册一族实际部署初态 `initial c = (r_c).map Subtype.val`，再由训练记录选择候选；该族必须真正用于已定义的联合实验，真实采样源 P 仍保持原接口的来源约束。原失败事件 E 仍固定；允许候选变化的初态或安全集，并不自动允许候选改变原 E。

本次没有提出或实现新的统计组合定理，也没有为既存部署实验追溯更换初态。这个提醒只说明 K2 未来接入时应在哪个参数位置履行同源约束。

## 5. 执行与集成边界

本次只进行了源码读取、静态数学推导和草稿写入，没有运行 Lean、lake build、native 导出或全库检查。没有修改 A 的 K1、生产模块、书稿、Git 或消费者。不会把私有草稿纳入当前冻结七模块的源身份、声明计数或发布范围。

根智能体确认 K1 的实际聚焦结果后，可先对该私有候选做一次聚焦编译。最可能需要的修正是 PMF/filter 支持参数、有限历史实例与局部记号的 elaboration；声明中的量词、同源初态、正概率前提不得为消除报错而变更。通用条件化引理已经给出证明体，仍须实际 Lean 验证后才算形式化完成。本报告没有使用“源码里有证明体”替代执行证据。
