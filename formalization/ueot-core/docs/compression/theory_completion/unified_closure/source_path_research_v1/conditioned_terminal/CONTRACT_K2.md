# 一般 K2：同源正存活条件终态律

## 0. 状态与范围

**PRIVATE PROOF DRAFT — NOT COMPILED。** 本文给出一般 K2 的准确命题和完整 Lean 证明候选；本轮没有运行 Lean、`lake build` 或 native。源码末尾的 `#print axioms` 只是未来执行请求，没有产生公理闭包收据。独立静态审查与后续真实编译必须分别记录。

候选源码：`SameSourceConditionedTerminal.lean`。

初版 SHA256：`7ab97381798440497a3a60fac5ee2dd405deb1f7100438e06b1a1b6a2e21d95c`。最终对应身份以同目录 `STATUS.json` 为准。

本轮只新增一般正存活条件律。没有修改生产七模块、书稿、冻结候选、Git refs 或远端。没有把 QSD 特化、Perron 存在、无限存活或条件路径的齐次 Markov 性并入结论。

## 1. 同一个实际实验与量词

固定以下数据。

| 数据 | 精确范围 |
|---|---|
| `X` | 有限状态类型，有可测单点；不另设 `Nonempty X`，实际 `p0 : PMF X` 已排除空状态实验 |
| `A` | 有限、非空行动类型，有可测单点；沿用已通过来源桥的输入范围 |
| `Y` | 任意观察类型；不要求有限，不添加可测性或 lumpability 假设 |
| `M : Model X (fun _ => A)` | 同一有限受控模型；本接口使用其转移行 |
| `q : X → Y`、`sigma : Y → PMF A` | 同一观察映射和时间不变的当前观察随机策略 |
| `p0 : PMF X` | 任意实际初始分布；允许在安全集外有正质量 |
| `K : Set X` | 任意安全集；不要求非空，不预先归一化到 `K` |
| `n : ℕ` | 当前有限窗口的转移次数；记录状态 `X₀,…,Xₙ` |

行动策略不是任意历史依赖策略：

\[
\pi_n(h_Y)=\sigma(\operatorname{last}(h_Y)).
\]

因此已通过的来源桥给出原状态空间上的固定齐次闭环核

\[
L(x,y)=\sum_{a\in A}\sigma(q(x))(a)\,M(x,a,y).
\]

Lean 中这正是 `policyMatrix M (liftedStationaryPolicy q sigma)`；不是另外提交一个矩阵再假设其与风险实验相同。完整实际行动—状态历史的分布是

```lean
causalLaw p0
  (riskMicroControlKernel q (fun _ => M.transitionPMF)
    (observationMarkovPolicy sigma)) n
```

记此分布为 `νₙ`。动作消去的完整状态历史推前身份已经由 `SourcePolicyPathBridgeCheck.actual_state_path_eq_stationary_path` 实际编译通过。对于任意历史依赖或时间变化控制器，下面的 `Qⁿ` 表达式并未自动成立：需要先建立适当扩充状态或逐时核的来源桥。K2 的一般过滤引理本身不要求 Markov 性，但本次复用的矩阵幂 K1 要求上述策略范围。

七模块已有风险端点允许任意完整因果策略，这不把 `viableFamilyPolicy` 自动识别为此处的 `observationMarkovPolicy sigma`。若未来将它接入这个同源矩阵幂接口，必须证明所用实际策略满足同一时间齐次反馈等式 `∀ n hY, π n hY = sigma (riskLastState n hY)`，或另行建立适当状态扩充的来源桥；不能以另一个策略的平稳性替代。

## 2. 存活事件与 K1 输入

定义实际事件

\[
S_n=\{h:\neg\operatorname{riskEverFailure}(x\notin K,n,h)\}
    =\{X_0,\ldots,X_n\in K\},
\qquad s_n=\nu_n(S_n).
\]

事件包含初始状态，区别于只检查末态是否安全。`n=0` 时 `S₀=K` 且 `s₀=p0(K)`。

使用已经通过 K1 的既有定义，不再新建一套来源证书：

\[
Q(v,w)=L(v,w),\qquad v,w\in K,
\qquad \eta_0(v)=p0(v).
\]

`η₀` 是原初始质量在 `K` 上的限制，通常只是次概率行；它没有除以 `p0(K)`。Lean 定义分别为 `killedMatrix`、`safeInitialRow`。已通过的两个 K1 端点给出

\[
\nu_n(S_n\cap\{X_n=v\})=(\eta_0Q^n)(v),
\qquad
s_n=\sum_{v\in K}(\eta_0Q^n)(v).
\]

两式均允许 `K=∅`、`n=0` 和 `sₙ=0`。本轮没有把它们重新放进假设。

## 3. K2 的准确结论

**额外前提仅为当前 `sₙ>0`。** 不要求所有未来窗口正存活，不要求初始律在 `K` 上全支撑，也不要求 QSD、左/右特征向量或不可约性。

从这个实际正质量内部推出

\[
\exists h\in S_n,\quad h\in\operatorname{support}(\nu_n).
\]

然后直接构造

```lean
(νₙ.filter Sₙ hs).map (riskLastState n) : PMF X
```

候选名为 `actualConditionedTerminal`。这一步先过滤真实完整历史，再推前到其末态；没有提前更换初始实验，也没有另外选一个满足某些矩阵性质的分布。

主端点 `actual_conditioned_terminal_mass`：对每个 `v : K`，

\[
\Pr_{\nu_n}(X_n=v\mid S_n)
=\frac{(\eta_0Q^n)(v)}{s_n}.
\]

同一构造的支撑包含于 `K`；对 `x∉K`，其 PMF 原子质量严格等于零。由 K1 总质量等式与联合质量非负性，派生安全子类型上的 PMF

\[
r_n(v)=\frac{(\eta_0Q^n)(v)}{s_n},\quad v\in K.
\]

候选使用已有 `FiniteProbabilityRow.ofRealRow` 构造 `normalizedKilledTerminal : PMF K`，并证明

```lean
actualConditionedTerminal ... hpos =
  (normalizedKilledTerminal ... hpos).map Subtype.val
```

此相等是 `actual_conditioned_terminal_eq_normalized_killed_map` 的结论。第二个 PMF 只是同一已归一化行在安全子类型上的表达；没有作为独立证书加入系统，也没有把来源相等本身设为前提。

## 4. 实际检查过的 Mathlib / 生产 API

本轮读取的是当前钉住源码：Lean `leanprover/lean4:v4.33.1`，Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`。

| API | 实际输入和用途 |
|---|---|
| `PMF.filter p S hs` | `hs : ∃ h ∈ S, h ∈ p.support`；返回原类型上的归一化 PMF。不是 safe subtype 构造器 |
| `PMF.filter_apply` | 实际原子为 `S.indicator p h * (∑' h, S.indicator p h)⁻¹` |
| `PMF.mem_support_filter_iff` | 过滤后支撑为 `S ∩ p.support` |
| `PMF.map_apply` / `PMF.mem_support_map_iff` | 原子求和和实际末态支撑推前 |
| `PMF.toMeasure_apply_fintype` | 同一有限 PMF 的可测事件质量等于原子有限和 |
| `PMF.toMeasure_apply_eq_zero_iff` | 事件零质量等价于支撑与事件不交；用于内部构造 `hs` |
| `FiniteProbabilityRow.ofRealRow` | 对已证非负、和为一的有限实数行构造 PMF；来源文件为 `UEOT/V3/FiniteDiscountedApproxQuotient.lean` |

在当前 Mathlib 的 Probability/MeasureTheory 源内没有查到 `filterSupport`；草稿不依赖这一不存在于已检索接口中的名称。

已有 `FinitePMFProjection.lean` 中的 `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.riskFiberPosterior` 实现的是正投影纤维上的后验，同一命名空间的 `risk_map_mul_fiberPosterior` 已证明其取消归一化因子的身份。本次事件过滤直接使用 Mathlib `PMF.filter`，仅加入一个**私有**有限过滤—推前原子求值引理；没有重复发布一套一般后验 API，也没有把未编译的 QSD 草稿作为依赖。

## 5. 证明路线与需要编译验证的地方

1. 在有限历史类型上，由 `sₙ>0` 和 `toMeasure_apply_eq_zero_iff` 导出真实支撑见证。反向也成立；有限概率测度排除了 `ENNReal` 的无穷质量情况。
2. 展开实际 `PMF.map_apply` 与 `PMF.filter_apply`。有限求和分配得到一般恒等式：

   \[
   ((p\mid S)\circ f^{-1})(z)
   =\frac{p(S\cap\{f=z\})}{p(S)}.
   \]

3. 在同一个 `νₙ,Sₙ,last` 上应用该引理，再用 K1 联合质量端点把分子替换为 `η₀Qⁿ`。分母保留同一实际实验的 `sₙ`。
4. 从 `riskEverFailure` 定义推出存活历史的末态在 `K`，结合过滤和推前的支撑定理，得到外部原子为零。
5. K1 给分子非负、总和 `sₙ`。除以正数得到标准概率行，使用已有 `ofRealRow`。
6. 在 `K` 内按 K2 原子公式比较，在 `K` 外双方都是零，得到两个 PMF 的外延相等。

当前草稿没有递归重建 `causalLaw` 或重证 K1，因此避免重复上轮完整历史乘积类型归约的证明体。仍须通过真实 Lean 运行检查：有限过滤求和的 `simp`/`rw` 匹配、证明无关性涉及的过滤见证、`ofRealRow` 的隐式参数与零时刻归约。静态逻辑正确不等于 elaboration 已通过。

## 6. 边界与反例

### 6.1 `K=∅`

K1 的总和在空子类型上为零，所以所有 `n` 都有 `sₙ=0`，包括 `n=0`。源码给出 `actual_survival_mass_empty`。`sₙ>0` 本身能推出 `K.Nonempty`，由 `safe_set_nonempty_of_survival_pos` 表达；没有另设 `[Nonempty K]` 来隐藏空集边界。

### 6.2 `sₙ=0`

`actual_zero_survival_no_filter_witness` 证明 `Sₙ` 与 `νₙ.support` 没有交点。因此 Mathlib 的过滤构造在此没有所需见证，K2 不提供这个 null event 的条件 PMF。实数公式中的 `0/0=0` 不能产生总和为一的概率行；若另选 fallback，那是额外约定，不是由该零概率实验唯一决定的条件律。

### 6.3 `n=0` 与任意初始律

源码给出 `actual_survival_mass_at_zero` 及 `actual_conditioned_terminal_mass_at_zero`：

\[
s_0=p0(K),\qquad r_0(v)=p0(v)/p0(K)\quad\text{当 }p0(K)>0.
\]

例如初始在两个安全状态 `a,b` 上各有 `1/4`、在不安全状态 `d` 上有 `1/2`，则 `s₀=1/2`，条件末态在 `a,b` 各为 `1/2`。原实验仍由原来的 `p0` 生成；上述过滤没有把不安全的初始质量从无条件实验中抹掉。

### 6.4 当前正存活不意味着下一窗口正存活

两状态 `a,d`，`K={a}`，唯一行动，`p0=δa`，确定转移 `a→d`。则 `s₀=1`、`s₁=0`。一般 K2 在 `n=0` 有意义，在 `n=1` 不提供条件 PMF。这也说明正存活要求不能用 QSD 的正特征值条件替代：本接口无需先存在任何 QSD。

### 6.5 末态安全不等于路径存活

仍取 `K={a}`，但初始 `p0=δd`，确定转移 `d→a`。一步末态安全的概率为一，`S₁` 的概率却是零，因为初态已失败。候选过滤的是包含初始状态的全路径存活事件，不能换成末态属于 `K`。

### 6.6 条件终态律不是完整条件路径结构定理

K2 不声称条件完整路径保留原来的转移概率，也不声称它在不同条件终点窗口下构成同一个齐次 Markov 链。未来存活筛选一般会改变过去状态的相对权重。后续若讨论 Doob 变换、观察后验递推或条件行动分布，必须使用相应条件事件和时间索引；不能从本终态公式直接推出。

## 7. 与 QSD 特化的关系

若今后另给实际初始律由 `r : PMF K` 的包含映射推前而来，并且该同源 `Q` 满足 `rQ=ρr`、`ρ>0`，既有 QSD 幂定理可推出 `sₙ=ρⁿ`，再代入一般 K2 得条件末态仍为 `r`。这是一般 K2 的后续特化，不是 K2 的假设。

本轮没有宣称 Perron/QSD 数据已从任意模型自动构造，也没有证明任意初始条件律收敛到 QSD。根的 `qsd_binding_draft/SameSourceQSDBinding.lean` 仍是独立未编译草稿；本文件没有导入它。后续集成时可由 QSD 特化复用已验证的一般 K2，避免两份并行的一般过滤证明。

## 8. 已通过依赖与尚待完成的门槛

| 项目 | 精确身份与状态 |
|---|---|
| `SourcePolicyPathBridge.lean` | SHA256 `108500fc13229b8faffc9829d886313167142075112bc3f6c023a086c074ae91`；私有聚焦编译已 PASS |
| 来源桥 `.olean` | SHA256 `0ef1132fbfb24b0e571693de99e2729f9a8ede4aa41203fb4b3be67d46915748`；位于 `resume-source-bridge/lean-attempt-002/` |
| `SameSourceKilledPath.lean` | SHA256 `fa4f5ce017d6bfa4d9f3fe77805ad629f1c04f34a7ac3495c9114c432bc6c826`；私有 K1 第 10 轮实际 PASS，前三个关键端点闭包仅标准公理 |
| K1 `.olean` | SHA256 `91c3d26034d72d7abeb140d057c78b55296d4e4e7450cf5b291ccc3ad748d1e5`；位于 `resume-killed-formalization/lean-attempt-010/` |
| 本一般 K2 | 完整私有 Lean 草稿；未编译，未取得公理闭包，未集成生产 |

实际依赖路径根为 `/workspace/scratch/9a8d58b21e30/tmp/finite-encoding-20261021/`。依赖和当前 Mathlib API 的文件身份在 `STATUS.json` 中绑定。过去的 K1 失败、草稿和 PASS 收据均保持原样。

下一项必要动作是独立量词/来源审查，再由根安排一个独立聚焦编译窗口，使用已经通过的两个私有 `.olean` 目录。当前 full build/native 的资源预约没有被本任务打断。任何真实编译结果必须新建实际日志与状态，不能把本合同或静态审查改标为编译 PASS。
