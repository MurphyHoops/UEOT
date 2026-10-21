# 同源 QSD 特化：复用一般 K2 的实际条件终态

本文件是原 `BINDING.md` 之后的增量合同。原稿、原清单和 `SameSourceQSDBinding_v1.lean` 保持原样。当前源码的真实执行状态由 `lean-attempt-004/STATUS.json`、`lean-attempt-004/lean.log` 与 `COMPILE_PASS.json` 记录：**私有聚焦 Lean PASS，尚未进入生产或 canonical main。**

合同编号对应已审 `CONTRACT_KILLED.md` 的 **K3（QSD 特化）**。一般 K2 是任意实际初态、当前正存活条件下的真实过滤终态律；本次直接复用其已经通过编译与独立增量审查的实现，不重复证明 `PMF.filter` 的有限求和适配。

## 1. 固定同一源，明确策略范围

类型假设为有限状态 `X`、有限非空行动 `A`，以及二者的可测空间和可测单点实例。观察类型 `Y` 没有有限性假设。固定实际模型 `M`、观察映射 `q : X → Y`、时间齐次当前观察随机策略 `sigma : Y → PMF A`。完整风险历史采用 `observationMarkovPolicy sigma`，状态核采用同源的 `liftedStationaryPolicy q sigma`。

安全集 `K : Set X` 可以任意给出，但本特化的额外输入 `r : PMF K` 本身要求安全子类型承载一份概率分布。不能在空安全集上构造此输入；这不为一般 K1 或 K2 添加非空假设。

唯一的 killed 核与真实初态分别定义为

```lean
Q := killedMatrix M (liftedStationaryPolicy q sigma) K
p0 := r.map Subtype.val
```

记 `rR v = (r v).toReal`。输入左特征关系为

```lean
hleft : ∀ v, rowApply rR Q v = rho * (r v).toReal
```

`safeInitialRow_map_subtype` 从 `PMF.map` 与 `Subtype.val` 的单射性证明真实初态限制行等于 `rR`。来源身份和初态行身份都是证明结论，没有加入假设。`hleft` 是明确的数学输入；本模块不证明这种概率左特征行的存在、唯一性或吸引性。

当前七模块的风险层允许完整因果策略，这不会自动把其中的 `viableFamilyPolicy` 识别为本模块的时间齐次 `sigma`。后续组合必须提供实际策略反馈等式，或先完成所需的状态扩充及来源桥。

## 2. 原始含行动记录路径的精确质量

令

```lean
nu n := causalLaw (r.map Subtype.val)
  (riskMicroControlKernel q (fun _ => M.transitionPMF)
    (observationMarkovPolicy sigma)) n
S n := {h | ¬ riskEverFailure (fun x => x ∉ K) n h}
```

`S n` 同时要求初态和其后 `n` 次转移的状态安全。对每个 `n : ℕ` 和 `v : K`：

\[
\nu_n(S_n\cap\{X_n=v\})=\rho^n r_R(v),\qquad
\nu_n(S_n)=\rho^n.
\]

这两个端点直接复用 K1 的实际事件到 killed 幂公式、已证初态限制行等式，以及生产 `QSDPerron.leftPerron_pow` / `qsd_survival_mass_pow`。不需要 `rho > 0`。由同一核非负、次随机和 `r` 的归一化，另证明 `0 ≤ rho ∧ rho ≤ 1`。

当 `rho > 0` 时，`sameSource_KilledQSDGOA` 直接构造既有 `KilledQSDGOA Q rR rho`；它使用本实际核，并未另造一个并列证书。既有 GOA 谓词要求严格正的 `rho`，因此不能用它覆盖零特征值下仍然成立的未归一化质量公式。

## 3. 当前正存活条件律与零特征值边界

新端点 `actual_qsd_conditioned_terminal_law_of_survival_pos` 只要求当前窗口的真实质量 `hpos : 0 < nu_n(S_n)`，结论为

```lean
actualConditionedTerminal M q sigma (r.map Subtype.val) K n hpos =
  r.map Subtype.val
```

左侧严格使用一般 K2 的定义：先对同一含行动记录的真实路径 PMF 按 `S n` 过滤，再推前到真实终态。其证明先把 K2 的 `normalizedKilledTerminal` 与 `r` 比较，利用实际联合质量和实际总质量消去共同的非零因子 `rho^n`；然后调用 K2 已证的实际条件律与归一化 killed 行推前相等。没有重新证明过滤公式，也没有把条件分布的来源等式当作前提。

两个边界端点给出精确范围：

\[
\nu_n(S_n)>0\quad\Longleftrightarrow\quad n=0\ \lor\ \rho>0.
\]

若 `rho = 0` 且 `n ≠ 0`，真实生存事件没有 PMF 支持见证，因而不给出该零事件上的条件 PMF。

| 情形 | 本次已形式化结论 | 范围限制 |
|---|---|---|
| `n = 0`，包含 `rho = 0` | 总生存质量为 `1`；当前正存活条件终态律等于实际初态 `r.map` | 初态已由 `r : PMF K` 构造在安全集中 |
| `rho = 0, n ≠ 0` | 生存质量为 `0`；没有 `PMF.filter` 所需支持见证 | 不用实数 `0/0` 充当条件概率 |
| `rho > 0` | 每个有限窗口正存活；条件终态律不变 | 不据此声称无限时域正存活或完整条件路径等于齐次 Doob 路径 |
| 空安全集 | 一般 K1、K2 的空集结论保持可用 | 本 QSD 特化不能提供不存在的 `PMF K` |
| 任意实际 `p0` | 一般 K2 继续给出 `eta0 Q^n / s_n` | 此处的 `rho^n` 特化只用于实际 `p0 = r.map` |

原端点 `actual_qsd_conditioned_terminal_law` 的严格正 `rho` 接口原样保留，其证明现在直接调用更一般的当前正存活端点；不同支持证明的选择由 Lean 的证明无关性处理，实际过滤事件和 PMF 均相同。

## 4. API 保留和实际复用

原 10 个公开定理的声明文本逐字保留。新增 3 个公开定理：

1. `actual_qsd_survival_pos_iff`：精确的正存活窗口判据。
2. `actual_qsd_conditioned_terminal_law_of_survival_pos`：只要求当前真实正存活的条件终态律。
3. `actual_qsd_zero_root_no_filter_witness`：零特征值在正时间的实际零事件边界。

原 `actual_qsd_masses_ofRealRow` 继续使用生产 `FiniteProbabilityRow.ofRealRow` 将非负、和为 `1` 的实数左行转为真正 PMF，并把这份 PMF 的推前作为实际初态。没有额外输入 `[Nonempty K]`。

一般 K2 的直接复用端点为 `actual_survival_pos_iff_support`、`normalizedKilledTerminal_apply_toReal`、`actual_conditioned_terminal_eq_normalized_killed_map` 和 `actual_zero_survival_no_filter_witness`。本文件已移除旧私有重复证明 `filter_map_apply_real` 与 `survives_last_mem`。

## 5. 真实验证及未覆盖门槛

实际聚焦编译第 4 轮通过，前三轮原始失败、逐轮源码快照与日志全部保留。最后修复使用 `convert` 和 `congr!` 显式处理 K1 与生产 `QSDPerron` 的矩阵幂可判定相等实例差异。最终源码没有新增透明度选项、结论性假设或未完成证明。

10 个关键端点的实际 `#print axioms` 输出仅含标准 `propext`、`Classical.choice`、`Quot.sound`。这是这 10 个端点的实际传递公理闭包，不充当本模块全量原生声明审计。完整生产源身份、工具链、缓存来源及三个私有依赖的源码和 `.olean` 身份另由收据绑定。

本次没有运行 `lake build`、native 或远端任务，没有修改生产、消费者、书稿或 Git。私有聚焦 PASS 与独立增量审查仍应分开记录；生产集成、全量公开声明注册、canonical 授权和 resulting-main 验证由根智能体另行安排。本模块的完成不等于待研究的完整有限窗条件路径、Doob 来源绑定或无限路径桥已经完成。
