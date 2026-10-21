# 安全前缀适配：实际 K1 事件到同一无限轨迹的有限存活质量

日期：2026-10-21。状态：**CONTRACT_READY_FOR_INDEPENDENT_REVIEW — NO_LEAN_IMPLEMENTATION_OR_EXECUTION**。

本任务只写入 `tmp/finite-encoding-20261021/safe-prefix-bridge-v1/`。此前来源桥、K1、G1–G3 及其独审/执行包全部保持冻结。本合同先由独立审查者核对；命题达成一致后才写最小私有 Lean 并进行必要聚焦编译，不运行全库 build/native，不修改生产、消费者、书稿、Git 或远端。

## 1. 唯一新增连接与已有来源

已过 K1 的公开端点 `SameSourceKilledPathCheck.actual_survival_mass_eq_killed_pow_sum`，给出实际行动—状态历史中从时刻 0 起未失败的实数质量。已过 G3 `SameSourceInfinitePrefixCheck.actual_state_prefix_event_mass`，把任意经完整状态前缀因子化的事件接到同一 `homTrajMeasure` 的圆柱事件。

本任务证明这两者所用的**安全事件确实相同**，然后组合它们。目标只到有限前缀存活质量及实数/ENNReal 两种形式；不在本批增加尾极限、最大不动点、QSD、Doob 或新的无限生存定理。

直接复用生产 `UEOT.V3.RecoveryHittingNonnegative` 中的两个集合，不另造平行定义：

\[
B_n(K):=historySurvivalSet(K^c,n)
 =\{z:\mathrm{Iic}(n)\to X\mid\forall i,\ z_i\in K\},
\]

\[
C_n(K):=survivalSet(K^c,n)
 =(frestrictLe_n)^{-1}(B_n(K)).
\]

这些 API 的参数是**命中目标**，故传 `Kᶜ`。它们的时刻范围包含 0 到 n，共 n+1 个状态。

## 2. 固定且共同的实际数据

质量命题沿用 K1/G3 的原量词：

- `X Y A : Type u`；`[Fintype X] [Fintype A] [Nonempty A]`。
- X 和 A 各有可测结构且单点可测；Y 无有限性或可测性前提。
- 任意原模型 `M : Model X (fun _ => A)`、观察 `q : X → Y`、`sigma : Y → PMF A`、实际初态 `p0 : PMF X`、安全集 `K : Set X` 和 `n : ℕ`。

沿用既有构造：

\[
\pi=liftedStationaryPolicy(q,\sigma),\quad
J=policyTransitionPMF(M,\pi),\quad R=pmfRowKernel(J),
\]

\[
\mu_\infty=homTrajMeasure(p_0.toMeasure,R),\quad
Q=killedMatrix(M,\pi,K),\quad \eta_0=safeInitialRow(p_0,K).
\]

其中 `eta0(v)=(p0 v.val).toReal` **不归一化**。定义式中的行来自同一模型及 sigma，R 来自该同一 J，没有另外给一个核再要求其相等。

实际有限实验仍为

\[
\nu_n=causalLaw\bigl(p_0,
 riskMicroControlKernel(q,M.transitionPMF,observationMarkovPolicy(\sigma)),n\bigr).
\]

这里 sigma 时间齐次且依赖当前观察，不依赖更早历史。不能把一般完整因果策略或 `viableFamilyPolicy` 自动识别为这个 sigma；本批不修改这一来源范围。

## 3. 三个适配命题及一个格式转换推论

以下名称是本目录未来候选端点名，**目前尚无 Lean 源或执行结果**。

### S1 — 状态历史表示与安全前缀相同

候选名 `stateHistoryEquiv_survival_iff`。

只要求 `X : Type u` 和 `[MeasurableSpace X]`，对任意 K、n、`h : CausalHistory X X n`：

\[
\boxed{stateHistoryEquiv(n,h)\in B_n(K)
 \iff SameSourceKilledPathCheck.stateSurvives(K,n,h).}
\]

此纯结构命题不需要有限性、PMF、模型、策略、正概率或 K 的可测性。K1 的 `stateSurvives` 正是“每个记录状态都在 K”，不是仅检查末态。

证明按 n 归纳：时刻 0 使用 G1 既有 `stateHistoryEquiv_zero` 与 `mem_historySurvivalSet_iff`；后继使用 G1 既有 `stateHistoryEquiv_succ`，并直接复用生产

`UEOT.V3.RecoveryHittingDrift.appendHistory_mem_historySurvivalSet_iff`：

\[
appendHistory_n(z,x)\in historySurvivalSet(A,n+1)
\iff z\in historySurvivalSet(A,n)\land x\notin A.
\]

令 A=Kᶜ 即可。不重证区间拼接或完整前缀理论。

### S2 — 原行动记录上的实际安全事件拉回

候选名 `actual_safe_prefix_pullback`。

只要求 `X A : Type u` 和 `[MeasurableSpace X]`，对任意 K、n：

\[
\boxed{(stateHistoryEquiv_n\circ eraseActionHistory_n)^{-1}(B_n(K))
 =\{h:CausalHistory\ X\ (A\times X)\ n\mid
 \neg riskEverFailure(\cdot\notin K,n,h)\}.}
\]

不假设这个集合等式，也不假设来源相等。先用 S1，再在证明内部对 n 作短递归，使用真实定义：`riskEverFailure bad 0 h = bad h`；后继分支是“旧历史已失败，或新状态失败”。本合同**不假定存在名为 `riskEverFailure_succ` 的公开引理**。

K1 源码内的 `stateSurvives_erase_iff` 是 private；它只证明了这段递归计算的先例，不把隐藏内部声明名当作稳定公开 API，也不修改冻结 K1 来暴露它。实际 `eraseActionHistory` 的定义是 `riskHistoryMap id Prod.snd`，始终保留初态和所有微观状态，仅擦除行动。

### S3 — 同一无限过程的有限安全实数质量

候选名 `homogeneous_survival_real_eq_killed_pow_sum`。

在第 2 节的共同实际数据及量词下，对任意 K、n：

\[
\boxed{\mu_\infty.real(C_n(K))
 =s_n:=\sum_{v:K}rowApply(\eta_0,Q^n)(v).}
\]

证明使用已过 G3 `actual_state_prefix_event_mass`，取 B=`historySurvivalSet Kᶜ n`。其左侧由 S2 改写为实际未失败事件，右侧按 `survivalSet` 的现有定义即为 C_n。对 ENNReal 等式应用 `congrArg ENNReal.toReal`，用 `Measure.real` 定义对齐，再调用 K1 公开的 `actual_survival_mass_eq_killed_pow_sum`。同一个 M、q、sigma、p0、K、n 在两个原端点中完全一致。

这没有重建另一份 killed 概率证书，也不把 s_n 的来源当作假设。

### S3E — 同一结果的 ENNReal 形式

候选名 `homogeneous_survival_mass_eq_ofReal_killed_pow_sum`。

在 S3 的相同量词下：

\[
\boxed{\mu_\infty(C_n(K))=ENNReal.ofReal(s_n).}
\]

这是 S3 的短格式转换推论，为后续既有尾极限接口服务，不是另一份独立模型证书。直接复用 Mathlib `MeasureTheory.ofReal_measureReal`。

## 4. real / ENNReal 的准确条件

G3 的 ENNReal 等式应用 `toReal` 是对函数的等式映射，不要求额外假设。要从 S3 恢复 ENNReal，则 `ofReal_measureReal` 要求 `mu∞ C_n ≠ ∞`。该条件由既有 `isProbabilityMeasure_homTrajMeasure` 和 `pmfRowKernel_isMarkov` 自动导出，不能把无限质量经 toReal 得 0 的退化情况忽略。

`s_n≥0` 由 S3 和 `MeasureTheory.measureReal_nonneg` 导出；不把非负性、上界或正存活作为独立数学输入。所有质量事实上不大于 1，但本批无需另造预算结构或新公理。

## 5. 必须保持的边界

- **原 p0 可以含不安全质量。** 初态不先过滤、不条件化；`s0=p0.toMeasure.real K`。若存在初始失败，质量仍计入总失败。
- **n=0 是实质边界。** 前缀仍有一个状态；C_0(K) 是 X0∈K，而不是空约束。
- **K 允许为空。** 不要求 `Nonempty K`；B_n、C_n 均为空，子类型有限和为 0。X 本身若为空则无法提供 p0，API 不凭空制造概率律。
- **零存活允许。** 无除法、归一化或条件 PMF，不要求 s_n>0。
- **始终安全与末态安全不同。** 例如 `a→d→a` 且 K={a}，n=2 末态安全但从未退出事件为假。S1/S2 必须保留所有旧坐标。
- **同一策略身份。** S3 的有限与无限来源都使用 `liftedStationaryPolicy q sigma` 对应的实际原 sigma；任意观察类型 Y 不意味着观察过程本身 Markov。
- **无 QSD/Perron/无限存活结论。** 全部有限 s_n>0 仍不保证极限正；一个安全状态每步以 1/2 退出给出 s_n=2^(-n)。已有全时域受控安全定理继续是已成立结果，不被本批描述为缺口。

## 6. 后续尾极限仅列真实复用路线

本次不实现这一节。完成 S3E 后，命中目标仍传 Kᶜ：

1. 对同一 R 直接调用 `UEOT.V3.Compression.Objecthood.survivalProb_tendsto_neverHitProb`，得到每个点质量初态的尾极限。
2. 用 `UEOT.V3.Compression.Objecthood.homTrajMeasure_apply_eq_lintegral_initial` 混合原 p0；有限 X 下由 `lintegral_countable'` 和 `tsum_fintype` 得有限和。先保留所有 x∈X，不安全初态项由既有 `survivalProb_eq_zero_of_mem` 及尾极限消失，不以 p0|K 替代原实验。
3. 有限和极限得到原 p0 的 `neverHitSet Kᶜ` 质量；已有 `neverHitSet_eq_iInter_survivalSet` 与 `antitone_survivalSet` 保证事件含义正确。如需实数极限，最后使用 `ENNReal.tendsto_toReal`；非无穷条件由概率上界给出。ENNReal 乘法不在 0·∞ 的退化点无条件使用连续性。

不重建 Ionescu–Tulcea，不重做既有全时域安全，不把这条未来组合写作已形式化结果。

## 7. 预期最小实现和验证边界

预期私有文件 `SameSourceSafePrefix.lean`；直接 imports 为冻结 `SameSourceInfinitePrefix`、冻结 `SameSourceKilledPath`、生产 `UEOT.V3.RecoveryHittingDrift` 和 Mathlib `MeasureTheory.Measure.Real`。两项冻结私有模块共同使用同一已过 `SourcePolicyPathBridge`，须绑定其源码和实际通过 olean，而不是重新运行它们。

独立合同审查 CLEAR 后，才写本批最小 Lean。必要聚焦验证沿主智能体已授权的单 Lean 进程、180 秒/轮、绝对 Lake/Lean、独立输出与完整失败保留协议；不得全库 build/native。实现只允许修复 routine elaboration；若必须改变数学量词或结论，先报告并重新达成一致。当前没有实现文件或编译进程。
