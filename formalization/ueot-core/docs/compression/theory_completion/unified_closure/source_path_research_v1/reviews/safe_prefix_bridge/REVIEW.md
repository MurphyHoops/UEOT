# 安全前缀适配合同：独立量词与接口审查

**结论：CONTRACT_AND_API_CLEAR_FOR_PRIVATE_IMPLEMENTATION — IMPLEMENTATION_AND_EXECUTION_PENDING。**

审查者 `/root/audit_resume`。本次只读合同、真实公开定义/定理与受钉住的既有私有接口，复用已完成的 K1 和 G1–G3 审查，不重复其完整数学或构建检查。当前目录没有 Lean 实现文件。本次未运行 Lean、lake、native、测试或 Git，也未改作者、生产或书稿。

可以按合同的三个适配命题加一个 ENNReal 格式转换推论实现最小私有文件；没有需要新增的数学假设或先行修正的量词。真正 Lean PASS 及公理输出仍需另行取得。新的任务与已冻结 Stage6 发布范围分离。

## 1. 绑定与已读接口

| 对象 | SHA256 |
|---|---|
| CONTRACT.md，9373 字节 | `30efc7a40f4b04efb390440e2289f072373fa6b8f039bdcd45958315a4963488` |
| API_INPUTS.json，7597 字节 | `d55e17e5dec33b52a7b193cd788003fc954e8a92e032325109d3b7e842c2f482` |
| STATUS.json，1284 字节 | `1b5491a25fb09592a1454e6576008db832437cd07e62398095e8f73e01fddd7e` |

24 个 API/证据输入的当前实际字节和哈希均匹配，明细见 `REVIEW_INPUTS.json`。三份私有源及其各自已通过的 olean 都是准确的先行接口：动作擦除来源桥、K1、G1–G3。这里不把 API 输入快照说成新的完整构建授权。

实际公开表面核对如下：

| 接口 | 可用性及本次意义 |
|---|---|
| `SameSourceKilledPathCheck.stateSurvives` | 公开定义；基步要求初态在 K，后继要求旧历史全安全且新状态在 K。 |
| `SameSourceKilledPathCheck.actual_survival_mass_eq_killed_pow_sum` | 公开定理；真实原行动记录的未失败实数质量等于同源受限初始行与 killed 矩阵幂的和。 |
| `SameSourceInfinitePrefixCheck.stateHistoryEquiv_zero/succ` | 公开、实际已通过；将递归完整状态历史接到既有 appendHistory。 |
| `SameSourceInfinitePrefixCheck.actual_state_prefix_event_mass` | 公开、实际已通过；原行动记录上经完整状态前缀因子化的任意事件，等于同一无限圆柱事件质量。 |
| `RecoveryHittingDrift.appendHistory_mem_historySurvivalSet_iff` | 生产公开定理；只要求 X 可测结构，提供旧前缀安全且新态未命中目标的准确后继式。 |
| `RecoveryHittingNonnegative.historySurvivalSet/survivalSet` | 已有集合定义，参数是命中目标；本批传 Kᶜ，避免另造相同事件。 |
| `MeasureTheory.ofReal_measureReal` | 公开格式转换；唯一有限性条件是该事件测度不等于 ∞，可由这里真实概率律自动推出。 |

K1 的 `stateSurvives_erase_iff`、`finite_event_mass`、`finite_map_event_mass` 都是 private。合同准确把它们限定为阅读参考，不调用其隐藏内部名称，也不修改冻结 K1。`riskEverFailure` 实际定义在 `MicroscopicFailureRisk.lean`；不能假定另有未经核对的 `riskEverFailure_succ`。

## 2. S1/S2：来源事件等式真实推出

S1 只是历史表示的结构命题：对任意 X、K、n 和 h，`stateHistoryEquiv n h` 属于 `historySurvivalSet Kᶜ n`，当且仅当公开递归谓词 `stateSurvives K n h`。除了表示等价所需的 X 可测结构，无需有限性、概率律、策略或 K 可测性。

证明路线充分：n=0 的 `piUnique.symm` 将原始状态放入唯一坐标；后继先用已过的表示递推，再直接用生产 `appendHistory_mem_historySurvivalSet_iff`。代入目标 Kᶜ 后，新增条件是“新状态不在 Kᶜ”，等价于在 K。没有丢掉任何旧坐标，也不需要重新证明 Iic 区间拼接。

S2 将 S1 用于 `eraseActionHistory` 后，剩余步骤确实只是两份真实递归定义的短归纳：

\[
\begin{aligned}
stateSurvives(K,n+1,erase(h,a,x))
 &\iff stateSurvives(K,n,erase(h))\land x\in K,\\
\neg riskEverFailure(\cdot\notin K,n+1,(h,a,x))
 &\iff \neg riskEverFailure(\cdot\notin K,n,h)\land x\in K.
\end{aligned}
\]

基步同为原初态属于 K。这个内部递归足以得到合同要求的**集合等式**；不需要把集合等式、核身份或路径身份放进假设。它对所有原始历史逐点成立，包括概率为零的记录，因为此处没有条件概率除法。

S2 无需 A 的可测结构：只是原行动记录集合上的函数拉回等式。到 S3 调用 G3 并在实际原记录上取测度时，合同才要求 X/A 的有限性和可测单点，与既有 G3/K1 完全对齐。

## 3. S3：原初态、原策略、同一矩阵

S3 沿用同一个 M、q、sigma、p0、K 和 n。有限实验仍是原 `riskMicroControlKernel` 的 causalLaw；无限核直接由同一 `policyTransitionPMF M (liftedStationaryPolicy q sigma)` 转成 PMF 行测度；Q 则是该同一策略矩阵在 K 上的限制。

初始行 `safeInitialRow p0 K` 仅保留 p0 在 K 上的原质量，不作归一化。合同没有假定 p0 支持于 K，也没有把初态换成条件分布或 QSD。

令 G3 的 B 为既有 `historySurvivalSet Kᶜ n`：左侧用 S2 变成实际 `¬riskEverFailure` 事件；右侧由现有 `survivalSet` 定义变成同一无限轨迹的有限安全圆柱。对这条 ENNReal 等式应用 `toReal` 后，K1 公开总质量端点给出目标有限和。两侧的数据一致，无独立的任意 Q 或自由初始行被混入。

sigma 仍是固定、时间齐次、仅依赖当前观察的随机反馈。任意 Y 不需要有限性/可测性，不能据此认定观察过程 Markov，也不能认定一般历史策略或 `viableFamilyPolicy` 等于这个 sigma。

## 4. real / ENNReal 和零质量

G3 的 ENNReal 等式应用 `congrArg ENNReal.toReal` 不需正质量或额外有限性假设；这只是函数保持相等。`Measure.real` 正是对应事件测度的 `toReal`，所以可与 K1 的实数目标准确接合。

反向恢复 ENNReal 的 S3E 不能无条件使用 `ofReal(toReal a)=a`；合同已经保留真实要求 `a≠∞`。这里 `pmfRowKernel` 是从 PMF 行构造的 Markov 核，p0.toMeasure 是概率测度，因此既有 `isProbabilityMeasure_homTrajMeasure` 给出整条无限轨迹为概率律，事件质量自动有限。实际 `ofReal_measureReal` 的签名正接受这一条件，并可用有限性机制消解。

因此 S3E 是 S3 的短格式推论，未增加模型或事件范围。s_n 非负可从 S3 与 `measureReal_nonneg` 推出，无需作为新输入；s_n=0 也完全允许。实现时不得加入 `0<s_n`、`Nonempty K` 或单位初始安全质量来消除类型或自动化困难。

## 5. 边界核对

| 情况 | 应保留的结果 |
|---|---|
| n=0 | 前缀含 X0；质量为原 p0(K)，不是 1。 |
| p0 在 K 外有质量 | 初始失败原样计入；不得过滤/归一化 p0。 |
| K=∅ | 因前缀包含时刻 0，有限安全事件为空；安全子类型和式为 0，包括 n=0。 |
| s_n=0 | 所有身份仍成立；不构造条件 PMF、不除以 s_n。 |
| 退出后返回 K | 末态安全不等于全前缀安全；a→d→a、K={a} 的例子正确排除这种误判。 |
| 所有有限窗存活为正 | 不推出无限存活质量为正；逐步半概率退出的例子给出 2^(-n)→0。 |

这些边界在合同目标的量词中均未排除。空 X 无法提供 p0，这是概率分布输入的真实限制，不需要额外随意构造默认状态。

## 6. 实现准入和后续范围

没有发现阻止最小私有实现的数学或实际 API 问题。可按冻结合同实现 S1、S2、S3 和 S3E；短内部递归可重新证明所需 action-erasure 安全逻辑，不能引用 K1 private 短名。预期 elaboration 风险是 n=0 的递归类型/可测实例、补集成员化简、`Set.ofPred`/集合谓词表示、有限安全子类型的自动实例，以及 `Measure.real` 的显式展开。这些应通过证明体和必要显式参数解决，不增加数学前提。

此时仍没有 Lean 源，也没有新的公理或执行收据。后续实现与聚焦运行按 root 已授权的单进程协议进行，保留原合同状态和所有实际失败；通过后只需对本合同到最终源码和真实执行做独立增量审查，不重跑 G1/K1 或全库/native。

尾极限章节准确列为路线：真实目标仍为 Kᶜ，可复用已有点初态尾极限、原初态混合和递减事件连续性；不能把未来的混合/有限和/实数极限适配提前写成当前已完成定理。若以后只需证明原 p0 的存活质量趋于永不失败质量，可先考虑直接对同一 μ∞ 使用既有递减事件连续性，再在需要逐初态分解时加入混合接口；这不改变本批有限质量目标。
