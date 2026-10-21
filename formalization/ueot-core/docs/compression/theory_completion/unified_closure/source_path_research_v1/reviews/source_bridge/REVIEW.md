# 同一实际源的完整状态路径桥：独立静态审查

审查者：`/root/audit_resume`。结论：**STATIC_MATHEMATICS_AND_INTERFACE_CLEAR — EXECUTION_PENDING**。

本次只读审查私有候选 `tmp/finite-encoding-20261021/resume-source-bridge/SourcePolicyPathBridge.lean` 及其直接使用的既有定义和定理；没有运行 Lean、测试、原生导出、Git 或远端操作，没有修改候选或生产源码。候选仍是 `WRITTEN_NOT_COMPILED`，不能引用当前七个生产模块的构建结果作为它的构建收据。

## 1. 审查对象与身份

候选 SHA256：`108500fc13229b8faffc9829d886313167142075112bc3f6c023a086c074ae91`，6477 字节。

配套 `CONTRACT.md` SHA256：`a25c675855f3285a5a548902f4153ab75f8e1e41175eaaeffaa2af4ee9fff7bf`。

配套 `STATUS.json` SHA256：`6d18a14a12857aa6994f2e21f94bb93c7b00878e737ce9342afbca5abc3eb158`。其中 `compile_executed = false`，与本次审查范围一致。

候选包含三个表示定义、两个私有辅理、两个公开终端定理及两个 `#print axioms` 指令。完整读取未发现 `sorry`、`admit` 或新增 `axiom` 声明。尚未执行的 `#print axioms` 不是原生公理闭包收据。生产入口 `UEOT.lean` 与 `TheoryCompletion.lean` 中没有该候选的导入。

本次核对的既有表面包括：

| 文件 | 使用的实际定义或证明 | SHA256 |
|---|---|---|
| `UEOT/V3/CoreOperationalAssembly.lean` | `policyTransitionPMF`、对应实数质量公式、`currentState`、`policyPathKernel`、`policyMatrix` | `1f8c4f5be6d3906cdeaa6d88809cc5e0fa5f601ce8b69b21cef67a16dc7a7384` |
| `UEOT/V3/PathError.lean` | `pmfExtend`、`CausalHistory`、`causalLaw`、历史有限类型实例 | `d561a56db79bbd5dd9d01673c5fa7970c7d31199356bd5169a416cd930d917ba` |
| `UEOT/V3/FiniteDiscountedPolicyResolvent.lean` | `StationaryPolicy`、`Model.policyTransition` | `bfd2f5365131022d55ea759db4af01012ca459211f7210274e1620b3ebb8a68a` |
| `UEOT/V3/FiniteDiscountedApproxQuotient.lean` | `Model.transitionPMF` 及实数质量公式 | `0120633e891b2424b1fe329d4973290ecb67571c74e3973788fd65b92967aab6` |
| `UnifiedClosure/DeploymentCoverage.lean` | `coverage_sum_toReal`、`coverage_map_extend_reference` | `5869824d0b059abcdf7e211d330cc944d0e5448275732bfad60f5728d1819585` |
| `UnifiedClosure/FiniteHorizonRisk.lean` | `riskHistoryMap`、`riskLastState`、`risk_last_project`、`riskMicroControlKernel` | `d39f58ddbc8a41edf0221bcbb875c294def320319230a7c113cb18765ad46f08` |
| `UnifiedClosure/FinitePMFProjection.lean` | `risk_map_extend_right` | `0807f667e0473e9bc063b446add02d0d1e477e6dbbf1125f15245093acc1ccc2` |

表中是被读到的相关接口身份，不是完整依赖闭包或新的构建身份。

## 2. 精确数学命题与量词

令 X 为有限微观状态类型、A 为有限非空共同动作类型，M 为既有 `Model X (fun _ => A)`。取任意观察类型 Y、任意映射 q : X → Y、固定的 σ : Y → PMF A。σ 不依赖时间，也不依赖当前观察以外的历史。

定义实际完整观察策略为

\[
\pi_n(h)=\sigma(\operatorname{last}(h))
\]

并使用同一个 M 的转移 PMF 作为每一步真实后继分布。诱导的实数平稳微观策略由

\[
\bar\pi(x,a)=\sigma(q(x))(a).\operatorname{toReal}
\]

直接构造。它的非负性与归一性来自这个实际 PMF，不是另行提供一份策略并要求两者相等。

若 x 是实际完整微观历史 h 的末态，则一次动作—状态核擦除动作后的分布为

\[
\sum_a \sigma(q(x))(a)\,M(x,a,\cdot),
\]

这正是 `policyTransitionPMF M (liftedStationaryPolicy q sigma) x`。这条身份对所有 n、所有 h 成立，含概率为零的历史；其理由是策略本身在所有历史上如此定义，而不是将正概率历史上的条件化命题扩大使用。

对每个初始 PMF p₀、每个自然数 n，候选进一步证明

\[
(e_n)_*\operatorname{Law}_{p_0,M,\pi}
   (X_0,A_0,X_1,\ldots,A_{n-1},X_n)
=\operatorname{Law}_{p_0,P^{\bar\pi}}(X_0,\ldots,X_n),
\]

其中 eₙ 只擦除动作记录。结论是**完整微观状态历史的 PMF 相等**，不是只比较 Xₙ 的边缘，也不是把全部历史替换成当前观察。

两个终端定理的参数中没有独立比较核、独立平稳策略、待假设的行身份或待假设的路径身份。两侧共享 M、q、σ、p₀；核与策略的来源由定义及内部证明固定。因此，这确实补上一条实际来源桥，而不是包装来源相等的外层假设。

## 3. 证明与接口核对

### 一步核

`pmfExtend_map_snd` 展开真实 `PMF.bind` 与 `PMF.map`；映射复合擦除动作后留下恒等映射，得到原动作混合的 bind。该辅理没有概率独立性或归一性的新假设。

`risk_last_project` 把观察历史的末态准确化简为 q(x)。随后对两个 PMF 用逐原子相等证明：PMF 原子都不是无穷，故 `ENNReal.toReal` 在此比较中可逆；有限 A 允许把 bind 的和写为有限和，并逐项取实数。`Model.transitionPMF_apply_toReal` 与 `policyTransitionPMF_apply_toReal` 将两边归约为同一个

\[
\sum_a \bar\pi(x,a) M.\mathrm{transition}(x,a,y).
\]

因此，一步结论不是由把目标放进假设得到，也不依赖未知的经验校准条件。

### 完整状态路径

`currentState_eraseActionHistory` 分别在 n = 0 与后继历史上由定义归约，准确统一两种当前状态表示。

路径归纳的基步是同一个 p₀ 的恒等推前。后继步使用

\[
e_{n+1}(h,(a,x'))=(e_n(h),x')
\]

分解为两次推前：先擦除新动作，再映射此前历史。`risk_map_extend_right` 完成第一步；刚证明的一步核身份将下一状态律写成只依赖 eₙ(h) 的 `policyPathKernel`；`coverage_map_extend_reference` 完成第二步；最后使用归纳假设。这保留了各时刻状态之间的相关性。

`coverage_map_extend_reference` 确实要求有限输入历史、有限输出历史和有限新状态。此处它们分别是 `CausalHistory X (A × X) n`、`CausalHistory X X n`、X，全部由已有有限 X/A 实例得到。Y 不出现在这三个有限性要求中。因此 `Fintype Y` 没有通过这一复用接口被隐式重新引入。

没有在上述归纳中使用条件核的正概率除法、观察可测性、观察可聚合性或反向解码。

## 4. 必须维持的边界

1. **策略是平稳的当前观察策略。** `sigma : Y → PMF A` 在 `observationMarkovPolicy` 定义中固定；对每个时间和每个完整可见历史，动作 PMF 只由当前观察决定。它是一个受限策略类，不是所有一般历史策略都可转换成这种形式的定理。
2. **微观转移也固定。** `fun _ => M.transitionPMF` 明确选择时间齐次的同一个控制模型。时间依赖策略或时间依赖环境需要另外的非齐次核；不能直接复用此处固定 `policyMatrix` 的长期结论。
3. **保留的是 X 路径。** q 不要求单射，但候选并不证明 Y 过程为 Markov，不提供观察强可聚合性，也不把当前观察纤维当成历史后验支持。
4. **擦除动作会丢失动作事件。** 结论可用于完整状态路径事件的相等；一般依赖动作记录的失败事件仍需证明其为状态事件的拉回，或保留原动作—状态律。不能仅凭此定理转移任意动作事件。
5. **有限性范围未扩大。** X 和 A 仍有限，A 非空是显式实例。Y 可任意。没有可测空间要求是因为目标仅为 PMF 相等；后续转成测度事件结论时，应使用相应可测结构和事件条件。
6. **没有长期性质或最优性结论。** 任意有限平稳链仍可能可约或周期；这条身份不推出唯一稳态、Cesàro 的具体值、混合率、QSD、生存概率、Bellman 最优性或无限路径对象。M 中既有的奖励和折扣字段没有参与本次状态路径证明。
7. **无正概率前提有正确原因。** 这里没有从实际条件分布恢复策略的步骤；策略和转移在所有历史上已定义，故可逐点证明。它没有改动此前真实后验支持身份中的正概率历史条件。

## 5. 不能把一般历史策略 Markov 化的具体反例

取 X = A = {0,1}、q 为恒等，控制转移确定为下一状态等于所选动作，初始状态公平取 0 或 1。第 0 步总选动作 0，第 1 步选择初始状态 X₀；之后任意完整定义。可取奖励恒为 0、折扣为 1/2，以符合现有有限控制模型字段。

长度为 2 的状态路径律是

\[
\tfrac12\delta_{(0,0,0)}+\tfrac12\delta_{(1,0,1)}.
\]

两个正概率历史在第 1 步具有相同当前状态 0，但下一状态条件律分别是 δ₀、δ₁。任何仅依赖当前状态的第 1 步核都必须在这两个历史上使用同一行，无法同时保留两条路径的条件概率。因此，即使允许时间非齐次，只看当前 X 的 Markov 核也不能保留此完整路径律。将该行替换成公平混合会产生原实验中不存在的交叉路径。

候选通过固定当前观察策略的定义排除了这个反例；没有悄悄弱化为只匹配单时刻边缘。该反例是本审查中的数学说明，尚未写成 Lean。

## 6. 与既有长期研究的准确关系

这份候选证明的两条目标，在实际编译前仍属于已静态审查的证明草稿。它们若通过内核检查，将把实际动作—状态实验接到既有 `policyPathKernel`，从而为后续同源长期研究提供所需的第一条来源身份。

候选没有实例化此前四状态 θ 模型，也没有构造 killed 矩阵。下一条实质桥应从同一个 `policyMatrix M (liftedStationaryPolicy q sigma)` 对安全域 K 直接取限制，而不再独立提供一个 Q 并假设它来自实际闭环。随后证明实际状态路径在 0,…,T 始终属于 K 的质量等于受限初始行乘该 killed 矩阵的 T 次幂再乘全一向量；初始律不全在 K 时要明确初始限制，条件生存律则必须保留分母为正的条件。

同样，矩阵轨道与路径末态律的对应、具体四状态实例、QSD 的特征关系及归一化条件、T = 0 和灭绝边界、无限路径扩展，各需各自的定义和证明。当前候选没有把这些作为自己的结论；此前 `SAME_SOURCE_STATIONARITY_QSD_RISK.md` 的完整书面研究也没有因此自动成为已完成 Lean API。

## 7. 最小后续行动与复用范围

未发现需要在一次聚焦编译前修正的数学命题、来源参数或量词。下一步由主智能体在其受钉住环境中编译该精确私有文件，并保存真实退出码、输出和两个公理打印结果。任何 Lean elaboration 修复均保留原失败源码与日志，按最终实际源码差异增量复核，不必重做既有七模块审查。

当前静态 CLEAR 仅绑定本页给出的候选哈希及已读接口含义；它不是完整依赖构建证明，不是新模块的原生类型比较，不是生产导入、消费者授权或 canonical 验收。正式生产化时，它应作为新候选单独计入实际 source scope，不能沿用此前七模块范围及计数。

若代码只发生证明实现修复且签名、构造与来源不变，可据保留的差异进行小范围复核。若改成任意历史策略、时间依赖模型、当前观察路径、动作事件或 killed/QSD 端点，则超出本次审查范围。
