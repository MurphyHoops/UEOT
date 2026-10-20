# UEOT-QM v31.5：实际随机混合与精确 TV 预算

## 本切片已经证明什么

新模块是 `UEOTQM/Mixture.lean`，公共命名空间是 `UEOTQM.Mixture`。它从实际密度矩阵和完整 Kraus 仪器构造随机混合，证明由有限权重数据控制的全效应距离和全输入态通道缺陷。这里的“实际”是指结论中的映射就是声明的 Kraus 矩阵作用；没有把最终更新公式、收缩性或误差上界作为结构字段。

设有限集合 β 上两组权重满足逐项非负、各自总和为 1，记

\[
\operatorname{TV}(p,q)=\frac12\sum_{b\in\beta}|p_b-q_b|.
\]

对同一个密度态库 `ρ : β → Density ι`，模块构造真实矩阵和

\[
\operatorname{mix}(p,\rho)=\sum_b p_b\rho_b,
\]

并从 PSD 的非负线性组合以及迹的线性性证明它仍然是密度态。对每个真实效应 `0 ≤ E ≤ I`，Born 概率等于各成员概率的加权和。因此

\[
d_E(\operatorname{mix}(p,\rho),\operatorname{mix}(q,\rho))
\le\operatorname{TV}(p,q).
\]

这是真正的 TV 界，保留了系数 `1/2`，没有退化成未减半的 l1 界。证明将每个 `f_b ∈ [0,1]` 写成 `(f_b − 1/2) + 1/2`，用双方归一化消去常数项，再用 `|f_b − 1/2| ≤ 1/2` 和有限和三角不等式。无需先识别 trace norm。

同一组权重下，两个密度态库的误差满足

\[
d_E(\operatorname{mix}(p,\rho),\operatorname{mix}(p,\sigma))
\le\sum_b p_b d_E(\rho_b,\sigma_b).
\]

同时改变权重及成员时，已证明上界 `TV(p,q) + Σ_b q_b d_E(ρ_b,σ_b)`。

## 真正的通道构造和最坏情况界

给定 `I : β → Instrument ι O κ`，`weightedInstrument p I` 的 Kraus 索引为 `β × κ`，在结果 `o` 与索引 `(b,k)` 处采用成员的矩阵 `I_b.kraus o k` 和权重 `p_b`。完整性从各个 `I_b.complete` 与 `Σ p_b = 1` 推导。转换成普通仪器后的真实矩阵是

\[
\widetilde K_{o,(b,k)}=\sqrt{p_b}K^{(b)}_{o,k}.
\]

零权重允许出现，平方根为零；不需要排除零概率分支。

模块分别证明分支、Heisenberg、完整通道和密度态输出的加权恒等式。最后的 `channelDefect` 采用既有定义：对全部密度输入的 `effectDistance` 取上确界，并插入零处理空密度态论域。因而

\[
\delta(\Phi_p,\Phi_q)\le\operatorname{TV}(p,q),
\qquad
\delta(\Phi_p,\Psi_p)\le\sum_b p_b\delta(\Phi_b,\Psi_b).
\]

同时改变权重和通道库的上界为 `TV(p,q) + Σ_b q_b δ(Φ_b,Ψ_b)`。同权重和联合变化两条定理允许两库分别采用不同的有限结果类型和 Kraus 索引类型，但每个库内部采用共有的类型。所有矩阵共享同一有限载体 `ι`。

## 精确有理预算如何消费

`RationalWeights` 只有有理权重以及非负、归一化证明；`toWeights` 保留这些前提。`rationalTV` 与 `rationalJointBudget` 只包含有限有理算术。`tv_toWeights` 证明有理 TV 转成实数后与真实 TV 完全相同。

因此，一个已在 Lean 中证明的有限有理不等式 `rationalTV p q ≤ budget`，能够通过 `channelDefect_weight_change_le_rational_budget` 直接给出实际通道对全部输入态的缺陷上界 `(budget : ℝ)`。这一同库路线不要求先提供一个未知的通道缺陷证书。

若库本身也改变，`channelDefect_fixed_weights_le_rational_sum` 和 `channelDefect_joint_change_le_rational_budget` 仍明确要求逐成员的真实缺陷上界证明。它们是可组合规则，不会把数值采样、外部声称或未验证的 oracle 输出升级成证明。

## 公开声明清单与审计范围

本模块有 **23 个显式 theorem、7 个 def、2 个输入结构**。7 个定义中，`density`、`weightedInstrument`、`instrument`、`RationalWeights.toWeights` 是 4 个带证明内容的构造；`tv`、`rationalTV`、`rationalJointBudget` 是 3 个数据定义。

所有 23 个定理及全部 7 个定义合计 **30 项**均独立执行了 `#print axioms`。原始结果是 `axioms.log`；机器名单是 `declarations.json`；审计文件是 `Audit.lean`。结果仅包含 `propext`、`Classical.choice`、`Quot.sound`，没有新增公理，也没有 `sorry`、`admit` 或 `native_decide`。

定理列表（均在 `UEOTQM.Mixture` 下）：

1. `tv_nonneg`
2. `tv_self`
3. `tv_comm`
4. `tv_le_one`
5. `expectation_sub_le_tv`
6. `density_matrix`
7. `probability_density`
8. `density_weight_change_le_tv`
9. `density_fixed_weights_le_sum`
10. `density_joint_change_le`
11. `instrument_kraus`
12. `instrument_branch`
13. `instrument_heisenberg`
14. `instrument_channel`
15. `instrument_channelState`
16. `channelDefect_weight_change_le_tv`
17. `channelDefect_fixed_weights_le_sum`
18. `channelDefect_joint_change_le`
19. `tv_toWeights`
20. `density_weight_change_le_rational_budget`
21. `channelDefect_weight_change_le_rational_budget`
22. `channelDefect_fixed_weights_le_rational_sum`
23. `channelDefect_joint_change_le_rational_budget`

## 实际验证和例证

官方 Lean 4.33.1 的最终 focused 编译返回 0，且无警告；`.lake/build/lib/lean/UEOTQM/Mixture.olean` 已生成。30 项公理审计返回 0。此处仅报告新模块的本地检查，整包集成、公共审计入口、CI 与主线验收由根代理另行完成。

独立的 `Examples.lean` 也实际编译返回 0，包含五条定理：

- 两个有理权重向量 `(3/4,1/4)` 与 `(1/4,3/4)` 的 TV 精确为 `1/2`。
- 对任意实际两通道库，使用这两组权重的通道缺陷不超过 `1/2`。
- 二维基态与第一个投影效应的 Born 概率逐项求出。
- 这两个正交基态的混合确实使全效应距离等于 `1/2`，证明该系数可达到。
- 两边权重完全相同但分别使用恒定的不同正交态库时，TV 为零而效应差达到一；故“同库”前提不能删去。

这些例证是 Lean 定理，不是有限输入抽样。例证属于临时交付，未擅自增加到公共模块定理统计。

## 保留的严格边界

1. 本模块在已经声明的有限复矩阵、Born 效应和完整 Kraus 仪器模型内部证明后果；不宣称从 UEOT Core 单独推出全部量子重构输入。
2. `effectDistance` 仍是全效应伪距离。本切片没有新增矩阵分离定理，也未证明它与 trace norm 或 diamond norm 的识别。
3. 通道缺陷界针对忘记结果后的完整通道。虽然分支恒等式已证明，但不把选择分支归一化后验声称为无条件收缩。
4. 没有自动证明加入任意辅助系统后的稳定性、一般自适应仪器差异或无限维推广。
5. 有理解释定理不等于 Python 导出器、JSON 解码器、一般程序消元或全生产链的正确性证明。外部数据仍须构造真实的 `RationalWeights` 与实际仪器，并完成相应有限算术证明。
6. 混合权重预算给出了通道缺陷的一条可认证上界路线，不声称能计算任意 Kraus 对的最优缺陷。

范围说明使用完整文字；不沿用总著旧版与上游接口冲突的 E/O/X 字母含义。
