# UEOT-QM v31.4：效应与实际稳定性合同

日期：2026-10-19 UTC。此文记录新增模块的作者范围核对、另一协作审阅者的独立语义复核，以及实际聚焦编译和公理审计。它不替代本轮统一包、CI 或主线验收回执。

## 1. 已完成的数学切片

新增 [Effects.lean](../../../formalization/ueot-qm/UEOTQM/Effects.lean) 与 [Stability.lean](../../../formalization/ueot-qm/UEOTQM/Stability.lean) 共 **60 个显式 theorem**。本轮对这些定理及全部 **14 个公开定义**逐项执行公理审计，共 **74 个新增命名目标**，真实结果为 PASS，仅使用 propext、Classical.choice、Quot.sound。

本次关闭的是 QMU-04 的一个实际量子接口：从完整 Kraus 通道及 Born 效应概率出发，证明全部效应响应的收缩、实际通道扰动的一步界、严格正事件的条件化界，再调用已有 Core M-TC 组合定理。量子一步递推已经由矩阵定义推出，没有作为结构中的最终结论字段输入。

| 模块 | 显式定理 | 公开定义 | 实际审计目标 |
|---|---:|---:|---:|
| Effects | 30 | 10 | 40 |
| Stability | 30 | 4 | 34 |
| 合计 | **60** | **14** | **74** |

14 个定义中，9 个构造返回携带证明的 Effect 或 Density；其余 5 个是概率、完整通道或上确界数据定义。本次为了明确覆盖整个公开接口而全部列入审计，不把 14 个定义全称为证明构造，也不将这些名字冒充编译器全部内部常量的普查。

## 2. 共同输入及矩阵语义

系统载体是同一个有限指标类型 $\iota$，带 Fintype 与 DecidableEq。矩阵仍是已有的有限复矩阵，Density 仍要求矩阵正半定且复迹为 1。每个 Instrument 只提供有限 Kraus 表以及完整性恒等式

$$
\sum_o\sum_k K_{o,k}^{\dagger}K_{o,k}=I.
$$

两个被比较的完整通道可以有不同的有限结果类型或 Kraus 指标类型，但作用于同一个 $\iota$。固定通道序列可随时间改变。此处没有从 generic Core 重构复 Hilbert 空间、Born 规则或 CP 仪器。

新 Effect 结构仅包含 matrix、positive、complement_positive 三项，分别规定实际矩阵 $E$、$E\succeq0$ 与 $I-E\succeq0$。零效应、恒等效应、补效应都是已证明合法的构造。

Born 配对采用原有 pairing：

$$
P_E(\rho)=\operatorname{Re}\operatorname{tr}(E\rho).
$$

**非交换矩阵的关键步骤：并未假设 $E\rho$ 本身正半定。** pairing_nonneg 使用固定 Mathlib 的 MatrixOrder API，从完整 PSD 谓词推出 $E=B^\dagger B$，再用迹的循环性把配对转到正半定矩阵 $B\rho B^\dagger$ 的迹。这是对所有已有 Density 的定理，输入没有被限制成事先选定的 Gram 表。

随后，补效应给出

$$
0\leq\operatorname{Re}\operatorname{tr}(EX)\leq\operatorname{Re}\operatorname{tr}(X)
\quad (X\succeq0),
$$

以及 $0\leq P_E(\rho)\leq1$、$P_{I-E}(\rho)=1-P_E(\rho)$。这些是实际 Born 概率界。

## 3. 完整仪器、选择分支与记录词

Instrument.pullbackEffects 允许每个结果 $o$ 使用不同的后续效应 $E_o$，定义

$$
\Psi((E_o)_o)=\sum_o\sum_k K_{o,k}^{\dagger}E_oK_{o,k}.
$$

其正性逐项推出；其补效应满足

$$
I-\Psi((E_o)_o)
=\sum_o\sum_k K_{o,k}^{\dagger}(I-E_o)K_{o,k}\succeq0,
$$

其中等式实际使用完整 Kraus 恒等式。保效应的结论不属于输入字段。

Instrument.channel 把所有结果分支相加；channelState 由已经证明的 PSD 保持与迹保持构造输出 Density。pullbackEffect 把所有 $E_o$ 取成同一个 $E$，证明真实通道的 Heisenberg 对偶关系

$$
P_E(\Phi(\rho))=P_{\Phi^*(E)}(\rho).
$$

branchEffect 将被选结果的后续效应设为 $E$，其他结果设为零。它因此仍为合法效应，但**选择分支并未被宣称为迹保持通道**。对严格正的原有分支概率 $p$，probability_posterior 从原有实际归一化矩阵推导

$$
P_E(\rho_{\mid o})=
\frac{P_{\Phi_o^*(E)}(\rho)}{p_\rho(o)}.
$$

recordTest 依照已有 chronological word 顺序递归构造 Effect；recordTest_matrix 证明其实际矩阵等于原有 recordEffect。于是每个有限记录词都有

$$
0\preceq E_w\preceq I,\qquad
\operatorname{response}(\rho,w)=P_{E_w}(\rho)\leq1.
$$

词长度没有统一上限。这里说的是每个有限词，不是以有限样本集合代替全部词。

## 4. 全部效应响应的伪距离

Stability 的定义是

$$
d_{\mathrm{eff}}(\rho,\sigma)
=\sup\bigl\{|P_E(\rho)-P_E(\sigma)|:E\text{ 为 Effect}\bigr\}.
$$

零效应保证集合非空；Born 概率界保证集合以 1 为上界。因此这里的实数上确界具有已证明的适用条件，不依靠空集或无界集合的默认值推导结论。

已经证明：

- 每个实际效应的概率差不超过这个上确界；
- $0\leq d_{\mathrm{eff}}\leq1$、自身距离为零、对称性与三角不等式；
- 一个数是距离的上界，当且仅当它控制所有效应的概率差；
- 距离为零，当且仅当所有效应的 Born 概率相等；
- 每个共同后续有限记录词的响应差不超过该距离。

本轮的零距离定理 **effectDistance_eq_zero_iff** 的右侧是“所有效应概率相等”。它没有在 Lean 中进一步证明 Density 相等，也没有安装 MetricSpace 实例。故本轮正式计账为 **all-effect response pseudodistance**。

本轮没有证明它与迹范数、trace distance 或 diamond norm 的识别关系；这些传统范数的附加识别与分离证明不能从本文件标题或命名中默认为已完成。

## 5. 真实完整通道收缩与扰动

完整 Kraus 通道把任意输出效应拉回为合法输入效应，因此实际证明

$$
d_{\mathrm{eff}}(\Phi(\rho),\Phi(\sigma))
\leq d_{\mathrm{eff}}(\rho,\sigma).
$$

通道缺陷也有实际定义：

$$
\delta(F,G)=
\sup\left(\{0\}\cup
\{d_{\mathrm{eff}}(F(\rho),G(\rho)):\rho\text{ 为 Density}\}\right).
$$

额外插入 0 处理空 Density 论域，且已证明 $0\leq\delta\leq1$。这不是由调用者填入最终一致性的 oracle 字段，也**不是计算该上确界的算法**。

Instrument.channelState_perturbation_bound 把收缩、三角不等式和定义中的统一上界组合为

$$
d_{\mathrm{eff}}(\Phi(\rho),\Psi(\sigma))
\leq d_{\mathrm{eff}}(\rho,\sigma)+\delta(\Phi,\Psi).
$$

该结论只对所定义的输出 Density 比较负责。特别地，channelDefect 比较的是**丢弃结果后的完整通道**；它不自动控制两个不同仪器的历史结果联合分布。若要纳入经典记录寄存器、不同自适应仪器的误差或 ancilla 稳定误差，必须先定义对应的扩大模型并证明所需桥。

## 6. 严格正事件的条件化

令 $p_\rho(o)>0$、$p_\sigma(o)>0$。对同一个 Instrument 的同一个选定结果，实际归一化概率公式和分支拉回给出

$$
d_{\mathrm{eff}}(\rho_{\mid o},\sigma_{\mid o})
\leq\frac{2d_{\mathrm{eff}}(\rho,\sigma)}{p_\rho(o)}.
$$

这是明确、保守的放大上界，不宣称常数最优，也不把条件化称为收缩。若另给 $\eta>0$ 与 $\eta\leq p_\rho(o)$，则上界可替换为 $2d_{\mathrm{eff}}(\rho,\sigma)/\eta$。对应定理仍显式保留第二个后验的正概率见证。

另有 probability_pos_of_effectDistance_lt：

$$
d_{\mathrm{eff}}(\rho,\sigma)<p_\rho(o)
\quad\Longrightarrow\quad p_\sigma(o)>0.
$$

因此小于事件质量的误差可以提供第二态事件仍为正的证明。零概率事件不会被偷偷赋予后验，原有 posterior 的严格正质量合同保持不变。

## 7. 实际调用 Core M-TC

channelTrajectory 从实际完整 Kraus 通道序列递归定义

$$
\rho_{n+1}=\Phi_n(\rho_n),\qquad
\sigma_{n+1}=\Psi_n(\sigma_n).
$$

channelTrajectory_transport_certificate 使用已经证明的一步量子扰动界，实际调用既有 [Transport.scalar_transport_certificate](../../../formalization/ueot-qm/UEOTQM/Transport.lean)，该定理继续实际复用 Core 的 weighted_chain_bound。量子应用不再把一步递推留成未经证明的应用侧前提。

取 $L_n=1$ 与已定义的 $\delta_n=\delta(\Phi_n,\Psi_n)$，最终得到

$$
d_{\mathrm{eff}}(\rho_n,\sigma_n)
\leq d_{\mathrm{eff}}(\rho_0,\sigma_0)+
\sum_{j<n}\delta_j.
$$

channelTrajectory_response_sub_le_sum 进一步把此界交付给**同一个共同后续操作库**的任意有限词响应。它不是两个不同自适应仪器全部记录律的比较定理，也不声称已有程序的轨迹解释与本次 Lean 递归定义对所有输入一致。

## 8. 实际验证与独立复核

固定编译器为官方 Lean 4.33.1；依赖继续使用原固定 Mathlib 版本 0df444a360eaa60ab8c11dca51a86af692955474。

| 检查 | 实际结果 |
|---|---|
| Effects 聚焦编译 | exit 0；最终版本无警告；会话 27527 |
| Stability 聚焦编译 | exit 0；最终版本无警告；会话 59793 |
| 74 个命名公理报告 | 74 个唯一名字，无缺项、重复或意外项；exit 0；会话 68193 |
| 基础公理集合 | 仅 propext、Classical.choice、Quot.sound |
| 独立语义复核 | CLEAR；由不同协作审阅者完成，未将其只读复核冒充机器编译 |
| Core 修改 | 无 |

作者记录的临时原始证据路径为 /tmp/qm314_metric_stage/MetricAudit.lean、metric-audit-names.json、metric-axiom-audit.log、metric-audit-receipt.json 与 stability-build.log。最后一份编译日志为空，是无诊断输出且进程返回 0 的真实聚焦结果。后续统一构建、运行验证、CI 和源码发布以整包回执单列，不由本节扩展认领。

固定源身份：

| 文件 | 字节 | SHA256 |
|---|---:|---|
| Effects.lean | 9597 | 3346f36a3d467cb7b52d346dfafa4e49828e39a3ee02e29ac12e6783473eef23 |
| Stability.lean | 14431 | de253ab45a4e45e2c8457dcbf3ad0c5cfd553e13a3a1dbc791f7d59eb2b5d389 |

实际公理日志 SHA256 为 22f87da113c96ddfe3bf31ba11dcb65e6fbead95b666a99ed6c3491bcce52653。审计请求源 SHA256 为 109b54b10d79927eab54294fdb115eb6b41180feeacdbe11e8e3b13a5b8a96c0。

独立语义复核明确核对了：零效应与有界性；空 Density 论域；完整性推导补效应；选择分支不冒充 TP；两个严格正概率见证和 $\eta$ 门槛；实际通道缺陷定义；共同有限载体；共同后续协议；以及范数识别、数值上界算法、一般自适应仪器差异和 ancilla 扩大模型的未完成边界。

## 9. 公开声明清单

以下清单按实际源顺序列出全部 60 个显式定理与 14 个公开定义；命名列表与真实公理输出集合完全一致。

### Effects：30 个显式定理

```text
UEOTQM.pairing_sub_left
UEOTQM.pairing_add_right
UEOTQM.pairing_sum_right
UEOTQM.pairing_nonneg
UEOTQM.Effect.ext
UEOTQM.Effect.zero_matrix
UEOTQM.Effect.one_matrix
UEOTQM.Effect.complement_matrix
UEOTQM.Effect.pairing_nonneg
UEOTQM.Effect.pairing_le_mass
UEOTQM.Effect.probability_nonneg
UEOTQM.Effect.probability_le_one
UEOTQM.Effect.probability_zero
UEOTQM.Effect.probability_one
UEOTQM.Effect.probability_complement
UEOTQM.Instrument.channel_posSemidef
UEOTQM.Instrument.trace_channel
UEOTQM.Instrument.channelState_matrix
UEOTQM.Instrument.pullbackEffects_matrix
UEOTQM.Instrument.pairing_pullbackEffects
UEOTQM.Instrument.pairing_pullbackEffect
UEOTQM.Instrument.probability_channelState
UEOTQM.Instrument.branchEffect_matrix
UEOTQM.Instrument.pairing_branchEffect
UEOTQM.Instrument.probability_branchEffect_one
UEOTQM.Instrument.probability_posterior
UEOTQM.recordTest_matrix
UEOTQM.recordEffect_complement_posSemidef
UEOTQM.response_eq_effect_probability
UEOTQM.response_le_one
```

### Effects：10 个公开定义

```text
UEOTQM.Effect.zero
UEOTQM.Effect.one
UEOTQM.Effect.complement
UEOTQM.Effect.probability
UEOTQM.Instrument.channel
UEOTQM.Instrument.channelState
UEOTQM.Instrument.pullbackEffects
UEOTQM.Instrument.pullbackEffect
UEOTQM.Instrument.branchEffect
UEOTQM.recordTest
```

### Stability：30 个显式定理

```text
UEOTQM.Effect.probability_abs_sub_le_one
UEOTQM.effectGapSet_nonempty
UEOTQM.effectGapSet_bddAbove
UEOTQM.Effect.probability_sub_le_effectDistance
UEOTQM.effectDistance_nonneg
UEOTQM.effectDistance_le_iff
UEOTQM.effectDistance_le_one
UEOTQM.effectDistance_self
UEOTQM.effectDistance_comm
UEOTQM.effectDistance_triangle
UEOTQM.effectDistance_eq_zero_iff
UEOTQM.response_sub_le_effectDistance
UEOTQM.channelDefect_bddAbove
UEOTQM.channelDefect_nonneg
UEOTQM.channelDefect_le_one
UEOTQM.effectDistance_le_channelDefect
UEOTQM.channelDefect_self
UEOTQM.Instrument.channelState_effectDistance_le
UEOTQM.Instrument.probability_sub_le_effectDistance
UEOTQM.Instrument.probability_pos_of_effectDistance_lt
UEOTQM.Instrument.channelState_perturbation_bound
UEOTQM.normalized_probability_difference_le
UEOTQM.Instrument.posterior_effectDistance_le
UEOTQM.Instrument.posterior_effectDistance_le_of_probability_lower_bound
UEOTQM.channelTrajectory_zero
UEOTQM.channelTrajectory_succ
UEOTQM.channelTrajectory_transport_certificate
UEOTQM.scalarBudget_one_eq_sum
UEOTQM.channelTrajectory_effectDistance_le_sum
UEOTQM.channelTrajectory_response_sub_le_sum
```

### Stability：4 个公开定义

```text
UEOTQM.effectGapSet
UEOTQM.effectDistance
UEOTQM.channelDefect
UEOTQM.channelTrajectory
```

### 9 个返回证明结构的构造

```text
UEOTQM.Effect.zero
UEOTQM.Effect.one
UEOTQM.Effect.complement
UEOTQM.Instrument.channelState
UEOTQM.Instrument.pullbackEffects
UEOTQM.Instrument.pullbackEffect
UEOTQM.Instrument.branchEffect
UEOTQM.recordTest
UEOTQM.channelTrajectory
```

另行审计的 5 个数据定义是 Effect.probability、Instrument.channel、effectGapSet、effectDistance、channelDefect，均位于 UEOTQM 命名空间。
