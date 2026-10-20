# 第 51–52 章只读数学与分类审查

**结论：数学、机器成果范围与先例边界 CLEAR；第 51.4 节有一处非阻断的类型说明建议。**

审查对象：`/tmp/qm315_book_stage/chapters_51_52.md`。复核者为 `finite_response`。本轮没有修改书稿、Lean 或运行源码，也没有重新运行已验收测试。新增的只有本审查备忘录和它的源身份回执。

## 1. 第 51 章逐项核对

### 51.1 / P-QMX-01

书稿的权重仅含逐项非负、总和为一；与 `UEOTQM.Mixture.Weights` 一致。密度混合的 PSD 与迹一不是结构中额外假设的结论，而是 `density` 的构造证明。

书稿明确一个库内部使用共同有限结果集和 Kraus 指标集，与 `weightedInstrument : Weights β → (β → Instrument ι O κ) → WeightedInstrument ι O (β × κ)` 一致。普通仪器的实际矩阵确为 sqrt 权重乘成员矩阵；`instrument_branch`、`instrument_heisenberg`、`instrument_channel` 和 `instrument_channelState` 分别承担正文公式。

第 49.5 节的补零引用确实对应既有 Weighted/Ragged 内容。零权重项合法，不需要删除协议结果。运行实现保存有理权重而不计算有理数不存在的平方根，与正文一致。

### 51.2 / P-QMX-02

TV 的一半因子确实由 `expectation_sub_le_tv` 的中心化和双方归一化推出。概率取值 `[0,1]` 来自 Effects 模块的实际 Born 效应界。`density_weight_change_le_tv` 对全部效应取上确界，`channelDefect_weight_change_le_tv` 再对全部密度输入取上确界；正文量词及同库前提正确。

`channelDefect` 定义额外插入零，正确覆盖空密度态论域。正文采用有实际输入态的物理语境，不会产生错误的空集上确界解释。

### 51.3 / P-QMX-03

联合变化上界中的成员权重确实是右侧的 `q_b`，与 `channelDefect_joint_change_le` 相符。固定权重版本与 `channelDefect_fixed_weights_le_sum` 相符。两库允许不同 `O/κ`，但仍共享 `β` 和有限矩阵载体 `ι`；正文准确。

交换模型得到 `p_b` 版本在数学上成立，使用距离与缺陷的对称性；应把它理解成正文直接推论，不另计一个本轮新增 Lean 声明或已实现的联合预算运行 API。正文“可择取”没有明确宣称这些额外接口已经存在，因此不构成错误。

同权异库的 I/X 反例正确：一个合法输入态和效应的差一已经足够否定零上界，无须枚举全部输入态。

### 51.4 / P-QMX-04

本节列出的四个 Lean 名称全部真实存在，且参数/结论匹配：

- `UEOTQM.Mixture.RationalWeights.toWeights`
- `UEOTQM.Mixture.tv_toWeights`
- `UEOTQM.Mixture.channelDefect_weight_change_le_rational_budget`
- `UEOTQM.Mixture.channelDefect_joint_change_le_rational_budget`

联合预算仍需要逐成员 `herror`，没有把外部数字升级为证明。正文也明确排除了 Python 解析、循环、索引和文件传输的自动程序正确性；范围清楚。

长期误差式可由既有 `UEOTQM.channelTrajectory_effectDistance_le_sum` 与逐项预算上界组成，前者确实经 `channelTrajectory_transport_certificate` 和 `Transport.scalar_transport_certificate` 消费 Core 组合证书。这里存在真实的代码消费链，与第 52.3 节仅有结构类比不同。

**唯一建议：补充现成轨迹接口的固定类型约束。** 该接口形如 `I : ℕ → Instrument ι O κ`、`J : ℕ → Instrument ι O' κ'`。每一串的结果/Kraus 类型在步数之间固定，左右两串允许不同类型，并共用 `ι`。“时间依赖的库可逐步声明”可以指相同类型上的矩阵与权重随时间变化，但不应读成已经无须适配地接受任意 `O_j/κ_j`。

建议在该段加一句：

> 现有 Lean 轨迹接口在每一串演化内固定有限结果与 Kraus 指标类型，左右两串可不同，并共享同一矩阵载体；各步索引改变时，有限时域须先提供明确的补零或重索引适配。

这是补全机器接口说明，当前不等式本身没有数学错误。本审查未编辑该段。

### 51.5

I/X 尖锐见证与重复恒等组件的非尖锐例均正确。运行预算只是上界，指纹标识具体 Kraus 表示，程序检查与通用 Lean 量词分开，均与已读代码一致。有限同载体、忘记结果后的完整通道、未给任意旁系统 diamond 距离的边界完整。

## 2. 第 52 章逐项核对

### 52.1 / P-QCE-01

平均包含初态，范围为 `range N`，需要 `0 < N`；准确对应 `averageState`。`matrix_residual` 的端点是 `iterateState ... N − ρ`，不是 N−1；正文正确。`effectDistance_residual_le` 的 `1/N` 控制平均自身的一步不变残差，不是到某个指定平稳态的距离；正文明确区分。

### 52.2 / P-QCE-02：谱范数与拓扑

范数是复 Euclidean 空间诱导的 operator norm。对 Hermitian 密度矩阵，它是最大特征值；这里没有偷换成 trace norm，也没有声称任意矩阵的该范数等于最大特征值模。

另核固定 Mathlib 的 `Mathlib/Analysis/CStarAlgebra/Matrix.lean`：`instL2OpMetricSpace` 使用 `replaceTopology` 和 `replaceUniformity` 保留既有逐项矩阵拓扑，随后 `Matrix.Norms.L2Operator` 的范数实例采用该结构。因此正文的拓扑说明成立。

`density_operatorNorm_le_one` 从谱分解、非负特征值和迹一证明范数上界；`densityMatrices_closed` 使用闭 PSD 锥与连续迹；`densityMatrices_compact` 用实际有限维 closed-and-bounded；`continuous_channel` 由实际通道的有限维实线性化得到连续性。残差 `2/N` 的常数及范数种类均对齐。没有将这些核心结论放在证书字段中。

### 52.3 / P-QCE-03：子列及 Core 关系

`exists_stationary_subsequence` 的返回值确实包含密度态、平稳性、StrictMono 子列与矩阵趋近。Lean 的总平均序列使用样本数 `n+1`；正文的正整数样本子列可取 `N_k = φ(k)+1`，不改变结论。`subsequence_limit_invariant` 要求 StrictMono，保证指标趋于无穷；极限的 PSD 与迹一由闭性得到。仅给通道时的存在性正确增加正维/非空有限载体前提，并用 `normalizedIdentity` 构造种子。

源码没有调用 `OccupationLimitInvariance` 的残差极限定理或 `P-PER-02`。它在 QM 矩阵对象上独立证明相应闭合步骤。另只读核对 Core 的 `OccupationLimitInvariance.lean`，其接口确实是残差趋零与连续可观测极限闭合，紧性等由适配层承担。因此书稿称研究接口/结构对应、明确否认直接代码消费，分类准确。

也只读核对了 `Survival.lean`：它实际引用 `UEOT.V3.QSDPerron` 的 `leftPerron_pow`、`qsd_survival_mass_pow`、`qsd_all_steps` 和 Doob 定理。因此“下一章直接消费 Core，而本章不是”有源码依据。

登记 P-QCE 结果时，不应仅凭概念对应或传递 import 就把 `M-OI-01/P-PER-02` 写为实际 Core theorem dependencies。可以另列 `conceptual_analogy` 或“研究来源”，并明确 `formal_consumption: false`。

### 52.4 / N-QCE-01

Pauli X 的周期轨道、平均对角元、奇偶残差，以及恒等通道非唯一平稳态均正确。正文明确说这些反例是代数证明与精确运行见证，不计入通用 Lean theorem 数量；没有冒称本轮已形式化完整轨道不收敛定理。

单次有限运行无法独立证明无限序列不收敛，但本章给出了完整奇偶代数论证，有限运行只是核验实例，因此来源范围合理。

### 52.5 与标准先例

已打开所引原始论文 Burgarth、Chiribella、Giovannetti、Perinotti、Yuasa，*Ergodic and Mixing Quantum Channels in Finite Dimensions*，New Journal of Physics 15, 073045 (2013)，arXiv:1210.5625v3。其 §2 明确列出有限 CPTP 固定态存在性，并将唯一固定态的 ergodicity 与所有输入逐时收敛的 mixing 分开。

原文：https://arxiv.org/abs/1210.5625v3

全文：https://arxiv.org/html/1210.5625v3

书稿把本轮机器成果限定为 Cesàro 子列与存在性，未借引用移入文献的更强遍历/混合结论；先例使用正确。该结果属于已知有限量子通道结构的实际接口形式化，不应宣传成 UEOT 首次发现平稳态存在。最后对无限维紧性不足的提醒也合理。

## 3. E/O/X 的兼容迁移口径

冻结合同 `physics/interfaces/CORE_PHYSICS_CONTRACT.md` 是字母含义的唯一来源：

| 字段中的字母 | 必须保留的合同含义 |
| --- | --- |
| C | Core-derived：实际 Core 来源与形式定理链 |
| B | Bridge：类型明确的 Core—物理桥，注明证明/猜想状态 |
| S | Sector-selection principle：额外理论选择原则 |
| P | Standard physical input：标准物理或经验约定输入 |
| E | Effective/modeling assumption：尺度或适用范围下的有效模型假设 |
| O | Observable consequence：由声明输入链得到的可测或可数值基准输出 |
| X | Open conjecture：尚未通过证明/经验关卡的 UEOT 特定猜想 |

**依赖角色与论证状态是两个独立维度。** 建议现有 `dependency_class`（或等价多值字段）仅使用上述合同；不要求为了本建议重命名已冻结的字段。原书的经验/开放/反例标签移至完整文字的 `argument_status`，并另用 `formal_status` 表示通用 Lean、正文证明或运行见证。

迁移不得机械替换字母：

- 旧 E“经验输入”应保留为 `argument_status: empirical_input`。其依赖角色要依据内容区分标准外部输入 P 与可观测后果 O；不能因为旧字母 E 就宣称存在有效近似。
- 旧 O“开放问题”不能一律变为 X。只有尚待验证的 UEOT 特定命题才是合同 X；已知数学结果尚未移植 Lean，属于 formalization backlog，并非科学猜想。
- 旧 X“反例”应保留为 `argument_status: counterexample`。已给出反例的失败推论不能迁移成“开放猜想”。

N-QCE-01 的清晰示例是：`argument_status: counterexample`；`formal_status: prose_proof_and_exact_runtime_witnesses`；`lean_theorems: []`。依赖类别按实际物理输入和可观测见证记 P/O 等适用项目，**不记 X**。其所反驳的“存在平稳态即推出逐时收敛或唯一性”是被反例否定的无条件推广，不是仍然等待验证的命题。

本两章末尾的 E/O 使用已符合合同通常含义。登记时仍宜逐结果标注；不要因为整章包含一次 Core 组合接口，就把章内每个独立矩阵引理都登记为直接 Core 推导。

## 4. 审查结论

没有发现需阻断两章整合的数学错误、函数名错误、循环前提、伪造通用 Lean 状态或先例误占。建议落实第 51.4 节的固定类型补句，并按上述双字段口径迁移 E/O/X。其余四个指定重点——51.4 名称、52.3 类比分类、N-QCE-01 证据等级、谱范数/拓扑——均已明确核对通过。
