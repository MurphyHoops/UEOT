# v31.5 Python 混合部分独立只读复核

结论：**CLEAR**。复核者 `finite_response`，未编辑或重新运行下列文件：

- `physics/qm/kernel/ueot_qm/finite_dynamics.py`
- `physics/qm/kernel/tests/test_finite_dynamics.py`
- `physics/qm/kernel/demo_v315.py`

本复核只对混合权重部分及它依赖的实际仪器/指纹接口发表结论，不把作者报告的测试通过当作本复核者重新执行的结果。

## 实际构造和前提

`ProbabilityWeights` 接受精确整数或 Fraction，额外拒绝布尔值，拒绝空、负或总和不为一的输入。TV 计算检查索引数一致；没有接受外部猜测的误差数值。

`mix_instruments` 检查每个成员是已有的完整 Instrument，匹配成员数、矩阵维度和结果标签。即使某成员的混合权重为零也保留这些上下文检查。它把成员自身的 Kraus 权重与混合权重相乘，拼接真实加权项；构造所得 Instrument 时再次精确检查完整性。已有 KrausTerm 的维度限制使本运行实现继续处在 1 至 4 维范围内。

Python 可以拼接不同成员/结果的不同长度 Kraus 列表。通用 Lean Mixture 定理的一个库内部采用共同有限 κ；既有 Weighted/Ragged 语义提供有限零填充解释，但没有在本 Python 代码中声称已经完成程序到 Lean 的自动细化。

## 预算、指纹和例证边界

`MixtureWeightBudget` 从同一个成员元组构造左右两个实际仪器，预算固定为左右权重的 TV。它的 `component_fingerprint` 借助既有 InstrumentLibrary 的精确序列号动作标签与 Kraus payload 绑定实际成员库，包括矩阵、原有项权重、结果和维度；没有宣称表示不变的通道等价类指纹。左右概率权重独立保存，所以这个字段是成员库指纹，而不是整个预算对象的唯一标识。

测试中 I/X 的输入态与投影给出达到 1/2 的下界例；预算本身仍从通用 TV 理由产生。相同成员重复的例子说明上界不必等于最优距离；同权重不同库的例子说明前提不可删除；含原有非整数项权重的 Hadamard 例验证嵌套权重相乘。

演示将 `computed_TV_upper_budget` 和 `attaining_P0_difference` 分开报告，没有用有限态/效应取样最大值定义预算，也未声称 diamond 范数界。模块与演示明确将 Python 执行证据和 Lean 数学证明分开。未发现混合部分的范围、指纹或预算说明越界。

## 可用于总著的前提—证明—反例映射

| 前提 | 证明对应 | 边界见证 |
| --- | --- | --- |
| 非负权重，双方分别归一化 | 中心化 Born 概率并消去总权差，得到精确半 l1 / TV | 错误总和、负权重、浮点参数被运行接口拒绝 |
| 共有实际通道库与有限矩阵载体 | 真实 sqrt 加权 Kraus 完整性及全输入态上确界 | 单成员权重均为 1，但 I 与 X 的输入态响应可差 1 |
| 只把 TV 声称为上界 | `channelDefect_weight_change_le_tv` | 重复同一个通道时权重 TV 可非零而通道相同 |
| 每个库内共有结果上下文 | 分支拼接与完整性推导；零权重也不改变声明合同 | 零权重成员的错标签、错维度仍被拒绝 |
| 有理预算必须与真实构造一致 | `tv_toWeights` 和 `channelDefect_weight_change_le_rational_budget` | I/X 与 `(3/4,1/4)`、`(1/4,3/4)` 使 1/2 界达到 |
| 同时改库须另外证明成员误差 | `channelDefect_joint_change_le_rational_budget` 的逐成员 herror | 同权异库反例阻止把零 TV 当成零总误差 |
