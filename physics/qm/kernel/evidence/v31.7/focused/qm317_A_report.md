# UEOT-QM v31.7 A 路最终交付报告

**状态：三个交付门均已实际聚焦验证通过，三份源码冻结。** 本报告不把聚焦成功替代 root 的统一源绑定、公理审计或远端验收。

## 1. 完成的核心数学责任

`QuantumPurification.IsPure` 对完整 `Density` 空间量化。归一向量外积的极点性质由正锥压缩、PSD Gram 因子和迹一识别实际证明；秩一形式没有被用作纯性的定义。`exists_purification (ρ : Density ι)` 从原有 `ρ.positive` 推出 Gram 因子，向量化后形成完整联合密度空间中的纯态，实际 `RectangularChannel.discardRight` 将其精确送回原态。调用者不提供 Gram 参数或纯性前提；没有隐藏的 `Nonempty` 假设，空载体由真实迹一条件排除。

`OperationalSystems` 给实际有限载体、状态、效应、过程、产品和丢弃。`Presentation` 只有操作；`Laws` 的七项规律分别在经典、实、复三个完整状态模型中证明。三套过程分别是真实随机核、有限实 Kraus、有限复 Kraus。`PurificationExistence` 与 `LocalTomography` 是独立候选 `Prop`。`complex_purification` 证明前者成立；`classical_not_purification` 和 `real_not_localTomography` 分别否定对应候选。`core_first_marginal_no_purifies` 使用既有真实 Core 终端商首边际，没有扩大先前有限接口切片的科学范围。

## 2. 实际验证与计数

| 对象 | 实际结果 | 声明与审计范围 |
|---|---|---|
| QuantumPurification | `qm317_A_purification_round2.log`，EXIT 0，8727 含缓存 jobs | 25 theorem，34 显式声明，34 审计目标 |
| OperationalSystems | `qm317_A_operational_round3.log`，EXIT 0，8776 含缓存 jobs | 25 theorem，55 显式声明，62 审计目标 |
| QuantumPurificationExamples | `qm317_A_witness_round3.log`，EXIT 0 | 13 theorem，20 声明，20 实际逐名公理输出 |

主模块合计 50 theorem、89 显式声明、96 审计目标。审计目标额外包含 5 个结构 `.mk` 和 2 个带实例属性的公开投影 `FiniteSystem.finite`、`FiniteSystem.decidableEq`。主模块逐声明输入保存在 `/tmp/qm317_A_targets.lean` 与 `.json`；依 root 指示没有另行重复运行，等待统一 gate 实际覆盖。见证的 20 个目标已逐名与输出对齐，全部只含 `propext`、`Classical.choice`、`Quot.sound`。

十份真实轮次日志全部保留。早期失败日志不作验收，失败时 elaborator 输出的临时 placeholder 公理记录亦不计为通过。最终三份源码没有 `sorry`、自定义公理、`native_decide` 或实现替换。

## 3. 独立有限见证

Bell 振幅取 `(1+i)/2`，与标准正实振幅仅差整体相位，外积是标准 Bell 投影。`bell_isPure` 在完整四维联合密度空间中成立；`bell_marginal` 精确得到 `I/2`；`bell_purifies_in_complex_interface` 把它接入共同操作接口。

三个范围对照均已通过：经典混态的普通扩展存在，但任意有限辅助经典系统都没有纯扩展；单元素受限状态集使同一完整单纯形中的混态成为“受限极点”，说明完整状态量词不能删除；解除实局部效应限制后，同一对实联合态可以被具体复乘积效应区分。最后一个对照使用共同接口，未把实模型标为纯化失败。

## 4. 边界与下一步

本轮证明的是“归一向量态必为极点”和所有有限复密度态的纯化存在。尚未证明极点必为向量态、任意纯化的本质唯一性、辅助空间等距比较或复模型的一般局部层析。下一轮若讨论任意纯化的唯一性，须先补反向极点刻画或明确只从向量纯化域起步。

Gram 选择使用 `Classical.choice`，不是已认证的数值平方根算法。实状态采用复矩阵内的全实取值 PSD 迹一子类型。当前结果没有从 UEOT 全部 Core 语义推出候选原则、复数域或完整物理理论，也没有排除所有其他可能模型。有限系统接口只证明所用操作和七项规律，没有声称完成庞大的范畴相干性库。

## 5. 冻结身份与交叉审查

- `UEOTQM/QuantumPurification.lean`：SHA-256 `fb0692ed93c14aa7182cb09b3e205060f493f005672d16a69fc6e8da59ca5b6d`，11143 bytes。
- `UEOTQM/OperationalSystems.lean`：SHA-256 `cb764474361fa833390fbe33e3d1b363a05c78639e0819d5d5de4648c1b5b55e`，19370 bytes。
- `scripts/witnesses/QuantumPurificationExamples.lean`：SHA-256 `57b764a8d9b7787509a0f8a5e92f04a86abc5f3f4db58f3c441be2e29a1c3e34`，6655 bytes。

C → A 的完整状态空间、Gram、偏迹、候选原则与三适配审查位于 `/tmp/qm317_C_quantum_purification_review.md/json`。A → B 对矩形通道、实际记录块、双边际、任意有限协议、全事件 TV 与实际含标签缺陷的审查位于 `/tmp/qm317_A_memory_cross_review.md/json`。第57章书稿审查位于 `/tmp/qm317_A_ch57_review.md/json`。

A 没有改 Core、共享导出、统一审计、CI、正式书稿或远端，没有运行全库构建。所有重型编译使用统一 `flock`，现在没有活动 A Lean 进程。
