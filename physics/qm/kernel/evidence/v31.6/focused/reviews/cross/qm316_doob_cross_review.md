# UEOT-QM v31.6：QuantumDoob 交叉语义审查

## 结论

对本次读到的两份源，未发现阻塞性数学或接口问题。此结论是独立源码语义审查，不替代 C 的官方 Lean 验收；我没有为 C 启动任何编译。两份源已由作者冻结并通过 focused 验收；本文已独立核对最终源码 SHA，未启动重复编译。

## 关键推导核对

### 左特征条件推出真正完备性

设 S 是显式可逆复矩阵，T=S⁻¹，H=S†S，源选中分支 Kraus 为 Kₖ。`transformed_gram` 证明

    ∑ₖ(SKₖT)†(SKₖT) = T†(∑ₖKₖ†HKₖ)T。

代入实际左特征关系 E†(H)=rH 后，`doob_complete` 用 r>0 与 ST=I 推出 r⁻¹ 加权 Gram 为 I。`doobWeighted` 仅承载这个已证明的恒等式，随后通过既有 `WeightedInstrument.toInstrument` 得到普通 Kraus instrument。新 filter 只输入两个矩阵及两侧逆恒等式，没有把 transformed completeness 或 stationary state 输入为字段。

### 任意初态的有限条件化

`mass_apply_pos` 使用密度 PSD、可逆共轭，以及 PSD 零质量只能是零矩阵，证明每个密度的滤波质量严格为正。`eigenmetric_successMass` 对任意复矩阵及任意有限 n 给出滤波质量的 rⁿ 缩放。结合 r>0，`eigenmetric_successMass_pos` 对所有初始密度证明实际源连续成功质量大于零。

`doob_finite_conditioning` 的结论是精确有限关系：先以实际有限记录条件化再滤波归一化，等于从滤波初态做 transformed instrument 的 n 次真正分支作用。归一化中的源成功质量消去，剩余滤波质量用左特征式归约。该定理没有右特征态假设；正记录质量仍显式出现在 Density 归一化的类型中，且同模块已在当前条件下证明可满足。

### 右特征态的额外责任

源几何生存率 pₙ=rⁿ、条件态固定，以及 transformed stationary state 另行输入实际右特征式 E(ρ)=rρ。新源码没有把这些性质扩张到任意初态。统一态的一步成功概率为 33/128，与 3/16 不同，专用负对照明确保护该区别。

### 见证确实作用在完整复矩阵空间

`source_branch_formula` 与 `transformed_branch_formula` 均全称量化任意 `X : Operator (Fin 2)`；索引枚举只用于证明每个矩阵条目中的复数环恒等式，并未枚举或取样 X。后者正确使用复 `X.trace`，得到

    D(X) = X/3 + Tr(X)/3 [[1,1],[1,1]]。

因此对非 Hermitian 输入仍有意义。`input_coherence_retained` 单独证明源把 E₀₁ 送到 E₀₁/16；`success_kraus_noncommuting` 证明两个具体 Kraus 不对易。这里得到的是在显示基中不同于纯对角擦除嵌入的完整量子操作见证；不能只凭 Kraus 不对易就宣称已经证明任意基中的不可经典模拟或非 entanglement-breaking，这些更强结论未被新源宣称。

### 滤波质量的物理解释边界

`F.state` 是可逆共轭后的归一化态映射，一般非线性；本轮没有把它证明为 CPTP 通道。`mass(F.apply ρ)` 是归一化因子，具体例中为 8/5，因此不能直接称作一次物理筛选的成功概率。`F.apply` 的迹不增性或一个经过标定的物理 filter 实现没有在此处证明。真正已构造且证明完备的量子 instrument 是 `doobInstrument`。源码没有误称这两者，书稿整合也应保持这个区别。

## 独立算术核对

- 成功 Gram 为 diag(3/8,9/64)，失败 Gram 为 diag(5/8,55/64)，两者之和为 I。
- 右密度 ρ=1/5[[1,2],[2,4]]；其 PSD 由实际 Gram 因子得到，trace 为 1。
- S=diag(2,1)，T=diag(1/2,1)，H=diag(4,1)，左右特征值均为 3/16。
- 滤波质量为 8/5，归一化滤波态为 1/2[[1,1],[1,1]]，与原右态不同。
- 移除失败分支后确实不完整，非右特征统一态的一步概率确实不是 QSD 特征值。

## 范围边界

有限变换恒等式、实际量子完备性、有限任意初态条件化和带右特征条件的平稳性均在本轮源码范围内。谱数据存在性、主导性、谱隙、无限视界极限、Yaglom 收敛及从 UEOT Core 推出这些额外谱数据不在本轮已证明范围。头部注释与实际定理接口保持这些边界。

## 已读源快照

- `/workspace/scratch/474cf6b1f047/qm_v316_work/formalization/ueot-qm/UEOTQM/QuantumDoob.lean`
  SHA-256: `d030d6b34dd7034da3d860ddc1ea382618d7aa65e8b0b21214b96055b3680a34`
- `/workspace/scratch/474cf6b1f047/qm_v316_work/formalization/ueot-qm/scripts/witnesses/QuantumDoobExamples.lean`
  SHA-256: `e46c40e308475bc7af01b6f6e597a439e4f3880d35a1197ef0493f82a860702f`

最终作者冻结与机器回执到达后更新本节。

## 主模块冻结复核

作者报告主模块正式 Lake focused 构建 exit 0。已独立回读修改处：两次 `mul_inv_rev` 显式限定为 `_root_.mul_inv_rev`，以及零质量矛盾末尾改为 `simp ... at hpos`；定理数学类型与审查结论不变。主模块最终 SHA-256 为 `345f06df8a70a0c38637cc90d1ee6f7d7c09a8e5715bd9a05943b0bc05bd8350`。见证冻结仍待作者实际验收回执。

## 两份源最终接受

已独立完整回读最终 witness：只补矩阵乘法、向量内积、共轭数码的化简，以及将非对易见证先写成同一个显式矩阵不等式；所有数学声明和参数范围保持不变。两份最终源均通过交叉语义审查，无阻塞项。

- `/workspace/scratch/474cf6b1f047/qm_v316_work/formalization/ueot-qm/UEOTQM/QuantumDoob.lean`
  最终 SHA-256：`345f06df8a70a0c38637cc90d1ee6f7d7c09a8e5715bd9a05943b0bc05bd8350`
- `/workspace/scratch/474cf6b1f047/qm_v316_work/formalization/ueot-qm/scripts/witnesses/QuantumDoobExamples.lean`
  最终 SHA-256：`5fbe70aca27378fead77fdb52658bb048463eff3b1e7e1299a43e5f40e2d456a`

作者回执：主模块标准 focused 构建 exit 0；witness 第二轮 exit 0，40/40 显式目标只含 `propext`、`Classical.choice`、`Quot.sound`。本 reviewer 不重复启动 C 的编译。
