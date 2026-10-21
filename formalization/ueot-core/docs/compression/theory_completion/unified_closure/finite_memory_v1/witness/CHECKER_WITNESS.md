# 可执行有限记忆判据的正例、拒绝与实际来源

状态：`FOCUSED_LEAN_COMPILE_PASS`。最终源码及其依赖 `SupportMemoryCheck` 已通过本批 `compile-04` 的实际 Lean 编译，退出码为 0，诊断日志为空；计算证明的源码与执行记录见 [compile-04 原始收据](../actual-execution/compile-04/STATUS.json)。本说明不替代整组生产导入、完整构建、native 导出和独立生产验收。

生产候选文件：`UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteMemoryCheckWitness.lean`。
命名空间：`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMemoryCheckWitness`。

## 程序输入与计算范围

复用 `FiniteMemorySeparation` 的常量观察 `observe` 和实际纯翻转来源 `source`。程序接收显式可判定关系

\[
R(x,a,z)\iff z=\neg x,\qquad C(x,a)\iff a=x,
\]

以及一个有限初始支持。`finiteMemoryCheck` 在明确界 \(2^{|\mathrm{Bool}|}-1=3\) 上复用已有有限时域关系检查器；它不把未知获胜策略当作输入，也不执行一般不可计算 PMF 的精确支持判定。

三个私有计算引理分别使用 `by decide`，由公开端点 `finite_decision_table` 合并给出：

| 初始支持 | 结果 | 原因 |
|---|---|---|
| `{false}` | `true` | 初始相位已知，随后支持逐步翻转 |
| `{true}` | `true` | 另一已知初始相位同样可行 |
| `{false, true}` | `false` | 第一个行动已无法认证两个可能状态 |

私有计算保持具体源输入；把结果合并成一个公开端点，也避免把几个经过定义展开都成为相同布尔恒等式的辅助计算当作不同公共 API。

## 从判定结果到同一个实际实验

`source_support_exact` 从 `PMF.pure` 的实际支持证明关系 \(R\) 精确表示每个时间的真实来源支持。初始支持匹配与认证匹配也分别提供，程序结果不会自动替代这些来源责任。

正向端点 `checked_support_controller_zero_uncovered` 使用初态 `initial = PMF.pure false`，它与记忆分离正例是同一个初始实验。公开计算结果通过 `finiteMemoryCheck_iff_controller_zero_uncovered` 推出本批 `supportMemoryController` 自己的实际部署行律在所有时间零未认证占据。这个选择产生的支持控制器无需等于另行写出的 `flipController`；两个控制器各自的实际律分别有证明。

负向端点 `mixed_initial_has_no_all_times_policy` 则**明确改用**初态 `PMF.uniformOfFintype Bool`。它的两个状态都有正概率，真实初始支持恰为被拒绝的 `{false, true}`。利用 `finiteMemoryCheck_iff_exists_all_times_policy`，拒绝结果排除该初始实验中的所有全时间零未认证占据因果策略。源转移和认证仍采用相同定义；负例不会把正例的初态悄悄换掉。

## 结论的范围

这里验证的是一个已有有限关系算法在同源全时间判据中的实际消费。没有声称执行了支持控制器中的非构造行动选择，没有给出运行时间或查询复杂度界，没有把它作为 C3 载体发现算法，也没有对噪声或近似来源支持输入给出保证。全部结果属于精确数学 PMF 实验和形式证明，不属于现实数据采集。
