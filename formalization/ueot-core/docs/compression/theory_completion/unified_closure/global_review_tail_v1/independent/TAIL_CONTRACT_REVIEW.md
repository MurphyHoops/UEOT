# 同源存活尾合同：独立数学与 API 审查

结论：**CONTRACT_AND_API_CLEAR_FOR_PRIVATE_IMPLEMENTATION_EXECUTION_PENDING**。

本审查只核对冻结合同与 25 项实际输入；复用已通过的 G1–G3、K1、SafePrefix 的原独审。未运行 Lean、Lake、native、测试或 Git，未修改作者包及生产。作者初始 STATUS/PENDING 保持原样。

## 唯一新目标

固定同一原模型 M、观察 q、时间齐次当前观察随机策略 sigma、原始任意初态 p0 和安全集 K，令 Q 为同一策略转移的安全限制、eta0 为原 p0 在 K 上的未归一化行。目标是 eta0 Q^n 1 收敛到同一 `homTrajMeasure` 的 `neverHitSet Kᶜ` 实数质量。

合同未把来源等式、事件等式、收敛、非负性或有限测度条件放进假设。它复用真实 S3 有限窗恒等式，再使用已存在的测度连续从上与 toReal 连续性。这是对原 p0 的来源适配；项目已有无限路径与 Dirac 初态尾收敛理论，不应把本项描述为从零创建无限过程理论。

## 精确 API 核对

- `DynamicsKernel.isProbabilityMeasure_homTrajMeasure` 从原初态概率测度及实际 Markov kernel 导出无限路径概率实例。
- `RecoveryHittingNonnegative.survivalSet` 及其 membership 端点覆盖 0 至 n；`measurableSet_survivalSet` 只需失败目标可测。有限 X 与可测单点给 Kᶜ 可测。
- `Objecthood.antitone_survivalSet` 是递减集合事实；`neverHitSet_eq_iInter_survivalSet` 的方向与目标补集一致。
- Mathlib `tendsto_measure_iInter_atTop` 要求每项 null-measurable、集合 antitone、至少一项质量非无穷；自然数 atTop 的所需可数生成实例有效，概率测度给最后条件。
- `ENNReal.tendsto_toReal` 仅要求极限不为无穷，该条件由同一个概率实例给出。
- SafePrefix 的 `homogeneous_survival_real_eq_killed_pow_sum` 精确提供序列与实际有限窗质量的点态等式，参数中的 M/q/sigma/p0/K 均相同；无需改成 Dirac 初态或另添混合律假设。

## 量词与边界

1. n = 0 时质量为原 p0(K)，包括初态是否安全的判断；不能写成恒为 1。
2. K 可空，所有有限质量及无限安全质量均为 0。合同没有 Nonempty K。
3. 不要求任何有限时刻正存活，也不作条件化或归一化。每个有限时刻正存活仍不蕴含极限正：一安全态每步以 1/2 留存给出 2^(-n) → 0。
4. Y 无 Fintype 或 MeasurableSpace 前提；X/A 及可测单点约束保留现有 S3 范围。
5. 该策略是同一固定当前观察 sigma；没有将任意因果策略、有限窗 viablePolicy 或 viableFamilyPolicy 替换为 sigma。
6. 结论是这个实际初态与策略下的尾极限，不是最大不动点、正无限存活判据、无限可行策略合成或一般非平稳极限定理。

## 实施准入

数学与 API 路线无阻塞。可按根既有授权只实施并聚焦编译唯一端点；没有新增数学假设要求。执行完成后另核对完整声明头、实际 source/env/import/olean/log 和关键公理闭包，不改本静态记录，也不重复既有全库或独审。
