# Cesaro.lean 独立只读语义复核

结论：**CLEAR**。复核者为 `finite_response`，没有修改或编译 Cesaro 文件；本结论与作者的实际编译结果分开。

已逐段检查实际固定完整通道的线性化、`range N` 望远镜求和、真实 Cesàro 密度平均、精确矩阵残差、全效应 `1/N` 界、Euclidean operator norm `2/N` 界，以及子列与不变态存在性链条。

拓扑核对另查固定 Mathlib 的 `Mathlib/Analysis/CStarAlgebra/Matrix.lean`：`instL2OpMetricSpace` 的实现通过 `replaceTopology` 和 `replaceUniformity` 保持已有逐项矩阵拓扑，随后 `Matrix.Norms.L2Operator` 的实例采用该结构。因此有限维紧性、迹的连续性、通道的连续性使用兼容的矩阵拓扑；正文关于这一点的说明有对应基础实现。

`density_operatorNorm_le_one` 从 PSD 的非负特征值、迹一和谱分解推导，不以范数界作为输入。`densityMatrices_closed` 把闭 PSD 锥与闭的迹一约束求交；`densityMatrices_compact` 再利用有限维 closed-and-bounded 定理，未把紧性作为证书字段。

`subsequence_limit_invariant` 明确要求 `StrictMono φ`，从其趋于无穷以及趋零残差和连续通道得极限不变。`subsequence_limit_density` 由闭性保存 PSD 与迹一。`exists_stationary_subsequence` 同时得到密度、不变性和真实平均子列；`exists_stationary` 明确增加 `[Nonempty ι]`，用 `normalizedIdentity` 构造初态。

须保持的表述边界：定理给出 Cesàro 子列和不变态存在性；不推出原始通道轨道逐点收敛、唯一不变态、统一收敛速率或随机轨道经验频率。空载体情形没有被无条件声明存在密度态。此处 operator norm 不冒称 trace norm 或 diamond norm。
