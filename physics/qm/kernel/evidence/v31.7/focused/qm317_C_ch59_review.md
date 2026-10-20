# C 对总著第59章的最终审查与命名定理映射

**PASS。** 第59章与三个冻结 C 源的实际证明范围一致。两处精度修订已回读确认：59.7 限定为重复指定成功分支及相应 Doob/条件态极限；N-QDD-01 将严格迹缩小限定为非零 PSD 输入，并明确密度态成功率1/4。

章文件：`/tmp/qm317_book_ch59.md`

章 SHA256：`53db28c918acc5bbdb204ce487e02ef4f60a48136f60d407db68d6687bc351eb`

## 五个编号结果

### P-QDD-01

`UEOTQM.QuantumDoobDynamics.doob_branch_formula`, `UEOTQM.QuantumDoobDynamics.doob_branch_trace`, `UEOTQM.QuantumDoobDynamics.doob_successOperator_formula`, `UEOTQM.QuantumDoobDynamics.doob_iterateState_matrix`, `UEOTQM.QuantumDoobDynamics.doob_stationary_plus`, `UEOTQM.QuantumDoobDynamics.doob_stationary_unique`, `UEOTQM.QuantumDoobDynamics.doob_effectDistance_exact`, `UEOTQM.QuantumDoobDynamics.doob_matrix_tendsto`, `UEOTQM.QuantumDoobDynamics.effectDistance_eq_of_matrix_sub_smul`。

### P-QDD-02

`UEOTQM.QuantumDoobDynamics.filterMass_diag`, `UEOTQM.QuantumDoobDynamics.filterMass_trace`, `UEOTQM.QuantumDoobDynamics.filterMass_metric_trace`, `UEOTQM.QuantumDoobDynamics.filterMass_bounds`, `UEOTQM.QuantumDoobDynamics.pullbackWeight_bounds`, `UEOTQM.QuantumDoobDynamics.normalizer_bounds`, `UEOTQM.QuantumDoobDynamics.unapply_plus`, `UEOTQM.QuantumDoobDynamics.source_successOperator_formula`, `UEOTQM.QuantumDoobDynamics.source_successOperator_density`, `UEOTQM.QuantumDoobDynamics.source_successMass_formula`, `UEOTQM.QuantumDoobDynamics.source_response_formula`, `UEOTQM.QuantumDoobDynamics.source_successMass_pos`, `UEOTQM.QuantumDoobDynamics.source_successMass_bounds`。

### P-QDD-03

`UEOTQM.QuantumDoobDynamics.source_conditionalState_matrix`, `UEOTQM.QuantumDoobDynamics.conditioned_matrix`, `UEOTQM.QuantumDoobDynamics.conditioned_matrix_affine`, `UEOTQM.QuantumDoobDynamics.conditioned_matrix_sub`, `UEOTQM.QuantumDoobDynamics.conditioned_effectDistance_exact`, `UEOTQM.QuantumDoobDynamics.conditioned_effectDistance_le`, `UEOTQM.QuantumDoobDynamics.normalizer_tendsto`, `UEOTQM.QuantumDoobDynamics.conditionalWeight_tendsto`, `UEOTQM.QuantumDoobDynamics.conditioned_matrix_tendsto`, `UEOTQM.QuantumDoobDynamics.conditioned_effectDistance_tendsto`。

### P-QDD-04

`UEOTQM.QuantumDoobDynamics.source_successMass_pos`, `UEOTQM.QuantumDoobDynamics.source_successMass_tendsto_zero`, `UEOTQM.QuantumDoobDynamics.filterMass_rho`, `UEOTQM.QuantumDoobDynamics.pullbackWeight_rho`, `UEOTQM.QuantumDoobDynamics.normalizer_rho`, `UEOTQM.QuantumDoobDynamics.source_successMass_rho`, `UEOTQM.QuantumDoobDynamicsExamples.uniform_filterMass`, `UEOTQM.QuantumDoobDynamicsExamples.uniform_pullbackWeight`, `UEOTQM.QuantumDoobDynamicsExamples.uniform_successMass_one`, `UEOTQM.QuantumDoobDynamicsExamples.uniform_successMass_one_ne_rate`, `UEOTQM.QuantumDoobDynamicsExamples.uniform_conditional_limit`, `UEOTQM.QuantumDoobDynamicsExamples.uniform_successMass_limit`。

### N-QDD-01

`UEOTQM.QuantumDoobDynamicsExamples.identitySource_complete`, `UEOTQM.QuantumDoobDynamicsExamples.identitySource_branch`, `UEOTQM.QuantumDoobDynamicsExamples.identityFilter_metric`, `UEOTQM.QuantumDoobDynamicsExamples.identitySource_left_eigen`, `UEOTQM.QuantumDoobDynamicsExamples.identityDoob_branch`, `UEOTQM.QuantumDoobDynamicsExamples.identityDoob_channelState`, `UEOTQM.QuantumDoobDynamicsExamples.identityDoob_iterateState`, `UEOTQM.QuantumDoobDynamicsExamples.rho_ne_plus`, `UEOTQM.QuantumDoobDynamicsExamples.identityDoob_not_unique_stationary`, `UEOTQM.QuantumDoobDynamicsExamples.identityDoob_not_common_limit`, `UEOTQM.QuantumDoobDynamicsExamples.identitySource_successMass`, `UEOTQM.QuantumDoobDynamicsExamples.identitySource_conditional_fixed`。

## 范围核验

全复迹没有提前变为实部；唯一不变态来自矩阵等式；全效应距离的精确式有正反 supremum 不等式；实际源迭代、成功词概率和规范化条件态分别对接已有 API。矩阵极限是实际整条轨道，而非 Cesàro 子列。概率趋零只涉及有限成功概率序列；不宣称已构造无限路径事件。当前指定源的任意特征率 QSD 唯一属于可选项，书中未冒称已证明。

条件态两个系数非负且和一，以及 H=I 严格正/非零 PSD 迹缩小，是已列式子与标准矩阵事实的直接解析推论，不新增计入命名 Lean 定理。正文对固定可解模型与一般 Perron/谱/实验责任的边界清楚。
