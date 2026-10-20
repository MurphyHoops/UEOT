# v31.7 C 路独立数学交叉审查（B）

状态：`PASS_INDEPENDENT_SEMANTIC_REVIEW_FOCUSED_RECEIPTS_VERIFIED_ROOT_UNIFIED_GATE_PENDING`。

本审查由 AI 子智能体 B 完成：全文阅读三份最终源码及第59章，逐项检查真实仪器、迭代、概率、条件态和反例的类型责任；重新计算文件 SHA 并核对 C 的实际聚焦执行日志。没有重复启动 C 的 Lean 编译。统一全包、公理门和发布验收仍由根端完成。

## 冻结身份

- `/workspace/scratch/474cf6b1f047/qm_v317_work/formalization/ueot-qm/UEOTQM/QuantumDoobModel.lean`：`cf5df67eb83e3c14e20699947a1c2e922af53a19c6483d40b788e234c9e8b5f3`；17 theorem、12 def、29 个显式审计目标。
- `/workspace/scratch/474cf6b1f047/qm_v317_work/formalization/ueot-qm/UEOTQM/QuantumDoobDynamics.lean`：`ee227ea4dcba6e9f2dafe33df614c382610f7468596d923489fc63e76a1556e3`；43 theorem、5 def、48 个显式审计目标。
- `/workspace/scratch/474cf6b1f047/qm_v317_work/formalization/ueot-qm/scripts/witnesses/QuantumDoobDynamicsExamples.lean`：`40d1af7c59ccbca3902b84004f3d9ec7ba29f690a1789879f1c3e5fd351cf2a6`；20 theorem、5 def、25 个显式审计目标。

第59章快照：`/tmp/qm317_book_ch59.md`，SHA `53db28c918acc5bbdb204ce487e02ef4f60a48136f60d407db68d6687bc351eb`。

## 核查结论

### MODEL_PROVENANCE_AND_ACTUAL_INSTRUMENT — PASS

The fixed rational model is the promoted v31.6 noncommuting witness. Explicit success/failure Kraus grams sum to identity. The right and left eigen equations at rate 3/16 and positive metric H=diag(4,1) are proved from matrices, not supplied as conclusions. Promotion is not new physical inference.

对应入口：`QuantumDoobModel.source_complete`, `QuantumDoobModel.source_branch_formula`, `QuantumDoobModel.source_right_eigen`, `QuantumDoobModel.source_left_eigen`, `QuantumDoobModel.success_kraus_noncommuting`。

### FULL_COMPLEX_OPERATOR_DYNAMICS — PASS

Doob branch and every actual successOperator iterate hold for arbitrary complex matrices, retaining complex trace until specialization to a density. The real/imaginary offdiagonal directions are not discarded. D^n(X)=a_n X+(1-a_n)Tr(X) sigmaPlus, a_n=3^(-n). Actual Cesaro.iterateState is the same density trajectory, not an unconnected scalar surrogate.

对应入口：`QuantumDoobDynamics.doob_branch_formula`, `QuantumDoobDynamics.doob_successOperator_formula`, `QuantumDoobDynamics.doob_iterateState_matrix`, `QuantumDoobDynamics.source_successOperator_formula`, `QuantumDoobDynamicsExamples.coherent_input_two_steps`。

### ALL_EFFECT_DISTANCE_AND_UNIQUENESS — PASS

Exact distance scaling is proved directly from the supremum over all legal effects, handling a=0 separately and dividing only under a>0. It does not assume tomography/separation. Unique stationarity follows from the actual matrix equation. Entire matrix orbits, rather than only Cesaro averages, converge.

对应入口：`QuantumDoobDynamics.effectDistance_eq_of_matrix_sub_smul`, `QuantumDoobDynamics.doob_stationary_unique`, `QuantumDoobDynamics.doob_effectDistance_exact`, `QuantumDoobDynamics.doob_matrix_tendsto`。

### ACTUAL_SOURCE_PROBABILITY_AND_STATE_DEPENDENT_DENOMINATOR — PASS

For every Density tau, c=Tr(H tau) in [1,4], b=5c/8 and z_n=a_n+(1-a_n)b in [5/8,5/2] are derived from PSD and trace one. Actual source successMass and response of the repeated true word equal (3/16)^n z_n. The proof does not replace the actual success probability by the eigenrate power for arbitrary input.

对应入口：`QuantumDoobDynamics.filterMass_bounds`, `QuantumDoobDynamics.normalizer_bounds`, `QuantumDoobDynamics.source_successMass_formula`, `QuantumDoobDynamics.source_response_formula`, `QuantumDoobDynamics.source_successMass_pos`, `QuantumDoobDynamicsExamples.uniform_successMass_one_ne_rate`。

### ACTUAL_CONDITIONAL_STATE_AND_FINITE_POSITIVITY — PASS

conditioned is exactly the old conditionalState with derived finite success positivity. Its matrix equals (a_n/z_n) tau+((1-a_n)b/z_n) rhoStar, so distance to rhoStar equals (a_n/z_n)d(tau,rhoStar), bounded by (8/5)a_n d(tau,rhoStar). This is not a pairwise arbitrary-source conditional contraction claim: z depends on tau. Finite success mass stays positive but tends to zero; no infinite surviving event or infinite conditioned path law is constructed.

对应入口：`QuantumDoobDynamics.source_conditionalState_matrix`, `QuantumDoobDynamics.conditioned`, `QuantumDoobDynamics.conditioned_effectDistance_exact`, `QuantumDoobDynamics.conditioned_effectDistance_le`, `QuantumDoobDynamics.conditioned_matrix_tendsto`, `QuantumDoobDynamics.source_successMass_tendsto_zero`。

### LEGAL_IDENTITY_DOOB_COUNTERMODEL — PASS

The negative control is an actual complete Bool by Fin3 source instrument, with Phi(X)=X/4, identity positive filter, actual left eigenmetric equation, and actual Doob channel D(X)=X. Every density is stationary; rhoStar and sigmaPlus are explicitly distinct, disproving unique stationarity and any common matrix attractor. Source successMass is 4^(-n), and original conditionalState stays at its input. No required premise was silently deleted.

对应入口：`QuantumDoobDynamicsExamples.identitySource_complete`, `QuantumDoobDynamicsExamples.identitySource_left_eigen`, `QuantumDoobDynamicsExamples.identityDoob_branch`, `QuantumDoobDynamicsExamples.identityDoob_not_unique_stationary`, `QuantumDoobDynamicsExamples.identityDoob_not_common_limit`, `QuantumDoobDynamicsExamples.identitySource_conditional_fixed`。

### CHAPTER_59_SCOPE_AND_MAPPING — PASS

Five numbered results match actual source declarations: P-QDD-01 Doob exact orbit; P-QDD-02 source probability; P-QDD-03 conditional convergence; P-QDD-04 state dependence and decreasing success mass; N-QDD-01 legal identity counterexample. General spectral existence, arbitrary-record conditional mixing, infinite-path conditioning, and empirical validity remain outside the proved scope. The prose strict trace shrink of the countermodel on nonzero PSD inputs is an analytic corollary of Phi=X/4 and PSD positive mass, not an extra named Lean declaration.

对应入口：`P-QDD-01`, `P-QDD-02`, `P-QDD-03`, `P-QDD-04`, `N-QDD-01`。

## 执行证据与限制

已核对 Model、Dynamics、witness 三个聚焦过程 exit code 为 0；witness 25 个显式声明和公共 77 个声明的公理输出均只含标准逻辑公理。实际日志均无 error 或 sorryAx。该结论引用已有真实执行回执，不伪称审查者另跑了一遍。

没有科学阻塞项。当前建立的是指定复量子模型中的精确动力学与严格反例，不是由 UEOT Core 推出复量子结构、一般谱存在、全部物理学或经验真理。全包与远端结果须由最终统一回执补充。
