# UEOT-QM v31.6：有限实量子局部层析分离证书

## 状态与责任边界

主模块已通过官方 Lean 标准 Lake focused 构建；专用 witness 已通过独立执行，其全部 5 个显式定理的公理依赖只含标准基础。两份源已冻结。主模块全部 50 个显式声明已交根端公共 AxiomAudit 统一审计，本 agent 不把该尚待根端回执的公共检查伪报为自己的已完成检查。
B 独占 `UEOTQM/RealLocalTomography.lean` 与 `scripts/witnesses/RealTomographyTwoRebit.lean`，没有修改 Core、公共 exports、AxiomAudit、workflow、书稿或 Git。基线 commit 为 `427f512745ca70f82cba6a1388edcab904da8a42`。

## 数学结论

令 Y 为标准 Pauli Y，H = Y ⊗ Y，ρ± = (I ± H)/4。复表示中 Y 不实，但 H 的全部条目为实。H† = H 且 H² = I，因此 P± = (I ± H)/2 为正交投影。用 P±†P± = P± 得到现有 Matrix.PosSemidef；Tr H = 0 给出 Tr P± = 2，故 ρ± = P±/2 是现有 Density 类型的真正成员。

对于任意现有 Effect E、F，若其矩阵所有条目虚部为零，其 PSD 已蕴含 Hermitian；实性与 Hermitian 一起推出对称性。于是 Tr(EY) = Tr(FY) = 0，Kronecker 乘法与迹乘法得到

    Tr[(E ⊗ F)(ρ+ − ρ−)] = Tr(EY) Tr(FY)/2 = 0。

这里 E、F 完全全称量化，没有有限取样，也没有把不可区分作为结构字段输入。`productEffect` 对任意既有复 Effect 构造实际 Kronecker Effect，并独立证明 PSD 与 I−E⊗F 的 PSD。主定理使用该 Effect 的实际 `probability`。

联合检验 G = P+ 是实 Effect；G 与 I−G=P− 的 PSD 均已推出。其响应为 p(G|ρ+)=1、p(G|ρ−)=0。这也证明 ρ+≠ρ−。联合分离检验的合法性没有被当作假设。

删除实局部限制后，局部检验 T=(I+Y)/2 是现有复 Effect，且形式证明其不是实矩阵。实际产品 T⊗T 对 ρ± 的概率分别为 1/2 与 0。这只说明本见证可被一个复局部检验区分，不是一般复局部层析重建定理。

## 专用 witness 的进一步检查

1. 实际矩阵的 (00,11) 条目分别为 −1/4 与 +1/4，直接核对隐藏相干分量的符号。
2. 对任意有限索引集、任意实系数 cₐ、任意实局部 Effect Eₐ、Fₐ，线性组合 ∑ₐcₐ(Eₐ⊗Fₐ) 对两态的 trace pairing 相等。系数无需非负或归一化，凸混合自然包含在内。
3. 因联合 G 的概率差为 1，所以 G 的矩阵不可能等于任何上述有限实线性组合。这将全称局部不可区分落实为一个联合效应不在实产品效应张成中的证书。
4. 不加实性条件的“所有复产品 Effect 也不可区分”被 +Y 检验明确反驳。
5. 联合检验与复局部检验的实际响应差分别为 1 与 1/2。

## 与 UEOT 核心追求的关系

该结果把既有书稿中的实量子排除算例接到仓库真正的 Operator/Density/Effect/trace/Kronecker API。它为“局部层析作为额外操作性筛选条件可排除这个有限实扇区”提供形式证书。

`IsReal` 明确定义为现有复矩阵中的实条目子空间；零虚部与 Hermitian 的对称性桥已经证明。实性选择、产品系统规则与 Born trace pairing 的解释是本模型输入，未从 Core 推出。没有构造完整实 OPT 的系统、通道或复合公理，也没有证明实量子满足所有 Core/ESP 前提。没有从本反例推出复 QM 的唯一性、普遍纯化、一般复局部层析或 UEOT 到完备 QM 的无条件重建。

## 文件与全部显式声明

### UEOTQM/RealLocalTomography.lean

- SHA-256: `76dfea1aa3ad7f16e699a8529bde5f22120badac9a1db60f0265eaef4eeddc9e`
- Counts: {'theorem': 37, 'def': 11, 'abbrev': 2}
- Lines: 314
- Status: frozen after focused acceptance

| 类型 | 完整声明 / axiom target |
|---|---|
| def | `UEOTQM.RealLocalTomography.IsReal` |
| theorem | `UEOTQM.RealLocalTomography.symmetric_of_real_hermitian` |
| def | `UEOTQM.RealLocalTomography.productEffect` |
| theorem | `UEOTQM.RealLocalTomography.productEffect_matrix` |
| def | `UEOTQM.RealLocalTomography.plusProjector` |
| def | `UEOTQM.RealLocalTomography.minusProjector` |
| theorem | `UEOTQM.RealLocalTomography.plusProjector_hermitian` |
| theorem | `UEOTQM.RealLocalTomography.minusProjector_hermitian` |
| theorem | `UEOTQM.RealLocalTomography.plusProjector_square` |
| theorem | `UEOTQM.RealLocalTomography.minusProjector_square` |
| theorem | `UEOTQM.RealLocalTomography.plusProjector_mul_minusProjector` |
| theorem | `UEOTQM.RealLocalTomography.one_sub_plusProjector` |
| theorem | `UEOTQM.RealLocalTomography.plusProjector_posSemidef` |
| theorem | `UEOTQM.RealLocalTomography.minusProjector_posSemidef` |
| def | `UEOTQM.RealLocalTomography.involutionEffect` |
| abbrev | `UEOTQM.RealLocalTomography.Qubit` |
| abbrev | `UEOTQM.RealLocalTomography.TwoQubit` |
| def | `UEOTQM.RealLocalTomography.pauliY` |
| def | `UEOTQM.RealLocalTomography.parity` |
| theorem | `UEOTQM.RealLocalTomography.pauliY_hermitian` |
| theorem | `UEOTQM.RealLocalTomography.pauliY_square` |
| theorem | `UEOTQM.RealLocalTomography.parity_hermitian` |
| theorem | `UEOTQM.RealLocalTomography.parity_square` |
| theorem | `UEOTQM.RealLocalTomography.pauliY_trace` |
| theorem | `UEOTQM.RealLocalTomography.parity_trace` |
| theorem | `UEOTQM.RealLocalTomography.parity_isReal` |
| def | `UEOTQM.RealLocalTomography.rhoPlus` |
| def | `UEOTQM.RealLocalTomography.rhoMinus` |
| theorem | `UEOTQM.RealLocalTomography.rhoPlus_matrix` |
| theorem | `UEOTQM.RealLocalTomography.rhoMinus_matrix` |
| theorem | `UEOTQM.RealLocalTomography.rhoPlus_isReal` |
| theorem | `UEOTQM.RealLocalTomography.rhoMinus_isReal` |
| theorem | `UEOTQM.RealLocalTomography.rhoPlus_symmetric` |
| theorem | `UEOTQM.RealLocalTomography.rhoMinus_symmetric` |
| theorem | `UEOTQM.RealLocalTomography.density_difference` |
| theorem | `UEOTQM.RealLocalTomography.trace_mul_pauliY_zero` |
| theorem | `UEOTQM.RealLocalTomography.trace_product_density_difference_zero` |
| theorem | `UEOTQM.RealLocalTomography.all_real_product_probabilities_equal` |
| def | `UEOTQM.RealLocalTomography.jointTest` |
| theorem | `UEOTQM.RealLocalTomography.jointTest_matrix` |
| theorem | `UEOTQM.RealLocalTomography.jointTest_isReal` |
| theorem | `UEOTQM.RealLocalTomography.jointTest_probability_plus` |
| theorem | `UEOTQM.RealLocalTomography.jointTest_probability_minus` |
| theorem | `UEOTQM.RealLocalTomography.rhoPlus_ne_rhoMinus` |
| theorem | `UEOTQM.RealLocalTomography.real_local_tomography_fails` |
| def | `UEOTQM.RealLocalTomography.complexLocalTest` |
| theorem | `UEOTQM.RealLocalTomography.complexLocalTest_not_real` |
| theorem | `UEOTQM.RealLocalTomography.complex_product_probability_plus` |
| theorem | `UEOTQM.RealLocalTomography.complex_product_probability_minus` |
| theorem | `UEOTQM.RealLocalTomography.complex_product_distinguishes` |

### scripts/witnesses/RealTomographyTwoRebit.lean

- SHA-256: `badfe81da1b3ddfa6c69927486d98fcf5ba48b115098de5838413dadfa0bfe15`
- Counts: {'theorem': 5, 'def': 0, 'abbrev': 0}
- Lines: 71
- Status: frozen after focused acceptance

| 类型 | 完整声明 / axiom target |
|---|---|
| theorem | `UEOTQM.RealLocalTomography.Examples.hidden_coherence_exact` |
| theorem | `UEOTQM.RealLocalTomography.Examples.finite_real_product_span_blind` |
| theorem | `UEOTQM.RealLocalTomography.Examples.joint_test_not_finite_real_product_sum` |
| theorem | `UEOTQM.RealLocalTomography.Examples.reality_restriction_is_necessary` |
| theorem | `UEOTQM.RealLocalTomography.Examples.response_gaps_exact` |

## 实际验收记录

工作目录：`/workspace/scratch/474cf6b1f047/qm_v316_work/formalization/ueot-qm`。官方工具链：`/tmp/lean-4.33.1-linux/bin/lake`，Lean 4.33.1。编译器未被替换或修改；环境使用工具支持的权限模式允许 Lean 读取自身可执行文件路径。

| 检查 | 实际命令 | 结果 | 完整日志 |
|---|---|---|---|
| 主模块标准 focused build | `/tmp/lean-4.33.1-linux/bin/lake build +UEOTQM.RealLocalTomography` | exit 0；生成 olean、ilean 与 Lake 依赖轨迹 | `/tmp/qm316_real_tomography_build.log` |
| 专用 witness | `/tmp/lean-4.33.1-linux/bin/lake env lean scripts/witnesses/RealTomographyTwoRebit.lean` | exit 0；5/5 显式定理审计输出；无警告 | `/tmp/qm316_real_tomography_witness.log` |
| 主模块完整显式声明审计 | 根端公共 AxiomAudit，已纳入本模块 50 个 target | 本 agent 提供完整 target 清单；根端负责实际公共回执 | 根端统一记录 |

主构建末尾为 `Built UEOTQM.RealLocalTomography (458s)` 与 `Build completed successfully (8719 jobs)`。这个 job 数包含依赖缓存回放，不代表本轮新增 8719 个定理或新编译模块。日志中的 linter 提示来自继承的 Observables；新 RealLocalTomography 模块没有警告。为减少已诊断的 8GB 内存压力，按根端要求省略重复的单模块全 50 项审计导入。

专用 witness 的 5 个目标分别为隐藏相干条目、任意有限实产品张成不可区分、联合检验不在该张成中、删除实性限制的必要性、两个响应差的精确值。全部实际输出仅依赖 `propext`、`Classical.choice`、`Quot.sound`，没有其他公理。两份源的 `sorry`、`admit`、`native_decide`、`unsafe`、自设 `axiom` 词项扫描为零。

## 章节与交叉审查

第55章矩阵基序、全部实局域效应量词、联合 1/0、复局域 1/2 与 0、有限实张成定理均通过核对。作者已修复两处 LaTeX `quad`，明确四维实 Hilbert 载体与密度矩阵空间的区别，并明确本例复局域删除见证不等于一般复局域层析定理。最终章节 SHA 为 `4629cc692db20132386497b92ed450e95811dc61d4fdaf06f01fce4976846153`；审查记录在 `/tmp/qm316_real_tomography_book_review.json`。

QuantumDoob 两源的独立语义交叉审查见 `/tmp/qm316_doob_cross_review.md/json`。主模块与专用 witness 均已冻结并独立回读最终源，绑定最终 SHA，未发现阻塞项；作者两份 focused 回执均为 exit 0，witness 40/40 公理目标只含标准基础。交叉审查额外记录：可逆共轭后的归一化态映射一般非线性，例中的滤波质量 8/5 是归一化因子，不能直接视作物理筛选概率；真正的完整量子 instrument 由 Doob 构造另行证明。
