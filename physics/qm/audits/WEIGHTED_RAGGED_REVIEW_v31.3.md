# UEOT-QM v31.3：非负加权与 ragged 零填充桥审查

日期：2026-10-19。范围：`UEOTQM/Weighted.lean` 与 `UEOTQM/Ragged.lean`。

## 1. 范围内结论

**数学合同审查 CLEAR；本地 Lean 实编译 PASS；38 项真实公理审计 PASS。**

两个模块共新增 **35 个显式定理**，以及 **3 个内部证明完备性或非负性的转换构造**。这些转换构造也纳入 `#print axioms`，没有仅审计外层定理而遗漏内部证明。实际依赖并集仅为 `propext`、`Classical.choice`、`Quot.sound`。源码不含 `sorry`、`admit`、`native_decide`、新增 `axiom` 或 `opaque`。

这是针对所列源码的作者范围审查与本地验证记录。整包构建、端到端导出实例、CI、独立交叉审查、PR/主线集成与 `CURRENT` 验收，由对应的集成证据决定；本文件不赋予这些环节验收状态。

模块保持已有有限维复矩阵量子仪器的 Class B 数学范围，没有修改 Core 冻结表，也没有增加第三代物理适配器已导出的主张。

## 2. 非负加权数据到普通 Kraus 的真实构造

`WeightedInstrument ι O κ` 的输入只有四项：

- `weight : O → κ → ℝ`；
- `kraus : O → κ → Operator ι`；
- `weight_nonneg : ∀ o k, 0 ≤ weight o k`；
- 实际加权完备性 `∑ o, ∑ k, weight o k • ((kraus o k)ᴴ * kraus o k) = 1`。

权重无需单独和为 1。归一化合同由全部加权 Gram 项的和等于单位矩阵给出。

`WeightedInstrument.toInstrument` 真实定义普通 Kraus 矩阵为

\[
L_{o,k}=\sqrt{w_{o,k}}\,K_{o,k}.
\]

`sqrt_smul_gram`、`sqrt_smul_krausTerm`、`sqrt_smul_heisenbergTerm` 利用实数平方根和共轭转置的代数规则证明：

\[
L^\dagger L=wK^\dagger K,\qquad
LXL^\dagger=wKXK^\dagger,\qquad
L^\dagger EL=wK^\dagger EK.
\]

由此逐项求和，得到普通仪器与原始加权表的 Schrödinger 分支相等、Heisenberg 拉回相等及完备性继承。最终等价关系没有作为结构字段输入。

证书层的主要接口是 `WeightedInstrument.toInstrument_heisenberg`。它把普通 Kraus 拉回改写成原始加权矩阵和，因此有理数证书不需要把通常不再有理的平方根展开成数据。`weightedKrausMap` 与 `weightedHeisenberg` 本身在定义时没有符号限制；转换、正半定性及本模块的迹配对桥使用显式非负性条件。

`toInstrument_probability` 和 `sum_mass_branch` 将该转换与已有概率、质量守恒合同连接；`toInstrument_posterior_matrix` 给出正概率分支的归一化矩阵。后验接口仍要求 `hp : 0 < probability`，没有为零概率结果制造条件后验。

## 3. 一般有限嵌入与依赖 Kraus 索引

`zeroExtend (e : α ↪ β) f` 在嵌入像上返回原值，在像外返回零。证明首先给出像内值、像外值、总和保持与实权重非负性保持，然后分别证明：

- `weightedKrausMap_zeroExtend`：加权分支保持；
- `weightedHeisenberg_zeroExtend`：加权 Heisenberg 拉回保持；
- `weightedGram_zeroExtend`：加权 Gram 总和保持。

这些恒等式沿任意给定有限嵌入成立，不要求填充项位于表尾，也不依赖特定 `Fin` 编码。矩阵和权重都在像外补零。求和证明使用嵌入的单射性和像外项为零，避免将求和不变作为额外假设。

`RaggedInstrument ι O (κ : O → Type*)` 允许每个结果 `o` 使用各自的有限 Kraus 类型 `κ o`。结构记录原始依赖索引的权重、矩阵、非负性和完整双重求和完备性。给定每个结果的嵌入

\[
e_o : \kappa(o)\hookrightarrow\kappa',
\]

`RaggedInstrument.toWeighted` 构造共同 Kraus 索引的 `WeightedInstrument ι O κ'`，并从 `weightedGram_zeroExtend` 推导完备性。`toWeighted_branch`、`toWeighted_toInstrument_branch`、`toWeighted_heisenberg` 分别连接原始依赖表、共同索引加权仪器及最终普通仪器。`toWeighted_toInstrument_kraus_of_not_mem_range` 还直接证明新增普通 Kraus 矩阵为零。

`WeightedInstrument.padOutcomes` 接受结果嵌入 `e : O ↪ O'`，构造共同结果类型中的加权仪器。它证明原结果的分支、拉回和概率保持；像外新增结果的分支、拉回与概率均为零。其完备性来自对结果索引的同一有限求和原则。

因此，对每个动作分别给出结果嵌入和各结果的 Kraus 嵌入，就可以组合 `toWeighted`、`padOutcomes`、`toInstrument`，处理不同动作拥有不同结果数、不同结果拥有不同 Kraus 数的表。这里的嵌入是明确输入；本模块没有另行证明最大长度的计算算法或有限索引编码生成算法。

## 4. 与 Python padding 和具体 Lean 实例的关系

该数学桥与 Python 实例承担不同的证明责任：

| 环节 | 本模块已证明的内容 | 仍由其他证据承担的内容 |
| --- | --- | --- |
| 权重解释 | 非负实权重通过平方根构造普通 Kraus，分支与拉回严格一致 | JSON 数值、精确有理数数据及其解释的正确性 |
| Kraus 零填充 | 给定每个结果的单射嵌入，依赖索引零扩展保持语义 | Python 选择的共同长度、位置映射及表元素确实对应该嵌入 |
| 结果零填充 | 给定结果单射嵌入，新增结果为零概率，原结果概率保持 | 实际 action/outcome 编码和导出表与原输入的对应 |
| 具体证书 | 经证明的 weighted/pullback 接口可连接后续有限表示合同 | 每份实例的字面矩阵等式、词见证、局部闭包及完整导出物的 Lean 检查 |
| 程序实现 | 通用数学合同可供实例使用 | Python 导出器、JSON parser、索引转换程序的全输入正确性 |

一个含实际零权重、零矩阵行的 `Fin` 实例，可以证明该具体共同索引表定义了正确仪器，并证明该实例的有限表示合同。若其证明没有进一步构造原 ragged 表及对应嵌入，就不能仅凭编译通过宣称整个 Python padding 程序已经细化到 `RaggedInstrument.toWeighted`。若实例显式提供了这些嵌入及对应等式，则本模块的通用定理可直接负责该实例的语义保持部分。

`zeroExtend` 使用 `Function.extend`，属于非计算数学构造。其 `Classical.choice` 依赖在允许基础中且已被实际审计；它不构成从 Lean 提取 Python 实现或验证生成器算法的证据。零概率分支的结论仅是零分支/零概率，不含对其后验状态的任意选择。

本审查也没有证明 Hilbert 维数最小性、`d²` 上界、闭包消元算法的正确性、近似或浮点误差界，或从 Core 唯一导出当前仪器族。这些范围不因加权与零填充桥闭合而自动升级。

## 5. 实际本地验证记录

固定工具链：官方 Lean **4.33.1**；Mathlib **`0df444a360eaa60ab8c11dca51a86af692955474`**。工作目录为 `/workspace/scratch/474cf6b1f047/qm_v313_work/formalization/ueot-qm`。

| 模块 | 显式定理 | 带证明的转换构造 | 实际审计项 | 最终 focused 编译 |
| --- | ---: | ---: | ---: | --- |
| `Weighted.lean` | 16 | 1 | 17 | exit 0，无警告 |
| `Ragged.lean` | 19 | 2 | 21 | exit 0，无警告 |
| 本审查合计 | 35 | 3 | 38 | 两个 `.olean` 均生成 |

实际执行的定向编译命令：

```bash
PATH=/tmp/lean-4.33.1-linux/bin:$PATH /tmp/lean-4.33.1-linux/bin/lake env lean UEOTQM/Weighted.lean -o .lake/build/lib/lean/UEOTQM/Weighted.olean
PATH=/tmp/lean-4.33.1-linux/bin:$PATH /tmp/lean-4.33.1-linux/bin/lake env lean UEOTQM/Ragged.lean -o .lake/build/lib/lean/UEOTQM/Ragged.olean
```

最终定向编译的会话编号分别为 `50913` 与 `1101`，均观察到真实退出码 0。首轮 Ragged 编译仅在最后的零概率定理引用名称上报错；改为展开 `mass` 的 trace 化简后重新编译通过。最终 Weighted 源码已消除无用 section 实例的 linter 警告。

公理审计实际执行：

```bash
PATH=/tmp/lean-4.33.1-linux/bin:$PATH /tmp/lean-4.33.1-linux/bin/lake env lean /tmp/qm313_weighted_audit.lean > /tmp/qm313_weighted_audit.log
```

审计会话 `61495` 真实退出码 0。解析检查要求：请求项无重复、实际报告恰好 38 项、名称集合完全一致、每项依赖均属于允许基础。四项检查均通过。

本地原始材料：

- `/tmp/qm313_weighted_audit.lean`：实际审计入口；
- `/tmp/qm313_weighted_audit.log`：Lean 原始 `#print axioms` 输出；
- `/tmp/qm313_weighted_audit_names.json`：38 项完整请求名单；
- `/tmp/qm313_weighted_audit_receipt.json`：由原始输出解析的 PASS 回执，含每项实际依赖和源码 SHA-256。

这些 `/tmp` 路径是本次本地执行材料的位置，持久集成回执由整包证据目录管理。

| 源码 | 本次编译与审计内容的 SHA-256 |
| --- | --- |
| `formalization/ueot-qm/UEOTQM/Weighted.lean` | `2910a80acb1a73c32bae7898773845b7db9cad7ea74b102ad6e51a473dc86b33` |
| `formalization/ueot-qm/UEOTQM/Ragged.lean` | `a3435d73cd766b55e6f504452de9fe3193ec2266e6cae3772f28cfb4158a718f` |

## 6. 建议追加到统一公理审计的完整名单

导入 `UEOTQM.Ragged` 或经统一入口间接导入后，追加下列 **38 项**。其中 `WeightedInstrument.toInstrument`、`RaggedInstrument.toWeighted`、`WeightedInstrument.padOutcomes` 是带证明构造，其余 35 项为显式定理。

```lean
#print axioms UEOTQM.sqrt_smul_gram
#print axioms UEOTQM.sqrt_smul_krausTerm
#print axioms UEOTQM.sqrt_smul_heisenbergTerm
#print axioms UEOTQM.krausMap_sqrtWeightedKraus
#print axioms UEOTQM.heisenberg_sqrtWeightedKraus
#print axioms UEOTQM.weightedKrausMap_posSemidef
#print axioms UEOTQM.weightedHeisenberg_posSemidef
#print axioms UEOTQM.pairing_weightedKrausMap
#print axioms UEOTQM.WeightedInstrument.toInstrument
#print axioms UEOTQM.WeightedInstrument.toInstrument_kraus
#print axioms UEOTQM.WeightedInstrument.toInstrument_branch
#print axioms UEOTQM.WeightedInstrument.toInstrument_heisenberg
#print axioms UEOTQM.WeightedInstrument.toInstrument_complete
#print axioms UEOTQM.WeightedInstrument.branch_posSemidef
#print axioms UEOTQM.WeightedInstrument.toInstrument_probability
#print axioms UEOTQM.WeightedInstrument.sum_mass_branch
#print axioms UEOTQM.WeightedInstrument.toInstrument_posterior_matrix
#print axioms UEOTQM.zeroExtend_apply
#print axioms UEOTQM.zeroExtend_of_not_mem_range
#print axioms UEOTQM.sum_zeroExtend
#print axioms UEOTQM.zeroExtend_nonneg
#print axioms UEOTQM.weightedKrausMap_zeroExtend
#print axioms UEOTQM.weightedHeisenberg_zeroExtend
#print axioms UEOTQM.weightedGram_zeroExtend
#print axioms UEOTQM.RaggedInstrument.toWeighted
#print axioms UEOTQM.RaggedInstrument.toWeighted_weight_apply
#print axioms UEOTQM.RaggedInstrument.toWeighted_kraus_apply
#print axioms UEOTQM.RaggedInstrument.toWeighted_branch
#print axioms UEOTQM.RaggedInstrument.toWeighted_toInstrument_branch
#print axioms UEOTQM.RaggedInstrument.toWeighted_heisenberg
#print axioms UEOTQM.RaggedInstrument.toWeighted_toInstrument_kraus_of_not_mem_range
#print axioms UEOTQM.WeightedInstrument.padOutcomes
#print axioms UEOTQM.WeightedInstrument.padOutcomes_branch_apply
#print axioms UEOTQM.WeightedInstrument.padOutcomes_branch_of_not_mem_range
#print axioms UEOTQM.WeightedInstrument.padOutcomes_heisenberg_apply
#print axioms UEOTQM.WeightedInstrument.padOutcomes_heisenberg_of_not_mem_range
#print axioms UEOTQM.WeightedInstrument.padOutcomes_probability_apply
#print axioms UEOTQM.WeightedInstrument.padOutcomes_probability_of_not_mem_range
```

## 7. 源码入口

- [Weighted.lean](../../../formalization/ueot-qm/UEOTQM/Weighted.lean)
- [Ragged.lean](../../../formalization/ueot-qm/UEOTQM/Ragged.lean)

依赖方向为 `Observables → Weighted → Ragged`。有理数解释层可以依赖 `Weighted`，两个被审查模块没有反向依赖 Exact、证书导出器或任何具体数字实例。
