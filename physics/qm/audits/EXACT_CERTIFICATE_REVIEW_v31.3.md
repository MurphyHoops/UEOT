# UEOT-QM v31.3 精确证书桥独立语义审阅

**结论：CLEAR。** 对本版 `ExactCertificate.lean` 与 `lean_export.py` 的只读审阅，未发现把全词响应结论放进输入条件、把任意矩阵冒充实际词效应、转置局部系数行，或通过 `Fin` 数字回绕替换索引的情况。本结论是数学语义与数值绑定审阅；具体生成实例是否被 Lean 接受，以对应源码和构建回执为准。

审阅者同时负责 `Exact.lean` 的研发和定点编译。因此，下文对精确数域层属于实现与验证说明；对 Root 编写的通用证书构造及另一研发分支编写的 exporter 属于独立交叉审阅。

## 1. 审阅对象与接口

| 层 | 实际源码 | 本次检查的合同 |
| --- | --- | --- |
| 精确数域 | [Exact.lean](../../../formalization/ueot-qm/UEOTQM/Exact.lean) | 可计算有理实部／虚部矩阵到真实复矩阵的单射解释及运算保持 |
| 加权仪器 | [Weighted.lean](../../../formalization/ueot-qm/UEOTQM/Weighted.lean) | 非负权重与实际加权完备性经平方根 Kraus 缩放生成普通 `Instrument` |
| 通用证书 | [ExactCertificate.lean](../../../formalization/ueot-qm/UEOTQM/ExactCertificate.lean) | 有限数值条件经 `check_sound` 构造普通量子仪器与有限观测表示 |
| 全词推论 | [FiniteCoordinates.lean](../../../formalization/ueot-qm/UEOTQM/FiniteCoordinates.lean)、[Adaptive.lean](../../../formalization/ueot-qm/UEOTQM/Adaptive.lean) | 局部生成性和闭包推出全部有限词与完整有限自适应树的响应结论 |
| 外部数据锚定 | [representation_certificate.py](../kernel/ueot_qm/representation_certificate.py) | 精确谱域、实际 Kraus 库、词见证、闭包、上下文指纹及额外的 Gram 独立性检查 |
| 源码生成 | [lean_export.py](../kernel/ueot_qm/lean_export.py)、[test_lean_export.py](../kernel/tests/test_lean_export.py) | 数字表、有限索引、标签映射、填零及来源元数据 |

## 2. 精确数域确实解释为复矩阵

`UEOTQM.Exact.MatrixData m n` 只有两个数值字段：

```lean
re : Matrix m n ℚ
im : Matrix m n ℚ
```

`A.toMatrix` 逐项解释为复数，其实部、虚部分别是对应有理数到实数的嵌入。`MatrixData.toMatrix_injective` 证明解释是单射，所以实部／虚部数据不会在解释过程中被商掉或丢失。

运算定义与证明逐项对应：

| 精确运算 | 数据定义与真实解释 |
| --- | --- |
| 零、单位 | 实部为零／单位矩阵，虚部为零 |
| 加、负、减 | 两个有理矩阵分量分别运算 |
| 乘法 | `(A + iB)(C + iD) = (AC − BD) + i(AD + BC)`，其中每个乘积均为矩阵乘积 |
| 伴随 | 实部转置，虚部转置后取负 |
| `scale q` | 两个分量乘同一有理数；解释后是 `(q : ℝ) • A.toMatrix` |
| `sum s f` | 有限集合上逐项求和；解释后是相同集合上的复矩阵和 |

对应定理为 `MatrixData.toMatrix_zero`、`toMatrix_one`、`toMatrix_add`、`toMatrix_neg`、`toMatrix_sub`、`toMatrix_mul`、`toMatrix_adjoint`、`toMatrix_scale`、`toMatrix_sum`。这些证明没有假定任何具体矩阵乘法结果。

三种加权数据运算的参数顺序固定为：

```lean
weightedBranch       s w K X
weightedPullback     s w K E
weightedCompleteness s w K
```

其解释分别为有限和

\[
\sum_{k\in s} w_k K_k X K_k^\dagger,\qquad
\sum_{k\in s} w_k K_k^\dagger E K_k,\qquad
\sum_{k\in s} w_k K_k^\dagger K_k.
\]

此处的 (w_k) 是有理权重在实数中的嵌入。`toMatrix_weightedBranch_univ` 与 `toMatrix_weightedPullback_univ` 直接连接 `weightedKrausMap`、`weightedHeisenberg`。代数定义本身允许任意有理权重；作为物理量子仪器所需的非负性由下述有限条件实际检查。

`WeightedInstrument.toInstrument` 使用 `sqrt w • K`。因此，未经归一化的有理 Hadamard 表与权重 `1/2` 可以描述真实普通 Kraus 矩阵，后者允许含有非有理平方根。`Exact` 不声称覆盖任意不可表示为这些数值输入的复矩阵。

## 3. `Conditions` 没有循环放入结论

`ExactCertificate.Data d a o k r` 只存储有限权重、Kraus 数据、候选基矩阵、实际词、一个有限单位索引和系数表。它没有 `all_word_response_iff`、后验同余或全局响应正确性字段。

`Conditions D` 实际检查以下五项局部命题：

1. 每个动作、结果、Kraus 项的有理权重非负。
2. 对每个动作，将所有结果和 Kraus 项的加权 Gram 矩阵相加，结果等于单位矩阵。
3. `D.word D.unitIndex = []`。
4. 对每个索引 `j`，从单位矩阵按实际加权 Heisenberg 递归计算 `D.word j`，所得矩阵等于 `D.basis j`。
5. 对每个事件 `e` 和每个索引 `j`，实际局部拉回满足
   `weightedPullback ... (D.basis j) = exactExpansion D e j`，其中展开严格采用 `∑ i, coeff e j i • basis i` 的行约定。

`check D` 是这些条件的可计算布尔判定，`check_eq_true_iff` 和 `check_sound` 将返回 `true` 与上述命题连接起来。数值输入本身不能提供一个跳过检查的证明字段。

从检查结果到复量子仪器的过程可以逐步审阅：

- `weightedInstrument` 将有理权重嵌入实数，利用已检查的非负性和加权完备性。
- `instrumentFamily` 经 `WeightedInstrument.toInstrument` 生成满足普通 Kraus 完备性的仪器。
- `branch_eq_exact`、`heisenberg_eq_exact` 将这些真实仪器的单步行为与精确计算连接。
- `exactRecordEffect_toMatrix` 对词归纳；`e :: w` 先递归计算尾词的效应，再施加首事件的拉回，与既有 `recordEffect` 的时间顺序一致。
- `basis_toMatrix` 使用第 4 项检查，把每个输入矩阵绑定到同一个仪器族下的实际词效应。
- `presentation` 同时使用这个绑定和第 5 项局部等式，将系数按同一行顺序嵌入实数，构造 `FiniteObservablePresentation`。

单位矩阵与候选基的关系并未遗漏：第 3 项与第 4 项合起来已经强制单位索引对应实际空词效应。Hermitian 或正半定性质也不依赖任意输入标签，而来自普通量子仪器产生的实际词效应。

## 4. 全词结论如何产生，范围到哪里

有限词见证证明每个生成矩阵属于实际可观测空间；空词提供单位矩阵；逐项局部闭包证明生成矩阵的实线性包在每个拉回下保持。`FiniteObservablePresentation.span_eq_observableSpace` 据此得到与全部记录效应生成空间相同的线性包。

`coordinates_eq_iff_response_eq` 随后证明：对这一已检查的普通仪器族，两个密度状态的有限坐标相同，当且仅当它们对每个有限记录词的响应相同。`response_eq_recordCoordinates_unit` 给出实际响应的有限坐标计算公式，`adaptive_leafProbability_eq` 则复用已有自适应协议定理。

这里的“全部”覆盖任意有限长度的词，以及规定字母表上的完整有限确定性自适应树。它不是仅检查给出的见证词后对更长词做经验外推，也没有预先假定这些全局结论。运行时见证长度上限 `d² − 1` 限制证据生成的工作量；全词定理本身没有这一长度上限。

形式层构造的是一个充分的有限闭合观测表示。其正确性不要求基线性独立。Python 的 Gram 检查额外检查独立性，但本轮 Lean 构造没有证明那个 Python 检查器、最小坐标维数，或更小的物理 Hilbert 实现。

## 5. Exporter 的数值绑定与有限索引

对 `lean_export.py` 的检查结果如下。

| 检查项 | 源码语义与审阅结论 |
| --- | --- |
| 实部／虚部 | `_matrix` 将每个四整数载荷的两个有理数分别写入实部、虚部矩阵，保留复数符号 |
| 实系数 | 系数提取载荷的实分量；调用前的 `verify_representation_certificate` 明确拒绝虚部非零的系数矩阵 |
| 行方向 | `coeff e j i` 来自第 `j` 行第 `i` 列，匹配 Python 检查式和 Lean 的 `exactExpansion` |
| 词方向 | `positions` 将每个动作／结果对转换成数字位置；列表顺序保留，解释层按正确的后向效应递归求值 |
| 有限索引 | 索引采用 `⟨index, by decide⟩ : Fin n`，越界必须无法证明；不依赖模 `n` 的数字字面量回绕 |
| 标签 | 原始标签仅进入 JSON 元数据，Lean 模块标识符只由固定前缀与 SHA256 摘要组成 |
| Kraus 填零 | 补齐项使用零权重与零矩阵，原有零权重项的原始矩阵和索引信息仍被保留 |
| 结果填零 | 补齐结果同时使用零项和零局部系数；原本声明的空分支与新增补齐结果在元数据中保持区分 |
| 外部锚定 | 生成前重新检查所期望的实际仪器库；提供 `expected_context_fingerprint` 时也固定所期望的坐标上下文 |
| 可复核产物 | 清单保存证书摘要、源代码摘要、数值布局和原标签对应；导出状态明确为 `LEAN_SOURCE_EXPORTED_NOT_COMPILED` |

每个生成模块中的数值检查为：

```lean
theorem checked : ExactCertificate.check data = true := by decide +kernel
```

该写法使用 Lean 官方的内核计算分支。固定工具链中部分有理运算对 elaborator 标记为不可自动展开，普通 `decide` 会在这些运算上停住；`+kernel` 允许内核直接化简并检查具体命题。它没有采用 native evaluation 作为证明捷径。

导出的定理讨论数字化并补齐后的模型。原标签与这个模型的对应由可审阅清单及外部预检查提供。本版尚未在 Lean 内证明 JSON 解码和 Python 源码生成器的普遍正确性，所以任意一个未经过 Lean 编译的导出文件都不能被当作已接受的实例证明。

资源合同也是分层的：运行时支持 `1 ≤ d ≤ 4`、`1 ≤ r ≤ d²` 和有限见证长度；exporter 额外限制整数字面量位数、补齐后的标量数和输出源码字节数。这些限制不构成任意输入的统一 Lean 编译时间保证。

## 6. 已直接核实的精确层证据与审计清单

本审阅分支对固定 Lean **4.33.1** 进行了实际定点编译，最终命令为：

```text
PATH=/tmp/lean-4.33.1-linux/bin:$PATH lake env lean \
  -o .lake/build/lib/lean/UEOTQM/Exact.olean UEOTQM/Exact.lean
```

该次进程返回 **exit 0**，`/tmp/qm313_exact_build_final.log` 为零字节，`Exact.olean` 已生成。对应 `Exact.lean` 的 SHA256 为：

```text
1160e084a3761179cf2a2fb8df9246d263088ecb28f54d6d5fe1a86f179eb915
```

文件中三个具体精确等式已经通过 `decide +kernel`：`imaginaryUnit_square_exact` 验证 `i² = −1`，`imaginaryUnit_adjoint_exact` 验证 `i† = −i`，`hadamard_complete_exact` 验证二阶未归一 Hadamard 表在权重 `1/2` 下的加权 Gram 完备性。`imaginaryUnit_square_complex` 与 `hadamard_complete_complex` 再通过解释定理得到实际复矩阵等式。

本模块新增 **24 个显式 theorem**，加上 **1 个含证明的可判定相等实例**，建议纳入 **25 个命名公理审计目标**：

- `UEOTQM.Exact.MatrixData` 下的 14 个 theorem：`ext`、`toMatrix_re`、`toMatrix_im`、`toMatrix_injective`、`toMatrix_eq_iff`、`toMatrix_zero`、`toMatrix_one`、`toMatrix_add`、`toMatrix_neg`、`toMatrix_sub`、`toMatrix_mul`、`toMatrix_adjoint`、`toMatrix_scale`、`toMatrix_sum`。
- `UEOTQM.Exact` 下的 5 个 theorem：`toMatrix_weightedBranch`、`toMatrix_weightedPullback`、`toMatrix_weightedCompleteness`、`toMatrix_weightedBranch_univ`、`toMatrix_weightedPullback_univ`。
- `UEOTQM.Exact.Examples` 下的 5 个 theorem：`imaginaryUnit_square_exact`、`imaginaryUnit_adjoint_exact`、`imaginaryUnit_square_complex`、`hadamard_complete_exact`、`hadamard_complete_complex`。
- 含证明的实例：`UEOTQM.Exact.MatrixData.instDecidableEq`。

该清单只统计本审阅分支负责的 `Exact.lean`。全包计数、通用证书编译、公理依赖输出及生成实例构建状态由 v31.3 集成回执统一记录；源码审阅不会将尚未核实的集成任务记作 PASS。

### 6.1 同一本地／CI 验证程序

[verify_lean_exports.py](../kernel/verify_lean_exports.py) 在通用包已构建后单独编译生成实例，不会重新编译整个包。它在临时目录重新调用 `demo_v313.export_examples`，要求总索引、六份源码及六份清单与固定 fixtures 逐字节一致，再保存待编译的实际副本。正例只接受七个指定且唯一的公理审计目标，允许的依赖只有 `propext`、`Classical.choice`、`Quot.sound`。

负控分别篡改 Z 的权重、候选基、局部系数及 HZ 的时间顺序。名为 `negative_weight` 的控制将一个权重由 `1` 改为 `2`，检查的是加权完备性失效；它并非负权重样例。所有控制都只改数值定义，原来的 `checked` 及其后证明文本保持不变。

每个负控必须同时满足两个独立的验收条件：

1. 原来的 `check data = true` 证明返回 Lean 的错误退出码，且唯一错误位于这一文件的 `checked` 行。超时、导入失败、语法错误和资源失败均不作为数学拒绝证据。
2. 保留同一完整数值前缀的独立文件，通过内核证明 `check data = false`，并通过其单一公理审计。

这是针对实际观察到的诊断限制：某些错误数值在固定工具链的失败日志中显示为 `Reduction got stuck`，仅凭这句话不能认定条件已经计算为假。独立的 `false` 证明消除了这一歧义。失败源的错误恢复输出可能含有 `sorryAx`；它不构成一个接受的证明，验证器明确将其与成功的 `false` 见证分开记录。

验证器绑定重生字节、编译前后源码摘要、原正例摘要、两份坏数据前缀的共同摘要以及两次负控编译后的原文一致性。实际日志、命令、时戳、退出码、公理列表和诊断写入 `--output-dir` 下的 `verification.json`。六个正例和四个负控总计需要十四次生成实例编译，其中四次是独立的 `false` 见证。

```text
python physics/qm/kernel/verify_lean_exports.py \
  --output-dir physics/qm/kernel/evidence/v31.3/lean-exports
```

### 6.2 统一验证器实际验收结果

最终验证于 **2026-10-19 17:44:58.865–17:46:30.238 UTC** 实际执行，进程返回 **exit 0**，完整 [verification.json](../kernel/evidence/v31.3/lean-exports/verification.json) 的状态为 **PASS**，`problems` 为空。此次使用同一冻结版本完成全部十四个实例调用，没有重新编译通用包。

| 正例 | Hilbert 维数 | 坐标数 | 实际 Lean 退出码 | 精确审计目标 |
| --- | ---: | ---: | ---: | ---: |
| Z | 2 | 2 | 0 | 7 / 7 PASS |
| HZ | 2 | 3 | 0 | 7 / 7 PASS |
| HSZ | 2 | 4 | 0 | 7 / 7 PASS |
| ragged | 2 | 3 | 0 | 7 / 7 PASS |
| d1 | 1 | 1 | 0 | 7 / 7 PASS |
| d4 | 4 | 2 | 0 | 7 / 7 PASS |

| 生成后篡改 | 原 `true` 断言退出码 | 同数据 `false` 见证退出码 | 双编译后数值前缀 |
| --- | ---: | ---: | --- |
| `negative_weight` | 1 | 0 | 完全相同 |
| `negative_basis` | 1 | 0 | 完全相同 |
| `negative_pullback` | 1 | 0 | 完全相同 |
| `negative_word` | 1 | 0 | 完全相同 |

四份原断言的唯一错误均位于实际 `checked` 行；四份 `false` 见证的单项公理审计均通过。六正例共 **42 项**接受证明审计，四个 `false` 见证另有 **4 项**接受证明审计，其实际依赖均在三个允许的基础公理内。这些实例数量独立于通用包 theorem／审计计数。

十三份重生产物均与固定 fixtures 字节一致；所有绑定的实现源码和本地依赖 `.olean` 在完整验证前后保持相同摘要。实际验收使用的验证器 SHA256 为：

```text
6d2c5504a2f625441f6fd1b2eb5adf13dc52acb8a574f862f11d85ee880564dd
```

完整回执 SHA256 为：

```text
134507aa7583498781d18269367149ba91129b68a181f0aed3f4a20ef0a08768
```

## 7. 信任边界与物理边界

一个实际被内核接受的实例证明了：它的明确有限数值数据满足上述局部条件；这些数据解释为真实复矩阵与普通量子仪器；相应有限观测坐标充分描述该固定模型的所有有限记录响应和所述有限树语义。

本轮没有形式化证明外部 JSON 解码器、闭包搜索、Gaussian 消元、Gram 检查器、Python exporter 或整个编译器实现的普遍正确性。Lean 内核实现、所固定工具链及经审计的基础公理仍属于信任基础。源码摘要和构建回执负责绑定这次实际被检查的产物，不能自动证明任意后续改动。

这些成果也没有提供实验识别、系统标定或经验适用性的证明。它们不把有限仪器模型等同于现实中的完整量子场论，不给出一般表示论、全局异常、真空选择或质量谱的推导。本轮精确证书建设没有改变三代选择器与谱桥所保留的物理前提；不能据此宣布从无条件公理推出自然界恰有三代。
