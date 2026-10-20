# UEOT-QM v31.6 / Kernel 1.6

当前状态：**LOCAL_VERIFIED_CI_PENDING**；实际远端验收以 [CURRENT](../status/CURRENT.json) 为准。本轮新增形式化经典Core边界、实局域层析与非交换Doob；精确运行程序保留混合预算、Cesàro及对角生存API，本轮重新执行其全部回归。

实际本地结果：22 主包模块、459 显式定理、573 项实际命名公理审计；100 运行方法、4 演示 PASS。六个精确实例、四组真假配对负控重新核验；四份具体 Lean 见证另计 62 定理／22 定义／84 项审计。[版本报告](../UEOT_QM_KERNEL_v31.6.md)、[证明回执](evidence/v31.6/lean-verification.json)、[运行回执](evidence/v31.6/runtime-verification.json)。完整理论见 [《UEOT物理学》正式 3.2](../book/UEOT_PHYSICS.md) 第 49–56 章。

## 立即运行

从仓库根目录执行；运行内核使用 Python 3.10+ 标准库，CI 固定 Python 3.12：

```bash
python physics/qm/kernel/demo.py
python physics/qm/kernel/demo_v312.py
python physics/qm/kernel/demo_v313.py --output-dir /tmp/qm-exports
python physics/qm/kernel/demo_v315.py
python physics/qm/kernel/verify_kernel.py --output /tmp/qm-runtime-v315.json
```

`demo.py` 保留干涉、有限协议差、后选择与误差链；`demo_v312.py` 保留 Z/HZ/HSZ 完整表示证书、自适应律与谱／331 异常；`demo_v313.py` 输出六份完整 Lean 候选及 companion manifest。仅导出源文件不会宣称 Lean 编译成功。

| 测试组 | 方法数 | 范围 |
|---|---:|---|
| 操作／协议／误差 | 32 | 干涉、相位、纠缠、正性、零分支、记忆与有限覆盖 |
| 表示证书 | 18 | 真实词生成、独立性、闭包、错顺序／转置、上下文与格式 |
| 谱桥与局域异常 | 22 | 行和、模板、复制、补偿、阈值与符号／权重 |
| Lean 源导出 | 15 | 精确数据、可变指标、标签／上下文绑定、恶意／畸形输入拒绝 |
| 混合／长期／存活 | 13 | 精确 TV、上下文、周期、非唯一、QSD、Doob、初态／行方向／损失与零事件 |
| 合计 | **100** | 方法数不作为 Lean 定理数；Lean 实编译由独立入口执行 |

## 混合、长期与存活 API

自v31.5沿用的 [finite_dynamics.py](ueot_qm/finite_dynamics.py) 的 ProbabilityWeights 只接受精确整数／Fraction 权重，检查非负和归一；MixtureWeightBudget 绑定同一个实际成员库及其表示指纹，计算精确有理 TV。零权重成员仍需满足共同载体和结果字母表。mix_instruments 通过 Kraus 权重乘法实现混合，运行端不需要近似平方根。

channel_operator 对任意矩阵线性作用；iterate_state 检查非负整数步数和密度态；cesaro_average 要求正整数 N，并使用第 0 至 N−1 个实际迭代态。substochastic_instrument 检查方形非负次随机 Q，按 pQ 的行方向提供 survive／lost 两结果。运行载体仍受既有精确矩阵库 1–4 维范围约束。

demo_v315 展示 TV 达界及非达界、bit-flip 周期与平均残差、恒等通道非唯一、QSD 的 2⁻ⁿ 生存及 Doob 的 qh。v31.5引入的13个方法同时检验删除前提的失败情形；本轮与其余方法一并重跑。它们是精确合成模型验证，不是实验数据。

完成通用 Lean 构建后，从仓库根执行：

~~~bash
python formalization/ueot-qm/scripts/verify_finite_witnesses.py --output-dir /tmp/qm-finite-witnesses
~~~

此门实际编译四份固定具体见证，审核全部84个声明并绑定79个QM/Core模块的源与olean。包含原混合/生存，以及新增实层析/非交换Doob见证；与六实例证书门分别统计，具体证明不增加459个主包定理的计数。[实际见证回执](evidence/v31.6/finite-witnesses/verification.json)

## 把具体证书交给 Lean

在本目录的 Python 环境中：

```python
from fractions import Fraction
from pathlib import Path
from ueot_qm import (
    Matrix, diagonal, KrausTerm, Instrument, InstrumentLibrary,
    PredictiveModel, export_representation_certificate,
    export_lean_representation,
)

z = Instrument({
    "0": [KrausTerm(diagonal([1, 0]))],
    "1": [KrausTerm(diagonal([0, 1]))],
})
h = Instrument({"ok": [KrausTerm(Matrix([[1, 1], [1, -1]]), Fraction(1, 2))]})
library = InstrumentLibrary({"H": h, "Z": z})
model = PredictiveModel(library)
certificate = export_representation_certificate(model)
exported = export_lean_representation(
    certificate, library,
    expected_context_fingerprint=model.context_fingerprint,
)
Path("/tmp/hz.lean").write_text(exported.lean_source)
Path("/tmp/hz.manifest.json").write_text(exported.canonical_manifest + "\n")
print(exported.source_sha256)
```

完成 `formalization/ueot-qm` 的 `lake build UEOTQM` 后，从该目录执行 `lake env lean /tmp/hz.lean`。文件中的 `checked : ExactCertificate.check data = true := by decide +kernel` 必须被内核接受；不能用 Python 预检代替。

可重复的完整验收从仓库根目录运行：

```bash
python physics/qm/kernel/verify_lean_exports.py --output-dir /tmp/qm-lean-exports
```

它重新生成 Z/HZ/HSZ/ragged/d1/d4，与 [固定 fixtures](certificates/v31.3/exports.json) 的完整源码／manifest 逐字节比较，编译并检查每例 7 项实际公理输出。另在生成后改坏四种数值数据；原 `check=true` 证明须失败，相同数据的 `check=false` 证明须成功。日志、执行状态和 SHA256 都保存到指定目录；超时或导入错误不能单独算数学拒绝。Lean 4.33.1 与固定依赖由 [专门包](../../../formalization/ueot-qm/README.md) 提供。

所有用户标签只在 manifest 出现；Lean 使用摘要命名空间和有界 Fin 构造。不同项数／结果数补零的每个数值都可检查，原有不可能分支也保留。manifest 的 `LEAN_SOURCE_EXPORTED_NOT_COMPILED` 是生成事件的状态；之后的成功记录在独立源码绑定回执中。

格式边界：Hilbert 维数 1–4、基数 ≤d²、见证词长 ≤d²−1；exporter 另限整数 4096 bit、补零标量 65536 项和 Lean 源 8 MiB。它们不限制定理量化的未来有限记录长度，也不提供统一编译时间上界。

本轮有通用 checker 可靠性定理与逐实例证据；Python/JSON/parser/exporter/闭包搜索/消元/树程序的全输入正确性仍是独立任务。量子扇区为明确输入，未增添实验确认或无条件三代结论。

## 导出 JSON 表示证书并独立检查

在上例产生 `model` 后继续执行：

```python
import json
from ueot_qm import (
    export_representation_certificate,
    verify_representation_certificate,
)

certificate_json = json.dumps(
    export_representation_certificate(model), ensure_ascii=False,
)
# certificate_json 可以保存或传输；检查时保留调用方认可的 library 锚。
certificate = json.loads(certificate_json)
verification = verify_representation_certificate(
    certificate,
    model.library,
    expected_context_fingerprint=model.context_fingerprint,
)
print(verification.response_dimension)  # H+Z 为 3，包含迹坐标
print(verification.checked_pullback_identity_count)  # 3 个分支 × 3 个基效应 = 9
print(verification.certificate_fingerprint)
```

导出只产生证据数据。checker 另行从认可的 Kraus 库重算完整性、每个实际词效应、Frobenius Gram 行列式和全部局部拉回恒等式，不调用闭包搜索、系数消元或 `Instrument.adjoint`。它与运行程序共享精确矩阵算术底座。

每个基效应有真实有限词见证，且基包含单位效应。每个允许分支均验证

\[
\Phi_e^*(B_j)=\sum_k A_{e,jk}B_k.
\]

生成与闭包的两个方向支持全部有限词的张成结论；实际坐标递推采用 `A @ x`。这个接口检查的是精确局部恒等式，没有把有限采样的相等当作全词充分性。

调用方提供 `expected_context_fingerprint` 时，基的身份也被固定。省略该参数时，认可同一操作库中满足证据格式的另一组有效词效应基，它会有自己的 context；任意线性混合基不属于此格式。不同 Kraus 清单即使给出相同物理通道，也不会自动共享库指纹。

## 有限谱接口

以下例子逐项列出三个家族和一个 Higgs，而不是把最终异常方程输入程序：

```python
from fractions import Fraction
from ueot_qm import (
    Orientation as O, MatterKind as M, Family, ExtraMatter,
    WeakWindow, Spectrum, inspect_spectrum,
    generalized_331_fields, local_331_anomalies,
)

families = (
    Family("f1", O.R, O.R),
    Family("f2", O.R, O.RBAR),
    Family("f3", O.R, O.RBAR),
)
higgs = ExtraMatter("H", M.COMPLEX_SCALAR, 1, Fraction(1, 2))
# 模型方需独立支持这四个窗口声明；布尔值本身不证明其物理真实性。
window = WeakWindow("declared SU(2) window", True, True, True, True)
receipt = inspect_spectrum(Spectrum(3, 1, families, window, (higgs,)))
result = receipt.to_dict()
print(result["status"])  # SELECTOR_APPLIES
print(result["sums"]["weak_b2"])  # 19/6
print(result["derived"]["selected_counts"])  # {'nc': 3, 'nf': 3, 'k': 1}

# 单独重算完整全左手 331 清单的六项局域异常，z = beta/sqrt(3)。
fields = generalized_331_fields(families, Fraction(1, 5))
local = local_331_anomalies(fields).to_dict()
print(local["all_six_cancel"])  # True；范围为六项局域异常
```

`receipt.canonical_json` 含每行贡献、求和、窗口声明、失败条件和条件选择计数；`receipt.sha256` 绑定其内容。`to_dict()` 返回可单独使用的副本。

主桥保留同质轻子、非零异常单位、额外 cubic 组合总和为零、所有 ordinary 双重态活跃和完整 (b_2>0) 等前提。混合两代、六代复制、补偿一代、失活阈值和额外屏蔽的拒绝理由分别输出。`CubicCompletion` 只记录声明的同通道贡献，不认证 completion 机制。

六项 331 求和器当前使用 singlet、fundamental 和 antifundamental 的声明系数，固定色群为 (SU(3)_C)。它属于精确运行证据；Lean 谱模块覆盖选定 cubic 通道和弱预算。详见 [谱桥及反例审查](../audits/SPECTRUM_BRIDGE_v31.2.md)。

## 合同与 API

| 入口 | 输入合同 | 输出 |
|---|---|---|
| `QComplex(real, imag)` | 整数或 Fraction | 精确有理复数 |
| `Matrix(rows)` | 非空等长矩阵行 | 不可变矩阵 |
| `Matrix.is_density()` | 方阵，Hilbert 维数 1–4 | 全 principal minors PSD、Hermitian、trace-one 校验 |
| `Instrument(outcomes)` | 每个结果的非负加权 Kraus 项 | 构造时验证完整性 |
| `library.posterior(rho,a,o)` | 合法密度态与已声明动作/结果 | 正概率后验或 `None` |
| `PredictiveModel(library)` | 固定时齐有限动作库 | 精确效应闭包、响应基和分支矩阵 |
| `model.encode(rho)` | 合法密度态 | 带上下文的物理响应坐标 |
| `model.update(x,a,o)` | 同一模型产生的坐标 | 后验响应坐标或 `None` |
| `word_law(state,actions)` | 完整控制词 | 保留零概率记录的 outcome law |
| `protocol_law(state,tree)` | 全结果分支的有限因果树 | 完整 action/outcome 记录律 |
| `export_representation_certificate(model)` | 已有精确响应模型 | JSON 可序列化的词见证、基效应和局部拉回矩阵 |
| `verify_representation_certificate(data,library,...)` | 外部认可的库、精确证据、可选预期 context | 独立检查回执，失败时抛出 `RepresentationCertificateError` |
| `inspect_spectrum(spectrum)` | 有限 family／额外条目和显式窗口声明 | 逐项算术、合同失败理由与条件计数 |
| `local_331_anomalies(fields)` | 全左手 Weyl 331 清单 | 六项局域异常的逐项贡献与总和 |

`InstrumentLibrary` 通过密度矩阵计算记录律；`PredictiveModel` 通过响应坐标计算。后者接受密度矩阵或已编码态作为记录接口输入。

证书接口从 `ueot_qm.certificates` 导入：

- `compare_finite_protocols(left,right,preparation_pairs,protocols)`：实际计算所有指定配对/因果树的 TV；范围与指纹绑定。
- `transport_budget(initial,steps)`：在声明局部前提下计算条件式标量预算。
- `verify_transport_trace(errors,initial,steps)`：实查初值和每一步递推；失败则拒绝。
- `certify_postselection(left,right,event)`：要求双方事件概率正，计算条件 TV 及含事件概率的上界。

## 准确范围

量子运行时支持 Gaussian-rational 数据和 Hilbert 维数 1–4；浮点数及超出状态维数的输入明确拒绝。Hadamard 使用整数矩阵加权 1/2，结果依然精确。谱接口使用整数重数和精确 Fraction 系数，不受量子态矩阵的 Hilbert 维数限制。

表示证据要求 (1\le r\le d^2)，每个词见证长度不超过 (d^2-1)。这个生成证据上限没有给预测协议设置统一时域上限。基础表示 checker 未统一限制整数位长和操作库规模；新的 Lean exporter 另施加前述 4096 bit／65536 项／8 MiB 边界。两者都不承诺总体固定运行时间。响应维数包含 trace 坐标，不代表一个更小 CPTP Hilbert 模型的维数。

操作库固定且时齐。时间、资源或自动机约束需另外编码；省略相关环境时，系统态不能自动充当充分对象。没有用于任意外部坐标的物理可实现性判定器；`EncodedState` 由工厂构造，指纹只是上下文检查。

有限协议证书只覆盖给出的准备配对和因果树。标量预算需要明确的逐步前提。二者不自动变成全部状态/全部协议上的 trace-distance 或 diamond-norm 保证。

22个主包Lean模块覆盖实际量子操作、响应商、有限坐标、完整树、精确checker、效应稳定性、混合全态TV、Cesàro、对角/非交换条件化与经典/实模型分离。459定理、573审计统一通过；数值实例与具体见证有独立源绑定回执。当前集成身份见 [CURRENT](../status/CURRENT.json)。

新 `channelDefect` 是全态输出伪距离的数学上确界，尚不是本 Python 运行时的可计算函数。实际量子一步界已经调用 Core M-TC 得到轨迹总误差；原有标量预算 API 仍要求输入它声明的局部合同。丢弃结果后的通道缺陷不自动控制两个不同仪器的标签或历史；后验界要求双方事件概率正。可认证的缺陷数值上界、完整经典记录扩展、旁系统稳定性和范数识别仍是独立任务。

Lean 的 finite presentation 允许冗余生成元；Python checker 另检查基独立性。数学数域、加权／可变指标桥与逐实例证明已经完成；Python/JSON 解码、索引映射程序、搜索／消元、PSD 判定和树遍历的全输入细化仍未完成。具体表示系数、matching 窗口、全局异常、真空或质量也继续独立。准确范围见 [v31.6 主报告](../UEOT_QM_KERNEL_v31.6.md)。

## 回执与版本身份

本版在 `evidence/v31.6/` 保存源码、运行、演示、通用 Lean 与实例回执。[本地证明回执](evidence/v31.6/lean-verification.json)、[实例验收](evidence/v31.6/lean-exports/verification.json) 与 [本轮台账](../status/CLAIM_LEDGER_v31.6.json) 分别记录实际结果、被测字节和开放义务。v31.2、v31.3、v31.4 原证据保留，并由各自独立集成回执记录已经完成的主线结果。

v31.1 的回执继续可读，保持其原源码身份：

- [Kernel 1 Lean 构建与源码身份](evidence/lean-verification.json)
- [Kernel 1 实际公理依赖](evidence/proof-axioms.json)
- [Kernel 1 的 32 项独立测试](evidence/runtime-verification.json)
- [Kernel 1 完整示例输出](evidence/kernel-demo.json)

运行时测试、机器证明、理论桥和物理适用性按独立状态登记。

