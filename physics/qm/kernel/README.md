# UEOT-QM v31.2 / Kernel 1.2

有限维操作内核：**合法量子操作 → 完整记录律 → 协议响应坐标 → 闭合递归更新 → 可检查的表示与误差证书**。本版新增可导出的全词效应表示证书、独立精确 checker，以及从有限谱条目求和进入三代选择的接口。

**当前状态：LOCAL_VERIFIED_CI_PENDING。** 官方 Lean **4.33.1** 已在本地实际完成 `lake build UEOTQM`，退出码 **0**；九模块的 **128 个显式 theorem 全部编译通过，137 项实际公理审计 PASS**，依赖仅为 `propext`、`Classical.choice`、`Quot.sound`。**72 个运行测试方法及 `demo.py`、`demo_v312.py` 均已通过。**

本地结果绑定源码提交 [`323db6d1c2e5`](https://github.com/MurphyHoops/UEOT/commit/323db6d1c2e50a432bdcf6a6872212426cc826ce)，见 [v31.2 本地证明回执](evidence/v31.2/lean-verification.json) 与 [主张台账](../status/CLAIM_LEDGER_v31.2.json)。GitHub Actions 仍在排队，[PR #333](https://github.com/MurphyHoops/UEOT/pull/333) 的远端 CI 和主线集成尚未验收；最近完成主线验收的版本仍是 v31.1。

理论、组合证明及物理边界见 [v31.2 内核说明](../UEOT_QM_KERNEL_v31.2.md)。[Lean 包](../../../formalization/ueot-qm/README.md) 固定继承 Core 的 Lean 4.33.1 与 Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`。

已验收的 [Kernel 1 / v31.1](../UEOT_QM_KERNEL_v31.1.md) 保留原身份：[工作流 39270031506](https://github.com/MurphyHoops/UEOT/actions/runs/39270031506) 对其测试提交验收了 32 个测试、56 个 theorem 和 59 个公理报告。本版使用独立的新回执；旧回执仅认证 v31.1 的原源码字节。

## 立即运行

从仓库根目录执行；Python 3.10+，只使用标准库，CI 使用 Python 3.12：

```bash
python physics/qm/kernel/demo.py
python physics/qm/kernel/demo_v312.py
python physics/qm/kernel/verify_kernel.py --output /tmp/ueot-qm-runtime-v312.json
```

`demo.py` 保留原有干涉、有限协议差、后选择与误差链示例。`demo_v312.py` 输出 Z/HZ/HSZ 的完整表示证书及独立检查回执、一个自适应协议的密度态／坐标完整律、逐项谱选择结果与六项 331 局域异常。

验收命令运行当前 72 个测试方法，并将源码哈希与实际结果写入指定位置。使用显式 `--output` 可保留历史回执。本轮交付证据放在 `evidence/v31.2/`；根层 `evidence/*.json` 继续保存 v31.1 的既有回执。

| 运行测试组 | 方法数 | 核查重点 |
|---|---:|---|
| 既有操作、协议及误差证书 | 32 | 干涉、相位、纠缠、正性、零分支、记忆与有限覆盖 |
| 新表示证书 | 18 | 真实词生成、独立性、闭包、错顺序／转置、上下文和格式拒绝 |
| 新谱桥与局域异常 | 22 | 行和、模板、复制、补偿、阈值、缺失 completion 和符号／权重错误 |
| 合计 | **72** | 方法可以包含多个精确实例；方法数不作为定理数 |

作为模块使用时，将本目录放到 Python 路径中，例如在本目录执行：

```python
from fractions import Fraction
from ueot_qm import (
    Matrix, diagonal, KrausTerm, Instrument,
    InstrumentLibrary, PredictiveModel,
)

z = Instrument({
    "0": [KrausTerm(diagonal([1, 0]))],
    "1": [KrausTerm(diagonal([0, 1]))],
})
h = Instrument({
    "ok": [KrausTerm(Matrix([[1, 1], [1, -1]]), Fraction(1, 2))]
})
library = InstrumentLibrary({"H": h, "Z": z})
model = PredictiveModel(library)
encoded = model.encode(diagonal([1, 0]))

print(model.dimension)  # 3，包含恒定 trace 坐标
print(model.word_law(encoded, ["H", "H", "Z"]))
# {("ok", "ok", "0"): Fraction(1), ("ok", "ok", "1"): Fraction(0)}
```

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

表示证据要求 (1\le r\le d^2)，每个词见证长度不超过 (d^2-1)。这个生成证据上限没有给预测协议设置统一时域上限。整数位长和库内动作／Kraus 总数没有统一上限，程序不承诺总体固定运行时间或完整资源配额。响应维数包含 trace 坐标，不代表一个更小 CPTP Hilbert 模型的维数。

操作库固定且时齐。时间、资源或自动机约束需另外编码；省略相关环境时，系统态不能自动充当充分对象。没有用于任意外部坐标的物理可实现性判定器；`EncodedState` 由工厂构造，指纹只是上下文检查。

有限协议证书只覆盖给出的准备配对和因果树。标量预算需要明确的逐步前提。二者不自动变成全部状态/全部协议上的 trace-distance 或 diamond-norm 保证。

九个 Lean 模块覆盖旧量子操作与响应商，并新增词效应空间、有限 presentation 到全词坐标、闭合坐标更新、完整有限自适应树和谱求和桥。这些数学声明已通过本地实际统一构建和公理审计；远端 CI 与主线集成另行验收，当前仍为 `LOCAL_VERIFIED_CI_PENDING`。

Lean 的 finite presentation 允许冗余生成元；独立运行 checker 另检查基的线性独立性。Python 的数值解码、加权／不同结果指标 Kraus 适配、搜索与消元、PSD 判定和树遍历尚未完成到 Lean 的程序细化。也没有证明具体表示系数、matching 窗口、全局异常、真空或质量。范围与原件审查见 [v31.2 主报告](../UEOT_QM_KERNEL_v31.2.md)。

## 回执与版本身份

本版以 `evidence/v31.2/` 保存新的运行、演示、Lean 构建与公理回执。[本地证明回执](evidence/v31.2/lean-verification.json) 记录本轮真实构建和公理结果，[本轮台账](../status/CLAIM_LEDGER_v31.2.json) 记录机器覆盖与开放义务。本地验证通过与远端 CI／主线验收分开登记，不用历史输出填充新状态。

v31.1 的回执继续可读，保持其原源码身份：

- [Kernel 1 Lean 构建与源码身份](evidence/lean-verification.json)
- [Kernel 1 实际公理依赖](evidence/proof-axioms.json)
- [Kernel 1 的 32 项独立测试](evidence/runtime-verification.json)
- [Kernel 1 完整示例输出](evidence/kernel-demo.json)

运行时测试、机器证明、理论桥和物理适用性按独立状态登记。

