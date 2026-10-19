# UEOT-QM Kernel 1

首个有限维操作内核：**合法量子操作 → 完整记录律 → 协议响应坐标 → 递归更新 → 有范围的误差证书**。

理论定义和物理边界见 [v31.1 内核说明](../UEOT_QM_KERNEL_v31.1.md)。Lean 源码位于 [formalization/ueot-qm](../../../formalization/ueot-qm/README.md)，固定继承 Core 的 Lean 4.33.1 和 Mathlib revision。

首版验收：[工作流 39270031506](https://github.com/MurphyHoops/UEOT/actions/runs/39270031506) 全绿，32 个运行测试方法通过，56 个 Lean theorem 声明编译通过，59 个声明完成实际公理审计。准确源码身份见下方回执。

## 立即运行

从仓库根目录执行；Python 3.10+，只使用标准库，CI 使用 Python 3.12：

```bash
python physics/qm/kernel/demo.py
python physics/qm/kernel/verify_kernel.py
```

第二条命令运行 32 个独立测试方法，并写出带源文件哈希的 `evidence/runtime-verification.json`。也可以用 `--output /tmp/qm-runtime.json` 指定回执位置。示例输出包括 Z/HZ/HSZ 的响应维数 2/3/4、H–H 干涉、有限协议差由 0 变为 1、稀有事件后选择及标量误差链。

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

`InstrumentLibrary` 通过密度矩阵计算记录律；`PredictiveModel` 通过响应坐标计算。后者接受密度矩阵或已编码态作为记录接口输入。

证书接口从 `ueot_qm.certificates` 导入：

- `compare_finite_protocols(left,right,preparation_pairs,protocols)`：实际计算所有指定配对/因果树的 TV；范围与指纹绑定。
- `transport_budget(initial,steps)`：在声明局部前提下计算条件式标量预算。
- `verify_transport_trace(errors,initial,steps)`：实查初值和每一步递推；失败则拒绝。
- `certify_postselection(left,right,event)`：要求双方事件概率正，计算条件 TV 及含事件概率的上界。

## 准确范围

运行时支持 Gaussian-rational 数据和 Hilbert 维数 1–4；浮点数及超出状态维数的输入明确拒绝。Hadamard 使用整数矩阵加权 1/2，结果依然精确。响应维数包含 trace 坐标，不代表一个更小 CPTP Hilbert 模型的维数。

操作库固定且时齐。时间、资源或自动机约束需另外编码；省略相关环境时，系统态不能自动充当充分对象。没有用于任意外部坐标的物理可实现性判定器；`EncodedState` 由工厂构造，指纹只是上下文检查。

有限协议证书只覆盖给出的准备配对和因果树。标量预算需要明确的逐步前提。二者不自动变成全部状态/全部协议上的 trace-distance 或 diamond-norm 保证。

Lean 提供具体量子操作、全词响应商、闭合更新、条件式 transport 与 G3 算术证明。Python 数值表示、PSD 判定、W* 算法与有限树解释器的程序细化尚未完成。两层的准确对应见 [交叉审查](../audits/KERNEL_REVIEW_20261019.md)。

## 回执

- [Lean 构建与源码身份](evidence/lean-verification.json)
- [实际公理依赖](evidence/proof-axioms.json)
- [32 项独立测试](evidence/runtime-verification.json)
- [完整示例输出](evidence/kernel-demo.json)

运行时测试、机器证明、理论桥和物理适用性按独立状态登记。

