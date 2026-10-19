# UEOT-QM v31.2：有限谱条目到三代选择的桥

日期：2026-10-19。承接 Kernel 1 的 `Selector.selects_three_without_atomicity` 与 [G3 物理接入合同](G3_PHYSICAL_ADAPTER_CONTRACT_20261019.md)。

本次将上一版尚未闭合的“谱计数桥”落实为显式数据、逐项求和、条件定理及精确执行。新代码不接收目标代数，也不接收 Selector 的最终整数式或弱预算作为结构字段。有限谱自身给出这些量。

**验收状态：`LOCAL_VERIFIED_CI_PENDING`。** 新增 Python 的 22 个独立测试方法已在本地全部通过，统一运行套件共 72 项通过。`Spectrum.lean` 的 15 个定理已随九模块统一构建通过，完整 137 项实际公理审计通过；源码绑定提交为 `323db6d1c2e50a432bdcf6a6872212426cc826ce`。详见 [本轮证明回执](../kernel/evidence/v31.2/lean-verification.json)。远端 CI 与主线集成仍待完成。原 Kernel 1 回执保持其既有源码身份。

实现：[Spectrum.lean](../../../formalization/ueot-qm/UEOTQM/Spectrum.lean)、[spectrum.py](../kernel/ueot_qm/spectrum.py)、[test_spectrum.py](../kernel/tests/test_spectrum.py)。冻结 Core 源码、106 项覆盖及四生成器台账保持原身份。

## 1. 输入合同与科学范围

一个 `Family` 是两条明确的手征 multiplet 数据：一个 color-singlet lepton 和一个色基本表示 quark。各自声明所研究三次异常通道上的 `R` 或 `Rbar` 方向。每个 quark multiplet 的色重数为输入的自然数 (N_c)，每个 lepton 的色重数为 1。每个 multiplet 在指定窗口活跃时，每色提供一个普通弱 Weyl 双重态。

其中，“包含这两类 multiplet、采用这些色表示、各提供一个双重态”是本次扇区模板。它们通过结构定义明确限定了被讨论的谱类。程序及 Lean 没有从一般表示论导出这些数据，也没有声称任意规范母结构只能采用此模板。

| 内容 | 数据及核查 | 剩余物理义务 |
|---|---|---|
| 异常方向 | `R` 的单位为有理数 (a)，`Rbar` 反号；选择需要 (a\ne0) | 具体表示确有此三次异常系数及共轭律 |
| 同质轻子 | 所有有限条目的 lepton 方向为 `R` | 为什么实际模型采用这个受限模板 |
| 额外物质 | Weyl 的有符号 cubic 系数、重数及弱 Dynkin index 逐项列出；标量 cubic 为零 | 表示、荷、实结构以及完整物种的来源 |
| 额外 completion | 独立列出所选通道的有符号项及来源 | inflow／completion 机制存在和有效的证明 |
| 弱窗口 | 固定 (SU(2)_L)、可微扰、active 谱完整、matching，以及 ordinary 各行是否活跃 | 这些模型声明是否有独立推导或经验支持 |

`WeakWindow` 的布尔字段记录物理声明，不能充当它们的证明。改变规范载体、没有匹配窗口、或所有被计家族并未同时活跃时，程序明确不给出三代选择结论。

额外物质的 `weak_index` 已包含除 `copies` 外的旁观重数，是每份额外条目的总弱 Dynkin index。程序强制非负，区分 Weyl、复标量、实标量权重；它不自动认证任意输入 index 是否对应某个实际表示。额外场的弱阈值失活不会静默删除规范母谱中的异常贡献。跨阈值的异常匹配仍须单独建立。

## 2. 实际求和怎样产生异常方程

设谱有 (n) 个家族，轻子取 `R` 的数量为 (\ell)，夸克取 `R` 的数量为 (k)。这些量均从列表计算。每个家族两行的 selected-channel contribution 是

\[
A_{L_i}=a s_{L_i},\qquad
A_{Q_i}=N_c a s_{Q_i},\qquad s\in\{+1,-1\}.
\]

对有限列表求和得到

\[
A_{\rm family}
=a\bigl[(2\ell-n)+N_c(2k-n)\bigr].
\]

`familyCubic_eq_counts` 从两行贡献的递归求和证明该恒等式。`quarkCount_le_length` 从逐条方向计数证明 (k\le n)。同质轻子条件再给出 (\ell=n)。

额外 Weyl 条目及其他 completion 的总和记为 (A_{\rm extra})。一般一致性只给

\[
A_{\rm family}+A_{\rm extra}=0.
\]

主桥明确另外要求 **额外项的组合总和为零**，允许额外项彼此抵消，不要求每一条独自为零。在 (a\ne0) 下，才得到

\[
n+N_c(2k-n)=0,
\qquad
\boxed{2N_ck+n=N_cn}.
\]

`selector_anomaly_of_spectrum` 输出最后的自然数等式。主定理输入中没有该等式。

这个区别已经有实算反例：一个 (N_c=3)、lepton-R、quark-Rbar 家族给出 (-2a)。外部补上 (+2a) 可使总异常为零，却不产生 family 子谱的选择方程。程序因此报告额外和条件失败。

## 3. 实际弱条目怎样产生预算

采用与前版一致的约定

\[
\mu\frac{dg_2}{d\mu}
=-\frac{b_2}{16\pi^2}g_2^3+O(g_2^5).
\]

固定 (SU(2)) 规范载体的一环反屏蔽项为 (22/3)。一个 Weyl 双重态的贡献为 (\frac23T(2)=\frac13)。每个活跃家族因此逐行贡献 (1/3+N_c/3)。

额外物质的屏蔽为

\[
S_{\rm extra}
=\frac23\sum_{\rm Weyl}m_i T_i
+\frac13\sum_{\rm complex\ scalar}m_i T_i
+\frac16\sum_{\rm real\ scalar}m_i T_i
\ge0,
\]

各和只计该窗口活跃的条目。所有 ordinary 家族两行均活跃时，有限求和证明

\[
b_2=\frac{22}{3}-\frac{n(N_c+1)}3-S_{\rm extra}.
\]

`familyScreening_eq_of_active` 证明 ordinary 项，`extraScreening_nonneg` 证明额外项的符号，`selector_budget_of_spectrum` 从实际 (b_2>0) 推出

\[
\boxed{n(N_c+1)<22}.
\]

该预算是必要条件。一个三代谱已有 ordinary 预算 12，但若另外有 20 份 complex scalar doublet，则额外屏蔽达到 (10/3)，完整 (b_2=0)。程序使用完整系数判断，不能仅凭 (12<22) 给这个扩展谱通过。

这些系数约定继承[此前 G3 精化审计 §3](G3_SELECTOR_REFINEMENT_20261019.md)，并与 [Luo–Wang–Xiao 原文 Eq. (30)](https://arxiv.org/pdf/hep-ph/0211440) 的一环项核对：二分量费米子取 \(\kappa=1/2\)，该文标量采用实分量约定，复标量换算后权重加倍。本桥证明其算术结果，不独立完成规范场论一环计算，也不把特定弱窗口解释成所有阈值以上的 UV 渐近自由。

## 4. 与已证 Selector 的真实组合

主声明为 `UEOTQM.Spectrum.spectrum_selects_three`。其核心输入是：

- (N_c\ge3)、非空有限 family 列表、非零有理异常单位；
- 同质 lepton-R，ordinary 两行均在指定窗口活跃；
- 额外 cubic 总贡献为零、完整逐项 cubic 求和为零；
- 按实际普通与额外屏蔽求得的 (b_2>0)。

先调用上述三个计数／预算桥，得到旧 Selector 的两个算术前提和 (k\le n)，再实际调用 `Selector.selects_three_without_atomicity`，输出

\[
\boxed{N_c=3,\quad \operatorname{length}(\mathrm{families})=3,
\quad \operatorname{quarkCount}(\mathrm{families})=1.}
\]

原子性、最小包、预先指定代数，以及目标异常方程都未作为本主声明的前提。上述谱模板、非零异常单位、额外总和与窗口前提继续保留其物理含义。

本 Lean 模块包含逐项数值对照：三代加一 Higgs、混合两代、六代复制、补偿一代、零异常单位一代、额外屏蔽闭合窗口。它们是同一实际定义下的有限行计算。

## 5. 独立的六项 331 局域异常计算

运行层另有 `Weyl331` 清单及 `local_331_anomalies`，输入全部使用左手 Weyl 约定。当前支持 (SU(3)) 的 singlet、fundamental、antifundamental；分别采用维数 (1,3,3)，quadratic index (0,1/2,1/2)，cubic index (0,+1,-1)。这些是声明的表示数据。

设某行色和左群维数为 (d_C,d_L)，重数 (m)、荷 (X)。逐行计算

\[
\begin{aligned}
A_{C^3}&=m d_L A(C),& A_{L^3}&=m d_C A(L),\\
A_{C^2X}&=m d_L T(C)X,& A_{L^2X}&=m d_C T(L)X,\\
A_{\mathrm{grav}^2X}&=m d_Cd_L X,& A_{X^3}&=m d_Cd_L X^3.
\end{aligned}
\]

`generalized_331_fields` 用精确有理参数 (z=\beta/\sqrt3) 生成显式的 (L,e^c,E^c,Q,u^c,d^c,J^c) 行。普通电荷固定为 ((0,-1)) 与 ((2/3,-1/3))。若两个方向符号为 (s_L,s_Q)，则

\[
X_L=-\frac12-\frac{s_Lz}{2},\quad
X_Q=\frac16-\frac{s_Qz}{2},\quad
q_E=-\frac12-\frac{3s_Lz}{2},\quad
q_J=\frac16-\frac{3s_Qz}{2}.
\]

singlet completions 使用相应共轭荷。该生成器固定色群为 (SU(3)_C)，family 数和两个方向均可变化。它没有预先设置 anomaly totals。

**范围：** 新 Lean 谱桥证明一个选定 cubic 通道和弱预算；六项局域异常计算是独立的精确运行证据。对多个 (z) 点计算通过，不登记成“任意实 β 的新 Lean 恒等式”。历史任意 β 的纸面／符号审计保留原证据身份。

## 6. 已执行的正例、反例与拒绝

本地命令：

```bash
cd physics/qm/kernel
python -m unittest discover -s tests -p test_spectrum.py -v
```

实际结果：22 个测试方法全部通过；每个方法可包含多个严格有理实例。

| 实例 | 实际精确结果 | 接口输出或含义 |
|---|---|---|
| 三代、1 个 quark-R、1 Higgs | cubic 为 0；(b_2=19/6) | 在声明合同下 Selector 适用 |
| 将异常单位整体改为 (-7/3) 或 (5/11) | 总异常仍为 0 | 非零系数不必正；全局约定反号不改变选择 |
| 混合轻子两代，β=0 | 六项局域异常全零；(b_2=14/3) | 同质轻子条件失败，不返回三代 |
| 复制为六代 | 六项局域异常全零；(b_2=-2/3) | 完整弱系数条件失败 |
| 一代加 (+2a) completion | family 异常 (-2a)，总异常 0 | 额外总和条件失败 |
| 零异常单位、一代 | cubic 为 0；(b_2=6) | 不允许约去零，拒绝选择 |
| 三代加 20 份 complex doublet | ordinary 预算 12；完整 (b_2=0) | 拒绝用必要预算代替完整系数 |
| 六代但仅三代在弱窗口活跃 | (b_2=10/3>0)，全谱预算 24 | 全 ordinary 活跃条件失败 |
| 三代缺 (E^c)，(z=0) | grav 残余 (-3/2)，cubic-X 残余 (-3/8) | 完整谱不通过 |
| 三代缺 (E^c)，(z=1/5) | grav (-12/5)，cubic-X (-192/125) | 保留一般参数的遗漏失效 |
| RHN 特殊点 (z=-1/3) 缺中性 (E^c) | 六项局域异常仍零 | 特殊中性点不支持一般省略 |
| 一个 (u^c) 错用 color-3 | (A_{C^3}=2) | 共轭方向错误可检出 |
| 一个 (E^c) 荷反号 | grav (-1)，cubic-X (-1/4) | 荷符号错误可检出 |
| 一个 (E^c) 重数从 1 改 2 | grav (1/2)，cubic-X (1/8) | 权重错误可检出 |

完整三代谱还分别在 (z=-2,-1/3,0,1/5,5/7) 五个精确有理点得到六个零。浮点输入、非整数／负重数、负 Dynkin index、标量的非零手征异常系数、错误枚举和重复标签均有拒绝检查。

## 7. 程序回执与尚未完成的桥

`inspect_spectrum` 返回不可变 canonical JSON 包装。`to_dict()` 每次产生新副本，内容包含每条输入贡献、所有求和、窗口声明、失败条件和条件选择的实际计数；散列绑定这份回执的内容。谱文件本身的源码身份由本轮整体运行回执另行绑定。

调用示例：

```python
from fractions import Fraction
from ueot_qm.spectrum import (
    Orientation as O, MatterKind as M, Family, ExtraMatter,
    WeakWindow, Spectrum, inspect_spectrum,
)

families = (
    Family("f1", O.R, O.R),
    Family("f2", O.R, O.RBAR),
    Family("f3", O.R, O.RBAR),
)
higgs = ExtraMatter("H", M.COMPLEX_SCALAR, 1, Fraction(1, 2))
window = WeakWindow("declared SU(2) window", True, True, True, True)
receipt = inspect_spectrum(Spectrum(3, 1, families, window, (higgs,)))
print(receipt.canonical_json)
```

上例仅展示如何输入一个已声明的窗口；真正接入某个模型时，必须给窗口声明附上独立依据。

本次关闭的是有限条目到条件 Selector 的算术桥。后续仍需：具体群表示及 anomaly coefficient 的形式化来源；规范母谱与弱 EFT 的阈值匹配；全部局域及全局异常、全球规范群和切结构；标量势、真空、质量及现象学；以及 Python 执行与 Lean 数据类型之间的程序细化。六个局域零和条件三代不能替代这些门。

## 8. 原始物理文献与归属

1. M. Luo, H. Wang, Y. Xiao, *Two-loop Renormalization Group Equations in General Gauge Field Theories*, Phys. Rev. D **67**, 065019 (2003)，[arXiv:hep-ph/0211440 原文](https://arxiv.org/pdf/hep-ph/0211440)，[DOI](https://doi.org/10.1103/PhysRevD.67.065019)。本轮直接核对 Eq. (30) 的一环规范项、Eq. (23) 附近的 \(\kappa=1/2\) 二分量约定，以及 §II 的实标量约定。由此换算本文 Weyl／complex scalar／real scalar 权重。此处使用的是该论文的一环公式，不引用其两环结果作为本内核新增覆盖。

2. M. E. Machacek, M. T. Vaughn, *Two-loop renormalization group equations in a general quantum field theory: (I). Wave function renormalization*, Nucl. Phys. B **222**, 83–103 (1983)，[原始期刊入口](https://www.sciencedirect.com/science/article/abs/pii/0550321383906107)，[DOI](https://doi.org/10.1016/0550-3213(83)90610-7)。这是一般规范耦合计算的经典原始来源；本轮可读系数逐式核对使用上一项原文。

3. R. A. Diaz, R. Martinez, F. Ochoa, *SU(3)c × SU(3)L × U(1)X models for β arbitrary and families with mirror fermions*, Phys. Rev. D **72**, 035018 (2005)，[arXiv:hep-ph/0411263 原文](https://arxiv.org/pdf/hep-ph/0411263)，[原始期刊入口](https://journals.aps.org/prd/abstract/10.1103/PhysRevD.72.035018)。§2 的 multiplet 分支和异常分类为任意 \(\beta\)、不同 family／方向模板提供原始研究背景。本文全左手清单和具体两代、缺 \(E^c\) 控制由当前程序逐项重算；不把该论文整个模型的真空／质量分析自动赋给这些测试清单。

这些参考文献支持标准表示谱与量子场论系数的来源。三代的具体条件选择、有限表求和实现、Lean 组合和反例回执仍各自按本项目的实际证据说明。
