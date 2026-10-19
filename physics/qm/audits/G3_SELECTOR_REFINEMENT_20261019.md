# UEOT-QM G3：删除原子性前提的条件选择定理

日期：2026-10-19。基准：UEOT-QM v30.11（2026-09-04）的 displayed theorem 与完整正文。

**状态：本轮独立纸面证明 + 新写精确有理代数检查；不是 Lean 已证明，不是原归档脚本复跑，也不宣布 UEOT 无条件推出三代。**

## 1. 实质升级

v30.11 的主选择定理使用了“primitive / realization-atomic anomaly packet”。重新检查一般整数解发现，这项前提可以删除：其余算术条件已自动排除多包复制，并强制唯一包。

这使理论不必额外假定“宇宙选择最小异常中性包”。选择力来自**指定表示模板的异常整除约束，与指定弱相互作用有效理论窗口的 screening 上界相交**。原有 primitive packet 分类仍有用，但不再作为选择定理的前提。

本注记是对项目既有条件定理的假设精简。331 的异常算术与利用渐近自由约束代数均有先行研究；不据此宣称新的世界首创机制。[Q1][E1]

## 2. 精确定理

设

$$
N_c,N_f,k\in\mathbb Z,\qquad
N_c\ge3,\quad N_f>0,\quad 0\le k\le N_f.
$$

假设水平/扩展弱群的规定费米子模板给出

$$
N_f+N_c(2k-N_f)=0, \tag{A}
$$

并且规定的弱 $SU(2)_L$ 有效理论窗口满足必要预算

$$
N_f(N_c+1)<22. \tag{W}
$$

则

$$
\boxed{N_c=3,\qquad N_f=3,\qquad k=1.}
$$

这里没有 primitive、atomicity、最小代数或最小复杂度假设。

### 证明

将 (A) 写成

$$
2N_ck=(N_c-1)N_f.
$$

模 $N_c$ 得 $N_c\mid N_f$。由于 $N_c\ge3$ 且 $N_f>0$，存在正整数 $t$ 使

$$
N_f=N_ct.
$$

代入异常方程并约去正整数 $N_c$：

$$
2k=(N_c-1)t. \tag{B}
$$

再代入 (W)：

$$
tN_c(N_c+1)<22.
$$

由于 $N_c(N_c+1)\ge12$，有 $12t<22$。正整数 $t$ 只能等于 1。于是

$$
N_f=N_c,\qquad 2k=N_c-1,\qquad N_c(N_c+1)<22.
$$

最后一个不等式与 $N_c\ge3$ 给出 $N_c\in\{3,4\}$。由于 $2k=N_c-1$，$N_c$ 必须为奇数，故 $N_c=3$，进而 $N_f=3,k=1$。证毕。

实际上，$0\le k\le N_f$ 也可由其余条件和 (A) 推出：

$$
k=\frac{N_c-1}{2N_c}N_f\in(0,N_f/2).
$$

保留这个条件是为了明确它作为 quark-family multiplicity 的物理含义，不应把它写成一个独立的深层选择原理。

### 与旧 primitive theorem 的关系

原有全部正整数解仍为

$$
d=\gcd(2N_c,N_c-1)=\gcd(2,N_c-1),
\quad
(N_f,k)=s\left(\frac{2N_c}{d},\frac{N_c-1}{d}\right),
\quad s\in\mathbb Z_{>0}.
$$

新定理证明的是 (W) 自动令 surviving packet 的 $s=1$，不是撤回这项分类。

## 3. 算术假设背后的物理合同

不能把上面五行算术前提直接缩写成“Core + HGP”。至少应分别记录下列接口。

| 接口 | 精确内容 | 来源/状态 |
|---|---|---|
| 色群与计数 | 色因子为 $SU(N_c)$，每个 quark multiplet 为其 fundamental，且该 fundamental 真正为 complex | 独立 sector choice；在这个群族中给 $N_c\ge3$ |
| 非零异常表示 | 指定 $G_H$ 的 complex $R$，$A(R)=a\ne0$、$A(\bar R)=-a$ | 表示论输入；complex 本身不对任意群保证非零 cubic anomaly |
| 同质轻子模板 | 每个 family 恰含一个 color-singlet $R$ lepton multiplet，所有轻子选择同一异常符号 | 独立限制；泛称“有水平规范 parent”并不蕴含 |
| 夸克模板 | 每个 family 恰含一个带 $N_c$ 色重数的 $R$ 或 $\bar R$ quark multiplet | 独立限制；高维表示、mirror/extra families 会改变方程 |
| 异常归属 | 此通道的总异常由上述 family 内容承担；其他物质或合法 inflow/completion 的剩余贡献已证明为零 | 否则总一致性仅给 $A_{\rm fam}+A_{\rm extra}+A_{\rm inflow}=0$，不给 (A) |
| 弱窗口 | 存在一个所有所计 ordinary families 都 active、弱群仍为 $SU(2)_L$、耦合可微扰处理的 EFT 窗口，且此窗口的 one-loop 系数 $b_2>0$ | 独立动力学/经验假设；不是 Core 定理 |
| 完整实现 | 全球群、spin/其他切结构、完整局域及全局异常、标量势、破缺真空、质量谱、阈值 matching | 本算术定理没有证明这些门 |

“HGP 存在”与“该 HGP 必须采用上述模板”是两件事。完成前者不会自动完成后者。

### 弱系数的范围

使用

$$
\mu\frac{dg_2}{d\mu}=-\frac{b_2}{16\pi^2}g_2^3+O(g_2^5).
$$

若 ordinary matter 是每代 $N_c+1$ 个左手 Weyl doublets，固定 $SU(2)_L$ gauge carrier，其他额外贡献仅来自普通费米子和标量，则

$$
b_2=\frac{22}{3}-\frac{N_f(N_c+1)}3
-\frac23\sum_{\rm extra\ Weyl}T(R_f)
-\frac13\sum_{\rm complex\ scalar}T(R_s),
$$

实标量取对应的一半权重。所有标量都计入最后一项；一个 complex Higgs doublet 贡献 $1/6$。因此 $b_2>0$ 必然要求 (W)。$N_c=N_f=3$ 的一 Higgs 情形给 $b_2=19/6$，但任意扩展标量谱仍需重新计算。

**这只是该弱 EFT 窗口的正 one-loop 系数。** 当 $SU(2)_L$ 在高阈值并入 $SU(3)_L$ 或出现其他 gauge bosons 时，规范 Casimir、active 内容及 beta 函数都会改变。不能把 (W) 直接称为跨越全部阈值的 UV 渐近自由，也不能把“所有额外 matter 都只 screening”延伸到任意 gauge enhancement。

若不存在所有所计 families 同时 active 的适用窗口，应输出 `WINDOW_NOT_ESTABLISHED`；不能将不适用的预算当成排除更高代数的证明。

## 4. 删除前提的精确反例

下表中普通算术反例逐项保留其余所列算术条件；“模板”例子的完整局域异常另见下一节。

| 被删除的条件 | 见证 | 为什么不再选择三代 |
|---|---|---|
| $N_c\ge3$ / complex $SU(N_c)$ color | $(N_c,N_f,k)=(2,4,1)$ | 异常为零，弱预算 $4(2+1)=12<22$ |
| (W) | $(3,6,2)$ | 异常为零；预算 24，正是被 (W) 排除的双包复制 |
| (A) | $(3,1,0)$ | 预算 4；family 异常为 $-2a$ |
| $N_f>0$ | $(4,0,0)$ | 空 matter 解满足异常及预算，不是三代 |
| 整数 multiplicity | $N_c=4,N_f=4,k=3/2$ | 异常为零且预算 20；整数表示重数不可省 |
| 所有 lepton multiplets 同为 $R$ | $N_c=3,N_f=2,\ell=k=1$，$\beta=0$ | 六项完整局域异常为零，弱预算 8；如下表 |
| $a\ne0$ | 选择 cubic anomaly 系数为零的表示 | anomaly equation 本身不再由物质求和得到；约去 $a$ 无效 |

额外 anomaly-canceling sector 或 inflow 也可取消 $(3,1,0)$ 的 family 残余；其完整有效性需单独实现。这说明总 gauge consistency 不自动要求 family 子谱自身异常为零。

## 5. 更强的模板反例：两代、六项局域异常全部抵消

令 gauge algebra 为 $su(3)_C\oplus su(3)_L\oplus u(1)_X$，取 $Q=T_3+X$，即 $\beta=0$。下表全为左手 Weyl 字段；重数写在最后一列。

| 字段 | $(SU(3)_C,SU(3)_L,X)$ | 重数 |
|---|---|---:|
| $L_+$ | $(1,3,-1/2)$ | 1 |
| $L_-$ | $(1,\bar3,-1/2)$ | 1 |
| $e^c$ | $(1,1,+1)$ | 2 |
| $E^c$ | $(1,1,+1/2)$ | 2 |
| $Q_+$ | $(3,3,+1/6)$ | 1 |
| $Q_-$ | $(3,\bar3,+1/6)$ | 1 |
| $u^c$ | $(\bar3,1,-2/3)$ | 2 |
| $d^c$ | $(\bar3,1,+1/3)$ | 2 |
| $J^c$ | $(\bar3,1,-1/6)$ | 2 |

ordinary lepton 与 quark doublets 的电荷分别仍为 $(0,-1)$、$(2/3,-1/3)$，anti-triplet 中分量次序可交换。额外分量为电荷 $-1/2$ 的轻子及 $1/6$ 的夸克。

若 $\ell$ 表示取 $R$ 的轻子数，则一般 cubic 方程变成

$$
(2\ell-N_f)+N_c(2k-N_f)=0.
$$

取 $N_f=2,\ell=k=1$ 即为零。所有右手共轭 singlets 按上表补齐后，独立 exact rational 求和还得到

$$
A_{C^3}=A_{L^3}=A_{C^2X}=A_{L^2X}=A_{\mathrm{grav}^2X}=A_{X^3}=0.
$$

弱预算是 $2(3+1)=8<22$。这个更大模板内的一代无法使 $\pm1\pm3=0$，因此该两代谱在 family-count 意义上已经是最小正闭合包。**重新加回“最小包”也无法从这个更大模板唯一选择三代。**

该见证用于反驳“广义 HGP/异常/weak-budget 条件已经自动含同质轻子模板”的推论。它目前只是局域异常谱与算术窗口见证，尚未认证全球群上的全部异常、标量真空、质量生成、稳定性或现实实验；这些门不能由六个零替代。

## 6. v30.11 任意 β 的完整谱说明需补齐 E^c

v30.11 generalized-331 段明确列出 $e^c,u^c,d^c,J^c$，但其任意 $\beta$ 的异常恒等式还需要说明 exotic lepton 的 singlet completion。对正文采用的 generic Dirac-completion class，应显式加入

$$
E^c:(1,1,-q_E),\qquad
q_E=-\frac12-\frac{\sqrt3\beta}{2}.
$$

否则轻子部分残余为

$$
A_{\mathrm{grav}^2X}^{\rm missing\ E^c}=N_fq_E,
$$

且完整谱公布的 $A_{X^3}$ 要再加 $N_fq_E^3$。例如 $N_c=N_f=3,\beta=0$ 给出残余 $-3/2$ 与 $-3/8$，并不为零。

补上 $E^c$ 后，本轮独立 Laurent 多项式检查精确重现

$$
A_{L^2X}=\frac{N_f(N_c-3)}{12},\qquad
A_{X^3}=-\frac{N_f(N_c-3)(1+\beta^2)}4,
$$

以及 $A_{\mathrm{grav}^2X}=A_{C^2X}=0$。这里已代入 $k=N_f(N_c-1)/(2N_c)$。

对 $\beta=-1/\sqrt3$ 的 331RHN witness，$q_E=0$，所以这个漏写不改变其 gauge-anomaly 求和。若选择第三分量与既有共轭场识别的特殊 β 模型，则应另列完整表，避免重复添加同一物理场。

把 ordinary quark charges 改为

$$
Q_u=\frac{N_c+1}{2N_c},\qquad
Q_d=-\frac{N_c-1}{2N_c}
$$

且相应调整全部 singlet/completion charges 后，本轮进一步精确确认：在 horizontal cubic cancellation 下，$A_{L^2X}$ **与** $A_{X^3}$ 都对任意非零 $N_c$ 恒为零。v30.11 的 charge firewall 因而可写得更完整：固定普通电荷导出的三色选择不能搬到一般电荷类。

## 7. 本轮验证与可形式化目标

新写脚本：[qm_frontier_exact_audit.py](../benchmarks/qm_frontier_exact_audit.py)；本轮输出：[qm_frontier_exact_audit.json](../benchmarks/results/qm_frontier_exact_audit.json)。

本轮确实执行了 13 项检查，13 项通过。使用 Python 标准库 `Fraction` 和有限支持有理 Laurent 多项式；没有近似浮点拟合。本脚本不依赖 SymPy；不声称进行了历史 SymPy 脚本复跑。

其中无原子性选择枚举是对**经证明的全部有限域**进行：由 (W)、$N_f\ge1$、$N_c\ge3$ 推出

$$
3\le N_c\le20,\quad 1\le N_f\le5,\quad0\le k\le N_f.
$$

共检查 360 个整数组合，仅 $(3,3,1)$ 存活。一般结论以第二节的整除证明为主；该枚举提供独立可执行核对。

后续 Lean 目标应保持算术表面，例如

```lean
-- Proposed declaration shape only; no compile-success claim in this note.
theorem horizontal_anomaly_weak_budget_selects_three
    (nc nf k : ℕ)
    (hcolor : 3 ≤ nc)
    (hfamilies : 0 < nf)
    (hquarks : k ≤ nf)
    (hanomaly : 2 * nc * k + nf = nc * nf)
    (hweak : nf * (nc + 1) < 22) :
    nc = 3 ∧ nf = 3 ∧ k = 1 := by
  -- Divisibility/parity proof, or interval cases using proved finite bounds.
  ...
```

示意中的省略号不属于任何已提交 Lean 源码。正式实现不能使用 `sorry` 或承认假设替代证明。这个 theorem 形式化后只证明整除/预算结论；另需 adapter 精确证明声明表示谱产生 `hanomaly` 与 `hweak`，并审计 adapter 的实际前提。

若后续环境具备 SymPy，可用独立实现复核：设置 $z=\beta/\sqrt3$，用 `Rational` 给出全部电荷；按完整谱直接求和六项异常；先输出未施加约束的多项式，再代入异常关系并 `factor`。不得直接把目标 factorization 作为计算输入。至少包含缺失 $E^c$、混合轻子 $3/\bar3$、额外 anomalous sectors、两包复制及无适用窗口这五类负/边界控制。

## 8. 来源与归属

- [Q1] `UEOT-QM_v30.11_P8R-G3_Gauge-Orbit-Horizontal-Anomaly-Atomicity_Strict.tex`，330 行完整正文。本轮经正文读取，不声称原始字节/归档 SHA 已验证。
- [Q2] `P8_G3_DEEP_AUDIT_v30_11.md`。
- [Q3] `UNIFIED_MAINLINE_v30_11.md`。
- [Q4] `NUMERICAL_REGRESSION_v30_11.json`。这是读取到的历史 27/27 报告，不能与本轮 13 项新检查混称。
- [E1] R. A. Diaz, R. Martinez, F. Ochoa, *SU(3)c × SU(3)L × U(1)X models for β arbitrary and families with mirror fermions*, Phys. Rev. D 72, 035018 (2005), [arXiv:hep-ph/0411263](https://arxiv.org/abs/hep-ph/0411263)。包含更一般 family/representation 选择，不能将熟悉的 331 模板视作泛型 gauge parent 的唯一形式。
- [E2] K. Yonekura, *Dai-Freed theorem and topological phases of matter*, JHEP 09 (2016) 022, [arXiv:1607.01873](https://arxiv.org/abs/1607.01873)。determinant line 与 η/Berry 描述的标准数学来源。
- [E3] I. García-Etxebarria, M. Montero, *Dai-Freed anomalies in particle physics*, JHEP 08 (2019) 003, [arXiv:1808.00009](https://arxiv.org/abs/1808.00009)。标准模型的 refined anomaly consistency 与额外 discrete-symmetry 假设需要分开。
- [E4] J. Davighi, B. Gripaios, N. Lohitsiri, *Global anomalies in the Standard Model(s) and Beyond*, JHEP 07 (2020) 232, [arXiv:1910.11277](https://arxiv.org/abs/1910.11277)。完整群的中心商与切结构会影响全局异常问题的定义。

本注记不修改 Frozen Core 的 106 项或压缩账本，不恢复 $\beta_1=3\Rightarrow\operatorname{Index}D=3$ 的退役推论，不将新的条件数学结论计为实验确认。
