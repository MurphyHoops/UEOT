<a id="ch-60"></a>

# 60. 全效应分离与复模型的普遍局部层析

第50章从实际 Born 概率构造了全效应距离，并证明概率界、对称性、三角不等式和通道收缩；其中距离为零的结论准确停在“所有效应给出同样概率”。第55章则证明，在完整实量子模型中，即使知道全部局域产品效应的统计，也可能无法确定联合态。第57章给出了同一操作语言中的完整复模型，留下了它是否对所有联合态满足局部层析的正向责任。

本章在原有完整有限复密度空间中闭合这两项责任。关键不是直接把矩阵元素当作可测量量，而是先把任意 Hermitian 测试写成合法效应的实线性组合，再从真实效应概率恢复矩阵。联合情形对任意密度态成立，包括并非产品态的输入；所用信息是两侧效应的联合概率，包含相关性，并非只给两个边际。

## 60.1 完整状态、完整效应与实值配对

固定任意有限载体 $\iota$。本章的矩阵、状态和效应分别为

$$
\begin{aligned}
M_\iota&=M_\iota(\mathbb C),\\
\mathcal D(\iota)&=\{\rho\in M_\iota:\rho\succeq0,\ \operatorname{Tr}\rho=1\},\\
\mathcal E(\iota)&=\{E\in M_\iota:E\succeq0,\ I-E\succeq0\}.
\end{aligned}
$$

正性采用完整复矩阵的正半定锥。没有把态限制成对角态、向量态、选定的 Gram 因子输入或有限样本，也没有把效应限制为某个仪器库恰好能实现的测试。Lean 的 `Density` 与 `Effect` 是此前已经使用的实际类型；新增证明不改动它们的定义。

对任意矩阵 $H,X$，记实值迹配对

$$
\langle H,X\rangle_{\mathbb R}
=\operatorname{Re}\operatorname{Tr}(HX).
$$

效应概率就是 $p_\rho(E)=\langle E,\rho\rangle_{\mathbb R}$。这个配对对两边都具有实线性。把复矩阵乘以复数之后再取实部，不会得到一个以复数为值域的复线性概率函数，因此以下全部概率扩张只使用实系数。

正算符次序 $H\preceq K$ 表示 $K-H$ 正半定。对 Hermitian $H$，有限矩阵的算符范数给出

$$
-\|H\|_{\rm op}I\preceq H\preceq\|H\|_{\rm op}I.
$$

这里的范数是复欧氏空间上的矩阵算符范数，Lean 在相应证明段显式使用 `Matrix.Norms.L2Operator`。上述次序界来自已锁定的有限矩阵 $C^*$ 数学依赖；它不是额外的物理谱假设，也没有预先要求调用者提供分离效应。[QM318]

## 60.2 每个 Hermitian 算符都由合法效应实线性张成

<a id="p-sep-01"></a>

**P-SEP-01（Hermitian 算符的合法效应表示）。** 对任意有限载体 $\iota$ 和任意 Hermitian 矩阵 $H$，存在实数 $r>0$ 与实际效应 $E\in\mathcal E(\iota)$，使

$$
H=2rE-rI.
$$

因此全部 Hermitian 矩阵都属于全部效应矩阵在实数域上的线性张成。

**证明。** 取 $r=\|H\|_{\rm op}+1$。由范数非负知 $r>0$；由上一节两个次序界，分别加上正半定的 $I$，得到

$$
H+rI\succeq0,\qquad rI-H\succeq0.
$$

定义

$$
E=\frac{H+rI}{2r}.
$$

系数 $(2r)^{-1}$ 严格为正，故 $E\succeq0$。还须验证效应的上界，而不能只验证正性。实际矩阵恒等式给出

$$
I-E=\frac{rI-H}{2r}\succeq0.
$$

这同时建立了 `Effect` 所要求的两个正性字段。由于 $2r\ne0$，重新整理定义即得 $H=2rE-rI$。单位矩阵本身是合法效应，因此 $H$ 是两个效应矩阵的实线性组合。∎

这里“张成”不是说每个 Hermitian 矩阵都是效应的凸混合。系数 $-r$ 可以为负，重建公式允许对不同效应的概率做有符号的实数运算；它并未把这个运算本身定义为一个新的随机混合实验。

形式化中的 `boundedHermitianEffect` 先处理任意给定的双侧次序界；`boundedHermitianEffect_affine` 证明实际矩阵恒等式；`exists_effect_affine_of_hermitian` 从 $H$ 本身导出所需界；`hermitian_mem_real_span_effects` 则把结论明确写进 `Submodule.span ℝ`。实系数性质是声明的一部分。[QM318]

这个构造在空载体上同样有意义：唯一矩阵为零，单位矩阵也为零，仍可取 $r=1$。后面关于密度态的前提则会自动排除空载体上的虚构归一态，见第60.6节。

## 60.3 全效应同概率迫使实际密度态相等

先从 P-SEP-01 得到一个可复用的中间步骤。若任意两个矩阵 $X,Y$ 满足

$$
\langle E,X\rangle_{\mathbb R}
=\langle E,Y\rangle_{\mathbb R}
\quad\text{对全部 }E\in\mathcal E(\iota),
$$

则它们对任意 Hermitian $H$ 的配对也相同。事实上，取 $H=2rE-rI$ 后，实线性分别给出

$$
\langle H,X\rangle_{\mathbb R}
=2r\langle E,X\rangle_{\mathbb R}
-r\langle I,X\rangle_{\mathbb R},
$$

对 $Y$ 同理。假设涵盖实际效应 $E$ 和单位效应 $I$，故两式相等。这个中间步骤不要求 $X,Y$ 为密度态，真正用到 Hermitian 性的是测试 $H$ 的合法效应表示。

<a id="p-sep-02"></a>

**P-SEP-02（全效应分离与距离零的矩阵含义）。** 对任意 $\rho,\sigma\in\mathcal D(\iota)$，

$$
\rho=\sigma
\quad\Longleftrightarrow\quad
\forall E\in\mathcal E(\iota),\ p_\rho(E)=p_\sigma(E).
$$

对第50章实际定义的全效应距离

$$
d_{\rm eff}(\rho,\sigma)
=\sup_{E\in\mathcal E(\iota)}
|p_\rho(E)-p_\sigma(E)|,
$$

相应有 $d_{\rm eff}(\rho,\sigma)=0$ 当且仅当 $\rho=\sigma$。

**证明。** 相等的密度态当然给出相等概率。反过来，令 $D=\rho-\sigma$。由两态的正性知它们都是 Hermitian，因此 $D$ 也是 Hermitian。以上实线性扩张可用 $H=D$，给出

$$
\langle D,\rho\rangle_{\mathbb R}
=\langle D,\sigma\rangle_{\mathbb R}.
$$

再对配对的右侧做减法，得到

$$
\operatorname{Re}\operatorname{Tr}(D^\dagger D)
=\operatorname{Re}\operatorname{Tr}(DD)=0.
$$

$D^\dagger D$ 正半定，其迹的虚部为零。于是完整复数迹也为零。有限矩阵恒等式

$$
\operatorname{Tr}(D^\dagger D)
=\sum_{i,j}|D_{ij}|^2
$$

说明每个矩阵元素都为零，故 $D=0$，即 $\rho=\sigma$。形式证明使用 `Matrix.trace_conjTranspose_mul_self_eq_zero_iff` 完成这一步，之前已单独补足实部为零到完整迹为零的理由。

距离部分使用第50章已经证明的上确界性质：距离为零当且仅当每个效应的概率相同。接上刚才的分离结论即得双向等价。∎

新公开号 `QuantumSeparation.effectDistance_eq_zero_iff_density_eq` 与旧的 `UEOTQM.effectDistance_eq_zero_iff` 分开命名。旧定理仍准确表达全效应同概率，新定理给出它与实际密度相等之间此前缺失的连接。这不需要改写旧的收缩、条件化或扰动证明，也不附带另一个矩阵范数的同一性声明。[QM318]

## 60.4 从四个合法产品测试扩张到 Hermitian 产品

现在固定两个任意有限载体 $\iota,\nu$，联合系统实际采用 $\iota\times\nu$。对局部效应 $E,F$，原有 `RealLocalTomography.productEffect` 的矩阵就是 $E\otimes F$。这个历史模块名并不限制其输入为实矩阵：定义本身接受任意复效应，实模型的限制由另一个实性字段单独承担。

产品效应的合法性来自 Kronecker 正性及恒等式

$$
I_{\iota\times\nu}-E\otimes F
=(I_\iota-E)\otimes I_\nu
+E\otimes(I_\nu-F).
$$

右边两项均正半定。因此这里的联合测试是一个具有完整正性和上界证明的实际效应。

设两个任意联合密度态 $\rho,\sigma$ 对全部局部产品效应给出相同概率。给定任意局部 Hermitian 矩阵 $H,K$，分别用 P-SEP-01 写成

$$
H=2rE-rI_\iota,\qquad K=2sF-sI_\nu,
\qquad r,s>0.
$$

实际 Kronecker 乘法分配律给出四项实展开：

$$
\begin{aligned}
H\otimes K={}&4rs\,E\otimes F
-2rs\,E\otimes I_\nu\\
&-2rs\,I_\iota\otimes F
+rs\,I_\iota\otimes I_\nu.
\end{aligned}
$$

假设分别涵盖 $(E,F)$、$(E,I_\nu)$、$(I_\iota,F)$、$(I_\iota,I_\nu)$ 四个真实局部测试组合。对四项使用实值配对的实线性，即得

$$
\langle H\otimes K,\rho\rangle_{\mathbb R}
=\langle H\otimes K,\sigma\rangle_{\mathbb R}.
$$

这就是 `hermitian_product_pairing_eq` 的实际结论。四个测试随 $H,K$ 的表示确定；证明没有假设 $\rho$ 或 $\sigma$ 自身可以分解为产品态的概率混合。展开的是测试算符，未对输入态做任何可分离假设。

## 60.5 实部、虚部与全部联合矩阵元素的恢复

令 $e_{ij}$ 表示第 $(i,j)$ 项为一、其余项为零的矩阵单位。定义两个 Hermitian 矩阵

$$
S_{ij}=e_{ij}+e_{ji},\qquad
T_{ij}=\mathrm i(e_{ij}-e_{ji}).
$$

这里 $\mathrm i$ 为虚数单位。转置共轭分别给出 $S_{ij}^\dagger=S_{ij}$ 和 $T_{ij}^\dagger=T_{ij}$。对任意 Hermitian $X$，设 $X_{ij}=u+\mathrm i v$，则 $X_{ji}=u-\mathrm i v$，从矩阵单位的迹配对可得

$$
\begin{aligned}
\langle S_{ij},X\rangle_{\mathbb R}
&=2\operatorname{Re}X_{ij},\\
\langle T_{ij},X\rangle_{\mathbb R}
&=2\operatorname{Im}X_{ij}.
\end{aligned}
$$

第二式的符号是正号：$\operatorname{Tr}(T_{ij}X)=\mathrm i(X_{ji}-X_{ij})=2v$。若改用 $\mathrm i(e_{ji}-e_{ij})$，恢复式的符号就必须反转。声明 `pairing_imaginaryUnit` 固定了本章方向，避免把两种约定混用。

两个局部载体上的上述矩阵单位还满足

$$
S_{(i,a),(j,b)}
=\frac12\bigl(S_{ij}\otimes S_{ab}
-T_{ij}\otimes T_{ab}\bigr),
$$

$$
T_{(i,a),(j,b)}
=\frac12\bigl(T_{ij}\otimes S_{ab}
+S_{ij}\otimes T_{ab}\bigr).
$$

逐项展开即可验证：第一式中交叉的 $e_{ij}\otimes e_{ba}$ 与 $e_{ji}\otimes e_{ab}$ 抵消，留下联合矩阵单位及其转置；第二式留下它们之差的 $\mathrm i$ 倍。所有外部系数仍为实数。

这些恒等式不要求 $i\ne j$ 或 $a\ne b$。例如 $S_{ii}=2e_{ii}$、$T_{ii}=0$；两个指标都重复时第一式仍恰好等于两倍联合对角矩阵单位，第二式两边都为零。对 Hermitian $X$，对角元的虚部本来也为零。这些边界包含在实际通用声明中。

<a id="p-clt-01"></a>

**P-CLT-01（完整有限复模型的普遍局部层析）。** 对任意有限载体 $\iota,\nu$ 和任意 $\rho,\sigma\in\mathcal D(\iota\times\nu)$，若

$$
\forall E\in\mathcal E(\iota),\ 
\forall F\in\mathcal E(\nu),\qquad
p_\rho(E\otimes F)=p_\sigma(E\otimes F),
$$

则 $\rho=\sigma$。因此第57章已经构造的 `OperationalSystems.complexModel` 满足原接口中的完整 `LocalTomography` 原则。

**证明。** 第60.4节把产品效应的同概率扩张为所有局部 Hermitian 产品的同配对。给定任意联合行列 $(i,a),(j,b)$，用 $S$ 的产品恒等式与配对实线性，得到

$$
\langle S_{(i,a),(j,b)},\rho\rangle_{\mathbb R}
=\langle S_{(i,a),(j,b)},\sigma\rangle_{\mathbb R}.
$$

两态均 Hermitian，故矩阵单位恢复式推出相应联合矩阵元素的实部相等。再使用 $T$ 的产品恒等式，以同样方式得到虚部相等。于是每个复矩阵元素相等，两个实际 `Density` 相等。

原 `complexModel` 的联合状态类型就是这里的完整联合密度空间，局部效应与产品概率也正是本章所用定义。将上述定理代入原有 `LocalTomography` 的全称量词，便得到所声明的模型原则，未另建一个较小状态空间的替代呈现。∎

这条结果说明，在该完整复矩阵模型中，全部产品效应的联合统计足以识别整个联合态。它没有要求先掌握一个全局纠缠效应，也没有把“只知道各侧边际”加强成不成立的层析前提。为特定设备设计有限测试表、估计抽样误差、控制病态重建或证明测量库完备性，仍是另有输入的任务。

## 60.6 空载体、单元素载体与不同局部维数

有限类型可以为空。空载体上迹的求和为零，因此不存在迹一密度态；具体见证 `empty_carrier_has_no_density` 保留了这个事实。通用定理接受任意有限载体，关于密度输入的结论在空态域上按逻辑正确成立，不需要添加一个隐藏的 `Nonempty` 前提来制造状态。

在单元素载体上，唯一矩阵元素就是迹。任意密度态的迹一条件因此迫使这个元素为一，任意两个密度态相等。见证 `singleton_densities_equal` 从实际迹一证明，而不是用一个未声明的非平凡二维测试。

两个局部载体的维数可以不同。本章的指标从一开始分成 $\iota$ 与 $\nu$，产品载体为 $\iota\times\nu$，所有分配律和矩阵单位恒等式分别保持两组指标。`unequal_local_dimensions_tomography` 将通用结论实际实例化到 $\operatorname{Fin}2\times\operatorname{Fin}3$。这个见证检验类型边界；通用结论仍对任意两个有限维数成立。

这些见证与本章通用定理分开计数。空态排除继承既有结果，单元素计算与 $2\times3$ 实例分别承担边界核查，它们不是三条新的自然定律。[QM318]

## 60.7 对角效应负控与完整实模型的继承障碍

全效应分离的量词不能删成“某些常用效应”。为同时检查实、虚两类相干信息，取二维 Hermitian 对合

$$
X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
Y=\begin{pmatrix}0&-\mathrm i\\\mathrm i&0\end{pmatrix}.
$$

它们满足 $X^2=Y^2=I$、$\operatorname{Tr}X=\operatorname{Tr}Y=0$。本章 $T_{01}$ 的约定为 $-Y$，所以这里使用标准 $Y$ 不改变第60.5节已经固定的恢复符号。

<a id="n-sep-01"></a>

**N-SEP-01（全部对角效应仍不能识别相干态）。** 定义

$$
\rho_{x,\pm}=\frac12(I\pm X),\qquad
\rho_{y,\pm}=\frac12(I\pm Y).
$$

这四个矩阵都是实际密度态。对每一个合法对角效应 $E$，分别有

$$
p_{\rho_{x,+}}(E)=p_{\rho_{x,-}}(E),\qquad
p_{\rho_{y,+}}(E)=p_{\rho_{y,-}}(E).
$$

然而两对密度态各自不同；存在实际效应使每一对的概率分别为一与零，而且

$$
d_{\rm eff}(\rho_{x,+},\rho_{x,-})
=d_{\rm eff}(\rho_{y,+},\rho_{y,-})=1.
$$

**构造与证明。** 对任意 Hermitian 对合 $A$，$P_\pm=(I\pm A)/2$ 是互补正交投影：直接乘法给出 $P_\pm^2=P_\pm$、$P_+P_-=0$，Hermitian 性与 $P_\pm=P_\pm^\dagger P_\pm$ 给出正性。对 $A=X,Y$，迹零和二维单位矩阵的迹二进一步给出 $\operatorname{Tr}P_\pm=1$，故得到上述四个密度态。

每个态的两个对角元都为 $1/2$。任意对角效应写成 $E=\operatorname{diag}(e_0,e_1)$，其概率只由对角元决定：

$$
\operatorname{Re}\operatorname{Tr}(E\rho)
=\frac12(e_0+e_1).
$$

合法效应的 Hermitian 性保证 $e_0,e_1$ 为实数，正性和补正性给出 $0\le e_0,e_1\le1$。所以等概率结论量化的是全部合法对角效应，而不是挑选出的两个例子。

另一方面取 $E_x=(I+X)/2$、$E_y=(I+Y)/2$。上面的互补正投影性质同时证明它们是合法效应。由 $P_+^2=P_+$ 和 $P_+P_-=0$ 得到各自的概率为一与零，直接证明两对态不同。每个全效应距离至少是这个合法测试的概率差一，而第50章已经证明它至多为一，故距离恰等于一。∎

对角测量家族在其声明的范围内完全合法，但它的统计等价类可以包含不同的完整密度态。这个反例同时保留了实非对角项与虚非对角项的丢失，避免仅检查一种相干方向就宣称测量库完备。

第55章的完整实模型障碍仍然成立，范围也没有缩成对角库。其两个合法实联合态为

$$
\omega_\pm=\frac14(I\pm Y\otimes Y).
$$

$Y\otimes Y$ 虽由两个含虚部的局部矩阵组成，联合矩阵本身却是实的 Hermitian 对合。对任意局部实效应 $E,F$，实 Hermitian 性给出对称性，进而 $\operatorname{Tr}(EY)=\operatorname{Tr}(FY)=0$。因此

$$
p_{\omega_+}(E\otimes F)
=p_{\omega_-}(E\otimes F)
=\frac14\operatorname{Tr}E\operatorname{Tr}F.
$$

两个态仍由合法联合效应 $(I+Y\otimes Y)/2$ 以概率一与零区分；允许复局部效应 $(I+Y)/2$ 后，其两侧产品的概率也变为 $1/2$ 与零。这些是第55章已编号、已证明的结果，在本章只作继承交叉核对。`full_real_model_not_localTomography` 直接调用原 `OperationalSystems.real_not_localTomography`，未修改实模型字段，也不重新计为本章新增的编号反例。[QM316；QM317；QM318]

这解释了复局部层析证明中虚部测试的具体角色。第60.5节的局部 $T$ 类 Hermitian 测试可以在复模型内写成合法效应的实组合；实模型不允许据此悄然加入含虚矩阵元的局部效应。两个模型共享真实的组合和迹运算，允许测试的范围仍有实际差别。

## 60.8 公开号、实际证据与仍待建立的物理桥

本章四个编号结果与实际代码按以下关系对应。表内前两组声明位于 `UEOTQM.QuantumSeparation`，第三组位于 `UEOTQM.ComplexLocalTomography`，最后一组见证位于 `UEOTQM.QuantumSeparationExamples`；因此命名空间与局部公开号共同确定稳定名称。

| 编号结果或证明环节 | 公共声明与实际责任 |
|---|---|
| P-SEP-01：双侧正性与效应表示 | `boundedHermitianEffect`；`boundedHermitianEffect_matrix`；`boundedHermitianEffect_affine`；`exists_effect_affine_of_hermitian` |
| P-SEP-01：实数域张成 | `hermitian_mem_real_span_effects` |
| P-SEP-02：实扩张和密度分离 | `pairing_eq_of_all_effect_pairings_eq`；`pairing_sub_right`；`density_eq_of_all_effect_probabilities_eq`；`density_eq_iff_all_effect_probabilities_eq` |
| P-SEP-02：距离零的实际含义 | `effectDistance_eq_zero_iff_density_eq` |
| P-CLT-01：局部矩阵单位 | `symmetricUnit`；`imaginaryUnit`；两者的 `_hermitian` 定理；`pairing_symmetricUnit`；`pairing_imaginaryUnit` |
| P-CLT-01：实产品展开 | `sub_kronecker`；`kronecker_sub`；`symmetricUnit_product`；`imaginaryUnit_product`；`hermitian_product_pairing_eq` |
| P-CLT-01：任意联合态与原模型 | `density_eq_of_all_product_effect_probabilities_eq`；`complex_localTomography` |
| N-SEP-01：全部对角效应同统计 | `diagonal_effect_pairing_eq`；`all_diagonal_effects_agree_x`；`all_diagonal_effects_agree_y` |
| N-SEP-01：实际区分和距离 | `xTest_probability_plus`、`xTest_probability_minus`；对应的 `yTest` 概率定理；`xPlus_ne_xMinus`、`yPlus_ne_yMinus`；`x_effectDistance_exact`、`y_effectDistance_exact` |
| 维度边界与继承原则交叉核对 | `empty_carrier_has_no_density`；`singleton_densities_equal`；`unequal_local_dimensions_tomography`；`full_complex_model_localTomography`；`full_real_model_not_localTomography` |

两份新增公共模块含20条显式 theorem 与3项定义；具体见证单列19条 theorem、8项定义和1项缩写。阶段性的实际聚焦回执分别完整核对23个公共声明与28个见证声明的逐名公理输出，并绑定成功编译的源码字节。允许基础只有 `propext`、`Classical.choice`、`Quot.sound`。实际编译保留普通 linter 警告。相应记录位于 `physics/qm/kernel/evidence/v31.8/A`；本轮统一验收、公开源码和远端发布状态由 v31.8 的统一回执另行承担。聚焦通过、统一验收与真实远端身份是不同的证据事实，定义、见证和编号结果也不是同一种计数。[QM318]

科学上，本章补足了已给复量子模型内部的可识别性：完整效应区分完整密度态，局部产品的完整联合统计区分完整联合态。对原有预测对象语言，这使“全效应响应相同”能够在明确的复矩阵实现中识别同一个密度对象；对受限仪器库，只能按其实际可用响应讨论相应商，N-SEP-01 保留了严格更粗的可能性。

本章的有限复向量空间、完整正半定态锥、完整效应锥、张量复合和迹概率属于已经声明的数学与量子扇区输入。其结果主要属于标准量子结构 P 及实际操作连接 B，具体概率承担 O；若要求自然界必须满足局部层析，则还须把这项选择原则及其背景按 S 登记并论证。冻结 Core 的106项与四生成器没有因此增加“必须为复数”的公理。本章也未证明这些候选原则唯一排除所有其他操作模型，未建立无限维或连续极限，未产生新的实验数据。

后续的物理桥应说明哪些 UEOT 机制选择这些状态、效应与复合规则，哪些真实设备实现所需测试，以及候选理论之间有哪些可区别的经验预测。本章为这项工作提供了完整且可检验的有限实现；它不把有限实现的完备性改称自然理论的最终完成。
