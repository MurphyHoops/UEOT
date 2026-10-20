<a id="ch-61"></a>

# 61. 完整纯性与有限纯化的酉等价

第57章已经从任意有限复密度态的正性导出 Gram 因子，并用实际偏迹证明纯化存在。然而，只证明某些向量态是纯态，还不能比较所有按完整凸极点定义给出的纯化；只构造一个 Gram 纯化，也没有说明同一边际的其他纯化与它有什么关系。本章补上这两个责任，并分别处理相同辅助载体与不同辅助载体。

结论建立在已经明确的有限复密度模型中：完整凸极点恰为归一向量的外积；相同辅助载体上的任意两个纯化由实际辅助酉变换连接；不同载体可先经实际等距通道嵌入共同直和，再在这个共同载体上比较。最后两种说法的矩阵类型不同，不能合并成一个没有维数条件的“矩形酉矩阵”断言。[QM318]

## 61.1 完整状态量词与归一约定

继续使用

$$
\mathcal D(\iota)=\{\rho\in M_\iota(\mathbb C):\rho\succeq0,\ \operatorname{Tr}\rho=1\}.
$$

其中 $\iota$ 是任意有限载体。`Density` 的两个条件是实际矩阵的正半定性和复迹一。`IsPure` 沿用第57章对全部密度态、全部 $0<t<1$ 的凸极点定义，没有缩小允许态集，也没有改为把向量表示作为定义字段。

对向量 $v:\iota\to\mathbb C$，记

$$
P_v=|v\rangle\langle v|,
\qquad (P_v)_{ij}=v_i\overline{v_j}.
$$

本章 Lean 声明中的归一条件写成 $\operatorname{Tr}P_v=1$。实际展开为 $\sum_i|v_i|^2=1$，即有限复欧几里得空间中的单位向量条件。这里的向量范数是二范数；不能把函数类型上某个不同的默认范数暗中代入。

对正矩阵 $X$，质量仍记作

$$
m(X)=\operatorname{Re}\operatorname{Tr}X\ge0.
$$

继承的正矩阵零质量定理给出 $m(X)=0\iff X=0$。只有在 $m(X)>0$ 时，才使用合法归一密度态 $\widehat X=X/m(X)$。这一条件在下面的凸分解中实际检查，零余项不被赋予一个虚构的归一态。[QM317；QM318]

## 61.2 极点的每个正质量正分量都指向同一态

先证明一个直接反映完整极点量词的中间结论。设 $\rho$ 为纯密度态，且

$$
\rho=X+Y,\qquad X,Y\succeq0,\qquad m(X)>0.
$$

则 $\widehat X=\rho$。由迹一，$m(X)+m(Y)=1$。证明分为两个实际可区分的情形。

如果 $m(Y)=0$，正性迫使 $Y=0$，因此 $m(X)=1$、$X=\rho$，归一不改变 $X$。如果 $m(Y)>0$，则 $0<m(X)<1$，而

$$
\rho=m(X)\widehat X+m(Y)\widehat Y
=m(X)\widehat X+(1-m(X))\widehat Y.
$$

两份归一态都属于完整 $\mathcal D(\iota)$，所以可直接把它们代入原有 `IsPure` 定义，得到 $\widehat X=\rho$ 和 $\widehat Y=\rho$。这里没有额外假定 $X$、$Y$ 的秩、支撑或对角形式。Lean 定理 `IsPure.normalize_eq_of_positive_summand` 逐项完成正性、严格正质量、归一重组和零余项分支。[QM318]

这个结论的作用是把极点性转成一个可以用于 Gram 列分解的约束。它不是把所需秩一结论放进假设；分量是否来自向量，还要在下一步由真实的正矩阵分解得到。

## 61.3 从任意凸极点导出归一向量

<a id="p-puc-01"></a>

**P-PUC-01（完整有限复密度空间的纯性刻画）。** 对任意 $\rho\in\mathcal D(\iota)$，

$$
\operatorname{Pure}(\rho)
\iff
\exists v:\iota\to\mathbb C,\quad
\operatorname{Tr}P_v=1\ \land\ \rho=P_v.
$$

**证明。** 反向，即归一向量态为完整凸极点，已经由 P-PUR-01 证明。现在设 $\rho$ 是按原定义给出的任意极点。从正性取得实际矩阵 $A$，使 $\rho=AA^\dagger$。对每一列 $a$，记 $u_a(i)=A_{ia}$，则逐项相乘给出

$$
\rho=AA^\dagger=\sum_a |u_a\rangle\langle u_a|
=\sum_a P_a,\qquad P_a\succeq0.
$$

取迹得到 $\sum_a m(P_a)=1$，所以至少有一列满足 $m(P_a)>0$。若所有列质量都不为正，其有限和至多为零，与迹一矛盾。对选中的一列，定义实际余项

$$
R=\sum_{b\ne a}P_b\succeq0.
$$

有限求和的删除重组给出 $\rho=P_a+R$。上一节的两分支结论于是推出 $\rho=P_a/m(P_a)$。令

$$
v=\frac{u_a}{\sqrt{m(P_a)}}.
$$

因为 $m(P_a)>0$，实平方根的平方等于 $m(P_a)$，且其实数倍在外积两侧各贡献一次系数。因此

$$
P_v=\frac1{m(P_a)}P_a=\rho,
\qquad\operatorname{Tr}P_v=1.
$$

这就从任意完整凸极点导出了归一向量，而非把向量作为调用者提供的见证。∎

Lean 中 `gram_eq_sum_outer` 证明真实 Gram 矩阵的列外积和，`outer_real_smul` 证明实数缩放的平方律，`IsPure.exists_vector` 完成上述构造，`isPure_iff_exists_vector` 再接回既有正向定理。选择正质量列和 Gram 因子的存在过程使用已允许的经典基础，但不引入新的秩一公理或物理谱假设。

空载体也没有被隐藏地排除。若存在迹一密度态，上述总质量为一的论证本身就能推出一个正质量列；空载体上这不可能发生，因此该情形根本没有合法 $\rho$ 可作为输入。定理无需额外添加一个用来掩盖此边界的非空字段。[QM318]

## 61.4 相同 Gram 数据怎样产生真正的酉变换

下一步先处理一个纯线性代数问题。设 $F,G:\mathbb C^{\iota}\to\mathbb C^{\alpha}$ 是任意有限复矩阵，满足

$$
F^\dagger F=G^\dagger G.
$$

对任意输入 $x$，欧几里得平方范数由实际 Gram 二次型给出，因而

$$
\|Fx\|_2^2=x^\dagger F^\dagger Fx
=x^\dagger G^\dagger Gx=\|Gx\|_2^2.
$$

所以 $Fx=0$ 蕴含 $Gx=0$。这使

$$
L:\operatorname{ran}F\longrightarrow\mathbb C^\alpha,
\qquad L(Fx)=Gx
$$

成为良定义的复线性映射：同一个 $Fx$ 的两个表示之差在 $\ker F$ 内，也就在 $\ker G$ 内。范数等式进一步说明 $L$ 是其实际生成支撑上的线性等距映射。

Lean 构造并未把 $L$ 的良定义当作注释跳过。它先经 $\ker F$ 商空间定义诱导映射，再使用商核到像的线性等价，把诱导映射转回 $\operatorname{ran}F$；随后证明每个像向量的范数被保持。`LinearIsometry.extend` 将这个子空间等距映射扩展为整个相同有限辅助空间上的线性等距映射。有限维自映射的单射性给出满射性，于是得到线性等距等价。

用标准正交基取其实际矩阵 $U$，得到

$$
U^\dagger U=I_\alpha,\qquad UU^\dagger=I_\alpha,
\qquad UF=G.
$$

两条酉恒等式都进入最终结论。这里不假定 $F$、$G$ 满秩，也不要求它们占满辅助空间；未被生成支撑占据的方向由有限维等距扩张处理。`exists_unitary_of_column_gram` 的输入只有实际 Gram 等式，输入中没有所求酉矩阵、可扩张性字段或酉等价结论。[QM318]

这是一项数学存在构造。它使用所固定 Mathlib 中已证明的商空间和有限等距扩张定理，并由精确命名公理审计检查其基础；本章没有另外声称得到一个已经认证、带数值稳定性界的矩阵分解算法。

## 61.5 行 Gram、转置和辅助作用的方向

纯化向量沿用固定的向量化约定

$$
\psi(i,a)=A_{ia},\qquad\phi(i,a)=B_{ia}.
$$

实际系统边际分别为 $AA^\dagger$ 和 $BB^\dagger$。如果两边际相同，得到的是**行 Gram** 等式

$$
AA^\dagger=BB^\dagger.
$$

本轮实际源码把这条等式转置，取 $F=A^\mathsf T$、$G=B^\mathsf T$。因为

$$
(A^\mathsf T)^\dagger A^\mathsf T
=\overline A A^\mathsf T=(AA^\dagger)^\mathsf T,
$$

上一节直接给出一个辅助酉矩阵，满足 $UA^\mathsf T=B^\mathsf T$。逐项读出便是

$$
B_{ia}=\sum_bU_{ab}A_{ib},
\qquad
\phi(i,a)=\sum_bU_{ab}\psi(i,b).
$$

因此真正作用在第二个向量指标上的矩阵就是 $U$，而矩阵因子的右乘写法为 $B=AU^\mathsf T$。相应联合向量关系是

$$
\phi=(I_\iota\otimes U)\psi.
$$

`exists_auxiliary_unitary_of_gram` 从转置后的真实 Gram 等式导出所需 $U$；`auxiliary_action_apply` 直接计算张量矩阵作用的每个条目；`auxiliary_action_vectorize` 明确证明右乘因子中的转置。这样，$U$、$U^\dagger$、$U^\mathsf T$ 与 $\overline U$ 不会在不同表示间被悄悄互换。

如果另从 $F=A^\dagger$ 开始，也可以走一条等价的数学路线，但从支撑等距矩阵转回向量辅助作用时必须再跟踪共轭。本章实际实现采用上面的转置路线；准备阶段讨论过的其他路线不作为这份源码已经执行的证明记录。[QM318]

## 61.6 同辅助载体上的任意纯化

<a id="p-pun-01"></a>

**P-PUN-01（同辅助载体的完整纯化酉等价）。** 设 $\Psi,\Phi\in\mathcal D(\iota\times\alpha)$ 都是完整联合密度空间中的纯态，且实际偏迹满足

$$
\operatorname{Tr}_\alpha\Psi=\operatorname{Tr}_\alpha\Phi.
$$

则存在实际矩阵 $U\in M_\alpha(\mathbb C)$，使

$$
U^\dagger U=UU^\dagger=I_\alpha,
\qquad
\Phi=(I_\iota\otimes U)\Psi(I_\iota\otimes U)^\dagger.
$$

**证明。** 先对 $\Psi$、$\Phi$ 分别使用 P-PUC-01，取得归一向量 $\psi$、$\phi$，使两联合密度为其真实外积。把原偏迹等式代入这些外积，得到对应矩阵因子的行 Gram 等式。上一节产生 $U$，使 $\phi=(I\otimes U)\psi$。最后用实际外积恒等式

$$
|K\psi\rangle\langle K\psi|
=K|\psi\rangle\langle\psi|K^\dagger
$$

得到联合密度的酉共轭关系。∎

这里的向量中间定理 `exists_auxiliary_unitary_of_equal_marginal` 甚至不需要归一假设：任意两个同载体联合向量，只要实际外积偏迹相同，就具有上述精确向量作用关系。最终 `pure_states_unitarily_equivalent` 则通过 P-PUC-01 处理所有按完整凸极点定义给出的纯密度，因而没有把“任意纯化”退化成“调用者已提供向量表示的纯化”。[QM318]

“唯一性”在这里是辅助酉作用下的等价性。它没有说 $\Psi=\Phi$，也没有说连接二者的 $U$ 是唯一矩阵。未使用的辅助方向仍可容纳不同酉扩张；向量代表的整体相位也可吸收到辅助酉中。第57章的纯化存在与本节的等价结论合起来，才描述了同一有限复模型中“有纯化，且所有同辅助载体纯化彼此可比较”的完整逻辑链。

## 61.7 不同载体先使用真正的矩形等距通道

<a id="p-aux-01"></a>

**P-AUX-01（辅助等距嵌入的实际通道、边际和纯性）。** 设 $J:\mathbb C^\alpha\to\mathbb C^\beta$ 是实际矩形矩阵，满足 $J^\dagger J=I_\alpha$。则

$$
\mathcal E_J(X)=(I_\iota\otimes J)X(I_\iota\otimes J)^\dagger
$$

是从 $\iota\times\alpha$ 到 $\iota\times\beta$ 的实际单 Kraus CPTP 通道，并且对**任意复输入矩阵** $X$，

$$
\operatorname{Tr}_\beta\mathcal E_J(X)
=\operatorname{Tr}_\alpha X.
$$

如果输入是完整联合状态空间中的纯密度态，输出也是完整放大后状态空间中的纯密度态。

**证明。** 令 $K=I_\iota\otimes J$。张量乘法与共轭转置给出

$$
K^\dagger K=I_\iota\otimes(J^\dagger J)
=I_{\iota\times\alpha},
$$

所以这个实际 Kraus 矩阵满足矩形通道完备性。第58章的矩形通道理论因此适用，包括任意有限辅助放大上的完全正性。

固定系统指标 $i,j$，令 $X^{ij}_{cd}=X_{(i,c),(j,d)}$，这是辅助载体上的实际复矩阵。直接计算输出相应块，得到

$$
(\mathcal E_JX)^{ij}=JX^{ij}J^\dagger.
$$

实际偏迹取这个块的迹，利用迹循环，有

$$
\operatorname{Tr}(JX^{ij}J^\dagger)
=\operatorname{Tr}(J^\dagger JX^{ij})
=\operatorname{Tr}X^{ij}.
$$

逐个 $i,j$ 即得边际恒等式。这个计算没有对 $X$ 施加正性、迹一、纯态或产品形式限制。

最后，若 $\Psi$ 为完整凸纯态，P-PUC-01 给 $\Psi=P_\psi$。通道输出等于 $P_{K\psi}$，归一由实际通道的迹保持得到，再由 P-PUR-01 或 P-PUC-01 的反向得知输出对全部放大后密度态仍为极点。∎

`auxiliaryEmbeddingChannel` 真正构造了这个带输入、输出类型的通道；`auxiliaryEmbeddingChannel_operator_apply` 给出块公式；`auxiliaryEmbeddingChannel_discard_operator` 量化全部复矩阵；`auxiliaryEmbeddingChannel_discard_state` 与 `auxiliaryEmbeddingChannel_preserves_purity` 分别把它接回实际密度和完整纯性。其前提只要求 $J^\dagger J=I_\alpha$。当输出空间更大时，$JJ^\dagger=I_\beta$ 一般不成立，不能把它加进结论。[QM318]

## 61.8 不同辅助维数经共同直和后比较

令共同辅助载体为不交和 $\alpha\sqcup\beta$；其复向量空间是两辅助空间的直和。定义实际矩形矩阵

$$
J_\alpha=\begin{bmatrix}I_\alpha\\0\end{bmatrix},
\qquad
J_\beta=\begin{bmatrix}0\\I_\beta\end{bmatrix}.
$$

两者分别满足 $J_\alpha^\dagger J_\alpha=I_\alpha$ 和 $J_\beta^\dagger J_\beta=I_\beta$。注意两个等式右侧属于不同源载体。由它们分别构造

$$
\widetilde\Psi=\mathcal E_{J_\alpha}(\Psi),
\qquad
\widetilde\Phi=\mathcal E_{J_\beta}(\Phi).
$$

<a id="p-pun-02"></a>

**P-PUN-02（不同有限辅助载体的共同扩展酉等价）。** 若 $\Psi\in\mathcal D(\iota\times\alpha)$、$\Phi\in\mathcal D(\iota\times\beta)$ 都在各自完整联合密度空间中为纯态，且实际系统边际相同，则存在 $U\in M_{\alpha\sqcup\beta}(\mathbb C)$，满足两条酉恒等式，并有

$$
\widetilde\Phi
=(I_\iota\otimes U)\widetilde\Psi(I_\iota\otimes U)^\dagger.
$$

**证明。** 两个规范嵌入的等距恒等式由分块矩阵乘法直接得到。P-AUX-01 保证 $\widetilde\Psi$、$\widetilde\Phi$ 是同一完整共同状态空间中的纯密度，并保持各自的原系统边际。原边际相同，因此可在共同辅助载体 $\alpha\sqcup\beta$ 上应用 P-PUN-01。∎

形式定义 `auxiliaryInl`、`auxiliaryInr` 给出真实矩形嵌入；`extendAuxiliaryLeft`、`extendAuxiliaryRight` 给出真实通道输出。四个纯性与边际定理先独立证明必要前提，`pure_states_common_extension_unitary` 才调用同载体酉等价定理。

本结论无需比较 $|\alpha|$ 与 $|\beta|$，也不把它们当作同一类型。代价是共同载体维数采用 $|\alpha|+|\beta|$，没有声称它最小。它没有直接给出一个从任意指定一侧到另一侧的满空间等距映射，更没有给出维数不同时两侧都满足逆关系的“酉矩阵”。若要登记最小辅助维数、在额外维数不等式下的直接等距延拓，或某个量子重建体系要求的特定补齐形式，仍须另写相应类型和证明。[QM318]

## 61.9 相同边际而联合态不同的精确正控

本轮选取的辅助矩阵含有实、虚混合条目，以便检查共轭与转置的方向：

$$
U=\begin{bmatrix}3/5&4i/5\\4/5&-3i/5\end{bmatrix}.
$$

它的两列分别为 $(3,4)^\mathsf T/5$ 与 $i(4,-3)^\mathsf T/5$，每列平方范数为一，列间内积为零。实际见证同时验证 $U^\dagger U=I$ 和 $UU^\dagger=I$。

取

$$
\psi_1=\tfrac35|00\rangle+\tfrac45|11\rangle,
$$

并按已经固定的第二指标作用计算

$$
\begin{aligned}
\psi_2=(I\otimes U)\psi_1
={}&\tfrac9{25}|00\rangle+\tfrac{12}{25}|01\rangle\\
&+\tfrac{16i}{25}|10\rangle-\tfrac{12i}{25}|11\rangle.
\end{aligned}
$$

对应向量化矩阵是

$$
A=\begin{bmatrix}3/5&0\\0&4/5\end{bmatrix},
\qquad
B=\begin{bmatrix}9/25&12/25\\16i/25&-12i/25\end{bmatrix}.
$$

精确相乘给出

$$
AA^\dagger=BB^\dagger
=\begin{bmatrix}9/25&0\\0&16/25\end{bmatrix}=\rho.
$$

例如 $BB^\dagger$ 的非对角条目为 $-144i/625+144i/625=0$。两向量的总平方范数都为一，所以对应两联合密度均为完整凸纯态，其实际偏迹都为 $\rho$。

两联合向量和两联合密度确实不同：其 $|00\rangle\langle00|$ 条目分别是 $9/25$ 与 $81/625$。这正好说明边际相同不意味着联合密度相等；正确结论是存在辅助酉变换连接二者。`exact_auxiliary_vector_action` 检查的是精确向量等式，`same_actual_marginal` 检查的是原有实际丢弃通道，`general_uniqueness_instantiated` 还实际调用一般完整纯态唯一性定理，避免只验证专门算出来的小矩阵。[QM318]

## 61.10 三种错误作用方向的联合密度负控

<a id="n-pun-01"></a>

**N-PUN-01（伴随、转置和逐项共轭不能替代实际辅助作用）。** 对上一节固定的 $U$ 与 $\psi_1$，若把正确辅助矩阵分别错换为 $U^\dagger$、$U^\mathsf T$ 或 $\overline U$，得到的联合密度都不等于 $P_{\psi_2}$。

**证明。** 定义 $\chi_T=(I\otimes T)\psi_1$。以下三个实际复矩阵条目已经分别精确计算：

| 所用辅助矩阵 $T$ | 所比较的联合密度条目 | $P_{\chi_T}$ 的值 | 正确 $P_{\psi_2}$ 的值 |
|---|---|---|---|
| $U^\dagger$ | $((0,0),(0,1))$ | $108i/625$ | $108/625$ |
| $U^\mathsf T$ | $((0,0),(0,1))$ | $-108i/625$ | $108/625$ |
| $\overline U$ | $((0,0),(1,0))$ | $144i/625$ | $-144i/625$ |

每行的虚部均不同，因此各自的实际联合密度不相等。∎

`wrong_adjoint_joint_density`、`wrong_transpose_joint_density` 和 `wrong_conjugate_joint_density` 是三条分别接受公理审计的负控定理，其条目值各有对应的精确计算定理。它们比较联合密度，因此即使某个错误向量只差整体相位，也不会被一个仅看向量表达式的表面差异误报为物理区分；本例的实际密度不等排除了这种遮蔽。

仅检查系统边际不足以发现这些方向错误。由 $U$ 的酉恒等式及转置、共轭关系可知，这三种替代矩阵也都是辅助酉矩阵，因此其辅助作用仍保持系统边际。负控所要检验的是“是否得到指定的同一个联合纯化”，所以证据必须落在精确联合向量或联合密度上。它不声称边际测试可以识别被丢弃辅助系统上的酉选择。[QM318]

## 61.11 二维到三维的实际嵌入与非酉负控

取 $\alpha=\mathrm{Fin}\,2$、$\beta=\mathrm{Unit}$，则共同载体 $\alpha\sqcup\beta$ 有三维。左规范嵌入的实际矩阵是

$$
J=\begin{bmatrix}1&0\\0&1\\0&0\end{bmatrix}.
$$

<a id="n-aux-01"></a>

**N-AUX-01（严格辅助扩维是等距嵌入，不是双侧酉等价）。** 上述实际 $3\times2$ 矩阵满足 $J^\dagger J=I_2$，但 $JJ^\dagger\ne I_3$。

**证明。** 前一等式由列正交直接得到。后一乘积是 $\operatorname{diag}(1,1,0)$；第三个对角条目为零，而 $I_3$ 的相应条目为一。∎

见证 `strict_embedding_isometry` 与 `strict_embedding_not_coisometry` 分别证明两项，`auxiliary_dimensions_differ` 证明这两个辅助载体的基数确实不同。把第61.9节的第二联合纯态沿此 $J$ 嵌入，得到 `largerState`：它在六维联合空间、三维辅助载体上仍是完整凸纯态，并保持原系统边际。它与原二维辅助载体上的 `firstState` 因而构成一对真正不同辅助维数的纯化。

`different_auxiliary_common_unitary` 对这一对实际密度调用 P-PUN-02。其共同辅助载体为 $\mathrm{Fin}\,2\sqcup(\mathrm{Fin}\,2\sqcup\mathrm{Unit})$，维数是五；一般定理给出这个共同载体上满足两条酉恒等式的矩阵。这里的五维矩阵通过已经证明的存在构造得到，见证没有额外列出一张经过数值求解的五维酉矩阵，也没有将两个原始辅助维数混写为相同维数。[QM318]

## 61.12 源码、逐声明审计与证据范围

本章新增公共源码为 `UEOTQM/PureStateCharacterization.lean` 与 `UEOTQM/PurificationUniqueness.lean`，具体见证为 `scripts/witnesses/PurificationUniquenessExamples.lean`。它们分别包含：

| 源文件 | 显式 theorem | 定义 def | 缩写 abbrev | 精确命名公理审计 |
|---|---:|---:|---:|---:|
| `PureStateCharacterization.lean` | 5 | 0 | 0 | 5 |
| `PurificationUniqueness.lean` | 22 | 5 | 0 | 27 |
| `PurificationUniquenessExamples.lean` | 28 | 10 | 0 | 38 |

两个公共模块合计27条显式定理、5个定义；见证另有28条定理、10个定义。公共与见证共70个不同稳定命名声明，在本路实际聚焦审计中全部只依赖 `propext`、`Classical.choice`、`Quot.sound`。见证的每个 theorem、def、abbrev 按源码顺序打印公理依赖，没有只抽查最后一个总定理。

实际接受日志、最终源码摘要、源码与 olean 绑定及逐名库存分别登记在 `physics/qm/kernel/evidence/v31.8/B/focused-verification.json` 和 `declaration_inventory.json`。聚焦模块验证对应 `pure-005`、`uniqueness-005`，最终具体见证对应 `witness-003`，公共精确审计对应 `public-audit-001`。这些都是实际退出零的调用；早先有意义的失败及其可取得源码快照被另行保留，不计入接受结果。

这份本路回执的层级是聚焦证明验收。版本统一构建、全量公理审计、继承见证及远端 CI 的完成与身份由主版本回执另行登记，不能用本地结果替代尚未实际回读的远端运行。普通 linter 提示与逻辑验收状态也应分开记录，不能把允许的普通警告改写为“零警告”。这里没有新增真实实验；有理复矩阵正负控是形式化见证，不是自然界的实验确证。[QM318]

## 61.13 已闭合的数学责任与仍开放的理论选择

第57章的存在构造、本章的完整纯性反向、同辅助载体酉等价与不同载体共同扩展，现已在同一个有限复密度模型中接通。纯态定义、Gram 因子、联合向量、实际偏迹和实际矩形通道各有清晰接口，结论不再依赖“所有纯态已经被假定为向量态”或“所求辅助酉由调用者给出”这类未完成责任。

与此同时，辅助酉矩阵本身的唯一性、共同扩展的最小维数、额外维数条件下的直接等距延拓及认证数值构造仍与已完成结论不同。无限维系统中的闭像、非有限秩与可扩张性问题也不能直接沿用本章的有限维满射论证。若某个量子重建原则对辅助补齐、允许的可逆过程或系统同构有更具体要求，必须把那个原则逐字段对接到当前已证明的类型，不能仅凭“本质唯一性”这一名称视为已经满足全部文献合同。

这些结果主要属于在标准有限复量子结构 P 与真实操作连接 B 下的数学结论。它们加强了这个候选模型的内部完备性和可检验接口，但从冻结的106项 Core 与四生成器唯一选择复量子结构的桥仍未建立。完整经典模型的纯化障碍与实模型的局部层析反例继续约束候选原则的选择责任；排除这两个已检查模型，不等于排除所有可能自然理论。

三代结论继续依赖原有谱、表示、阈值与有效窗口等前提；本章既不修改那些前提，也不产生新的经验数据。UEOT 的目标仍是把理论思想、实际推导、反例与经验责任连成可审查的整体。本章完成的是其中一段有限量子数学责任，下一步的自然理论主张仍须提出独立前提、实际证明及可检验的物理对应。[QM318]
