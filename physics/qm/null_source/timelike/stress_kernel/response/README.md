# 共同几何中的平均源等价、推迟响应与局域 lapse 灵敏度

基线：29d49e3eee6299e2085492b0e061288b8166b5fa。本节接续同一自由最小无质量实场、完整光滑准备和固定重整化方案。旧目录保持冻结，Core 只读，GI 不在范围。

本轮已闭合的关系：

1. 新旧完整制备在任意共同的合法光滑几何上具有相同的平均 RSET 泛函；其存在的几何变分、平均半经典解集及同一确定性线性响应算子相同。
2. 完整有序应力连接核的差是一个显式的实对称秩一项。噪声改变，推迟交换子核保持相同。
3. 同轮对原局部四维测试的完整噪声上界，直接给出一个实际紧支撑度规扰动对后续 Weyl 仪器记录的严格一阶概率灵敏度界。

第1项不证明平均半经典解集非空；第3项是参数零点的导数界，不是有限扰动的概率误差或自洽引力演化。

[共同前提](../../response/CONTRACT.md) · [同轮完整噪声证书](../noise/README.md) · [检查器](check.py) · [回执](result.json)

## 1. 固定共同过去，才有同一个几何响应问题

取共同流形上的一类光滑、全局双曲度规 \(g\)，均在一个含 Cauchy 面的过去邻域内等于同一准备度规。原零均值 quasifree Hadamard 参考态的完整 Cauchy 二点数据固定，包括正规零模的完整位置—动量协方差。经典位移解的 Cauchy 数据也固定。

对每个这样的 \(g\)：

- \(W_g\) 是该共同初值经自己的 Klein–Gordon 算子传播后的完整参考核；
- \(f_g\) 是同一初值经自己的经典方程传播后的位移解；
- 源强在当前固定 \(\lambda\) 的几何变分中不重新调整；
- 重整化方案、有限局域耦合和物理标度约定保持相同。

整体改变 \(\lambda\) 时仍按精确相关族重调源；这与固定 \(\lambda\) 后研究一个局部参数 \(\varepsilon\) 的几何变分是不同操作。局部扰动支撑在物理初片之后，所以共同过去和初片数据均保持原值。

不要求这些共同几何彼此同形，也不把旧完整核直接移植到新几何。传播算子本身随 \(g\) 改变。

## 2. 全几何平均源等价定理

对固定候选标签 \(s=\pm1\)，旧分布为
\[
Y=s/2\pm\sqrt3/2\quad\text{等概率},
\]
新分布为
\[
P(Y=+1)=(2+s)/4,\qquad P(Y=-1)=(2-s)/4.
\]
二者均有 \(\mathbb EY=s/2,\ \mathbb EY^2=1\)。

令 \(\omega^g_P\) 表示在 \(W_g\) 上施加随机相干位移 \(Yf_g\) 的完整正混合。其一、二点函数准确为
\[
\omega_P^g(\Phi(x))=\mathbb EY\,f_g(x),
\]
\[
\omega_P^g(\Phi(x)\Phi(y))
=W_g(x,y)+\mathbb EY^2 f_g(x)f_g(y).
\]
故对每个共同 admissible \(g\)，
\[
W_{\mathrm{old,full}}^g=W_{\mathrm{new,full}}^g
=W_g+f_g\otimes f_g.
\tag{1}
\]

### 证明不依赖未经认证的几何微分

设共同 Cauchy 数据的完整二点矩阵为 \(M_{\rm in}\)。自由场的线性传播给
\[
M_g=U_g M_{\rm in}U_g^T.
\]
新旧初始矩阵相同；用同一个 \(U_g\) 传播就保持相同。式 (1) 是逐个度规成立的准确恒等式，不需要先假定 \(g\mapsto U_g\) 或 RSET 映射具有某种全局 Banach 可微性。

固定局域协变重整化方案后，平均应力由完整二点函数的同一个局域微分与减除过程给出。因此
\[
\boxed{\ \langle T_{ab}\rangle^g_{\rm old}
=\langle T_{ab}\rangle^g_{\rm new}\ }\quad
\text{对共同几何类中的每一个 }g.
\tag{2}
\]
每个新符号分支 \(+f_g\)、\(-f_g\) 本身也具有式 (1) 的二点函数，因此亦满足式 (2)。各分支的一阶场均值不同，不能将 \(T[\langle\Phi\rangle]\) 当作 \(\langle T[\Phi]\rangle\)。

### 对平均引力的准确后果

在相同几何类、几何初边值、引力耦合和重整化方案中，定义
\[
\mathcal S_P=
\{g:\mathcal E[g]=\langle T\rangle_P^g\},
\]
其中 \(\mathcal E\) 是所声明的完整平均引力方程左侧。式 (2) 直接给
\[
\boxed{\mathcal S_{\rm old}=\mathcal S_{\rm new}.}
\tag{3}
\]
这不声称该集合非空，也不将前轮受迫线性候选宣布为其中一个元素。

沿任意共同度规族，凡是两边相应的变分存在，它们均相等。于是同一平均解上的确定性线性响应算子及其固定规范/边界条件下的齐次稳定性问题相同。等价本身不证明导数存在、有界、可逆或解稳定。

该定理使用自由线性场及二次应力结构；相互作用、依结果选取几何、改变准备反馈规则或不同有限重整化方案均需新论证。

## 3. 同一个连接应力核，分清对称和反对称部分

对任意两个合法实四维紧支撑张量测试 \(H,K\)，记
\[
T(H;Y)=A_H+YB_H+Y^2D_H,
\qquad D_H=T[f_g](H).
\]
\(A_H\) 是参考量子应力，\(B_H\) 是参考场的线性量，\(D_H\) 为实 c 数。零均值 Gaussian 参考态的奇矩为零。以完整混合均值中心化后，有序连接核为
\[
\mathcal C_P(H,K)
=\mathcal C_0(H,K)+\mathcal C_1(H,K)
+\operatorname{Var}_P(Y^2)D_HD_K.
\tag{4}
\]
这里保留有序量子乘积及其虚部，不把混合态当作 Gaussian，也不假定两个应力算子对易。

因为旧 \(\operatorname{Var}(Y^2)=3/4\)，新值为0，
\[
\boxed{\mathcal C_{\rm old}(H,K)-\mathcal C_{\rm new}(H,K)
=\frac34 D_HD_K.}
\tag{5}
\]
这个差纯实、对称，且对任意有限实系数 \(\alpha_i\)
\[
\sum_{ij}\alpha_i\alpha_j\Delta\mathcal C(H_i,H_j)
=\frac34\left(\sum_i\alpha_iD_{H_i}\right)^2\ge0.
\]
因此对称噪声核降低一个正半定秩一项，而
\[
\boxed{\langle[T(H),T(K)]\rangle_{\rm old}
=\langle[T(H),T(K)]\rangle_{\rm new}.}
\tag{6}
\]
旧幅度平方的随机项只贡献 c 数随机源，不能产生量子交换子。

对任何已经合法构造、两态共用的线性响应 \(R\)，以及其定义域内的有限读出，诱导协方差差随之为
\[
\Delta\operatorname{Cov}_{\rm induced}
=\frac34(RT[f_g])\otimes(RT[f_g]).
\tag{7}
\]
式 (7) 是条件推论；它没有自行构造完整 Einstein–Langevin 算子、初始内禀噪声或其推迟逆。标量齐次约化与完整张量几何的区别见同轮几何研究。

## 4. 推迟响应还包含局域项

在共同过去固定状态，令 \(\delta H[h]\) 是固定 canonical 变量时的 Hamiltonian 变分。其积分生成元记为 \(G_h\)。对位于扰动之后、定义不随度规变化的可观测量，
\[
\delta\langle O\rangle
=i\langle[G_h,O]\rangle.
\tag{8}
\]
此式的正负号由实际 Hamiltonian 验证，不依赖混用相对 Cauchy 演化的不同约定。

对于齐性共形尺度变化 \(a\mapsto a(1+\varepsilon r)\)，每模
\[
H=\tfrac12(p^2/a^2+a^2\omega^2q^2),\qquad
\delta H=r(-p^2/a^2+a^2\omega^2q^2).
\tag{9}
\]
它给
\[
\delta K=
\begin{pmatrix}
0&-2r/a^2\\
-2ra^2\omega^2&0
\end{pmatrix},
\]
与前轮 Duhamel 状态变分相同。

一般平均应力变分还必须包含观察张量、标架、体积元和局域重整化接触项的显式变化。式 (6) 保证交换子部分相同，式 (2) 进一步保证所有这些共同局域项也具有相同的新旧均值。它们的完整数值范数尚未获得。

特别地，加入一个随度规变化的局域 c 数应力项，不改变连接噪声，却可以改变平均几何响应。因此只知道 \(C_0\) 或整个对称噪声核，仍不足以重建完整 RSET 响应。

时空支撑严格排序时，推迟门在两测试支撑上恒定，可以直接使用完整涂抹算子的交换子。支撑交叠时，不能把 Heaviside 因子与奇异分布相乘后不经延拓、接触项与域审查，便套用同一个两测试 Cauchy 界。

## 5. 守恒应当随几何一起变分

在共同坐标识别下，由 \(\nabla^a T_{ab}=0\) 微分得到
\[
\nabla^a\delta T_{ab}
-h^{ac}\nabla_cT_{ab}
-g^{ac}\delta\Gamma^d_{ca}T_{db}
-g^{ac}\delta\Gamma^d_{cb}T_{ad}=0.
\tag{10}
\]
所以 \(\delta T\) 通常不单独满足旧背景守恒式。

在齐性共形时间规范中，令 \(h=a'/a\)、\(r=\delta a/a\)，则
\[
\boxed{
\delta\rho'+3h(\delta\rho+\delta p)
+3r'(\rho+p)=0.
}
\tag{11}
\]
对固定动量的刚性标量源，\(\rho=p\)、\(\delta\rho=\delta p=-6r\rho\)，式 (11) 精确为零。若错误删去最后一项，残差为 \(-6r'\rho\)。检查器实际保留此负控。

对紧支撑微分同胚扰动 \(h_{ab}=2\nabla_{(a}\xi_{b)}\)，完整守恒和分部积分使应力生成元为零（相应共同观察也按同一识别处理）；这与局域协变的规范责任一致。这里只在无引力/微分同胚异常的当前实标量理论中使用该结论。

## 6. 完整噪声直接控制一个真实局部度规扰动

使用 A 线原来的同一个测试
\[
F(\eta,\chi)=
b(32(\eta-3/32))\,b(8\chi),
\]
其时间支撑为 \((1/16,1/8)\)，径向支撑为 \(\chi<1/8\)。仍记
\[
D=\int F\rho_f\,d{\rm vol}_g,\qquad
A_\lambda(F_\lambda)=\int F_\lambda\rho_\lambda\,d{\rm vol}_{g_\lambda},
\quad F_\lambda=\lambda^{-4}F.
\]

固定 \(\lambda\)，构造一个新的、明确指定的局域 lapse 家族：
\[
g_{\varepsilon,\lambda,00}
=-a_\lambda^2\left(1-\frac{2\varepsilon F}{D\lambda^2}\right),
\qquad
g_{\varepsilon,\lambda,ij}
=a_\lambda^2\gamma_{ij}.
\tag{12}
\]
其线性项是
\[
\delta g_{ab}=\frac{2F}{D\lambda^2}u_{\lambda a}u_{\lambda b}.
\]
这是一阶几何量级 \(\lambda^{-2}\) 的明定扰动；它不是前轮已经求解的齐性尺度路径，更不是一个已知的自洽半经典解。

\(F_{\max}=e^{-2}\)。旧证书对 \(D\) 的正下界保证：\(\lambda\ge8192,\ |\varepsilon|\le1\) 时式 (12) 的 lapse 严格为正，\(00\) 分量的相对变化绝对值小于 \(10^{-4}\)。扰动在过去和后续读出区域均为零。

### Hamiltonian 归一化

在固定空间几何和 canonical 数据时，lapse 乘以 Hamiltonian 密度。式 (12) 给
\[
G_\lambda
=-\frac1{D\lambda^2}\int F\rho_\lambda\,d{\rm vol}_{g_\lambda}
=-\frac{\lambda^2}{D}A_\lambda(F_\lambda).
\tag{13}
\]
生成元允许相差一个中心 c 数相位；这不改变交换子或连接方差。于是新符号态的完整生成元方差准确为
\[
\operatorname{Var}G_\lambda
=\frac{c_0}{\lambda^4}
+\frac{d_\lambda^2c_1}{\lambda^2},
\qquad c_i=C_i/D^2.
\tag{14}
\]

这一步的 \(\lambda^2\) 不能漏掉。如果固定相对 lapse 轮廓而删掉式 (12) 中的 \(\lambda^{-2}\)，生成元改为 \(-\lambda^4A_\lambda/D\)，方差为 \(c_0+d_\lambda^2\lambda^2c_1\)，并不随尺度减小。弱应力相对噪声不自动意味着固定幅度度规驱动的弱响应。

### 从实际空间变动的 KG 算子构造推迟态变分

记 \(\alpha=F/(D\lambda^2)\)、\(h=a_\lambda'/a_\lambda\)。对式 (12) 的实际最小无质量算子，直接微分得
\[
\delta\Box\,\phi
=a_\lambda^{-2}
[-2\alpha\phi''-(4h\alpha+\alpha')\phi'
-\nabla\alpha\cdot\nabla\phi].
\]
在未扰动解上还可写成
\[
\delta\Box\,\phi
=-a_\lambda^{-2}
[2\alpha\Delta_{S^3}\phi+\alpha'\phi'
+\nabla\alpha\cdot\nabla\phi].
\]
这包含径向 lapse 的空间梯度，未将局域扰动偷换为一个对角齐次模式变化。

固定共同过去数据时，\(\delta\phi=-E_{\rm ret}\delta P\,\phi\)，从而完整二点核的变分是
\[
\delta W_{\rm full}
=-(E_{\rm ret}\delta P)_x W_{\rm full}
 -(E_{\rm ret}\delta P)_y W_{\rm full}.
\]
此表达式定义的是同一过去态的推迟变分；\(\delta W\) 在扰动之前为零。将其代入 RSET 仍须处理几何微分算子与 Hadamard 减除的变化，本节没有以该表示代替无限场 RSET 的定量导数范数。

### 原后续 Weyl 读出的导数存在

前轮第二仪器窗为 \([5/32,3/16]\)，其起点与扰动末端严格相隔 \(1/32\)。仪器所在区域的度规、测试及耦合定义均保持不变。

对有限 Weyl 仪器的每个固定记录效应，期望可写成有限个 Weyl 特征函数及 c 数交换相位。共同过去的自由传播把其测试线性、光滑地运输。参考特征函数是 Gaussian 因子，位移部分是有界两点分布的特征函数，因此这些记录概率沿该光滑度规家族在 \(\varepsilon=0\) 可微。对应弱导数由式 (8) 的应力二次形式给出。

本节固定同一仪器与校准映射，不对其随 \(\varepsilon\) 的未知漂移给界。问询前准备失败率若固定、失败标签完整保留，则全启动记录导数再乘一个至多为1的成功概率；一般选择性中途损耗不属于此约定。这里使用原后续 Weyl 仪器的窗口和效应类，新尺度的绝对分类概率由主审另外重算，不由本节的导数界自动继承。

这里不从应力的有限二阶矩推断所有有界算子都有度规导数，也不假定四维应力涂抹已被证明本质自伴。对一般有界效应，下面的界以相同弱导数/生成元合同成立为前提。

### 有限记录的严格灵敏度界

对于 \(0\le E\le1\)，Cauchy 不等式与 \(\operatorname{Var}E\le1/4\) 给
\[
\boxed{
\left|\frac{d}{d\varepsilon}P_\varepsilon(E)\right|_{\varepsilon=0}
\le\sqrt{\operatorname{Var}G_\lambda}
\le
\sqrt{\frac{\overline c_0}{\lambda^4}
+\frac{\overline c_1}{\lambda^2}}.
}
\tag{15}
\]
对于一般 \(\|O\|\le1\) 的可微收缩观测，右侧多一个因子2。

同轮完整 \(C_0\) 证书给出的明确尺度为 **32768**，将其上界与旧全模式 \(\overline c_1=1722.5894542402807\ldots\) 组合，实际认证单效应概率斜率小于 **0.06710438**。精确有理上界和 lapse 正性区间见 result.json。

式 (15) 是 \(\varepsilon=0\) 的响应界。有限 \(\varepsilon\) 的完整概率区间，需要沿整条路径统一的方差或二阶余项，当前未认证。它也没有替代全部 RSET 的几何导数范数、非线性固定点或约束反馈求解。

## 7. 验证对象与证据范围

检查器实际执行：

- 两个完整分布的矩、任意共同线性传播下的二点等价；
- 有序连接核的纯实秩一差、正半定性及交换子相同；
- 二次 canonical 交换子闭合及局域 c 数响应负控；
- Hamiltonian 号、lapse 缩放归一化、Duhamel 矩阵及实际空间变动 KG 算子的对接；
- 随几何变分的 Ward 恒等式及错误背景守恒负控；
- 同一局部测试的数值噪声输入、明确尺度、后续时间间隔、lapse 正性和概率斜率。

旧输入绑定到准确基线；同轮完整噪声代码与回执按实际字节冻结。没有重跑旧模式积分、没有新增 Lean 或硬件数据。对无限场和全几何的解析定理在本文给完整论证，符号检查不被称为无限维机器形式化证明。

## 8. 标准依据与符号约定

- [Brunetti–Fredenhagen–Verch, The Generally Covariant Locality Principle](https://arxiv.org/abs/math-ph/0112041)，§4：相对 Cauchy 演化、微分同胚协变和应力生成元的标准框架。
- [Fewster–Schenkel, Locally covariant quantum field theory with external sources](https://arxiv.org/abs/1402.2436)，§3、附录A及脚注5：经典传播变分及原 BFV 正负号约定问题。本节使用实际 canonical Hamiltonian 固定响应号，不直接拼接不同文献约定。
- [Hu–Verdaguer, Stochastic Gravity: Theory and Applications](https://arxiv.org/abs/0802.0658)，§3–4：噪声、交换子和局域作用量二次变分项的不同角色。本节的新旧秩一差与具体 lapse 数值门由上述完整制备独立推得。
