# 光滑几何读出、初值消去与局域约束噪声接口

直接基线：29d49e3eee6299e2085492b0e061288b8166b5fa。本文接续上一轮 [线性几何](../../response/geometry/README.md) 与 [完整应力噪声](../../response/noise/README.md)，解决它们之间尚未合法接通的测试函数与初值问题。

**已完成三项结果：**精确刻画旧线性 Green 算子产生合法紧支撑测试的充要条件；构造一个明确的非零平滑几何差分读出并认证其增益；以实际 Klein–Gordon 模式证明局域空间平均会产生通量项，继而给与原局部密度测试完全一致的条件 ADM 约束读出。

本页没有构造完整 Einstein–Langevin 解，没有把旧齐次 ODE 当成完整非齐次度规响应，也没有把源噪声称为任意度规噪声。

[检查程序](check.py) · [实际区间回执](result.json)

## 1. 为什么普通正几何窗口还不属于原噪声测试域

本节沿用前轮的固定共形时间识别；时间读出本身尚不构成任意规范下的完整局域度规观测。保留旧算子和基本解：
\[
L=\partial_\eta^2+1-3\sec^22\eta,\quad
v=(\cos2\eta)^{-1/2},\quad
u=\frac{\sin2\eta}{2\sqrt{\cos2\eta}},
\]
\[
G(t,s)=u(t)v(s)-v(t)u(s),\qquad
0\le s\le t\le T=3/16.
\]
其 Wronskian 为1，\(G(s,s)=0,\partial_tG(s,s)=1\)。

对一般受迫解
\[
b(t)=b_0v(t)+b_1u(t)+\int_0^tG(t,s)f(s)\,ds
\]
和 \(q\in C^\infty_0(0,T)\)，定义时间读出
\[
O_q=\int_0^Tq(t)b(t)\,dt.
\]
形式交换积分给有效源测试
\[
K_q(s)=\int_s^Tq(t)G(t,s)\,dt.
\]
在 \(s\) 早于 \(q\) 的支撑时，
\[
K_q(s)=v(s)\int q u-u(s)\int q v.
\tag{1}
\]
若 \(q\ge0,q\not\equiv0\)，则 \(u(t)>0\) 给
\[
K_q(0)=\int q(t)u(t)\,dt>0.
\]
将它在初刻以前置零，得到有跳跃的测试；原四维 \(C^\infty_0\) 应力方差定理不能直接应用。这不是关于实际方差必然发散的普遍断言，而是明确指出旧证书的假设不满足。

数值程序对下面的正 bump \(q=\psi\) 实际包围了这个严格正的初刻端点。[Hu–Roura–Verdaguer 的附录D](https://arxiv.org/pdf/gr-qc/0402029)也明确讨论有限初刻的 Green 核乘阶跃函数不属于合格测试的问题；本文没有把其 Minkowski 发散结论直接外推到当前背景。

## 2. 合法伴随域的充要条件与显式构造

**定理。** 对 \(q\in C^\infty_0(0,T)\)，以下命题等价：

1. \(K_q\) 延拓为 \(C^\infty_0(0,T)\) 函数。
2. 两个矩同时为零：
   \[
   \int_0^Tqv=0,\qquad \int_0^Tqu=0.
   \tag{2}
   \]
3. 存在唯一 \(\psi\in C^\infty_0(0,T)\)，使
   \[
   q=L\psi,\qquad K_q=\psi.
   \tag{3}
   \]

**证明。** 式(1)及 \(u,v\) 的线性独立性证明1与2等价。对任何 \(q\)，\(L_sK_q=q\)，且 \(K_q(T)=K_q'(T)=0\)；2保证它在初端附近也为零，从而得到3。反向也可直接用 Lagrange 恒等式：
\[
\frac{d}{dt}\left[G(t,s)\psi'(t)-\partial_tG(t,s)\psi(t)\right]
=G(t,s)L\psi(t).
\]
两端积分后，终端因 \(\psi,\psi'\) 消失，初端因 Green 单位导数跳跃留下 \(\psi(s)\)。同样的恒等式以 \(u,v\) 替代 \(G\)，证明两矩为零。

取标准 bump
\[
b(x)=
\begin{cases}
e^{-1/(1-x^2)},&|x|<1,\\
0,&|x|\ge1,
\end{cases}
\]
并明确选择
\[
\psi(\eta)=b\!\left(32(\eta-3/32)\right),\qquad q=L\psi .
\tag{4}
\]
它们都支撑在 \((1/16,1/8)\)，完全处于旧几何认证区间。\(q\) 不是正窗口：在 \(\eta=3/32\) 严格为负，在 \(\eta=19/160\) 严格为正；这两点由有向区间认证。实际上，由 \(v>0\) 和 \(\int qv=0\)，任意非零合法 \(q\) 都必须改变符号。

### 任意齐次初值及其相关都被读出消去

对式(4)，
\[
\boxed{O_q=\int\psi f.}
\tag{5}
\]
\(b_0,b_1\) 的值可以未知或随机，也可以与 \(f\) 相关；它们分别乘以两个严格为零的矩，所以在这个读出中消失。无需额外假设“初始几何噪声为零”或“初始噪声与源独立”。

对一般 \(q\)，这种消去不成立。此时协方差包含齐次初值、诱导项及其交叉相关，不能只保留一个 \(GNG^*\)。这与标准随机引力中 intrinsic/induced 涨落的区分相容，但本文给的是当前具体 \(L\) 的精确有限时间读出定理。

仅令两制备的初始几何边缘分布相同，仍不足以保证总几何方差按诱导方差排序。一个精确统计负控为：独立 \(Z,E\) 满足 \(\operatorname{Var}Z=3/4,\operatorname{Var}E=1\)，旧源为 \(E+Z\)、新源为 \(E\)，共同初始项为 \(H=-Z\)。诱导方差的旧减新为 \(+3/4\)，总量 \(H+\xi\) 的旧减新却为 \(-3/4\)。这个负控只说明缺少交叉相关假设时的逻辑问题，不声称已经构造了真实 Einstein–Langevin 初态。式(5)逐样本消去齐次项，因此不需要该独立假设。

量子应力响应若把 \(L\) 改成另一个尤其非局域算子，式(4)须重新设计；当前两矩条件没有自动覆盖新的响应算子。

## 3. 读出保留可见的幅度噪声，并量化其测量增益

原单位正幅度标量满足
\[
\rho_f=p_f=\frac{27}{2A^6},\qquad A=\sqrt{3\cos2\eta}.
\]
它在尺度方程中的方向为
\[
\frac{A^3}{3}(\rho_f-3p_f)=-\frac9{A^3}.
\tag{6}
\]

为清楚区分尺度，令 \(\beta=\delta a/\lambda\)。在声明的经典 Einstein–标量受迫线性模型中，
\[
L\beta=\frac{\lambda^2 A^3}{3}(\xi_\rho-3\xi_p).
\]
位移幅度平方的源方向是
\(\xi_\rho=\xi_p=d_\lambda^2\lambda^{-2}(Y^2-1)\rho_f\)，故
\[
O_q^{\rm amp}=-d_\lambda^2D_\psi(Y^2-1),
\qquad
D_\psi=9\int\frac{\psi}{A^3}>0.
\tag{7}
\]
旧制备 \(\operatorname{Var}(Y^2)=3/4\)，新制备该方差为零。因此在同一线性响应和相同其余源协方差下，
\[
\Delta\operatorname{Var}(O_q)
=\frac34d_\lambda^4D_\psi^2>0.
\tag{8}
\]
对有限读出向量，记有符号增益
\(\kappa_i=-d_\lambda^2D_{\psi_i}\)，则
\[
\Delta\operatorname{Cov}_{ij}=\frac34\kappa_i\kappa_j .
\]
该矩阵半正定、秩至多一；不同读出的交叉协方差必须保留有符号增益。

式(8)是共同线性映射下的准确协方差恒等式。原幅度噪声为 \(O(1)\)，该恒等式没有证明原态处于实际引力线性化的有效范围。消除齐次初值也不等于消除源的幅度噪声。

### 绝对标尺与各分支自身初始体积不能混同

式(7)读出的是共同绝对尺度标尺下的 \(\beta\)。这里存在一个精确但范围有限的负控：
\[
LA=-\frac{36}{A^3},\qquad
\int qA=-4D_\psi.
\]
幅度方向可以取
\[
\beta_{\rm amp}
=\frac{d_\lambda^2}{4}A(Y^2-1).
\]
这个解带有与源相关的初始尺度变化；它给出式(7)的相同读出，因为两矩仍消去所有齐次差异。但按每个分支自身初片归一的对数体积
\[
y(\eta)=\frac{3\beta(\eta)}{A(\eta)}
-\frac{3\beta(0)}{A(0)}
\]
在此方向上为零。更直接地，纯经典刚性标量族
\[
a_M^2=\sqrt{M/3}\cos2\eta,\qquad M>0
\]
满足
\[
\frac{V_M(\eta)}{V_M(0)}
=(\cos2\eta)^{3/2},
\]
与 \(M\) 无关。

**该盲区只在共同共形时间标签 \(\eta\) 下成立。** 若仪器按共同法向固有钟 \(\tau=\int_0^\eta a(s)ds\) 取样，整体尺度变化 \(a_\varepsilon=(1+\varepsilon\kappa)a_0\) 同时改变时间识别：
\[
\delta\eta\big|_\tau=-\frac{\kappa\tau}{a},
\qquad
\delta\log(V/V_0)\big|_\tau
=-\frac{3\kappa h\tau}{a},
\]
收缩段一般不为零。因此不能据此宣布原 proper-clock 仪器整套失明，也不能把量子校准的固定背景 Weyl 概率移植到按 \(Y^2\) 关联的另一个几何模型。

反过来，若只有相对体积记录 \(y\)，重建式(7)还需要绝对初片尺度：
\[
\int q\beta
=\frac13\int qAy
-4D_\psi\frac{\beta(0)}{A(0)}.
\]
本文没有把这一绝对差分读出当作原相对体积仪器已经完成的测量。

### 有向积分及校准成本

程序以2048格有向 Riemann 包围计算 \(D_\psi\)，并用准确峰值
\[
x_*^4=\frac13,\qquad
\max|b'|
=\frac{2x_*e^{-1/(1-x_*^2)}}{(1-x_*^2)^2}
\]
得到
\[
\|q\|_1
\le
128\max|b'|+
\left(3\sec^2(1/4)-1\right)\int\psi.
\]
因此归一化读出 \(O_q/D_\psi\) 对一项均匀的 \(\beta\) 读数误差 \(e_{\rm read}\) 满足
\[
\left|\Delta(O_q/D_\psi)\right|
\le\frac{\|q\|_1}{D_\psi}e_{\rm read}
<5000\,e_{\rm read}.
\tag{9}
\]
这说明差分读出有明确的增益成本，不能把它当成无噪声、免费或已经安装的几何仪器。精确有理区间保存于 result.json。

## 4. 空间局域化的真实阻塞：多出的通量项

上面的 \(L\) 来自齐次背景的约化。原噪声测试却含局域空间窗
\[
w(\chi)=b(8\chi).
\]
对一般守恒源，在 FLRW 背景上令 \(J^i=-A^{-2}\gamma^{ij}T_{\eta j}\) 为共形时间连续方程中的三球通量，其中 \(\gamma\) 是单位三球度规。对实标量就是 \(J^i=-A^{-2}\phi' D^i\phi\)。于是
\[
\rho'+3h(\rho+p)+D_iJ^i=0,\qquad h=A'/A.
\]
积分后得到
\[
\boxed{
\rho_w'+3h(\rho_w+p_w)=\int D_iw\,J^i\,d\Omega_3 .
}
\tag{10}
\]
空间窗非恒定时，右侧不能直接删掉。均值通量因对称性为零，也不意味着通量算符或其涨落为零。

**实际场反例。** 取合法实 Klein–Gordon 模式
\[
\phi(\eta,\chi)=u(\eta)\cos\chi,\qquad
u''+2hu'+3u=0,
\]
在 \(\eta_0=3/32\) 选 \(u(\eta_0)=u'(\eta_0)=1\)。其径向流为
\[
J^\chi=A^{-2}\cos\chi\sin\chi.
\]
因为 \(w'<0\) 于 \(0<\chi<1/8\)，局域通量严格非零。分部积分精确给
\[
\int D_iw\,J^i d\Omega_3
=
-\frac{4\pi}{A^2}
\int_0^{1/8}
w(\chi)\sin^2\chi\left(3-4\sin^2\chi\right)d\chi<0.
\tag{11}
\]
检查器验证 \(-\Delta_{S^3}\cos\chi=3\cos\chi\)、分部积分恒等式及该非零量的严格区间。

因此，把局域应力平均直接填进旧齐次 ODE 会丢掉能量通量及相关非齐次约束。一个全空间齐次投影属于不同测试与不同物理出口；本文没有用它替换原有限内球的密度测试。第2–3节的 ODE 读出涉及 \(\rho-3p\) 的测试，不能直接消费密度 \(\rho\) 的 \(C_0\) 数值并宣布整个 ODE 几何噪声已小；下一节的 ADM 接口才与原密度测试完全一致。

若要得到真实局域度规噪声，需要完整张量的线性 Einstein–标量系统、能流与各向异性应力、相容初值和合法响应域。

### 平滑应力测试确实合法，但它本身不是局域度规响应

为明确四维测试对象，取单位三球上任意归一化光滑空间窗 \(w\)，例如将原 \(b(8\chi)\) 除以其正积分。记 \(P_\lambda^{ab}=g_\lambda^{ab}+n_\lambda^an_\lambda^b\)，则
\[
\rho-3p=(n_\lambda^an_\lambda^b-P_\lambda^{ab})T_{ab}
=-g_\lambda^{ab}T_{ab}.
\]
上面时间滤波对应的完整应力测试张量为
\[
H_{\psi,w}^{ab}
=\frac{\psi w}{3\lambda^2 A}
 (n_\lambda^an_\lambda^b-P_\lambda^{ab})
=-\frac{\psi w}{3\lambda^2 A}g_\lambda^{ab},
\]
因为 \(d{\rm vol}_{g_\lambda}=\lambda^4A^4d\eta d\Omega_3\)。因此
\[
\xi(H_{\psi,w})
=\int\psi\,\frac{\lambda^2A^3}{3}
 \int w(\xi_\rho-3\xi_p)d\Omega_3\,d\eta .
\]
这是合法的 \(C^\infty_0\) 四维张量测试；其支撑仍在原内球、有限时间窗中，没有单时刻的应力限制，也没有尖端 Green 核。**把这个合法源读出认作实际局域几何读出仍须解决式(10)的完整响应问题。**

完整噪声也可在这个测试上准确表达。明确取未重调的正幅度基解
\(f_\star\)，满足 \(A^2f_\star'=\sqrt{27}\)，其余初值沿用冻结基解。
在同形度规上 \(\rho_\star=p_\star=\lambda^{-2}27/(2A^6)\)。
把场写为 \(\Phi=\varphi+d_\lambda Yf_\star\)，令
\(L_{f_\star}(H)=\left.\partial_\epsilon T[\varphi+\epsilon f_\star](H)\right|_{\epsilon=0}\)
为 Gaussian 场的线性算符，并记 \(D(H)=T[f_\star](H)\)。
这里 \(f_\star\) 不含 \(d_\lambda\)，避免与已经重调的位移符号混淆。
对任意两个合法实测试 \(H,K\)，新符号制备满足
\[
N_{\rm new}(H,K)
=N_G(H,K)+d_\lambda^2
 \operatorname{Re}\langle L_{f_\star}(H)L_{f_\star}(K)\rangle_G ,
\]
旧制备则为
\[
N_{\rm old}(H,K)
=N_{\rm new}(H,K)+\frac34d_\lambda^4D(H)D(K).
\]
式中 Gaussian 奇阶矩为零、\(\mathbb E Y^2=1\)，新制备 \(Y^2=1\)；这保留所有 Gaussian 应力项和位移线性项，而非只计算幅度方差。对 \(H_{\psi,w}\)，\(D(H_{\psi,w})=-D_\psi\)，所以式(8)的符号和归一一致。这里尚未给出该 trace 测试的 \(N_G\) 全模数值上界；密度测试的 \(C_0\) 不能直接替代它。

## 5. 与原局部密度测试完全一致的 ADM 读出

空间问题不能用旧齐次 ODE 消除，但可建立一个明确、局域、条件性的几何约束接口。

采用 \(4\pi G=1\)，定义经典 Einstein–标量残差
\[
\mathcal E_{ab}=G_{ab}-2T^\phi_{ab}.
\]
以同一单位法向 \(n\) 和叶片几何定义
\[
\mathcal C
=\frac12\mathcal E_{ab}n^an^b
=\frac14\left({}^{(3)}R+K^2-K_{ij}K^{ij}\right)-\rho_\phi .
\tag{12}
\]
这是完整局域约束；空间曲率和外曲率保留所有非齐次贡献。

这里的 \(\phi\) 是代表相同二阶源的正幅度经典基解，负分支整体取负；它不表示偏置混合态的场一阶均值。在经典基线 \(a=\lambda A,\ P_\phi^2=27\lambda^4\) 上，
\[
\mathcal C_0=
\frac{3(a'^2+a^2)}{2a^4}-\frac{P_\phi^2}{2a^6}=0.
\]
检查器进一步验证：若
\(a=\lambda(A+\varepsilon b)\)、
\(P_\phi^2=\lambda^4(27+\varepsilon m)\)，则
\[
\delta\mathcal C
=
\frac3{2\lambda^2A^4}
\left(2A'b'+2Ab+\frac{18b}{A^3}-\frac{m}{3A^2}\right).
\tag{13}
\]
它与前轮一阶 Friedmann 约束的归一化一致。

### 明确的条件定理

假设选定的经典受迫线性系统满足
\[
\delta\mathcal E_{ab}=2\xi_{ab},
\]
且噪声协方差由同一完整量子态的对称连通应力二点分布给出：
\(\mathbb E[\xi(H)\xi(K)]=N(H,K)\)。
那么
\[
\delta\mathcal C=\xi_{nn}.
\]
使用原来同一个
\[
F=b\!\left(32(\eta-3/32)\right)b(8\chi),
\qquad F_\lambda=\lambda^{-4}F,
\]
构造
\[
\mathcal O_F=\int F_\lambda\,\delta\mathcal C\,d{\rm vol}_{g_\lambda}.
\]
它严格满足
\[
\boxed{
\operatorname{Var}(\mathcal O_F)
=\operatorname{Var}\!\left(T_{uu}(F_\lambda)\right)
=\lambda^{-8}C_0+d_\lambda^2\lambda^{-6}C_1
}
\tag{14}
\]
用于新偏置符号制备。原局部 \(C_0,C_1\) 证书因此可直接接入这个明确的约束读出，而不用把局部测试换成整球投影。

\(\mathcal O_F\) 是中心化量，均值为零；若要报告无量纲噪声，可除以原背景尺度 \((\lambda^{-2}D)^2\)，不能除以它自身为零的均值平方。式(14)只使用二阶随机协方差合同，没有把通常选取的 Gaussian 随机源当成完整非 Gaussian 应力所有高阶记录的再现。

### normal、规范和背景的责任

经典背景上 \(\mathcal E_{ab}=0\)，因此变化单位法向产生的项乘以零背景残差，\(\delta\mathcal C=\tfrac12n_0^an_0^b\delta\mathcal E_{ab}\)。对同时作用在度规和经典标量上的线性微分同胚，
\(\delta_X\mathcal E=\mathcal L_X\mathcal E_0=0\)。这给出此线性残差读出的规范不变性。

这里使用的是确实满足经典方程的基线。相关调源后的量子背景仍有前轮认证的有限平均残差；它尚未成为完整 SCE on-shell 背景，不能直接套用完整 SCE 的规范结论。

### 完整量子反馈需要再减去响应项

若完整 Einstein–Langevin 算子包含量子 RSET 变分，正确接口应为
\[
\delta\mathcal C-\delta\langle T^q_{nn}\rangle=\xi_{nn},
\tag{15}
\]
其中应包含局域重整化项、法向及态变分。于是式(14)对应的是减去量子响应后的残差读出。未减去的几何曲率噪声还包含该响应及其交叉协方差，不能由 \(C_0\) 单独认证。

本文给出式(14)的条件数学接口，而非完整随机方程的解存在证明。相容随机初值、完整响应算子、非线性余项、实际几何读出和外区匹配继续分别开放。

## 6. 审查、执行与文献范围

check.py 独立验证 Green 基本解与导数跳跃、Lagrange 公式、bump 二阶导数、经典幅度方向、绝对尺度与相对体积及固有钟的区别、协方差秩一正性、ADM 归一化、真实 KG 模式及局域通量，并以有向区间计算具体读出。旧 geometry/noise 回执、共同合同和执行清单逐字节绑定到29d49e3e；新增模式 ODE为0。

- [Gourgoulhon，3+1 Formalism and Bases of Numerical Relativity](https://arxiv.org/pdf/gr-qc/0703035)：ADM 分解及 Hamiltonian 约束。
- [Hu–Roura–Verdaguer，Induced quantum metric fluctuations and the validity of semiclassical gravity](https://arxiv.org/pdf/gr-qc/0402029)：区分本征与诱导涨落，以及完整噪声响应所需的随机方程。本文没有移植其 Minkowski 稳定性结论。
- [Fröb–Hack–Higuchi，Compactly supported linearised observables in single-field inflation](https://arxiv.org/pdf/1703.01158)，式(2.18)及第3节：on-shell 协变残差与紧支撑线性观测的规范条件。这里只使用协变变分原则，没有把其平坦空间切片的具体定理照搬到闭三球。
