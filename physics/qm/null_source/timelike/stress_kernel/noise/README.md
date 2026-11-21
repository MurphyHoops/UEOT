# 原局部四维测试的完整二次应力噪声上界

基线：29d49e3eee6299e2085492b0e061288b8166b5fa。这里关闭前轮 [完整噪声](../../response/noise/README.md) 留下的定量缺口：对完全相同的局部四维测试，给原静态过去所定义参考态的完整 \(C_0\) 上界，不改用空间全域测试，不改变时间窗口，不重积分模式 ODE。

实际有向计算得到
\[
\boxed{\frac{C_0}{D^2}<5.190\times10^{15}.}
\]
沿前轮声明的精确相关调源族，选择明确尺度
\[
\boxed{\lambda=32768}
\]
后，完整相对方差上界为
\[
\boxed{
\frac{\operatorname{Var}(A_\lambda)}
{(\mathbb EA_\lambda)^2}
<0.004595<0.01 .
}
\]
该充分尺度是本轮完整界导出的数值，不是最优性或 Core 独立选择的结论。对8192，本保守界约为1.17578，因而仍未通过1%门；没有证明8192的实际噪声大于1%。

[程序](check.py) · [精确有理回执](result.json)

## 1. 状态、测试及准确的双模式表示

保持原最小、无质量、实自由场和零均值纯 quasifree 参考态。它由原光滑辅助静态过去给定，包含原正规零模；本处 Wick 分解仅用于该参考态。新偏置符号制备仍按前轮完整方差公式接入，未对非 Gaussian 混合态作 Gaussian 完成。

完全沿用
\[
F(\eta,\chi)=h(\eta)w(\chi)
=b(32(\eta-3/32))\,b(8\chi),
\quad b(x)=
\begin{cases}e^{-1/(1-x^2)},&|x|<1,\\0,&|x|\ge1.\end{cases}
\]
时间支撑为 \((1/16,1/8)\)，径向支撑为 \(\chi<1/8\)，仍在原有限内域。单位三球上取完整实正交球谐 \(Y_n\)，非零模式记 \(n=(k,j)\)，\(k\ge2\)，频率 \(\omega_k=\sqrt{k^2-1}\)，简并度 \(k^2\)。零模式归入 \(k=1\) 的单个标签，但其真实空间频率为0。

定义
\[
M_{nm}=\int_{S^3}wY_nY_m\,d\Omega,\qquad
N_{nm}=\int_{S^3}w\,\nabla Y_n\cdot\nabla Y_m\,d\Omega.
\]
故 \(N_{0m}=N_{m0}=0\)。另有独立恒等式
\[
N_{nm}=\frac12\left[(\omega_n^2+\omega_m^2)M_{nm}
+M_{\Delta w,nm}\right].
\]

密度涂抹量为
\[
A_0=\frac12\int h a^2[(\Phi')^2+|\nabla\Phi|^2]\,d\eta\,d\Omega
+\hbox{重整化 c 数}.
\]
在原真空表示中，其作用于真空的中心化部分只保留成对产生项：
\[
P_{nm}=\frac12\int h a^2
[u_n'u_m'M_{nm}+u_nu_mN_{nm}]\,d\eta.
\]
将共轭全部加入或全部去掉不改变以下范数。令 \(B_{nm}=2P_{nm}\)，则
\[
\boxed{C_0=2\sum_{n,m}|P_{nm}|^2=\frac12\|B\|_{\mathrm{HS}}^2.}
\]
这是先对平滑测试形成振荡的模式系数，再取其平方和；没有对奇异 Wightman 核取点态绝对值平方。

取 \(K=256\)，低块 \(L\) 包含零模和 \(2\le k\le K\)，高块 \(H\) 包含所有 \(k>K\)。对称矩阵给
\[
C_0=\tfrac12[
\|B_{LL}\|_{\mathrm{HS}}^2+
2\|B_{LH}\|_{\mathrm{HS}}^2+
\|B_{HH}\|_{\mathrm{HS}}^2].
\]
低—高交叉块的因子2明确保留。

## 2. 空间求和：简并度、零模与加权 Bessel

令 \(w_0=\|w\|_\infty\)，\(w_1=\|\nabla w\|_\infty\)。以下每条先对一个完整模式标签 \(n=(k,j)\) 成立，随后才对 \(k^2\) 个标签求和。

Parseval 给
\[
\sum_m|M_{nm}|^2\le w_0^2.
\]
谱 Cauchy 及乘积导数给
\[
\sum_{m\ne0}\omega_m|M_{nm}|^2
\le\|wY_n\|_2\|\nabla(wY_n)\|_2
\le w_0(w_1+w_0\omega_k).
\]

归一化梯度 \(\nabla Y_m/\omega_m\) 是向量 \(L^2\) 中的正交族，因此
\[
\sum_{m\ne0}\frac{|N_{nm}|^2}{\omega_m^2}
\le\|w\nabla Y_n\|_2^2\le w_0^2\omega_k^2.
\]
另一方面，
\[
\sum_m|N_{nm}|^2
=\|\operatorname{div}(w\nabla Y_n)\|_2^2
\le2w_0^2\omega_k^4+2w_1^2\omega_k^2.
\]
两式作 Cauchy，得到
\[
\boxed{
\sum_{m\ne0}\frac{|N_{nm}|^2}{\omega_m}
\le\sqrt2\,[w_0^2\omega_k^3+w_0w_1\omega_k^2].
}
\]
零模的 \(N\) 行列为零，从未除以零模频率。上述求和覆盖完整空间简并度，没有要求球心处只有某类角模。

## 3. 低块和低—高块：实际完整制备的能量界

前轮原制备总对数变差证书给
\[
|a u'_k|^2\le H\omega_k,\qquad
|a u_k|^2\le H/\omega_k,\qquad
H=e^{2r_*}/2 .
\]
第二式与第一式来自同一瞬时 Hamiltonian 系数估计，使用
\(|\alpha|+|\beta|\le e^{r_*}\)。正规零模满足
\[
|a u'_0|^2=\frac{3}{2a^2}<H
\]
在本测试时间支撑上成立；程序单独检查这个不等式。其梯度项为零。

记
\[
L_0=\int h\,d\eta,\qquad
S_j=\sum_{k=1}^{K}k^j,\qquad
X=w_0^2S_4+w_0w_1S_3.
\]
把上一节的全空间行界代入，并用 \(\omega_k\le k\)，得到
\[
\boxed{
\|B_{LL}\|_{\mathrm{HS}}
\le N_{LL}
=HL_0\left[w_0\sqrt{KS_3}+2^{1/4}\sqrt X\right].
}
\]
低—高块的动量项先对所有高模式作加权 \(M\) 行求和，空间梯度项用加权 \(N\) 行界：
\[
\boxed{
\|B_{LH}\|_{\mathrm{HS}}
\le N_{LH}
=HL_0(1+2^{1/4})\sqrt X .
}
\]
这些块没有用截断高模替代全谱。零—高交叉也在 \(B_{LH}\) 中，并在最终方差中计两份。

## 4. 高模式：W2 正频列与真实准备余项

这里复用 [旧 UV 程序](../../evolution/stress/tail.py)及其 [K256 回执](../../evolution/stress/tail_K256_M1024.json)中实际证明的模式系数界；没有直接复用旧平均 RSET 尾作为噪声尾。

令 \(v_k=a u_k\)，
\[
v_k''+(k^2+q)v_k=0,\qquad q=-1-a''/a.
\]
旧二阶 WKB 频率 \(W_k\) 在整个准备过程正，静态过去与原真空数据准确匹配。令
\[
w_k=(2W_k)^{-1/2}e^{-i\theta_k},\quad\theta_k'=W_k,
\qquad
w_k''+(k^2+q)w_k=R_kw_k.
\]
用变参数法同时表示 \(v_k,v_k'\)，系数满足
\[
\alpha_k'=-ic_k(\alpha_k+e^{2i\theta_k}\beta_k),\quad
\beta_k'=ic_k(e^{-2i\theta_k}\alpha_k+\beta_k),\quad
c_k=R_k/(2W_k).
\]

必须先去掉对角相位。写
\[
\alpha_k=e^{-i\int c_k}\widetilde\alpha_k,\qquad
\beta_k=e^{+i\int c_k}\widetilde\beta_k,\qquad
\phi_k=\theta_k+\int c_k.
\]
原 \(\alpha_k\) 本身不一定接近1。对新的系数，静态初值是
\(\widetilde\alpha_k=1,\widetilde\beta_k=0\)，且
\[
|\widetilde\alpha_k-1|\le\cosh I_k-1,\quad
|\widetilde\beta_k|\le\sinh I_k,\quad
I_k\le D_5/k^5.
\]
这里的 \(D_5\) 消费旧回执中从静态过去一直到 \(3/16\) 的统一界。因此
\[
|\widetilde\alpha_k-1|+|\widetilde\beta_k|
\le e^{I_k}-1
\le E_5/k^5,\qquad
E_5=e^{D_5/(K+1)^5}D_5.
\]

物理段用 \(W_k=k\sqrt{\mathcal B_k}\)，
\(g_k=a'/a+\mathcal B_k'/(4\mathcal B_k)\)。正频列的两个分量为
\[
a u_k^+=\frac{e^{-i\phi_k}}{\sqrt{2W_k}},\qquad
a (u'_k)^+=
\frac{(-g_k-iW_k)e^{-i\phi_k}}{\sqrt{2W_k}}.
\]
这是变参数表示中的场和动量列；第二个分量不能误写成第一个分量的普通时间导数，因为 \(\phi_k'=W_k+c_k\)。

本轮有向 jets 对全部 \(k>K\) 验证
\[
|a u_k^+|\le k^{-1/2},\qquad
|a(u'_k)^+|\le2k^{1/2}.
\]
对应负频列是共轭。令 \(\eta_k=E_5/k^5\)，则实际列与正频列的差分别由上述界乘 \(\eta_k\) 控制，且 \(\eta_k<1\)。

### 4.1 准备余项的完整 Hilbert–Schmidt 界

动量乘积差的绝对值至多
\(8\sqrt{kl}(\eta_k+\eta_l)\)，
场乘积差至多
\(2(\eta_k+\eta_l)/\sqrt{kl}\)。
用
\((\eta_k+\eta_l)^2\le2(\eta_k^2+\eta_l^2)\)、
空间加权行界及 \(l\le2\omega_l\)，得到
\[
\boxed{
N_{\rm err}
=32L_0E_5
\sqrt{\frac{w_0^2}{5K^5}+\frac{w_0w_1}{6K^6}}
}
\]
作为高—高余项的范数上界。系数32大于分别来自动量和梯度项的
\(16\sqrt2+4\,2^{1/4}\)。
尾和使用
\(\sum_{k>K}k^{-p}\le K^{1-p}/(p-1)\)。
两种交叉频率及双负频率都包含在这个余项界中。

## 5. 高频正频主项：保留振荡的三次分部积分

正频主项系数为
\[
(B^+_{HH})_{nm}
=\frac{\sqrt{kl}}2M_{nm}
 \int h\,A_{kl}^{\rm kin}e^{-i(\phi_k+\phi_l)}d\eta
+\frac{N_{nm}}{2\sqrt{kl}}
 \int h\,A_{kl}^{\rm grad}e^{-i(\phi_k+\phi_l)}d\eta ,
\]
其中
\[
A_{kl}^{\rm kin}
=\frac{(g_k/k+i\sqrt{\mathcal B_k})
       (g_l/l+i\sqrt{\mathcal B_l})}
      {(\mathcal B_k\mathcal B_l)^{1/4}},
\qquad
A_{kl}^{\rm grad}=(\mathcal B_k\mathcal B_l)^{-1/4}.
\]

令 \(\phi_k'=k\sigma_k\)，
\(S_{kl}=(k\sigma_k+l\sigma_l)/(k+l)>0\)。
对 \(\mathcal D_S f=(f/S)'\)，三次分部积分给
\[
\left|\int hA e^{-i(\phi_k+\phi_l)}d\eta\right|
\le (k+l)^{-3}\|\mathcal D_S^3(hA)\|_1.
\]
原 bump 在端点无限阶平坦，所有边界项为零。正频率之和没有被替换为频率之差。

### 实际导数常数如何认证

代码用实际物理段 \(q=\sec^22\eta\) 的0至7阶有向 Taylor jets，复用旧 W2 的准确代数式，统一包围
\(\delta_k=k^{-2}\in[0,257^{-2}]\)。
\(\sigma_k=\sqrt{\mathcal B_k}+\delta_k^3R_{n,k}/(2\sqrt{\mathcal B_k})\)。
对 \(S_{kl}\)，每一阶导数系数是两种 \(\sigma\) 系数的凸组合，故同一公共区间包围有效；两种频率仍是独立变量。

将
\[
\mathcal D_S^3(hA)=\sum_{j=0}^3 c_j(\eta)h^{(j)}(\eta)
\]
按每个 \(h^{(j)}\) 的单位 jet 分别求出，取有向复系数绝对值界，再乘各 \(L^1\) 导数范数。没有采样频率或把普通浮点误差估计当成认证。

时间 bump 的范数使用：

- \(L_0\le\sqrt3\int h/a\)，右侧来自前轮原测试的有向积分。
- \(L_1=2/e\)。
- \(L_2=32\cdot4\max|b'|\)，极值 \(x^4=1/3\)。
- \(L_3\) 由 \(b''\) 的总变差控制。令 \(z=(1-x^2)^{-1}\)，
  \(b''=(4z^4-12z^3+6z^2)e^{-z}\)，
  \(b^{(3)}=4xz^3(-2z^3+14z^2-21z+6)e^{-z}\)。
  准确 Sturm 计数给 \(z>1\) 两个临界点，分别位于
  \([159/100,8/5]\)、\([5,51/10]\)；
  对这两个区间直接有向求值，得到 \(L_3\) 上界。

程序保存完整导数系数与 \(L_{\rm kin},L_{\rm grad}\)。空间求和使用
\[
\sum_{n,m\in H}
\frac{kl|M_{nm}|^2}{(k+l)^6}\le\frac{w_0^2}{K},
\]
\[
\sum_{n,m\in H}
\frac{|N_{nm}|^2}{kl(k+l)^6}
\le\sqrt2\left(\frac{w_0^2}{K}+\frac{w_0w_1}{2K^2}\right).
\]
每个完整 \(k\) 标签贡献 \(O(k^{-4})\)，乘简并度 \(k^2\) 后是可求和的 \(k^{-2}\)。因此
\[
\boxed{
N_{\rm main}
=\frac12\left[
\frac{L_{\rm kin}w_0}{\sqrt K}
+2^{1/4}L_{\rm grad}
\sqrt{\frac{w_0^2}{K}+\frac{w_0w_1}{2K^2}}
\right].
}
\]

## 6. 完整数值出口和明确尺度

合并全部分块：
\[
\boxed{
C_0\le\frac12\left[
N_{LL}^2+2N_{LH}^2+(N_{\rm main}+N_{\rm err})^2
\right].
}
\]
非负密度测试的旧 \(D\) 下端点用于归一化。实际程序得到
\(C_0/D^2\) 上界约 \(5.189751962328455\times10^{15}\)；
完整精确有理数记录在 result.json。

沿每个尺度重新调节的精确相关源，旧定理保证
\(\epsilon_\rho<0.01\)、\(0<d_\lambda^2<1\) 对所有 \(\lambda\ge8192\) 成立。保持原 \(C_1/D^2\) 全模式上界后，
\[
\frac{\operatorname{Var}(A_\lambda)}{(\mathbb EA_\lambda)^2}
\le
\frac{c_0/\lambda^4+c_1/\lambda^2}{0.99^2}.
\]
程序在8192起的二次幂尺度中找到32768，实际右侧
\(0.0045944256384241045\ldots<1\%\)。
此选择不保持8192处的固定有理 \(M_2\)，而使用随尺度重新调节的精确相关源。

回执的稳定机器接口：

- certificate.c0_over_D2_upper：完整二次项上界，Fraction 字符串。
- certificate.c1_over_D2_upper：原完整线性项上界，Fraction 字符串。
- certificate.lambda_certified：明确通过尺度32768。
- certificate.full_relative_variance_upper：完整相对方差上界，Fraction 字符串。
- certificate.lambda8192_one_percent_certified：false。
- certificate.lambda8192_one_percent_failure_proved：false。

测试、完整态和测量单元保持同形合同；物理大小与固有时长随尺度增大。这个数值闭合不认证改动后的非同形几何、完整非线性 SCE 或实际硬件。把该应力噪声接入几何记录须另给合法响应合同及测试域。

## 7. 验证身份

check.py 绑定本文件所用旧源码、原测试回执、原制备与 W2 回执到基线29d49e3e，并在运行前后检查字节身份。实际执行包含 bump 代数、根隔离、空间归一、W2 jets、全谱分块、有向区间及新尺度门；新增模式 ODE 为0。

静态匹配 W2 的既有准备估计被明确复用；原平均应力尾数字未被当作噪声尾。谱界推导、数值复核与外部物理输入分别登记。数学物理背景仍为前轮列出的 Hadamard/Wick 分布理论；本轮新增的是同一已指定参考态和原局部测试的完整数值上界。

本轮未新增 Lean 证明或真实硬件数据，Core 仍是只读依赖。
