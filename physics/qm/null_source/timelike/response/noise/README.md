# 完整应力方差、局部全谱线性噪声与有限测试族的弱噪声极限

基线 d6ec9eda409ba78d1d7993d7648ba26b5a34374d。本文接续 [compatibility](../../compatibility/README.md)，保留原参考核、物理有限耦合及全部旧证书。只改变已声明的位移分布，并重新判断完整应力方差。

本轮得到三个不同层次的结果：

1. 对四维光滑紧支撑密度涂抹，严格给出完整量子方差的缩放公式。新偏置符号混合消去原幅度混合项，但不消去量子噪声。
2. 对一个实际位于原内区的光滑测试，用全模式能量增长和空间 Sobolev 估计认证线性量子噪声常数，不截断模式、不重新积分 ODE。
3. 对任意预先固定的有限组上述测试和任意目标相对方差，证明存在有限的充分尺度，并给出显式依赖固定参考常数的阈值。

完整二次参考应力常数 \(C_0\) 的有限性已证明；其数值上界本轮尚未认证。因此 **\(\lambda=8192\) 的完整量子方差小于 1% 仍未被数值验收**。下面的局部数值是线性量子项的完整全谱上界。

[计算程序](check.py) · [精确有理区间回执](result.json)

## 1. 同一个完整背景、同一个参考态和明确的测试族

使用最小、无质量、自由实场，度规号差 \((-+++)\)。在内核
\[
a(\eta)=\sqrt{3c},\qquad c=\cos2\eta,\qquad
u=a^{-1}\partial_\eta,
\]
取共动密度 \(\rho=T_{ab}u^au^b\)。\(W\) 是原零均值 quasifree Hadamard 参考态的二点核；正规零模与非零模式使用同一实际光滑制备。

原正经典解 \(f\) 满足
\[
a^2 f'=\sqrt{27},\qquad
\rho_f=\tfrac12(uf)^2=\frac1{2c^3}.
\]
取任意非零、非负、实 \(F\in C^\infty_0\)，支撑包含于已认证的物理内区，定义
\[
A_0=\int F\rho_{\rm ref}\,d{\rm vol}_g,\qquad
D=\int F\rho_f\,d{\rm vol}_g>0.
\]
\(D\) 同时是原几何所需密度的涂抹。重整化常数项包含在 \(A_0\) 的均值内。

整体同形运输为
\[
g_\lambda=\lambda^2g,\quad W_\lambda=\lambda^{-2}W,\quad
u_\lambda=\lambda^{-1}u,\quad F_\lambda=\lambda^{-4}F.
\]
因此 \(F_\lambda d{\rm vol}_{g_\lambda}=F d{\rm vol}_g\)。这是固定共形形状、随背景一起放大的时空测量单元；固定物理孔径和固定固有时长属于另一测试族，不能套用下面的固定常数。

位移是 \(Yd_\lambda f\)，其中
\[
d_\lambda=\frac{\sqrt{M_2/27}}{\lambda^2},\qquad
d_\lambda^2=1-\frac{2Q_{\rm eff,0}}{\lambda^2}
\]
用于相关精确源。显式有理源则直接用 \(d_\lambda^2=\widehat M_2/(27\lambda^4)\)。两支的 \(0<d_\lambda^2<1\) 从旧实际回执分别核验。

新分布为 \(Y=\pm1\)，偏置概率使 \(\mathbb EY=s/2\)，其中 \(s\) 是固定标签。它保留 \(\mathbb EY^2=1\)，但改变完整制备；不再满足旧 \(X=Y-s/2\) 对称的要求。因此原对称族的噪声下界没有被撤回。

## 2. 完整量子方差的准确分解

令
\[
B=\int F(uf)(u\Phi)\,d{\rm vol}_g.
\]
这是一个线性场可观测量。分部积分给
\[
B=\Phi(j_F),\qquad
j_F=-\nabla_a[F(uf)u^a].
\]
约定 \(\Phi(j)=\int j\Phi\,d{\rm vol}_g\)。在当前齐性源中，\(a^2f'=\sqrt{27}\)，所以还可写为
\[
\boxed{j_F=-\sqrt{27}\,a^{-4}\partial_\eta F.}
\]
紧支撑保证无边界项。

把缩放态拉回原参考表示，密度可观测量是
\[
A_\lambda(Y)
=\lambda^{-4}A_0+k_\lambda{\bf1}
+Yd_\lambda\lambda^{-3}B
+Y^2d_\lambda^2\lambda^{-2}D.
\]
\(k_\lambda\) 包含重整化缩放异常的 c 数项。其值影响均值，但不影响连通方差。

记
\[
C_0=\operatorname{Var}_{\rm ref}(A_0),\qquad
C_1=\operatorname{Var}_{\rm ref}(B)=W(j_F,j_F).
\]
零均值 Gaussian 参考态的奇数阶矩为零，因此
\[
\langle (A_0-\langle A_0\rangle)B+
B(A_0-\langle A_0\rangle)\rangle=0.
\]
这里使用的是非交换算符的对称交叉项，不是默认为 \(A_0,B\) 可交换。

对独立于参考态选择的相干位移混合，\(\mathbb EY^2=1\) 给出
\[
\boxed{
\operatorname{Var}(A_\lambda)
=\lambda^{-8}C_0
+d_\lambda^2\lambda^{-6}C_1
+\operatorname{Var}(Y^2)d_\lambda^4\lambda^{-4}D^2.
}
\]

| 制备 | 幅度混合贡献 | 保留的量子贡献 |
|---|---|---|
| 原 bounded A：\(Y=s/2\pm\sqrt3/2\) | \((3/4)d_\lambda^4\lambda^{-4}D^2\) | \(\lambda^{-8}C_0+d_\lambda^2\lambda^{-6}C_1\) |
| 新偏置符号：\(Y=\pm1\) | 0 | 完全保留同样两项 |

消除的是经典幅度平方的不确定性，量子涨落仍被完整计入。两个完整混合态虽有相同的一阶和二点函数，通常均不是 quasifree；不能把混合后的完整二点核直接代入 Gaussian Wick 公式。这里的 Wick 展开始终针对同一个零均值参考态，然后对位移分布取平均，因而保留了不同的四点信息。

### 完整二次项为何有限

在局部正交标架 \(e_0=u,e_i\) 中令
\[
K_{\alpha\beta}(x,x')
=(e_\alpha\otimes e'_\beta)W(x,x').
\]
连通密度核由 Wick 定理给出
\[
C_0=\frac12\sum_{\alpha,\beta=0}^3
\operatorname{Re}\left\langle K_{\alpha\beta}^{\,2},
F\otimes F\right\rangle.
\]
这是分布配对。核中是有序两点函数导数的平方，**不是** \(|K_{\alpha\beta}|^2\) 的绝对积分。后者会破坏关键的频率方向，不能用来声称一个有限上界。

Hadamard 波前集的方向性保证这些导数乘积作为分布有定义；对四维光滑紧支撑测试，其配对是有限数。相干位移只增加光滑函数，有限混合保持本处的定义域。\(C_1=W(j_F,j_F)\) 则直接由光滑场测试的二点函数给出有限非负数。

原始依据是 [Brunetti–Fredenhagen–Köhler，§5，定理5.7及其导数说明](https://arxiv.org/pdf/gr-qc/9510056)对 Wick 多项式的构造，以及 [Hollands–Wald](https://arxiv.org/pdf/gr-qc/0103074)对局域协变 Wick 量与有限重整化自由度的处理。本文的质量为零情形使用 Hadamard 波前集与导数乘积论证；没有把 BFK 文中以 massive 写出的应力推论单独当作省略零模的理由。

## 3. 对任意固定有限测试组的弱噪声定理

定义无量纲固定常数
\[
c_0=C_0/D^2,\qquad c_1=C_1/D^2.
\]
从旧均值证书，对于同形运输的非负测试，
\[
|\mathbb EA_\lambda-\lambda^{-2}D|
\le\epsilon_\rho(\lambda)\lambda^{-2}D.
\]
因此新符号混合满足
\[
\boxed{
\frac{\operatorname{Var}(A_\lambda)}
{(\mathbb EA_\lambda)^2}
\le
\frac{c_0/\lambda^4+d_\lambda^2c_1/\lambda^2}
{[1-\epsilon_\rho(\lambda)]^2}.
}
\]

这里对每个 \(\lambda\) 都使用声明的相关源族 \(M_2^\star(\lambda,Q)\)。不能把8192处那个固定有理数 \(\widehat M_2\) 保持不变，再将本定理外推到所有尺度。

旧均值界保证该相关源族在 \(\lambda\ge8192\) 时
\(0<d_\lambda^2<1\)、\(\epsilon_\rho(\lambda)<1/100\)，且均值缺陷趋于零。于是，对任何固定测试 \(F\) 和目标 \(\tau>0\)，一个明确的充分条件为
\[
\lambda\ge8192,\qquad
\lambda^2\ge
\frac{c_1+\sqrt{c_1^2+4\tau(0.99)^2c_0}}
{2\tau(0.99)^2}.
\]
\(c_0,c_1\) 由未缩放的参考态与测试直接定义，既不依赖目标 \(\tau\)，也不以待证的缩放态方差倒填。

**有限测试组。** 先固定任意有限组 \(F_1,\ldots,F_m\)，分别有 \(D_i>0\)，再用
\[
c_0^\star=\max_i C_{0,i}/D_i^2,\qquad
c_1^\star=\max_i C_{1,i}/D_i^2
\]
代入同一个阈值。两者有限，所以存在有限充分尺度，使该组所有相对方差同时不超过 \(\tau\)。还可与均值误差阈值、另行证明的线性几何响应阈值取最大。

这是“先固定有限测试，再选择尺度”的结论，不是“给定一个尺度，对所有分辨率的测试统一小噪声”。

还可得到准确的渐近速率。参考均值和缩放异常使 \(\lambda^2\mathbb EA_\lambda/D=1+O(\log\lambda/\lambda^2)\)，且 \(d_\lambda^2\to1\)。所以对每个固定测试，
\[
\lim_{\lambda\to\infty}\lambda^2
\frac{\operatorname{Var}(A_\lambda)}{(\mathbb EA_\lambda)^2}
=c_1\ge\frac1{9\pi^2}>0.
\]
最后一个下界来自第5节的正规零模。新制备达到弱噪声极限，同时保留明确的量子噪声主阶；没有宣称方差严格为零。

更一般地，若 \(\mathbb EY^2=1\) 且有限 \(v=\operatorname{Var}(Y^2)\) 不随尺度消失，同一准确公式给相对总方差趋于 \(v\)。因此原 bounded A 的极限是 \(3/4\)，而真实制备的幅度平方误差也会形成噪声底。若能独立认证 \(|Y^2-1|\le\kappa\) 且二阶矩仍为1，则 \(v\le\kappa^2\)；符号概率本身不会引入这个能量噪声底，幅度一致性需要实际校准。

### 分辨率负控

在四维无质量 Minkowski 真空，归一化短距测试
\(F_\varepsilon(x)=\varepsilon^{-4}F(x/\varepsilon)\)
与二点函数的精确齐次性，直接给出二次应力方差
\(C_0(F_\varepsilon)=\varepsilon^{-8}C_0(F)\)。
因此不能一边改变测试分辨率，一边把 \(c_0,c_1\) 当作固定常数。当前曲背景的定理也没有提供对所有 \(F\) 的共同数值上界。

## 4. 实际局部测试的全谱线性噪声界

选择标准 bump
\[
b(x)=
\begin{cases}
\exp[-1/(1-x^2)],&|x|<1,\\
0,&|x|\ge1,
\end{cases}
\]
以及
\[
F(\eta,\chi)=
b\!\left(32(\eta-3/32)\right)b(8\chi).
\]
时间支撑为 \((1/16,1/8)\)，径向支撑为 \(\chi<1/8\)。径向函数依赖 \(\chi^2\)，在球心平滑；边界处无限阶平坦。整个支撑满足
\[
\chi+\eta\le1/4<\arcsin(1/\sqrt3),
\]
确实位于原认证内区。

写 \(F=h(\eta)w(\chi)\)。由同一个原始制备，
\[
B=\sqrt{27}\int h(\eta)
\left[\int w(x)\Phi'(\eta,x)d\Omega_3\right]d\eta.
\]

### 全模式增长控制

在制备区间 \([-1/8,-1/16]\)，[原态合同](../../continuation/SOURCE.md)中的实现插值的是 \(a\)，并有 \(S'\ge0\)。令
\[
a_0=\sqrt3,\quad
b_a=\sqrt{3\cos(1/4)},\quad
a_1=\sqrt{3\cos(1/8)}.
\]
由 \(|a_s'|\le S a_{\rm ph}'+(a_0-a_{\rm ph})S'\) 及 \(a_s\ge b_a\)，
\[
\int_{\rm prep}|a_s'/a_s|
\le\frac{a_0+a_1-2b_a}{b_a}.
\]
从 \(-1/16\) 经转折点0到测试末端 \(1/8\)，总对数变差可取
\[
r_\star=
\frac{a_0+a_1-2b_a}{b_a}
+\log(a_0/a_1)+\log(a_0/b_a).
\]
实际证书给出 \(r_\star<1/16\)。

静态过去的每个非零模式满足 \(\beta=0\)。瞬时 Hamilton 系数增长给
\[
|\alpha|\le\cosh r_\star,\quad |\beta|\le\sinh r_\star,
\]
因此对所有 \(k\ge2\)，
\[
|u_k'(\eta)|^2
\le\frac{e^{2r_\star}}{2a(\eta)^2}\,\omega_k,\qquad
\omega_k=\sqrt{k^2-1}.
\]
这一界包含全部模式，没有 K 截断。

在单位 \(S^3\) 的完整球谐基上，由 Parseval 和 Cauchy，
\[
\sum_{k\ge2,l}\omega_k|w_{kl}|^2
\le\|w\|_2\|\nabla w\|_2.
\]
简并度已经由完整 \(l\) 求和计入，不能再遗漏或重复乘 \(k^2\)。于是非零模式满足
\[
C_{1,\ne0}
\le
27\,\frac{e^{2r_\star}}2
\left(\int\frac{h}{a}d\eta\right)^2
\|w\|_2\|\nabla w\|_2.
\]

程序以每个一维积分2048格的有向 Riemann 包围计算全部积分。每格用函数的全区间范围；对 bump 导数平方使用精确最大点 \(x^4=1/3\)，不以普通浮点误差估计冒充积分证书。

实际有向积分给 \(D\in(5.45142\times10^{-5},5.48291\times10^{-5})\)，以及包含正规零模的严格上界
\[
\boxed{c_1<1722.590.}
\]
精确有理上下端点见 result.json。此处界的是线性量子项完整全谱，不是完整应力方差。

## 5. 正规零模的精确份额

使用原 \(Y_0=1/\sqrt{2\pi^2}\)、\(\operatorname{Var}p=3/2\) 和守恒零模动量。对于任意本节合法密度测试，
\[
\boxed{\frac{C_{1,0}}{D^2}=\frac1{9\pi^2},\qquad
\frac{C_{0,00}}{D^2}=\frac1{648\pi^4}.}
\]
两者不依赖测试形状。它们分别是线性项的零模贡献与二次项的零—零模贡献。由于模式块正交独立，其他贡献不能用来负抵消这些份额；但这些数只是全量的份额/下界，不能当作全量噪声的上界。

数值程序把第一项加到非零模式全谱上界中，再用精确/有理源各自的均值下界换算。第二项只作为精确交叉核验保留。

## 6. 已完成与剩余数值责任

在 \(\lambda=8192\) 上，已认证：

- 两个源分支的 \(d_\lambda^2>0\) 与同一全段均值误差下界。
- 当前局部测试线性量子噪声相对总均值平方的完整全谱上界：精确相关源小于 \(2.568348\times10^{-5}\)，显式有理源小于 \(2.568336\times10^{-5}\)。
- 完整应力噪声若要小于1%，二次参考常数 \(c_0\) 必须另外被认证低于回执中给出的正预算；程序没有假定该条件已经成立。

一个共同的具体后续门槛是：若再认证 \(c_0<4.4894\times10^{13}\)，则这两个源分支在8192尺度上的完整相对方差均小于1%。回执保存了两支各自更准确的有理预算；本轮没有把这个待证条件填写为通过。

尚未认证的是完整 \(C_0\) 的定量上界。它涉及二次应力的双模式/双点结构，不能从旧平均 RSET 尾界直接继承，也不能通过去掉高频项获得合法上界。Hadamard 有限性足以证明上面的有限测试族存在定理，但不足以确定给定 \(\lambda\) 的完整数值噪声门。

本文不把应力噪声直接称为度规噪声。若把线性几何 Green 核用于噪声传播，还须检查初值端点、时间开关、空间涂抹和约束条件产生的有效测试域；不光滑的 Heaviside 核不能自动代入本处 \(C^\infty_0\) 定理。

## 7. 验证与物理范围

check.py 独立核验方差多项式、零模归一、阈值方程、完整制备变差界、实际局部积分以及两个源分支的全谱线性噪声上界。旧源和均值证书逐字节绑定到 d6ec9eda，并在运行前后检查 SHA；源码未变的旧模式计算不重跑。

新增模式 ODE 积分为0。没有新硬件数据、没有新增 Lean 证明。新制备、同形测量单元、自由场、Hadamard 参考和半经典均值规则均为明确物理输入；本轮没有据此宣称它们已由 Core 唯一导出。
