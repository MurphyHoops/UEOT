# 显式曲率平方变形的因果反演与非零变形反馈反例

[检查器](check.py) · [精确回执](result.json) · [局部几何算子](../local/README.md) · [共同合同](../CONTRACT.md)

直接基线：c57e2f411e58dc1dae60de8f3c97fbd680e46d8b。

## 0. 固定物理工作点与研究对象

继承 AE/Hadamard 参考处方、物理 μ=1、原总方程 G=2T、源侧 α=0 和无额外有限曲率项。AE 约定的 H1=−HR，故
\[
\boxed{(z,b_{\rm extra},c_{\rm extra})=(1,0,0)}.
\]
这些数值已经固定。RW 均值上 Weyl² 不可见，不会重新开放新的物理参数。无额外有限项也不表示固定参考响应的接触项为零。

实际待解问题是
\[
\boxed{D_T h-4a^2\Pi_{\rm ref}^{TT}[h]=f},\qquad f=4a^2F,
\tag{0}
\]
其中 F 是外加 mixed TT 应力，f 是吸收 Einstein 归一后的强迫；Pi_ref 包括同一固定参考处方的全部局部接触项、显式 metric 变分和因果非局域响应。本包没有收齐或反演 Pi_ref。

本节反演 Einstein 加显式常系数 R²/C² 变形的辅助几何子算子 L_z,b,c。以下简记 b=b_extra、c=c_extra。非零参数改变该子算子；没有证明同一给定背景也是相应变形理论的自洽背景。非零 c 的反例只针对这个辅助族，不能套到原物理工作点的零额外系数。

## 1. 背景与精确局部算子

取无量纲空间 TT 扰动
\[
g=a^2[-d\eta^2+(\gamma+h)_{ij}dx^idx^j],\quad
a^2=3\lambda^2\cos2\eta,\quad
0\le\eta\le T=3/16,\quad\lambda=32768.
\]
gamma 是单位三球度量，
\[
\mathcal H=-\tan2\eta,\quad
R=-2/(\lambda^2\cos^32\eta),\quad R'/R=6\tan2\eta.
\]
对 l≥2 的全部 TT 模式，
\[
-\Delta_\gamma Y_l=[l(l+2)-2]Y_l,\quad
\kappa_l=l(l+2),\quad\nu=l+1.
\]
定义
\[
D_T=\partial_\eta^2+2\mathcal H\partial_\eta-\Delta_\gamma+2,\qquad
W=(\partial_\eta^2-\Delta_\gamma+2)^2+4\partial_\eta^2.
\]
局部几何证书给出
\[
\delta(H_R)^i{}_j=a^{-2}(R D_T+R'\partial_\eta)h^i{}_j,\quad
\delta(H_C)^i{}_j=-a^{-4}Wh^i{}_j,
\]
\[
W_l=(\partial_\eta^2+l^2)(\partial_\eta^2+(l+2)^2).
\]
mixed Hessian 的变分为 −R'h'/(2a²)：下指标的 −R'(Hh+h'/2) 与升指标补项 +HR'h 抵消。不能遗漏升指标接触项。

辅助族定义为
\[
\boxed{L_{z,b,c}=(z-4bR)D_T-4bR'\partial_\eta+(4c/a^2)W}.
\tag{1}
\]
本节解 Lh=f，f 为已知强迫。把依赖未知 h 的 4a²Pi_ref[h] 移到右侧，不能据此套用已知强迫定理并宣布完整反馈已解。

## 2. 非零 c 的准确时间依赖因果方程

仅在 c≠0 的辅助族内，令
\[
q=z-4bR,\quad\gamma_c=a^2/(4c),\quad m=\gamma_c q.
\]
gamma_c'=2H gamma_c，q'=−4bR'，故 Lh=f 等价于
\[
\boxed{W_lh+(mh')'+\kappa_lmh=\gamma_c f}. \tag{2}
\]
准确背景系数是
\[
m=\frac{3\lambda^2z}{4c}\cos2\eta+\frac{6b}{c\cos^22\eta},
\]
\[
m'=-\frac{3\lambda^2z}{2c}\sin2\eta+
\frac{24b\sin2\eta}{c\cos^32\eta}.
\]
这里不冻结系数，不要求 q 非零，也不凭空加入 (4c/a²)'h'''。

指定四项零过去数据 h(0)=h'(0)=h''(0)=h'''(0)=0，向过去延拓为零。它们防止四阶分布导数产生额外初值 delta 项；这不是给原物理工作点增加初始条件。

W_l 的因果核为
\[
G_l(u)=\frac{\sin(lu)/l-\sin((l+2)u)/(l+2)}{4(l+1)},\quad u\ge0.
\tag{3}
\]
其前三项初值为零、G'''(0)=1、u>0 时 W_lG=0。两个二阶 oscillator 核卷积给
\[
|G_l(u)|\le\int_0^u v(u-v)dv=u^3/6. \tag{4}
\]
准确导数满足
\[
G_l'=\frac{\sin(\nu u)\sin u}{2\nu},\quad
G_l''+\kappa_lG_l=\frac{\sin(\nu u)\cos u}{\nu}.
\]
对 (mh')' 两次分部积分，利用全部端点条件，得到 h=U+Vh，
\[
U_l(t)=\int_0^tG_l(t-s)\gamma_c(s)f_l(s)ds,
\]
\[
\boxed{K_l(t,s)=\frac{\sin(\nu(t-s))}{\nu}
[-m(s)\cos(t-s)+\tfrac12m'(s)\sin(t-s)]},\quad
(V_lh)(t)=\int_0^tK_l(t,s)h(s)ds. \tag{5}
\]
全部真实时间依赖保留在 m、m' 中。

空间因果性由 W=(D0+2i∂η)(D0−2i∂η)、D0=∂η²−Δ+2 得到；两因子都是具有同一光锥的正常双曲算子。因果 Green 的复合、局部微分和收敛的因果迭代保持支撑。源空间已指定为 TT，未把非局域 TT 投影当作局部源操作。

## 3. 全模式唯一解与可计算余项

令
\[
\Gamma=\sup|\gamma_c|,\quad M_0=\sup|m|,\quad
M_1=\sup|m'|,\quad A=M_0+TM_1/2.
\]
由 |sin(νu)|/ν≤u、|sin u|≤u，
\[
|K_l(t,s)|\le A(t-s),\qquad
\|V^n\|\le A^nT^{2n}/(2n)!. \tag{6}
\]
谱上一致界直接给任意实 s 的 C([0,T];H^s_TT) 算子范数；不额外乘模式简并度。于是
\[
\boxed{h=\sum_{j\ge0}V^jU}
\]
绝对收敛，无需小耦合或 ||V||<1。差解 w=V^nw 及 (6) 直接证明唯一性。

全场是 CH^s mild 解；每个模式是经典四阶解，完整方程分布意义成立。初值按模式数据和零过去延拓解释，不声称所有四阶时间导数仍在同一 H^s。

响应上界为
\[
\boxed{\|h\|\le\Gamma\|f\|
\sum_{j\ge0}\frac{A^jT^{2j+4}}{(2j+4)!}}. \tag{7}
\]
A>0 时该级数为 [cosh(√A T)−1−AT²/2]/A²；A=0 时为 T⁴/24。
截断 j=0,...,N 的尾为
\[
\boxed{\|{\rm tail}\|\le\Gamma\|f\|
\frac{A^{N+1}T^{2N+6}}{(2N+6)!}\cosh(\sqrt A T)}. \tag{8}
\]
若 rho=AT²/[(2N+8)(2N+7)]<1，也可用首漏项/(1−rho)。
式(8)由此后的阶乘比至少为 (2j)! 得到。这是有限时间存在、唯一性和连续依赖；很大的有限界不构成长时间稳定性结论。

## 4. 精确有理参数常数

当前区间有 cos(3/8)≥119/128、sin(3/8)≤3/8、tan(3/8)≤48/119<1/2。因此
\[
\Gamma\le\frac{3\lambda^2}{4|c|},\quad
A\le\frac{(411/512)\lambda^2|z|+(13467648/1685159)|b|}{|c|}.
\]
lambda=32768 时
\[
\boxed{\Gamma\le805306368/|c|},\quad
\boxed{A\le[861929472|z|+(13467648/1685159)|b|]/|c|}. \tag{9}
\]
这些是非零 c 辅助族的常数，不是原物理工作点的误差条。c→0 的界发散表明四阶/二阶奇异极限，不能据此判断 c_extra=0 的物理模型不稳定。

## 5. 非零 Weyl² 块经过旧二阶逆后的反例

保持实际时间依赖背景，固定 l=2、kappa=8，
\[
d=a^{-2}=\sec2\eta/(3\lambda^2),\quad p=-2\tan2\eta,\quad
D=\partial_\eta^2+p\partial_\eta+\kappa,
\]
\[
P=d\partial_\eta^2-d'\partial_\eta+d''+(\kappa+4)d.
\]
记 r=tan2η，精确算子除法给
\[
DP=dW+\mathsf u\partial_\eta+\mathsf v,\quad
\mathsf u=48dr(1+r^2),\quad
\mathsf v-\mathsf u'=12d(1+r^2)(\kappa-8r^2). \tag{10}
\]
检查器用 r'=2(1+r²) 的多项式递推检查每阶系数。

取固定 0≤chi≤1，紧支撑于 (1/16,1/8)，t*=3/32 附近为1；Y2 为 H^s 归一 TT harmonic。令
\[
h_n=\chi(\eta)\cos[n(\eta-t_*)]Y_2,\qquad\|h_n\|_{CH^s}=1.
\]
全部初始 jets 为零，故
\[
D_{\rm ret}^{-1}(dWh_n)=Ph_n-D_{\rm ret}^{-1}(\mathsf u h_n'+\mathsf v h_n).
\]
对余项中的 h' 分部积分，其核是
\[
-\mathsf u(s)\partial_sR_D(t,s)+(\mathsf v-\mathsf u')(s)R_D(t,s).
\]
端点由 R_D(t,t)=0 和初始支撑消去，余项只作用于 h_n。

能量缩放的基本解界给
\[
|R_D|\le e^{P_0T}/\sqrt\kappa,\quad
|\partial_sR_D|\le e^{P_0T}(1+P_0/\sqrt\kappa),\quad P_0=\sup|p|.
\]
初时导数是 ∂s R_D=−Phi11+p(s)R_D，符号不可漏。
用 r≤1/2、d≤2/(3λ²)、P0≤1、√kappa≥2、e^T≤1/(1−T)≤4/3，
\[
|\mathsf u|\le20/\lambda^2,\quad
|\mathsf v-\mathsf u'|\le100/\lambda^2.
\]
余项范数至多
\[
(3/16)(4/3)[20(1+1/2)+100/2]/\lambda^2=20/\lambda^2.
\]
另外 |d''+(kappa+4)d|≤12/λ²，d(t*)≥1/(3λ²)。中心处 h_n'=0、h_n''=−n²Y2，因此
\[
\boxed{\|D_{\rm ret}^{-1}(dWh_n)\|_{CH^s}\ge(n^2/3-32)/\lambda^2}. \tag{11}
\]
非零额外 c 的反馈下界是 4|c|(n²/3−32)/λ²；n²>96+3λ²/(4|c|) 时已大于1。任意固定非零 c 和有限 λ 的同空间全频算子无界。

R² 和 Einstein 修正不能抵消 n² 增长：
\[
D(Rh)=R Dh+2R'h'+(R''+pR')h,
\]
因此 D_ret^-1(RDh+R'h')=Rh−D_ret^-1[R'h'+(R''+pR')h]，再分部积分后余项 C→C 有界；Einstein 修正是恒等倍数。

在原物理工作点 c_extra=0 时，额外 Weyl² 反馈贡献为零。式(11)不证明实际 Pi_ref 增益无界或有界；Pi_ref 的量子 logarithmic 结构须独立导出。无限高频是否处于另行规定的有效理论频带也未由此证明，反例不是实际失稳判断。

## 6. 二阶支路、边界负控及剩余责任

辅助族 c=0 时为 qD_T h+q'h'=f。inf|q|>0 则是正则二阶方程，需两项初值；不包含 q 过零退化。实际工作点 q=1，几何子算子就是 D_T，但 (0) 中的参考量子响应仍须保留。

纯 W_l 的 cos(lη)−cos((l+2)η) 前两项初值为0、二阶初值为4(l+1)；这是漏掉额外初值的负控。正确 l=2 频率2多项式为0，错误的 (∂²+8)² 为16，是漏曲率项负控。

仅作常系数辅助诊断，m 常数时平方频率 r 满足
\[
r^2-(2\kappa+4+m)r+\kappa(\kappa+m)=0,\quad
{\rm discr}=(m+4)^2+16\kappa.
\]
m<−kappa 时有负平方频率。此例不用于判断实际背景稳定性，只区分存在因果逆与没有增长支路。

order reduction 是需要独立频带、舍弃支路和误差责任的低能近似，不是同一精确方程的改写。

本节关闭显式辅助几何块的反演、全模式界及级数余项。固定 AE/Hadamard 的全部接触项、完整 Pi_ref、物理反馈逆、量子噪声传播、非线性 SCE 与硬件实现仍开放。若日后从固定参考响应中导出同一常系数块，必须按实际导出值核对本定理适用条件。

检查器冻结 c57 操作合同与主审输入，绑定本轮 local 三文件及自身源码说明；不运行旧检查器，不新增模式/几何 ODE。Core 只读，GI 排除。
