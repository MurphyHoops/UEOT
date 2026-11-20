# 后释放共同历史：存在性闭合后的物理审查

日期：2026-11-20（Asia/Shanghai）。基线：741209b3c010bc6dcfe695d8d3b71cba4448fe3f。Core 只读，GI 不在范围。本文与代码是物理研究候选，没有晋升正式书稿、Lean 证明或经验身份。

**本轮得到一个正向数学闭环：对此前任一实际初片根，保留同一完整态和固定源强，在初端保留固定准备区间并施加预定光滑数学驱动后，存在一条新的共同几何—量子态历史，在正长度释放区间满足完整无驱动平均方程。**

**随后继续物理审查，证明这项准备驱动必在某个开区间违反类光能量条件（NEC）。** 另构造合法双场完成模型，证明原场降噪可被完整总源的旋转不变性消去到全部记录概率律。这两个后续结论收窄了下一任务：实际量子准备系统、总源涨落和真实引力仪器，不能由平均历史存在性代替。

[实际态范数](state_norms.json) · [完整反馈](feedback.json) · [后释放存在证书](history.json) · [全阶解析证明](REGULARITY.md) · [总源定理](total_source.json) · [独立审查](REVIEW.md) · [复核回执](review.json) · [六项验证](run_verification.py) · [总回执](verification.json)

## 1. 本轮裁决

| 问题 | 结果与范围 |
|---|---|
| 原历史从 \(0\) 立即无驱动延续 | 仍被此前全根法向导数定理排除 |
| 同一实际态的规则反馈输入 | 零模、全部根、有限模盒、无限尾均已认证 |
| \(T=2^{-21}\) 上完整差分预算 | \(\kappa<0.164799\)，不单独等同自映射或存在性 |
| 新构造的总时间窗 | \(T=2^{-40}\) |
| 完全保留参考历史 | \([0,T/4]\)，所有候选使用同一个固定区间 |
| 完全撤除数学驱动 | \([3T/4,T]\) |
| 实际参考积分残差 | \(D<3.735471570\,10^{-6}\) |
| 新窗完整收缩率，含预定驱动几何依赖 | \(<6.494552\,10^{-12}\) |
| 自映射余量 | \(>0.0613793585\) |
| 固定 \(M_2\) 的端点射击 | 唯一 \(\alpha_*\)，\(|\alpha_*|<1.120641471\,10^{-5}\) |
| 最终几何和态 | 同窗 \(C^\infty\)；同一实际态沿该几何 KG 传播，保持 Hadamard |
| 释放后方程 | 加速方程与 Hamiltonian 约束在同一正长度区间同时成立 |
| 本驱动的普通 NEC 实现 | 排除；必有 \(\rho_D+p_D<0\) 的开区间 |
| 双场完成的完整不变记录 | 旧／新总变差 \(0\)，等先验误判 \(1/2\) |
| 物理统一、装置及实验结论 | 仍开放；已把下一验收收窄为明确总源与仪器问题 |

所有显示数值向外舍入；精确有理端点见 JSON。后释放固有时长度约 \(1.29\,10^{-8}\) 个模型单位，不是秒。这里没有长时稳定性、EFT 有效性或宏观观测窗认证。存在性由解析定理与区间不等式给出，没有计算一个数值轨迹或 \(\alpha_*\) 的具体近似值。

## 2. 保持的物理对象

仍为最小无质量实标量场、原正规零模、原静态种子、闭球面模式与原有限内核解释：
\[
\lambda=32768,\quad \mu_{\rm AE}=1,\quad \alpha_{\rm AE}=0,\quad
G_{ab}=2\langle T_{ab}\rangle .
\]
没有增加有限曲率项。

任取此前已证明存在的初片根
\[
|\theta_*|<8.433194\,10^{-9}
\]
并一次性固定
\[
M_2=27\lambda^4-54\lambda^2Q_\rho(\theta_*).
\]
\(\theta_*\) 是整条过去历史的参数；下文 \(\alpha\) 是整条准备协议的常数。二者都不是逐时选择的根。

同一参考历史在物理段为
\[
a_{\rm ref}(t)=\lambda\sqrt{3\cos2t}\,e^{\theta_*t^2/2},
\quad h_{\rm ref}=-\tan2t+\theta_*t,
\quad q=-1-h'-h^2,\quad f=q'.
\]
当前初片 \(q_0=1-\theta_*,f_0=0\)。完整 KG Cauchy 核从原静态过去传来，没有在 \(0\) 重置。新候选按自身的 \(q,h,a\) 传播这个核。

此前全根结论
\[
Q_p'(0)\in[-13.769547,-11.113955]
\]
继续成立，并排除保持原过去、从 \(0\) 立即无驱动的光滑延拓。本轮改变的是释放协议，不是这一导数或初片 jets。

## 3. 从实际模式证书得到态范数

定义瞬时频率 \(\Omega_k=\sqrt{k^2+q_0}\)，实际 \(v_k=a u_k\)。采用
\[
n_k=\frac{\Omega_k|v_k|^2+|v_k'|^2/\Omega_k-1}{2},
\]
\[
C_k=\frac{\Omega_k|v_k|^2-|v_k'|^2/\Omega_k}{2}
+i\Re(\bar v_kv_k').
\]
数值输入是中心化参考态，经典位移源 \(M_2\) 另行固定，不把两者混作占据数。

本轮消费此前的 \(k=2,\ldots,512\) 认证盒，未重跑任何模式。对全根半径 \(r_\theta\)，在原能量框中加入已证的
\[
\Delta X\le e^{H_*}(e^{r_\theta/64}-1).
\]
之后对整个中心和误差盒用 \(\theta\) 区间转到瞬时框。因
\(\Omega_\theta\ge\sqrt{k^2-1}=\omega_k\)，框变换范数为
\(\sqrt{\Omega_\theta/\omega_k}\)。二次型误差为
\[
\|X\|\varepsilon+\varepsilon^2/2.
\]
两个 coherence 分量的联合界来自两个 Pauli 矩阵的反对易关系，不能分别放大后漏掉共同误差。

### 3.1 零模与无限尾

正规零模保留原种子
\(u_1=1/\sqrt6,\ p_1=-i\sqrt{3/2}\)，并使用真实过去积分
\[
I_0=\int_{-1/8}^0 A_{\theta_*}^{-2}\,dt
\in\left[
\frac1{24e^{r_\theta/64}},
\frac{e^{r_\theta/64}}{24\cos(1/4)}
\right].
\]
于是
\[
|v_1|^2=\tfrac12+\tfrac92I_0^2,\quad
|v_1'|^2=\tfrac12,\quad
\Re(\bar v_1v_1')=\tfrac32I_0 .
\]

无限尾复用此前覆盖整个 \(|\theta|\le1/256\) 的 \(D_5\)：
WKB2 基的 \(|\beta_k|\le\sinh(D_5/k^5)\)。在初片 \(W'=0\)，从 WKB2 转瞬时基，得到
\[
|\beta_k^{\rm inst}|\le b_4/k^4+b_5/k^5,\quad k\ge513.
\]
写 \(x=k^{-2}\)、\(A=1+q_0x\)、\(B=A-q_0''x^2/(4A)\)，可用
\[
c_4\ge\frac{|q_0''|}
{8A(\sqrt A+\sqrt B)(AB)^{1/4}},
\]
\[
b_4=c_4\cosh(D_5/513^5),\quad
b_5=\sqrt{1+(c_4/513^4)^2}\,D_5\cosh(D_5/513^5).
\]
代码用有向区间取上界。由 \(n=|\beta|^2\)、\(|C|\le|\beta|\sqrt{1+|\beta|^2}\)，全部尾和由积分判别封闭，不截断无限场。

| 实际全根范数 | 向外上界 |
|---|---:|
| \(N_0=\sum n_{k,0}\) | \(0.060969289\) |
| \(S_1=\sum k|C_{k,0}|\) | \(42.841740\) |
| \(S=\sum k(n_{k,0}+|C_{k,0}|)\) | \(43.026175\) |
| \(S_2=\sum k^2|C_{k,0}|\) | \(13697.978605\) |
| \(N_{1,0}=\sum k n_{k,0}\) | \(0.184434977\) |

这些有限阶范数用于定量反馈；全阶 Hadamard 正则性由独立的静态种子证明承担。

## 4. 完整反馈预算

继续使用实际 Wick 平方
\[
P=\frac1{2\pi^2}\sum k^2\left(|v_k|^2-\frac1{2k}+\frac q{4k^3}\right),
\]
\[
C_{\rm AE}=19+15[\log(a^2/4)+2\gamma],\quad
J=2C_{\rm AE}f+(60-4C_{\rm AE})hq-56h-\frac{56}{3}h^3.
\]
实际迹方程的积分形式是
\[
P'-2hP-\frac J{480\pi^2}
=K_{\rm init}+\int_0^t
\left[6a^2q-\frac{2M_2}{a^2}
-\frac{(h')^2+(h^2+1)^2}{16\pi^2}\right]ds
+6\int_0^t aF\,ds.
\]

### 4.1 规则量子响应

令 \(0\le q\le Q=2\)、\(|f|\le F_*=1\)、\(c=(8\pi^2)^{-1}\)。
共同初态的比较满足
\[
\Delta P'=\mathcal T_s\Delta f+\Delta H
-\frac1{4\pi^2}\int(f_1D_1-f_2D_2),
\quad
\|\Delta H\|\le\frac{T^2S_1}{2\pi^2}\|\Delta f\|.
\]
其中 \(\mathcal T_sf=-c\int f'(s)\log[2\sin(t-s)]ds\)，
\(D\) 为减去普适 \(\sin2k(t-s)\) 后的实际核。

可直接复核的统一常数为
\[
I=F_*T/4,\quad
N_T=N_0+e^{2I}\left[\frac{F_*TS_1}{2}
+\frac{F_*^2T^2(2N_0+\zeta_4)}{16}\right],
\]
\[
Z_p=\zeta_p+2N_0,\quad
L_n=2e^{3I}\left(\frac{TZ_2}4+\frac{F_*T^2Z_4}4+
\frac{F_*T^3Z_3}8\right),
\]
\[
r_T=\frac{T^2/6}{1-T^2/6},\quad
J_T=\frac{T^2}2\left(\frac12-\log2T+r_T\right),
\]
\[
A_T=(Q\zeta_2+2N_T)T+QJ_T+\frac{Q^2\zeta_3T^2}8+
\frac{Q^2\zeta_2T^3}6,
\]
\[
B_T=T^2\zeta_2+TJ_T+\frac{3Q\zeta_3T^3}4+
\frac{Q\zeta_2T^4}3+2N_T(T^2+T^3/2)+2TL_n.
\]
因此
\[
L_{\rm reg}=\frac{T^2S_1}{2\pi^2}
+\frac{A_T+F_*B_T}{4\pi^2}.
\]
在 \(T=2^{-21}\)，实际态给 \(L_{\rm reg}<4.121011\,10^{-8}\)。

### 4.2 其余全部项

设 \(d_0=3,H=d_0T,E=e^{2HT},\ell_*=d_0T^2/2\)，
\[
\mathcal A=a_0^2e^{2\ell_*},\quad
\mathcal B=a_0^{-2}e^{2\ell_*},\quad
L_h=ET^2/2,\quad L_\ell=ET^3/6.
\]
可取
\[
L_P=cT(1-\log2T+r_T)+TL_{\rm reg},
\]
\[
P_{\max}=\frac{S+3q_0^2\zeta_3/16}{2\pi^2}+F_*L_P.
\]
常 \(q\) 只作为同初始核的 Wick 平方比较，不作为一个新 Hadamard 候选替换实际态。

完整右端 Lipschitz 账包含：
\[
\begin{aligned}
L_{\rm full}={}&L_{\rm reg}+2(P_{\max}L_h+HL_P)\\
&+\frac{(|60-4C_0|+120\ell_*)(QL_h+HT)
+120HQ L_\ell+56(1+H^2)L_h}{480\pi^2}\\
&+3\mathcal A T^2+\tfrac Q2\mathcal A ET^4
+\tfrac16M_2\mathcal B ET^4\\
&+\frac{d_0T^2+\frac23HE(d_0+1+H^2)T^3}{16\pi^2}
+c(\ell_*+F_*L_\ell)+L_{\rm driver}.
\end{aligned}
\]
冻结接触项以后的变量接触贡献已经列入，没有遗失固定 AE 局部项。旧因果逆界 \(M<75\) 在 \(T\le2^{-21}\) 仍有效；正实对数极点保留。

在 \(T=2^{-21}\)，即使先取条件性 \(\|F\|_{L^1}\le1\) 的驱动几何预算，
\[
\kappa=ML_{\rm full}<0.164799.
\]
这一步只有完整差分控制。真正自映射和驱动射击在下一节另行认证。

## 5. 从实际参考残差闭合自映射

定义加速缺陷和 Hamiltonian 缺陷
\[
B=a''+a+\frac{M_2}{3a^3}-\frac{a^3}{3}(\rho_q-3p_q),
\]
\[
C=a'^2+a^2-\frac{M_2}{3a^2}-\frac23a^4\rho_q.
\]
同一固定源、同一实际态满足 \(C'=2a'B\)。令
\[
R_{\rm ref}(t)=6\int_0^t a_{\rm ref}B_{\rm ref},\qquad R_{\rm ref}(0)=0.
\]

### 5.1 不重算旧模式的残差界

取 \(T=2^{-40}\)。参考几何的显式区间计算给 \(|q_{\rm ref}''|<9\)，故 \(|f_{\rm ref}|\le9T\)。

比较常 \(q_0\) 的同初态 Wick 演化，
\[
P_{\rm ref}'-P_{\rm ref}'(0)
=H_{\rm const}(t)-H_{\rm const}(0)+\mathcal T_sf_{\rm ref}
+\Delta R_{\rm reg}.
\]
有限块的相干变化用
\[
\frac{2\sqrt3\,T}{\pi^2}\sum_{k\le512}k^3|C_{k,0}|
\]
控制。尾部使用
\[
|e^{-2i\Omega_kt}-1|\le\min(2,2\sqrt3\,kT)
\]
并在 \(K=T^{-1}\) 分割，得
\[
\frac{\sqrt{1+\beta_{\max}^2}}{\pi^2}
\left\{
b_4[2\sqrt3\,T\log(K/512)+2/K]
+\frac{2\sqrt3\,Tb_5}{512}
\right\}.
\]
主项界为 \(9cT(1-\log2T+r_T)\)，规则变化为 \(9TL_{\rm reg}\)。

加入 \(2hP,J\) 和完整积分源。大 Einstein 项与固定源先在初端精确相消：
\[
6a_0^2q_0-\frac{2M_2}{a_0^2}
=36Q_\rho-18\lambda^2\theta_*,
\]
再使用旧 \(|Q_\rho|\le508\) 证书；不能先分别取 \(O(\lambda^2)\) 的绝对值。

最终
\[
\boxed{\|R_{\rm ref}\|_\infty\le D<3.735471570\,10^{-6}.}
\]

### 5.2 固定预定驱动

选 \(C^\infty\) cutoff：
\[
\chi=1\ (t\le T/4),\quad \chi=0\ (t\ge T/2),
\]
以及单调阶跃 \(\Psi=0\ (t\le T/2),\Psi=1\ (t\ge3T/4)\)。
令
\[
H_\alpha=\chi R_{\rm ref}+\alpha\Psi,\quad
|\alpha|\le A=3D,\qquad
\boxed{F_\alpha=\frac{H_\alpha'}{6a_{\rm ref}}.}
\]
这里 \(F_\alpha\) 预先固定，仅使用参考历史；它是数学加速残差协议，并非已实现的完整装置应力。

实际几何 \(r=a/a_{\rm ref}\) 上，正确驱动为
\[
6\int aF_\alpha=rH_\alpha-\int r'H_\alpha.
\]
只有参考几何上才等于 \(H_\alpha\)。其几何 Lipschitz 界为
\[
L_{\rm driver}\le r_{\max}E(D+A)
\left(T^3/3+3T^5/15\right).
\]
这避免了不必要的 cutoff 大导数界。

在半径 \(\rho=1/16\) 的固定缓冲球上，
\[
M(D+A)<(1-\kappa)\rho,
\]
并且
\[
\kappa<6.494552\,10^{-12},\qquad
(1-\kappa)\rho-M(D+A)>0.0613793585.
\]
几何球 \(q\in[0.9,1.1]\)、\(|h'|\le3\) 自动满足。因果性保持同一 \([0,T/4]\) 参考段。因此每个 \(|\alpha|\le A\) 都有唯一 \(C^0\) 固定点。

## 6. 全阶正则性与一次性约束射击

[全阶证明](REGULARITY.md) 从实际静态种子出发，只在高模使用瞬时基，有限低模精确消去其普适 principal 减项。一次 \(t\) 导数后使用 \(\partial_t+\partial_s\) 的对角导数，保留
\[
\partial_tD_{\rm vac}
=(A(t,s)^2-q(t)+2q(s))\log(2\sin(t-s))
-A(t,s)\cot(t-s)+R_{\rm abs}.
\]
规则量子部分因此从 \(C^m\) 增益到 \(C^{m+1}\)。在解上由 trace 方程提升 \(P\)，再以加权 \(C^m\) Banach 范数证明同窗主逆保正则性。归纳得到 \(C^\infty\)，没有缩短到趋零时间窗，也没有假设未经认证的解析 moment 增长。

此时完整态在同一光滑几何上保持 Hadamard，守恒恒等式合法。令 \(t_r=3T/4\)、\(g_\alpha=a_\alpha'/a_{\rm ref}\)、\(\psi=\Psi'\)。有
\[
C_\alpha(t_r)
=-\frac13\int_0^{T/2}g_\alpha'\chi R_{\rm ref}
+\frac{\alpha}{3}\int_{T/2}^{3T/4}g_\alpha\psi.
\]
几何球给 \(|g'|\le3\)、\(g\le-9T/10\) 于 \(\psi\) 支撑上。保守参数界
\[
\|f_\alpha-f_\beta\|\le300|\alpha-\beta|,\quad
\|g_\alpha-g_\beta\|\le900T^2|\alpha-\beta|,\quad
\|g_\alpha'-g_\beta'\|\le900T|\alpha-\beta|
\]
给
\[
C_A\le-\tfrac25DT+450D^2T^2<0,\qquad
C_{-A}\ge\tfrac25DT-450D^2T^2>0,
\]
\[
C_\alpha-C_\beta
\le-\frac{\alpha-\beta}{3}
\left(\tfrac9{10}T-3150DT^2\right)\quad(\alpha>\beta).
\]
端点符号余量 \(>1.35895664\,10^{-18}\)，单调斜率余量 \(>2.72848410\,10^{-13}\)。

故存在唯一 \(\alpha_*\in(-A,A)\)。释放后 \(F_{\alpha_*}=0\)，并由 \(C(t_r)=0\)、\(C'=2a'B\) 得
\[
\boxed{B=0,\quad C=0\quad\text{于 }[3T/4,T].}
\]
这关闭了同一态、同一固定源、同一几何正时间窗的平均方程。它不要求原初片根 \(\theta_*\) 本身唯一。

## 7. 闭合后反思：这条驱动必有 NEC 违反

由缺陷定义数学总源
\[
\rho_D=\frac{3C}{2a^4},\qquad
p_D=\frac{C}{2a^4}-\frac{F}{a^3}.
\]
它严格守恒：
\[
\rho_D'+3h(\rho_D+p_D)=0.
\]
这是残差张量的身份，不是构造了量子装置态。其 trace 为
\(\rho_D-3p_D=3F/a^3\)，与积分 trace 驱动归一化一致。

本轮 \(q>0,h(0)=0\)，所以 \(h'=-1-q-h^2<0\)，全部 \(t>0\) 处于收缩。初片和释放端有
\[
\rho_D(0)=\rho_D(t_r)=0.
\]
在实际参考缓冲段，\(F=B_{\rm ref}\)，且
\[
F'(0)=a_0^3p_q'(0),\qquad
(\rho_D+p_D)'(0)=-p_q'(0)>0.
\]
旧全根证书给
\(\lambda^4(\rho_D+p_D)'(0)\in[11.113955,13.769547]\)。
因此每个根有一个非空初端正区间；没有另行声称其统一数值长度已认证。

令 \(w=-h>0\)。守恒和两端零密度给
\[
0=3\int_0^{t_r}w(\rho_D+p_D),\qquad
\int w(\rho_D+p_D)_+=\int w(\rho_D+p_D)_->0.
\]
连续性迫使存在非空开区间
\[
\boxed{\rho_D+p_D<0.}
\]

所以本驱动不能由始终满足 NEC 的普通齐性正动能源独立实现。量子负应力没有因此被排除，但必须构造实际态与动力学，检验其 RSET 和全部相关。量子能量不等式只能提供必要条件；满足一个不等式不能替代实现性证明。

此外，一个齐性 canonical scalar 若无能量交换、势光滑且不显含时间，并要求释放后的全部应力恒零，则速度与势都为零；KG 唯一性迫使它此前也为同一静止真空。这是另一条具体装置排除，不泛化到有交换、非齐性或量子系统。

平均装置应力释放后为零，不代表装置噪声或场—装置交叉噪声为零。

## 8. 接着关闭总源问题：完整统计的双场反例

原两个制备标签，对 \(\sigma=\pm1\)，分别为
\[
Y_{\rm old}=(\sigma\pm\sqrt3)/2\quad(p=1/2),
\]
\[
Y_{\rm new}=1\quad(p=(2+\sigma)/4),\qquad
Y_{\rm new}=-1\quad(p=(2-\sigma)/4).
\]
二者 \(\mathbb EY=\sigma/2,\mathbb EY^2=1\)，但旧 \(\mathbb EY^4=7/4\)，新为 \(1\)。

加入第二个同参数、同 AE 的真实量子标量场，参考态为两个相同零均值 quasifree Hadamard 态的乘积。它在 species 的 \(O(2)\) 旋转下不变。

设 \(d=\sqrt3/2,\ell\ge1+d,r_y=\sqrt{\ell-y^2}\)，定义
\[
O_y=\ell^{-1/2}
\begin{pmatrix}r_y&y\\-y&r_y\end{pmatrix},\qquad
O_y(0,\sqrt\ell\,u_{\rm cl})=(y u_{\rm cl},r_yu_{\rm cl}).
\]
\(O_y^TO_y=I,\det O_y=1\)。令
\[
\rho_* =W(0,\sqrt\ell\,u_{\rm cl})\rho_{\rm ref}W^\dagger,\qquad
\rho_y=U(O_y)\rho_*U(O_y)^\dagger.
\]
第一场边缘恰好是原 \(W_1(yu_{\rm cl})\rho_0W_1^\dagger\)；没有更换其分布或幅度。

同参数总应力 \(T^{\rm tot}=T^{(1)}+T^{(2)}\) 和对称 AE 减项在旋转下不变。因此任意满足 \(U^\dagger E_AU=E_A\) 的有界记录效应有
\[
\operatorname{Tr}(\rho_yE_A)=\operatorname{Tr}(\rho_*E_A).
\]
两种原混合标签的完整记录概率律相同：
\[
\boxed{\mathsf P_{\rm old}=\mathsf P_{\rm new},\quad
d_{\rm TV}=0,\quad e_{\rm Bayes}=1/2.}
\]
证明直接使用有界效应不变性，没有从有限个矩相等推断分布相等。对任何已建立且保持相同内部对称性的引力通道，结论同样适用；这里没有预设这样的引力通道已经完成。

真实 reservoir 提供自己的量子涨落：
\[
X_y^{\rm tot}=Q_1+Q_2+yL_1+r_yL_2,\qquad y^2+r_y^2=\ell.
\]
例如方差为 \(2V_0+\ell V_1\)，全部高阶和记录律由对称性控制。只添加一个无量子涨落的经典标签补偿项不能获得这个结论。

### 8.1 明确的成本与原几何排除

此处下界仅针对非负相干位移预算：
\[
M_{\rm tot}=\ell M_{\rm field},\qquad
\mathbb EM_{\rm reservoir}=(\ell-1)M_{\rm field}
\ge\frac{\sqrt3}{2}M_{\rm field}.
\]
最小 \(\ell=1+\sqrt3/2\) 取到下界。若总位移预算固定，原场份额最多为
\[
M_{\rm field}/M_{\rm tot}\le4-2\sqrt3.
\]
这改变物质内容与预算，不是原单场模型的免费修复，也不是所有重整化量子能量的普遍下界。

第二场的参考 RSET 也必须计入。对原初片根令
\(r=2Q_\rho/\lambda^2,\ m_*=M_2/(27\lambda^4)=1-r\)，旧证书给
\(|r|\le127/134217728\)。原几何上的新约束为
\[
C_{\rm new}/a_0^2=-(\ell-1)m_*-r.
\]
因此
\[
\boxed{|C_{\rm new}|/a_0^2
\ge\frac{\sqrt3}{2}-
(1-\frac{\sqrt3}{2})\frac{127}{134217728}
>0.866025.}
\]
该合法固定背景双场完成严格不能修复原几何。要研究其共同历史，必须重新求解总物质模型。

抽象受控旋转是合法 unitary，并与双场自由 Hamiltonian 可交换；全局对称操作仍不等于已经给出紧支局域控制器、其应力和 CP 仪器。

## 9. 下一闭环已按结果重排

1. **实际制备可实现性。** 为本次必要的 NEC 违反选择明确量子器件、初态和交换动力学，计算总平均 RSET、守恒与释放；或重新设计准备过去，使现有收缩与零端点预算障碍不再适用。不能把任意残差直接命名为已实现装置。
2. **完整总源涨落。** 计算 \(N_{\rm field}+N_{\rm device}+N_{\rm cross}\) 以及完整推迟响应。双场定理已经排除“原场降噪必然给总引力增益”的普遍断言；必须对固定装置模型逐项判断。
3. **在同一新历史上的仪器与反馈。** 重建实际几何、全部 contacts、约束及规范一致的反馈，再接真实固有钟／探针 CP 仪器。旧固定背景概率、窗口和资源数字不能直接迁移到本次极短释放窗。
4. **物理统一的最终责任。** 半经典平均历史存在只关闭一个必要接口。仍须给出独立物理选择、完整涨落动力学、适用尺度和可区分的经验检验；不以数学闭合自动宣布统一完成。

## 10. 可复核证据与文献

本轮六项检查为实际态范数、完整反馈、精确代数、后释放存在界、完整总源、独立审查。复用49项先前结果，冻结186个旧科学文件；没有重跑旧检查，没有旧／新模式或几何 ODE 数值积分。旧证据通过精确提交、文件散列及已成功的对应提交 CI 绑定。

    python -B physics/qm/null_source/timelike/compatible_evolution/run_verification.py

新 JSON 是70位有向区间算术或精确代数的回执；解析存在和光滑性证明在本文及 REGULARITY 中。执行通过不等于形式化证明或外部同行接受。研究 PR 继续保持 draft。

一手参考用于界定背景和适用条件，本轮特定数值与新构造由上述文件承担：

- [Meda–Pinamonti–Siemssen，2007.14665](https://arxiv.org/abs/2007.14665)：非共形半经典方程与低阶正则性的边界。
- [Gottschalk–Siemssen，1809.03812](https://arxiv.org/abs/1809.03812)：平滑 towing、Hadamard 传播、能量约束射击；不直接套用其 moment 空间假设。
- [Fewster，1201.3295](https://arxiv.org/abs/1201.3295)：自由标量 multiplet 的内部自同构结构。
- [Fewster–Verch，1810.06512](https://arxiv.org/abs/1810.06512)：局域系统—探针耦合、散射与完全正仪器；全局对称操作不能替代这些实现责任。
