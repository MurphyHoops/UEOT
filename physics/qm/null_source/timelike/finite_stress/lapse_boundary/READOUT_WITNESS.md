# 明确的 proper-expansion 测试与有限参数下的拒收

本页固定 QUIET_WINDOW 的同一 c=exp(−20000)、b(c)、incoming 态和 σthin，
不把近静态渐近式当作固定参数证书。先证明一个明确读数确实看见初始列，
再分别计算原 fullmode R 与修复后 W1 的成本。
结论只对这份 source-GNS 线性候选成立，不是实际已制备度规的测量方差。

## 1. 固定物理时钟测试，不用逐背景选波形

令 σF 是冻结完整响应的 fast 根，r=σF/A，且
\[
 \beta(x)=Z^{-1}e^{-1/[x(1-x)]}\mathbf1_{(0,1)},\quad
 Z=\int_0^1 e^{-1/[x(1-x)]}dx,\quad
 g(\tau)=r\beta(r\tau-16).                                      \tag{W1}
\]
g 非负、光滑、单位积分，支持在 [16A/σF,17A/σF] 模型固有时。
使用 PREPARED_READOUT P1 的同一实际 proper-time pullback F_U；
不用静态 F0 替换实际 F_U。

Z≥e^(−9/2)/3 来自 [1/3,2/3]。逐项微分并用
max(y^m e^(−y))=m^m e^(−m) 给
\[
 \|\beta'\|_\infty<1000,\quad\|\beta''\|_\infty<10000,\quad
 \|g'\|_\infty<2\,10^5,\quad\|g''\|_\infty<2\,10^7 .
\]
取 Ts=18/σF<2·10^−5，γ=24A 仍用原来的权重，有 γTs<40。
所有测试与实际 pullback 都在这个更短的区间内；
不以原 T=1/50 的大指数权重掩盖短区间估计。

## 2. 全部 Green 核给出非零初端，未只保留 fast pole

在中间 Bromwich 线 γm=σF/2 上，
冻结的完整因子分解 P=(s²−r1)(s²−r2)Fspec 给
\[
 G_0(t)=R_F e^{\sigma_Ft}+G_m(t),\qquad
 |G_m'(t)|\le {e^{\gamma_m t}\over
                    2c_{\rm spec}\gamma_m^2\delta_{1m}},
 \quad\delta_{1m}=1-r_1/\gamma_m^2 .                           \tag{W2}
\]
这里 |s²−4γm²|≥|s|²，且 Re(−Fspec(s²)/s)>0 给这条线的界。
冻结区间证明 prefactor<3，R_F σF<−11/30；
slow pole、其他模及轮廓余项全部留在 Gm 中。
故在 [16/σF,17/σF] 上
\[
 G_0'(t)<-{11\over30}e^{16}+3e^{17/2}<-3\,10^6 .
\]
静态 F0=−A g'(At)，分部积分无端点项，
\[
 r_0=(G_{p,0}^*F_0)(0)=\int g(At)G_0'(t)dt<-30,               \tag{W3}
\]
因为 A<10^5 且 ∫g(At)dt=1/A。

记 ε=||U||E4,future<e^−1158。|τ−At|<4ε 和 W1 的导数界给
||F_U−F0||∞<10^14ε。保留 γTs<40 后，
\[
 \|F_0\|_{Y^-}<e^{65},\quad
 \|F_U-F_0\|_{Y^-}<e^{75}\epsilon,\quad
 \|F_U\|_{Y^-}<e^{66}.
\]
ACTUAL_INVERSE 中 M0<e35、qinv<e42ε 的独立 advanced 逆，
连同 M_U^* 的乘子和 terminal Hardy trace 给
\[
 |(G_{p,U}^*F_U)(0)-r_0|<e^{145}\epsilon<1 .                  \tag{W4}
\]
例如 action-adjoint H4 差<e144ε，M* point correction<e104ε；
|z(0)|≤√(5/32)γ^(−7/2)||z''''||Y−<||z''''||Y−。
W4 因而有足够余量，不依赖 cancellation 的浮点测量。

实际 raw pressure 测试 q_F=−a²G_p^*F_U 满足
\[
 \boxed{q_F(0)>29A^2}.                                       \tag{W5}
\]
所以不减初端的 sharp-start p(q_F) 有已证明的 K³ 方差发散。
这里的非零是证明，不是“通常不为零”的假设。

## 3. 原 fullmode R 的完整源成本

同一估计给 |q_i'−3h_iq_i|<A²e105。
incoming 零模 primitive 的固定相位满足 |A² I_i|≤3ε，
故 |A²I_i(q_i'−3h_iq_i)|<A²。PREPARED_READOUT 的精确系数于是给
\[
 \alpha_D>{28\over3V_0A^2}>0.
\]
保留同一态的 C–R 交换块，原 fullmode R 满足
\[
 \mathrm{RMS}\,R(q_F)\ge {|\alpha_D|E_z\over\sigma_{\rm thin}\sqrt{\mu_2}}
 >400.                                                       \tag{W6}
\]
最后一界只使用 Ez>8·10^5、A²<7·10^9、V0<20、
σthin<2.2·10^−7、μ2<1/3。

W6 是这个 fullmode 初端减除选择的绝对 proper-expansion 线性读数；
不是源压力相对 RMS，也不是已建立物理度规的“400 倍误差”。
有限低模边界完成可以改变 W6。
CONSTRAINT_RESIDUAL 已独立证明这份原 R 未满足 density 行。

## 4. 修复后必须重算：实际有限 c 的反三角预算

MIXED_BOUNDARY 的 λ=1 修复精确抵消旧 αD 主项。
本节不转用 W6；直接在同一 source GNS 中保留全部交叉。

### 4.1 固定源的有限向量界

原 normalized annular profile 是
varpi(x)=Zb^(−1/2)exp[−1/(1−x²)]，|x|<1。
Zb≥exp(−8/3)，令 y=(1−x²)^−1，则
varpi'=−2xy²varpi，
varpi''=(4y⁴−12y³+6y²)varpi。
由相同指数极值界得 ||varpi'||∞<10、||varpi''||∞<200。
在冻结参数 8·10^4<A<10^5、eN<10^6、
2·10^−7<σthin<2.2·10^−7 下，
完整 radial 支持能量由冻结中心加 σ 验证小于 10^6；从 [-1,1] 上 sup 界转 L² 时保留 √2。
对每个原源支撑向量，有保守范数（不是范数平方）
\[
 \|Z_Q\psi_N\|<10^8,\quad
 \|D\psi_N\|<10^{15},\quad
 \|Z_P\psi_N\|<10^{22}.                                      \tag{W7}
\]
本轮只新验算这些显式预算；canonical uncertainty 原理本身不是新定理。

零模 H_i−AδH_in 的系数依次为
−A²h_i'/2、h_i−A²h_i'I_i、
h_i I_i−A²h_i'I_i²/2。
用 |I_i|<10^−14、W7、高模 pair 主项的精确抵消和
Σj=0³||V^(j)||L1(past)<5ε，得到
\[
 \|H_i-A\delta H_{\rm in}\|_2<e^{60}\epsilon .
\]
原 μ2>1/128 和 Aσthin>0.016 给
\[
 \boxed{\|H_i\|_2>10^{-3}}.                                  \tag{W8}
\]
zero–shell 的交叉没有被当成独立噪声；这里是同态向量三角界。

### 4.2 完整 R 的有限上界

保留 PREPARED_READOUT P3 的 terminal Hardy 因子 γ^−1：
\[
 \|q_F\|_{H^3}\le {768 A^2M_0\over\gamma(1-q_{\rm inv})}
                   \|F_U\|_{Y^-}<e^{117}<e^{120}.             \tag{W9}
\]
其中前因子<e51，不能丢 γ^−1 后沿用同一数字。
w=q/(3V0a⁴)、r=w''+3hw'+Vw 给
||w||H3<e122、||r||H1<e123，
||r||1+||w||1<e124。
实际 zero+shell 的 Q,H0 中心化范数<e50，
故 low RMS<e174。全高模 Bessel 界给 high RMS<e126。
由共同 GNS 三角不等式，
\[
 \|R(q_F)\|_2<e^{175}<e^{200}.                               \tag{W10}
\]
这些大幅留余量的界只为固定 c 的严格拒收服务。

### 4.3 一次选参的 h_i 仍严格正，但过小

b(c)≤1.1c，冻结解析系数给 nonlinear part 初导
|Θv_i|≤C0 r0²<e202 c²<c。
因此
\[
 0<h_i<1.1(937000)c+c<e^{14}c=e^{-19986}<e^{-19980}.            \tag{W11}
\]
没有数值下溢、重新选参或重新执行几何 ODE。

MIXED_BOUNDARY 中 Λ(q)=−q_i/(3V0A⁴h_i)，W5 给
|Λ(q_F)|>10^−11/h_i。
W8–W11 的反三角式保留全部同源 cross：
\[
 \mathrm{RMS}\,{\cal W}_1(F_U)
 \ge |\Lambda(q_F)|\,\|H_i\|_2-\|R(q_F)\|_2
 >10^{-14}e^{19980}-e^{200}
 >\boxed{e^{19000}} .                                       \tag{W12}
\]

## 5. 验收结论和下一门

原 R：平滑源与 pressure 弱行通过；density 残差不为零。
修复 W1：两条齐次弱行及同源正 Gram 通过；
这个明确 proper-expansion 读数在固定 c 下不处于受控弱涨落范围。
因此拒收该具体修复为当前分支的受控弱涨落候选。

W12 不是物理 spacetime 方差的实验预测，也不是非线性解发散定理。
它没有排除改变实际准备过去、完整裸源态、约束量子化空间、
或不同初始几何列的方案。它说明平均源噪声很小和加权逆存在，
均不足以签收正常、稳定、可校准的引力准备。
接下来要审查 action 强制的初始动量–源相关能否由正常联合态和实际准备实现，
同时保留其完整总源与尺度预算。
