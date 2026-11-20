# 三种引力约束与输入无关的操作

本节的定理是对当前模型合同的审查，不向原 mean-SCE 任务追加强算子约束。
固定经典几何、两个正规零模、与零模独立张量因子的自由高模，以及既定重整化。

## 1. 不同要求的关系

平均方程要求 G(g)=tr(rho T[g])。给定完整经典记录 r 的条件平均方程要求
G(g_r)=tr(rho_r T[g_r])。强约束则要求 C_r rho_r=0（或相应平方二次型期望为零）。

只要平方矩存在，逐记录精确分解为

E tr rho_r (C_r/G_r)^2
= E Var_r(T_r)/G_r^2 + E (G_r-tr rho_r T_r)^2/G_r^2.

因此条件平均闭合并不消除本征量子涨落。反过来，强约束无正规解不否定平均方程。
前轮 >7% 是固定源边缘、fixed incoming A、特定正频 E4 小域与中央 CQ 几何下的定量结果；
本节的谱定理量词不同，不能互换。

## 2. 正规强约束没有核

H_zero=L2(R2,d2P)，S0=(P1^2+P2^2)/C，C>0。对每个实数 s，
集合 |P|^2=C s 的二维 Lebesgue 测度为零，故 E_S0({s})=0。

令 H_high 为独立高模张量因子上的任意自伴算符，alpha != 0。
对乘积向量，alpha S0 tensor I + I tensor H_high 在单点 c 上的谱测度为

integral mu_zero({(c-h)/alpha}) d mu_high(h) = 0.

由 Tonelli 与乘积向量的稠密性，单点谱投影为零。该结论无需高模谱离散、
无需能量半有界，也允许态在两个因子间纠缠。于是没有正规密度算符使
tr rho (alpha S0 + H_high - c)^2=0。可测中央 CQ 几何的每个正规条件态同样如此。

**独立张量因子不可删除。**仅有强交换不够，例如 H=-alpha S0 会直接抵消。
约束后的分布态、rigging map、另一物理内积、非交换几何或相互作用总源不在此定理内。

## 3. 不存在核不等于存在统一误差下限

取无量纲 S=P1^2+P2^2、v_n=1/(4n^2)，让动量为二维纯 Gaussian，
均值 (sqrt(1-2v_n),0)、协方差 v_n I。则

E S=1，Var S=1/n^2-1/(4n^4)>0，Var Q_i=n^2.

每个 n 的态都是正常 Schwartz 态，残差范数趋零而没有任何一个态达到零。
此序列改变原源谱及准备资源，不反驳前轮固定边缘的 7% 结果。

## 4. 固定 prior 与普适反馈不是同一个合同

固定一次原 prior rho0 与 instrument I_y 后，预先标定 m(y)=E_rho0[S0|y]。
以该固定函数选择后续控制，是合法的输入无关策略；其整体 record map 仍可线性/CP。
若对每个未知输入 rho 都重新计算 E_rho[S0|y]，则改变了控制律，
不能不经证明就称为同一个量子通道。

对 Gaussian 源仪器 K_y=f_y(S0)，有限精度时 f_y(s)>0。
若存在输入无关 m(y) 令所有正常输入都满足条件源均值等于 m(y)，则须有

K_y (S0-m(y)) K_y=0，

与连续非平凡谱及 f_y>0 矛盾。具体正规反例取径向波函数

psi_a(P)=(pi C)^(-1/2) sqrt(630) (s-a)^2(a+1-s)^2 1_[a,a+1](s)，s=|P|^2/C，

a=1 与 3。其源均值分别 a+1/2、方差 1/44，每个 Var Q_i=24(a+1/2)/C。
两者在每个实 y 都有正记录密度，但后验均值分别严格处于 (1,2) 和 (3,4)。
任何共同 m(y) 对至少一个输入的绝对均值误差严格 >1/2。
有限零模矩修改保留既有高模 Hadamard 性。

一般普适逐记录 mean 合同可写为 I_y^*(C_y)=0；strong 合同进一步要求
I_y^*(C_y^2)=0。它们不是可由一个 prior 的数值根自动推广的式子。

## 5. O(2) 协变不能替代 affine 操作

上述两个径向态张成的二维子空间上，O(2) 作用恒等。
令 Z=|psi_1><psi_1|-|psi_3><psi_3|，f(rho)=(tr Z rho)^2。
f 为 O(2) 不变函数，但同一混合态既可分解为 psi_1/psi_3 等权，
也可分解为 psi_±=(psi_1±psi_3)/sqrt2 等权。
若逐纯分支将 f 当可读几何，前者总输出 1，后者总输出 0。

没有额外实际经典标签时，这违反同一密度算符的 affine record law。
在通常远端 steering 的假设下，可进一步构成信号反例；
若准备标签确已提供，则是不同协议资源，不能混同。

Core 已提供指定记录律之后的商、接口和误差运输，不负责从 O(2) 不变性
自动选择 Hilbert/Born、物质内容或引力反馈。下一物理门是一个实际输入无关、
因果局域且能结算总源的联合 instrument/feedback 模型。

本节为直接证明；semantics.py 核验积分、有限矩阵反例与精确有理恒等式，
不冒充已在 Lean 完成泛函分析形式化。


## Complete normal source-QND instruments cannot select a universal mean

A stronger instrument statement does not depend on the particular Gaussian reader. Assume a normal complete instrument has bounded Kraus densities and its nonselective adjoint fixes every spectral projection \(P\) of \(S_0\). Then
\[
\int\sum_j[P,M_{y,j}]^\dagger[P,M_{y,j}]\,dy=0.
\]
A countable generating family of rational spectral intervals shows that its Kraus operators commute with \(S_0\) almost everywhere. If one additionally asks that every input state, for a given outcome \(y\), have the same posterior mean \(m(y)\), polarization of the expectation identity gives
\((S_0-m(y))E_y=0\). The source spectrum is atomless, so its singleton projection is zero, and hence \(E_y=0\) almost everywhere, contradicting completeness.

This excludes a universal input-independent exact mean selector within that source-only normal QND contract. It does not exclude the actual fixed-prior Bayesian instrument, nor a model where a different high/device source compensates the total constraint. The instrument assumptions and outcome density matter; no stronger claim about all abstract singular instruments is made.
