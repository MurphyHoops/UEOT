# 原 AE 处方下的作用量响应与共同对数主部

本页继续完成同一作用量到实际响应的映射，不新增重整化自由参数。
原KERNELS的逐模式、ω→k转换、参考k=1减项、两个场的占据、
实际零模和全部局部AE项都保留。结果是齐次action行的精确重写，
不是已经完成的非静态全场因果逆定理。

## 1. 重整化的 Q 变量及完整 action 行

记D=∂η，D_U=D²+2hD，D_U†=D²−2D(h·)，V=h′+h²，X_k=|v_k|²。
由原KERNELS §3，逐模有
\[
 -e_k+3p_k=D_U^\dagger X_k.
\]
§4给
\[
 e_\omega^d-3p_\omega^d
 =-D_U^\dagger\left({1\over2\omega}+{V\over4\omega^3}\right).
\]
§6的两个固定转换常数K1,K3与§7参考k=1项分别贡献
D_U†(K1/2+K3V/4)与D_U†(−3/4−V/4)。
定义
\[
 \bar Q_U=\sum_{k\ge2}k^2\!
 \left[X_k-{1\over2\omega_k}-{V\over4\omega_k^3}\right]
 +{K_1\over2}-{3\over4}+{K_3-1\over4}V+8nX_2 .       \tag{A1}
\]
8n含两个场与完整k=2简并，不能改成4n。
该和在实际严格内域收敛；有限K证明后，按同一smooth域取极限。

以N=1、固定共形lapse的u变分为准，
\[
 \Gamma_{m,u}=D_U^\dagger\bar Q_U
     +2V_0a^4\rho_z-4V_0a^4U_0-4t_{\rm an}.         \tag{A2}
\]
这里t_an完整沿用冻结KERNELS，含ell=ell0+2U。
引力行是Γ_g,u=3V0a²(1+V)，所以总行恰等于
\[
 \Gamma_u=3V_0a^2(S+E/2).                           \tag{A3}
\]
没有把固定共形lapse与固定固有lapse的变分混成同一列。

## 2. 实际态的因果 Q 响应

对零过去的smooth w，δV=D_Uw。
保持同一incoming态、全部端点运输不变，
\[
 \delta X_k(t)=\int \chi_{U,k}(t,s)\delta V(s)\,ds,
 \quad
 \chi_{U,k}(t,s)
 =2\theta(t-s)\operatorname{Im}[v_k^*(t)^2v_k(s)^2]. \tag{A4}
\]
静态时χ=θsin[2ω(t−s)]/(2ω²)，Laplace乘子
1/[ω(z²+4ω²)]，符号和二倍频都固定。

按同一AE减项定义
\[
 \mathcal K_U=
 \sum_{k\ge2}k^2\left(\chi_{U,k}-{1\over4\omega_k^3}I\right)
 +{K_3-1\over4}I+8n\chi_{U,2}.                       \tag{A5}
\]
有限K上是普通核加接触项，全场作为同一renormalized smooth响应的分布极限。
δQbar=K_U D_Uw；不能分别将裸χ和无限局部减项求和。

由δD_U†=−2D(w′·)，精确得到总作用量行的导数
\[
\begin{split}
 \mathcal H_U w={}&3V_0a^2[D_Uw+2(1+V)w]
  +D_U^\dagger\mathcal K_U D_Uw
  -2D(\bar Q_Uw')\\
 &-4V_0a^4\rho_z w-16V_0a^4U_0w
  -4\delta t_{\rm an}[w].                           \tag{A6}
\end{split}
\]
A6的每一个局部项都有冻结表达来源。
它是physical retarded variation；符号“Hessian”不表示retarded核时间对称，
完整CTP两支核仍按各分支定义。

## 3. 与压力逆比较前，先使用正确的 action 归一化

在actual E=S=0背景、零过去/零初始约束荷方向上，Ward给
\[
 e(t)=2e^{-U(t)}\int_{\eta_i}^t e^{U(s)}h(s)s_{\rm lin}(s)\,ds
 =\mathcal J_U s_{\rm lin}(t).
\]
这里s_lin=δS，且不是慢根s_*。
若L_Uw=δS，则
\[
 {\mathcal H_U\over3V_0A^2}
 =e^{2U}(I+\mathcal J_U/2)L_U.                       \tag{A7}
\]
初始约束荷非零时另有明确的e^{−U}齐次项，不能省略。
静态U=0时J=0，A7还原同一冻结P(D)。

## 4. 四阶对数主部的精确代数组织

写K_U=K_0+R，保持所有局部接触不动。有严格算子恒等式
\[
\begin{split}
 D_U^\dagger K_U D_U-D^2K_0D^2
 ={}&D^2K_0(2hD)-2D[hK_0D^2]\\
 &-4D[hK_0hD]+D_U^\dagger R D_U.                    \tag{A8}
\end{split}
\]
因此在正确action行归一化后，没有额外的U D⁴logD乘法主项。
前三项显式把h放在至少一个一阶差因子上；最后项必须从
真实χ_U−χ_0核估计，不能仅凭“U很小”把它宣告有界。

其余差项已完全列明：引力、零模、U0的有限低阶差，
−2D[(Qbar_U−Qbar_0)D]及−4(δtan(U)−δtan(0))。
最后一项至四阶、系数含完整动态ell差2U；它不是新的可调常数。

## 5. 接下来真正需要闭合的范数

CAUSAL_DOMAINS已给静态G0:L²γ→H⁴γ。
为了得到actual-U逆，应在共同prepared域证明
\[
 \left\|(\mathcal H_U/(3V_0A^2)-L_0)G_0\right\|<1,
                                                               \tag{A9}
\]
或者提供同样充分的Volterra/resolvent控制，并处理A7及初始荷。
原P具有四阶对数增长；裸H⁴与完整L0 graph域不可等同。
A8将风险集中到明确的R核与乘法交换项，但没有自动证明A9。

本页关闭的是精确作用量重写、固定AE接触绑定、因果Q核以及
比较主部的正确归一化。任意tensor Hessian、actual全场inverse、
正常联合geometry态和真实装置准备仍继续验收。
