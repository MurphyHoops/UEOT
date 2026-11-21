# 同一实际态的全部线性响应与随机约束

本文件接在 README 的实际双场 Einstein-static 平均历史之后。固定一次 M2、预算 b、半径 A 和真实物质常数 U；不随时间重选源、种子或真空。

## 1. 合法 retarded 态族

在任意有限观测段令 a_delta(eta)=A exp(delta e^(s eta))，s>0，之后可共同光滑延为正几何。过去所有扰动 jets 指数趋零。高模用同一个静态 incoming positive-frequency 条件定义 Jost KG 解：过去 Volterra 核可积，任意阶分部积分给 all-order WKB 渐近，故保持 Hadamard。不是在观测端重取 instantaneous vacuum。

零模保持同一 canonical P、同一 asymptotic intercept Q：

\[
q_\delta=Q+P\left[(\eta-\eta_0)/A^2+
\int_{-\infty}^{\eta}(a_\delta^{-2}-A^{-2})\,d\zeta\right].
\]

Var P=A^2/2 不随 delta 调整；同一 coherent momentum 与同一 Y,Z law 也不变。这定义合法 off-shell 几何—态族，其切向响应在下述特征根满足全部线性化 mean 方程；没有证明该切向已经积分成 nonlinear SCE 解族。

记 epsilon=delta e^(s eta)，则一阶 h=epsilon'，q=-1-epsilon''。

## 2. 高模真实 KG 响应

omega_k=sqrt(k^2-1)，v0=e^(-i omega_k eta)/sqrt(2omega_k)。方程

\[
\delta v_k''+\omega_k^2\delta v_k=\epsilon''v_k^{(0)}
\]

的固定 incoming 解为

\[
\delta v_k/v_k^{(0)}=\frac{s}{s-2i\omega_k}\epsilon.
\]

因此

\[
\delta|v_k|^2=\frac{s^2}{\omega_k(s^2+4\omega_k^2)}\epsilon,
\quad
\delta|v'_k|^2=-\frac{\omega_k s^2}{s^2+4\omega_k^2}\epsilon.
\]

裸 energy e_k=|v'-hv|^2+(k^2-1)|v|^2，
裸 pressure s_k=|v'-hv|^2-(k^2-1)|v|^2/3，得到

\[
\delta e_k=0,\quad
\delta s_k=-\frac{4\omega_k s^2}{3(s^2+4\omega_k^2)}\epsilon,\quad k\ge2.
\]

正规零模不可代入 omega=0 的振子真空公式。
固定 canonical P 给 e_1=s_1=|P|^2/a^2，基值 1/2，
delta e_1=delta s_1=-epsilon。

## 3. 全部减项

密度减项

\[
e_k^d=k+E_1/k+E_3/k^3,\quad
E_1=(h^2-1)/2,\quad
E_3=[q^2-2(h^2-1)q+2hq']/8.
\]

在静态 q=-1、h=0 上 delta E_1=delta E_3=0。
因此全部数值密度贡献

\[
\delta\rho_{\rm num}
=-4\rho_{\rm num}\epsilon-\epsilon/(4\pi^2A^4).
\]

压力减项

\[
s_k^d=k/3+P_1/k+P_3/k^3,
\]

\[
P_1=q/3+h^2/2+1/6,\quad
P_3=-q^2/8-q''/12-(3h^2+1)q/12+hq'/4.
\]

所以 delta P_1=-s^2 epsilon/3，
delta P_3=(-s^2/6+s^4/12)epsilon。
含 k=1 的正规零模和减项后，完整收敛 symbol 为

\[
D_{\rm num}(s)=-1+s^2/2-s^4/12+
\sum_{k=2}^{\infty}
\left[-\frac{4k^2\omega_ks^2}{3(s^2+4\omega_k^2)}
+\frac{s^2k}{3}+\frac{s^2/6-s^4/12}{k}\right].
\]

## 4. 固定 AE contacts

直接使用 [Anderson–Eaker](https://arxiv.org/pdf/gr-qc/9906055) Eq. (10),(12),(14)，并注意论文 trace 是 rho-3p。mu=1、m=xi=0、K=1，
C_A=19+15[log(A^2/4)+2gamma]。

H1 系数 C_A/(17280pi^2)，H3 系数 1/(2880pi^2)；静态 H1^0_0=-18/A^4、H3^0_0=3/A^4，delta C_A=30epsilon。
线性 trace 变化为

\[
\delta H^{(1)\mu}_{\ \ \mu}
=(-36\epsilon^{(4)}+72\epsilon'')/A^4,\quad
\delta H^{(3)\mu}_{\ \ \mu}=12\epsilon''/A^4.
\]

完整解析密度和压力为

\[
\delta\rho_{\rm an}
=-4\rho_{\rm an}\epsilon-\frac{\epsilon}{32\pi^2A^4},
\]

\[
\delta p_{\rm an}=-4p_{\rm an}\epsilon+
\frac{C_A\epsilon^{(4)}/1440-(C_A-29)\epsilon''/720-\epsilon/96}{\pi^2A^4}.
\]

这里 -1/96 包括 log 变化、trace 和基准压力前因子，不可只保留高阶项。A/B 两线分别读过一手原文核对，stability.py 再核对符号代数。

定义

\[
Z(s)=D_{\rm num}(s)+C_As^4/360-(C_A-29)s^2/180-1/24.
\]

则

\[
\delta p_q=[-4p_q+Z(s)/(4\pi^2A^4)]\epsilon,
\]

\[
\delta\rho_q=[-4\rho_q-9/(32\pi^2A^4)]\epsilon
=-3(\rho_q+p_q)\epsilon.
\]

最后一式独立核对零模、全部 local terms 与守恒，不是对静态 rho_q(A) 参数族直接求导。

## 5. 不重跑模式的无限尾认证

1<=s<=3，u=k^-2，z=s^2/4，d_s=z-1。
单项可重写为

\[
\frac{s^2k}{3}\left[1+(1/2-z)u-
\frac{\sqrt{1-u}}{1+d_su}\right].
\]

对 0<=u<=1/4、-3/4<=d_s<=5/4，设 f=sqrt(1-u)/(1+d_su)。直接求导并用
1+d_su>=13/16、sqrt(1-u)>=4/5、(1-u)^(3/2)>=3/5，得到

\[
|f''|\le20/39+400/169+12800/2197=57380/6591<9.
\]

Taylor 余项给单项绝对值<=27/(2k^3)。
sum_(k>=2) k^-3 <=1/8+integral_2^infinity x^-3 dx=1/4，
所以无限和绝对值<=27/8，|D_num|<=125/8。
尾 k>N 的绝对界是 27/(4N^2)。

在 2lambda<A<3lambda，
|B(A^2)|<1/20，0<C_A<400，从而

\[
\left|\frac83 B-D_0+\frac Z{4\pi^2}\right|
<3.326006048<4.
\]

新 checker 还以 k=2..128 的新代数响应和及严格尾检查 s=1,2,3；这是新 response symbol 求值，未传播任何旧模式。

## 6. 固定参数的齐性增长根

两场、固定 U 与总 coherent momentum 给特征式

\[
\mathcal D(s)=s^2-4+
\frac2{A^2}\left[\frac83B-D_0+\frac Z{4\pi^2}\right]=0.
\]

同一 mean 历史上 Hamiltonian 变化满足
delta rho_tot=-3epsilon/A^2=delta rho_geo，空间方程给上式。因而这不是仅满足压力方程的 off-shell 模。

连续性与统一尾界给 D(1)<0、D(3)>0。存在正根且

\[
|s-2|=\frac{|s^2-4|}{s+2}
<\frac8{3A^2}<6.208818\,10^{-10}.
\]

固有增长率 s/A，时间是模型单位。静态背景的尺度变分不是时间重标产生的 gauge 模；齐性 lapse 只改 clock。

这里证明线性增长模存在，不证明根唯一、非线性失稳或线性解可积成 nonlinear SCE 族。尤其不能无限延长有限幅度指数扰动的线性近似。

## 7. 全部总能量噪声与线性随机约束的矛盾

在 proper-time 法向投影下，几何密度为
rho_geo=3(H^2+a^-2)/2。a=A(1+epsilon)，背景 H=0，故

\[
\delta\rho_{\rm geo}=-3\epsilon/A^2.
\]

完整物质守恒一阶积分是

\[
\delta\rho_{\rm ind}=-3(\rho+p)\epsilon+C_{\rm state}
=-3\epsilon/A^2+C_{\rm state}.
\]

固定同一 retarded in-state 意味着 C_state=0。将实际源的空间平均能量噪声 xi_rho 接入 Einstein–Langevin 00 约束，要求

\[
0=\delta G_{nn}-2\delta\rho_{\rm ind}=2\xi_\rho.
\]

然而 RECORDS 的完整能量谱精确给

\[
\operatorname{Var}\xi_\rho=
\frac{M_2^2\operatorname{Var}R}{4A^{12}}
+\frac{M_2(1+b)}{4\pi^2A^{10}}
+\frac1{16\pi^4A^8}>0.
\]

两个零模正规 Gaussian 保证最后两项严格正。高模静态 vacuum 的总 Hamiltonian 是定值，U 与 AE local terms 也是 c-number，不会消除这一方差。局部真空噪声仍然存在。

因此 **固定物质参数、固定 retarded 初态、只允许齐性 FLRW 一阶几何响应的随机完成不存在**。这不是普遍量子引力 no-go，也不否定 mean 解。确定性增长模是零源齐次解，与这个约束矛盾并不冲突。

允许改变初态能量积分常数时，必要条件变成 C_state+xi_rho=0；不能不声明地加入这种相关。换 Green 函数、抹掉增长极点或增加一阶初始 H 都不能产生约束缺失项，因为 H^2 从二阶才出现。

## 8. 关闭错误捷径后，下一任务是什么

在相同 A 上仅随机选择 H0，首个约束是 3H0^2=2delta rho，不能覆盖负能量偏差支。经典零阶 M=A^4、U=A^-2 的诊断给

\[
3(AH)^2=\delta M/M+12(\delta a/A)^2
-6(\delta M/M)(\delta a/A)+21(\delta M/M)(\delta a/A)^2+\cdots.
\]

它显示平方根尺度和二阶几何责任，但不是新量子解。改变 H、a 或 higher jets 必须同步给合法 Hadamard Cauchy 数据；固定 AE 的量子二阶 contacts 尚未认证。

精确总零模能量本征态在原非紧实实标量的正规 Hilbert 表示中不可归一化，不能通过免费后选择消噪。可研究窄能量窗、相关 C_state、背景/源联合分布或非线性响应；都要实际构造、检查正性/CCR、约束和传播。

下一验收因此锁定为 **约束相容的状态—几何联合初值族及其共同演化**，之后才接真正局域引力探针。

参考背景：
[Hu–Roura–Verdaguer gr-qc/0402029](https://arxiv.org/abs/gr-qc/0402029)区分 intrinsic 与 induced 波动；
[Losic–Unruh gr-qc/0408011](https://arxiv.org/abs/gr-qc/0408011)处理不同 perfect-fluid 模型的二阶约束。
这些论文不代替本轮特定自由量子态、AE symbol 和随机约束推导。
