# 全记录的完整重整化应力余项

## 1. 验收对象

本节在 PROFILE 的同一个实际辅助过去 in-state 上估计完整双场 AE rho 与 p，
保留实际零模之外的全部 k>=2 模及两场 k=2 的八个热振子。
它给 EVOLUTION 领先阶历史的完整 mean-SCE 方程残差。
度规和量子态沿整段一致，没有逐时选不同参数根。

这是明确新准备的参考态族，不是原局域 instrument 的完整输出态。
小残差也不自动给出附近精确 SCE 解：其因果响应、高阶导数与逆算子仍须控制。

## 2. 精确模式与四阶比较函数

scaled conformal 导数 D=b d/dtau，p=sqrt(kappa)omega_k，omega_k=sqrt(k^2-1)。
实际模式 w 满足 w''+(p^2-V)w=0，并在辅助静态过去给精确正频初值。
取比较频率

Omega=p+a/p+c/p^3，a=-V/2，c=(V''-V^2)/8。

比较函数 (2Omega)^(-1/2)exp(-i integral Omega) 只用于误差证明，
不替换实际无限阶 Hadamard 态。令 Q=Omega/p，其精确方程缺陷为

R=p^-4[-2ac-c^2/p^2-c''/(2Q)
       +a''(a+c/p^2)/(2Q)+(3/4)(a'+c'/p^2)^2/Q^2]。

设 A=V0/2,A1=V1/2,A2=V2/2，
B=(V2+V0^2)/8，B1=(V3+2V0V1)/8，B2=(V4+2V1^2+2V0V2)/8。
在 P0=16，A/P0^2+B/P0^4<1/2，所以 p/2<=Omega<=3p/2。
由直接绝对值估计

CR=2AB+B^2/P0^2+B2+A2(A+B/P0^2)+3(A1+B1/P0^2)^2，

有 |R|<=CR/p^4。精确与比较初值在静态过去吻合。
Duhamel 的 oscillator energy 范数给

N_delta=(|delta'|^2+p^2|delta|^2)^(1/2)
<=C_delta p^(-9/2)，C_delta=L CR exp(V0 L/P0)。

令 D0=A+B/P0^2，D1=A1+B1/P0^2，
CA=sqrt[(3/2+D1/P0^3+H/P0)^2+1]，
CD=C_delta sqrt[(1+H/P0)^2+1]。
实际模式的 energy/pressure 与比较函数之差均不超过
Cs/p^4，Cs=2CA CD+CD^2/P0^5。

四阶比较函数减去原 omega 型局部减除项的余项为 Ce5/p^5 或 Cp5/p^5：
Ce5=A^2D0+2AB+B^2/P0^2+H^2(AD0+B)+H(5A1D0+2B1)+D1^2；
Cp5=Ce5+(2/3)(2AB+B^2/P0^2+2D0^3)。
这些保守常数由真实精确模式的误差导出，不是有限模采样的拟合尾。

## 3. 完整谱和与对数抵消

取 P=17、K=floor(P/sqrt(kappa))，k>K 时 p_k>P0。
三维完整尾满足

kappa^(3/2) sum_{k>K} k^2/p_k^4 <=16/[9(P-1)]，
kappa^(3/2) sum_{k>K} k^2/p_k^5 <=(4/3)^(5/2)/[2(P-1)^2]。

转回固定 AE 的 k 减除时，以 ptilde=sqrt(kappa)k，
omega-counter 与 k-counter 的差再由
[bcoef+|A_j|+4|C_j|]/ptilde^5 控制。

定义
A_e=h^2/2，C_e=V^2/8+h^2V/4-hV'/4；
A_p=h^2/2-V/3，C_p=-V^2/8+h^2V/4-hV'/4+V''/12。
b_e=1，b_p=1/3，
T1_j=A_j-b_j kappa/2，T3_j=C_j+kappa A_j/2-b_j kappa^2/8。

令
L_j=kappa^(3/2) sum_{2<=k<=K} k^2 tbar_j(p_k)，
U_j=kappa^(3/2) sum_{k>K} k^2[tbar_j-(b_j ptilde+T1_j/ptilde+T3_j/ptilde^3)]，
S1=sum_1^K k，S3=sum_1^K k^3，
J_K=H_K+0.5 log kappa，ell_b=log(xc b^2/4)+2gamma。

原 k=1 减项不能丢。保留它后，完整双场真空密度正好是

rho_vac=lambda^4/(2pi^2 b^4) {
L_e-kappa^2 S3-kappa E1 S1+U_e
+E3[19/30+ell_b/2-J_K]+J3/720-(h^2V+kappa h^2)/4 }。

压力正好是

p_vac=lambda^4/(2pi^2 b^4) {
L_p-kappa^2 S3/3-kappa P1 S1+U_p
+P3[19/30+ell_b/2-J_K]+(J3-L3)/2160
+[4hV'-8h^2V+3V^2+4kappa V-8kappa h^2+kappa^2]/24 }，

J3=3h^4+6kappa h^2+3kappa^2，
L3=12Vh^2-12h^4+12kappa V-12kappa h^2。

其中 E/P 系数就是上面的 T 系数。完整局域恒等式 H1=144E3、
(H1-T1_tensor)/3=144P3 使 log kappa 精确抵消。
利用 K=floor(P/sqrt(kappa)) 有
log P<J_K<=1+log P；不能单独把局域 log a 当全应力的发散。

## 4. 低频、热壳与正窗上界

PROFILE 的真实能量不等式给低频物理 rho 与 |p| 各不超过

lambda^4 *34 P^2(P+1)^2/(8pi^2)。

正窗 b>=1，故其余括号直接使用 b^-4<=1。
又 kappa^2 S3<=[P(P+1)/2]^2、kappa S1<=P(P+1)/2。
原八个热振子的物理密度附加项及 |pressure| 不超过
4 n_old *34 sqrt3 lambda^4/pi^2；没有重复乘两场因子。

ultraviolet.py 对所有局域项、低模、无限高模和热壳作有向传播，
给出 rho/p 以正尺度 3lambda^2/2 归一后的两个残差均 <4.2e-6。
该归一不是除以可能过零的压力分量，也不是度规误差。

完整量子涨落需另用光滑时间窗；瞬时空间平均二次应力的方差不能由 mean 界推出。
