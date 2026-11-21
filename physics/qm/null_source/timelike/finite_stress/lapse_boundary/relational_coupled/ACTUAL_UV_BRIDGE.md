# 同一实际背景上的共同截止二阶 CTP 桥

本页新增的是同一实际 incoming 历史、同一 AE 处方、共同有限模式截止的
potential 响应与绝对噪声定量尾，及固定共形 lapse 的 u–u 弱 Hessian 接触尾。
TENSOR_NOISE T8/T11 已给全场实际张量噪声，T16/T22 已给平滑应力尾；
ACTION_RESPONSE A4/A5 已给实际因果 Q 核；ACTUAL_INVERSE I4/I7 已给
全场逆所需的 Laplace/Schur 界。这些结果复用，不重新计为新的存在定理。
本页不证明有限截止逆 G_K 收敛或联合量子几何的全场极限。

## U1. 背景、状态与共同截止

I=[0,1/50]，a=Ae^U，h=U'，V=U''+h²；所有导数为共形时间 eta。
ACTUAL_INVERSE I3/I5 给
\[
 \mu=\sum_{j=0}^3\|V^{(j)}\|_{L^1(-\infty,T]}
 \le4\varepsilon+15\varepsilon^2<5\varepsilon<.1,\qquad
 \varepsilon<e^{-1158}.
\]
固定原 rho_±；k=2 的 NOON 块、正常零模及其相关不重置，k>=3 为
incoming 真空。实变分 f 属 C_c³(I)，离开初末端，不改变初始密度算子
或端点 canonical 运输。实际模式为
v_k=e^(-i omega_k eta)F_k/sqrt(2 omega_k)，omega_k=sqrt(k²-1)。
本页使用冻结模式界，没有重新积分旧模式或几何 ODE。

令 Qosc,K=(1/2) sum_(k=2..K,species,m) q_km²，每壳有 2k² 个实模式。
同一 action 的 potential 反项是 B_K V-H_K V²/8，
H_K=sum_(k=1..K)1/k，B_K=-[K(K+1)+H_K]/4。因此
\[
 Q_K^{AE}=Q_{\mathrm{osc},K}+B_K-H_KV/4,\qquad
 R_K^{AE}=\sum_{k=2}^K k^2\chi_{\mathrm{unit},k}
                   +8n\chi_{\mathrm{unit},2}-{H_K\over4}I,
 \tag{U1}
\]
其中
\[
 \chi_{\mathrm{unit},k}(t,s)
   =2\theta(t-s)\operatorname{Im}[v_k(t)^{*2}v_k(s)^2].
\]
固定 canonical potential 方向的 Qosc 不显含 V，有限 K Kubo 核本身
没有另一个 delta seagull；局部接触严格是 -H_K I/4。

若 X_k=|v_k|²，均值为
\[
 \bar Q_K=\sum_{k=2}^K k^2X_k+8nX_2+B_K-H_KV/4 .
 \tag{U2}
\]
与 ACTION_RESPONSE A1 的 omega 减项表达相等时，必须使用
K1,K=sum_(2..K)[k²/omega-k-1/(2k)] 和
K3,K=sum_(2..K)[k²/omega³-1/k]。参考 k=1 项 -3/4-V/4 保留。
有限 K 直接使用完整 K1,K3 会改变该有限 K action。

U1 的等价写法为
\[
 R_K^{AE}=\sum_{k=2}^K[k^2\chi_{\mathrm{unit},k}-I/(4k)]
                    -I/4+8n\chi_{\mathrm{unit},2}.
 \tag{U3}
\]
最后 -I/4 不能遗漏；若只列 k>=3，低块接触为 -3I/8。
“截断 A5 的 omega 和、保留完整 K3”的另一序列比 U3 多
Delta3,K I，Delta3,K=(K3-K3,K)/4，0<Delta3,K<=1/(2K²)。
这是逐壳差 <=4/k³ 与和尾 <=1/(2K²) 的结果。两序列同极限，
但有限截止不得混用。其余 AE anomaly、gravity、U0 和零模项仍按 A6 保留。

## U2. 同态二点函数与低模记录

高壳中心化有序核、噪声和响应为
\[
 W_k(t,s)=k^2v_k(t)^2v_k(s)^{*2},\quad
 N_k(f,g)=k^2\operatorname{Re}[J_k(f)\overline{J_k(g)}],
 \quad J_k(f)=\int f v_k^2,
\]
\[
 \chi_k f(t)=-2k^2\operatorname{Im}
       \left[v_k(t)^2\int_{-\infty}^t v_k(s)^{*2}f(s)\,ds\right].
 \tag{U4}
\]
因 H_int=-fQ，静态极限为正的
k² theta(t-s) sin[2omega(t-s)]/(2omega²)。

p=4n，X2,f=integral fX2 时，完整 oscillator-potential 噪声为
\[
 N_{Q,K}^{\pm}(f,g)=4p(1-p)X_{2,f}X_{2,g}
 +[4+(6\pm4)p]\operatorname{Re}[J_2(f)\overline{J_2(g)}]
 +\sum_{k=3}^K k^2\operatorname{Re}[J_k(f)\overline{J_k(g)}].
 \tag{U5}
\]
低壳有序核可取同一数目项加
a_± J2,f bar(J2,g)+b_± bar(J2,f)J2,g，
a_±=4+(4±2)p，b_±=2(1±1)p。
两系数非负，a_±+b_±=4+(6±4)p，
a_±-b_±=4+2p=4+8n，精确还原 U1 的响应系数。
这保留 NOON 符号。Qosc 不含零模；完整 metric 噪声中的零模/k2
交叉块仍按 TENSOR_NOISE T5–T7/T11 整体加入。

## U3. Wronskian 与实际响应尾

I5 给 |F|<=2，|F-1|<=2mu/omega，及
|F'|<=4mu/omega，|F''|<=8mu/omega，|F'''|<=16mu/omega。
Wronskian 精确给
\[
 |F|^2-{\operatorname{Im}(F'\overline F)\over\omega}=1.
\]
所以 ||F|²-1|<=8mu/omega²，||F|⁴-1|<=40mu/omega²。
仅使用 |F-1|=O(omega^-1) 不足以得到此局部接触匹配。
对 H=bar(F)²，可取
|H|<=4，|H'|<=16mu/omega，|H''|<=64mu/omega，
|H'''|<=256mu/omega。

固定 t，A_t(s)=F(t)²bar(F(s))² f(s)，lambda=2omega。三次分部积分：
\[
 \int_{-\infty}^t e^{-i\lambda(t-s)}A_t(s)ds
 =-{iA_t(t)\over\lambda}+{A_t'(t)\over\lambda^2}
  +{iA_t''(t)\over\lambda^3}
  -{i\over\lambda^3}\int_{-\infty}^t
                 e^{-i\lambda(t-s)}A_t'''(s)ds .
 \tag{U6}
\]
过去边界为零，A_t(t)=|F(t)|⁴ f(t) 实数。Leibniz 给
|Im A_t'|<=64mu ||f||infty/omega；
|A_t''|<=256mu ||f||infty/omega+128mu ||f'||infty/omega
+16||f''||infty；
integral |A_t'''|<=1024mu ||f||1/omega+768mu ||f'||1/omega
+192mu ||f''||1/omega+16||f'''||1。

D=(4/3)^(5/2)<3，omega²>=3k²/4，且
0<k²/(4omega³)-1/(4k)<=(3D/8)k^-3。代入 U4 得
\[
 \|\chi_k f-f/(4k)\|_\infty\le D\,r_\mu(f)/k^3,
\]
\[
 r_\mu(f)=(3/8+34\mu)\|f\|_\infty+8\mu\|f'\|_\infty
 +\|f''\|_\infty+64\mu\|f\|_1+48\mu\|f'\|_1
 +12\mu\|f''\|_1+\|f'''\|_1 .
\]
34mu 分别来自局部振幅的 10mu、Im A' 的 8mu、A'' 的 16mu。
因此共同 AE 序列在 K>=2 满足
\[
 \boxed{\|(R_\infty^{AE}-R_K^{AE})f\|_\infty
                      \le {3r_\mu(f)\over2K^2}.} \tag{U7}
\]
同样控制任何 L>K 的 Cauchy 差；这不是裸核逐点绝对收敛或
L²→L² 截止算子范数收敛。

## U4. 噪声、正性和共同二阶 CTP

对 m=1,2,3，置
\[
 b_m(f)=\sum_{j=0}^m {m\choose j}c_j\|f^{(m-j)}\|_1,\quad
 (c_0,c_1,c_2,c_3)=(4,16\mu,64\mu,256\mu).
\]
分部积分给 |J_k(f)|<=b_m(f)/(2^(m+1)omega^(m+1))，从而
\[
 |N_{Q,\infty}(f,g)-N_{Q,K}(f,g)|
 \le {b_m(f)b_m(g)\over3^{m+1}(2m-1)K^{2m-1}} . \tag{U8}
\]
f=g 的尾非负。全部高低块是同一态的 Gram 核。
有限 K 满足 R_K-R_K^T=-2 Im W_K，实对称 AE contact 在反对称部
消去。两类尾允许共同极限，
W_infty=N_Q,infty-(i/2)(R_infty-R_infty^T) 仍正型。
没有套用平稳 Fourier 涨落耗散公式。

Delta=f_+-f_-、Sigma=(f_++f_-)/2，S_IF=-i log Z 约定下
\[
 S_K^{(2)}[\Delta,\Sigma]
       =\int\Delta R_K^{AE}\Sigma+{i\over2}N_{Q,K}(\Delta,\Delta).
\]
因而
\[
 |S_\infty^{(2)}-S_K^{(2)}|
 \le {3\|\Delta\|_1r_\mu(\Sigma)\over2K^2}
 +{b_m(\Delta)^2\over2\,3^{m+1}(2m-1)K^{2m-1}} . \tag{U9}
\]
正虚部、S^(2)[0,Sigma]=0 及两支交换共轭关系同时保留。
这是精确二阶变分，不是有限幅度的完整影响泛函；
包含一阶项的 Taylor 多项式还需下面的 mean 误差。

## U5. 均值尾与该态上的 GNS–L² 域

I5 对 j=0,1,2 给
|F^(j)-delta_j0-i J^(j)/(2omega)|<=4mu/omega²，J=int_-infty^eta V。
Wronskian 及其导数，连同 |V|,|V'|<=mu，给安全界
\[
 |\partial_\eta^j[|F|^2-1-V/(2\omega^2)]|
                       \le24\mu/\omega^3,\qquad j=0,1.
\]
在 j=1，F'bar(F') 为实数，故不贡献 Im。
高壳
qren,k=k²|F|²/(2omega)-k/2-(1+V)/(4k)
于是满足
\[
 |q_{\mathrm{ren},k}|
 \le D(3/16+3\mu/8)k^{-3}+(64/3)\mu k^{-2},
\quad
 |q_{\mathrm{ren},k}'|
 \le(3D\mu/8)k^{-3}+(64/3)\mu k^{-2}.
\]
所以
\[
 \|\bar Q_\infty-\bar Q_K\|_\infty\le
 m_K={D(3/16+3\mu/8)\over2K^2}+{64\mu\over3K},
 \tag{U10}
\]
导数尾 <=3Dmu/(16K²)+(64/3)mu/K。
所有低模、thermal、参考 k=1 已在 K>=2 包含。

同一 incoming Hilbert/GNS 表示中，各高壳 pair-creation 输出相互正交，
从而中心化尾的 Hilbert–Schmidt 范数平方精确等于 U8 的对角噪声尾。
以该 Cauchy 序列定义极限并加回共同 mean 减项，有
\[
 \|(Q_\infty^{AE}-Q_K^{AE})(f)\rho_\pm^{1/2}\|_{HS}^2
 \le m_K^2\|f\|_1^2+
 {b_m(f)^2\over3^{m+1}(2m-1)K^{2m-1}}. \tag{U11}
\]
这只给该态上的 L² 极限，不宣称全 Fock 唯一自伴闭包或尖锐时刻方差有限。
U9 若比较包含一阶项的 Taylor 多项式，另加 ||Delta||1 m_K。

## U6. 固定共形 lapse 的 u–u Hessian 弱尾

令 D_U=partial²+2h partial，D_U†=partial²-2partial(h·)；
w,z 属 C_c⁵(I)，故 D_Uw,D_Uz 属 C_c³(I)。
在同一背景上比较 ACTION_RESPONSE A6 的有限 K action 行，
low zero/k2、gravity、U0 和完整有限 anomaly 项相同，差严格为
\[
 {\cal H}_{U,\infty}-{\cal H}_{U,K}
 =D_U^\dagger(R_\infty^{AE}-R_K^{AE})D_U
                  -2\partial[(\bar Q_\infty-\bar Q_K)\partial].
 \tag{U12}
\]
第二项由 delta D_U† 产生，必须保留。紧支测试令端点项为零，因此
\[
 |\langle z,({\cal H}_{U,\infty}-{\cal H}_{U,K})w\rangle|
 \le {3\|D_Uz\|_1 r_\mu(D_Uw)\over2K^2}
                        +2\|z'w'\|_1m_K . \tag{U13}
\]
此处 Hessian 指 physical retarded action 行；不声称 retarded 核时间对称。

高壳在 u 方向耦合 Q_k(D_Uw)，同态 u-action noise 截止差由 U8
取 f=D_Uz、g=D_Uw 给出。实际零模与 k2 的全部联合低块保持，
不删除其交叉项。U9 和 U13 因此同时给同一固定 lapse 的 u–u
二阶 CTP 弱测试收敛。

## U7. 验收范围

本页闭合共同有限 K potential response/noise 的定量尾、AE 接触、
同态正性/交换子兼容、GNS–L² 域，以及固定共形 lapse 的 u–u 链式接触。
全部 source 截断在同一无限场背景 U 上；没有声称每个有限 K 背景
各自满足原精确平均方程。示例数值只是声明测试范数归一化的尾界，
不是仪器误差、度规精度或秒数。

任意 lapse/tensor 变分和有限初片混合块、联合几何—源传播子与正常态的
全场极限、有限幅影响泛函余项、G_K→G_U、装置/控制器及实验桥仍开放。
