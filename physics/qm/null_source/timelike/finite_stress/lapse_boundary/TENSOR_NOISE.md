# 同一实际非静态历史的完整源应力噪声

## 1. 已计算的对象

本页给出 BOUNDARY_STATE 的两个正常薄层源，在 GEOMETRY_MATCHING 已匹配实际历史 U 上的完整、绝对、中心化应力张量噪声，作为光滑时空测试上的双分布。它不是只给两种噪声的差，也不是把旧静态公式换一个尺度因子。

所得表达由同一精确模式、实际两点函数和有限个非 Gaussian 四阶累积量决定；这些有限累积量在下文全部列出。无限高模仍是实际 incoming 真空。一般 tensor 测试的合法性用 Hadamard/Wick 分布论；有限空间谐波的 density/pressure 测试还给明确 O(1/K) 截止尾界。

本页只计算物质源。完整 retarded metric Hessian 的局部接触延拓、几何初态、装置总源和受控 Einstein–CTP 演化没有因此完成。

## 2. 原态、场和真正时间依赖

原定义保持：
\[
 d=4,\quad p=4n,\quad\varepsilon=\sqrt3/A,\quad
 e_0=E_*=E_z+2p\varepsilon,\quad e_2=E_*-2\varepsilon,
\]
\[
 \rho_\pm=(1-p)|\psi_0,0\rangle\langle\psi_0,0|
        +p|\psi_2,A_\pm\rangle\langle\psi_2,A_\pm|.
\tag{T1}
\]
ψ_N 是原固定光滑动量环包；其条件零模能量是 e_N+σX，X 的共同律为 w²，均值零、方差 μ2。k≥3 为 incoming 真空。所有参数只选一次，随 U 运输，不逐时重置能带。

令 Y0=V0^−1/2，I′=a^−2，精确模式 v_k 满足
\[
 v_k''+(\omega_k^2-a''/a)v_k=0,\quad
 v_kv_k^{*'}-v_k'v_k^*=i,\quad \omega_k^2=k^2-1.
\]
物理场为
\[
 \Phi_i=Y_0(Q_i+P_i I)
  +\sum_{k\ge2,m}[(v_k/a)Y_{km}a_{ikm}+{\rm h.c.}].
\tag{T2}
\]
因此所有场导数不含 Q：
\[
 \partial_a\Phi_i=P_i z_a+
   \sum_{km}[u_{a,km}a_{ikm}+u_{a,km}^*a_{ikm}^\dagger],
\quad
 z_a=\delta_a^\eta/(\sqrt{V_0}a^2),\quad
 u_{a,km}=\partial_a[(v_k/a)Y_{km}].
\tag{T3}
\]
这里是原物理 Cauchy frame 的共同运输；不能另把不同 h 的 raw Fock 空间认成同一个裸态。

## 3. 实际两点函数与完整有限四阶修正

写 τ=A³Ez，n_k=n 1_{k=2}。两种符号的完整导数两点函数相同：
\[
 G_{ab}^{ij}(x,x')=\delta_{ij}\left[
 \tau z_a(x)z_b(x')
 +\sum_{km}\{(1+n_k)u_a(x)u_b^*(x')
            +n_ku_a^*(x)u_b(x')\}\right].
\tag{T4}
\]
定义 κ4 为实际有序四点函数减去具有同一两点数据的 Gaussian Wick 配对。也可直接用这个代数差定义，不依赖把实际态当成 Gaussian。

设 α=(species,m) 属于八个 k=2 振子；s_α 在物种一为 1，在物种二为所选 ±。所有非零累积量由下列生成式给出：
\[
 \kappa(P_i,P_j,P_l,P_m)
 =\frac{A^6}{2}
  [4p(1-p)\varepsilon^2+\sigma^2\mu_2-E_z^2]
  (\delta_{ij}\delta_{lm}+\delta_{il}\delta_{jm}
                              +\delta_{im}\delta_{jl}),
\tag{T5}
\]
\[
 \kappa(P_i,P_j,a_\alpha^\dagger,a_\beta)
 =A^3n(e_2-E_z)\delta_{ij}\delta_{\alpha\beta},
\tag{T6}
\]
\[
 \kappa(a_\alpha^\dagger,a_\beta^\dagger,a_\gamma,a_\delta)
 =\frac pd\,s_\alpha s_\gamma\delta_{\alpha\beta}\delta_{\gamma\delta}
  -n^2(\delta_{\alpha\gamma}\delta_{\beta\delta}
                         +\delta_{\alpha\delta}\delta_{\beta\gamma}).
\tag{T7}
\]
其余由排列和复共轭生成。κ 对重排完全对称：CCR 重排只产生二点项，而实际与参考二点项相同，差中精确抵消。奇数个 P、壳层 creation-number 不平衡及含任意 k≥3 符号的 κ 都为零。

T5 的推导是二维径向矩：
\[
 \langle P_iP_jP_lP_m\rangle
 =\frac{A^6}{2}\langle e^2\rangle
   (\delta_{ij}\delta_{lm}+\delta_{il}\delta_{jm}
                             +\delta_{im}\delta_{jl}),
\quad
 \langle e^2\rangle=E_z^2+4p(1-p)\varepsilon^2+\sigma^2\mu_2.
\]
T6 来自条件 N=2 的零模二矩 A³e2，而不是把零模与壳层独立。T7 来自实际两粒子向量：
\[
 a_\gamma a_\delta|A_\pm\rangle
       =s_\gamma\delta_{\gamma\delta}|0\rangle/\sqrt d .
\]
新检查器用不截断的 occupation-word 作用及精确有理数检验全部有序四振子词；它没有利用坏 CCR 的有限 Fock 矩阵边界。

## 4. 完整 tensor 噪声公式

令
\[
 {\cal Q}_{ab}^{ef}
 =\delta_a^{(e}\delta_b^{f)}-\tfrac12g_{ab}g^{ef}.
\]
把 T3 的十八个低模符号（P1,P2,八个 a、八个 a†）代入 T5–T7，得到光滑有限和 K_{ie,if,jg,jh}(x,x,x′,x′)。则
\[
 \boxed{
 N_{abcd}(x,x')=
 {\cal Q}_{ab}^{ef}(x){\cal Q}_{cd}^{gh}(x')
 \operatorname{Re}\sum_{ij}
 [G_{eg}^{ij}G_{fh}^{ij}+G_{eh}^{ij}G_{fg}^{ij}
                         +K_{ie,if,jg,jh}].}
\tag{T8}
\]
G 的两个因子都取 (x,x′) 的相同 Wightman 方向；不能换成 |G|²。这里
\[
 N(F,G)=\tfrac12\langle\{\delta T(F),\delta T(G)\}\rangle
\]
没有额外 1/2 或 1/4 归一化。U0、AE 和任何同处方 c-number 在中心化噪声中消去，但它们的 mean 与 metric contact 责任仍保留。

这是一份实际可代入的绝对源核：T4 给全部无限 Gaussian 项，T5–T7 给全部非 Gaussian 修正。没有只计算某个相对差后宣称绝对背景已知。

## 5. 全场定义域、正性和 Ward

高频 G 是实际 Hadamard 二点函数的导数。其波前集在第一端的 covector 取同一未来方向，在第二端取相反方向；两个同向 G 因子的 covector 之和不可能为零。因此 Hörmander 乘积在整个 M×M 上定义 T8 的 Gaussian 双分布。导数不扩大波前集，有限 K 修正是光滑项。

这不是给 x=x′ 的点值，也不把尖锐时间空间平均方差写成有限数。任意实、光滑、紧支 tensor 测试 F 给有限二次型；实际正常态与 Wick 多项式的定义给
\[
 N(F,F)=\|\delta T(F)\rho^{1/2}\|_{\rm HS}^2\ge0.
\tag{T9}
\]
不要求有限 κ 单独正定，也不在没有域证明时宣称每个复合算符的唯一自伴闭包。

每个极化经典应力
\[
 B_{ab}(f,g)=\nabla_{(a}f\nabla_{b)}g
             -\tfrac12g_{ab}\nabla f\cdot\nabla g
\]
满足
\[
 \nabla^aB_{ab}
 =\tfrac12[(\Box f)\nabla_bg+(\Box g)\nabla_bf]=0.
\]
T2 的实际模式与零模均满足原 KG，故 T8 在两端守恒。对 compact ξ,F，相应纯 gauge 测试的噪声为零。触及初始边界时必须另保留 surface 项。

这里没有 θ(t−s) 乘积。retarded commutator 延拓及其 equal-time contact 是另外的对象；噪声 Ward 不能替代 retarded Hessian 的重整化。

原始方法来源为 Brunetti–Fredenhagen–Köhler,
https://arxiv.org/abs/gr-qc/9510056，特别是波前集乘积与 Wick 多项式。
本质量为零的有限零模已单独正常处理；不把文献中特定 massive 推论无条件移植。
时间有序／应力 Ward 的规范责任另参 Hollands–Wald,
https://arxiv.org/abs/gr-qc/0404074。

## 6. 完整齐次矩阵：从 T8 直接投影

记 r_k=v_k′−hv_k，λρ=1、λp=−1/3，定义真正非静态系数
\[
 D_{Xk}=\frac{|r_k|^2+\lambda_X\omega_k^2|v_k|^2}{V_0a^4},
\quad
 B_{Xk}=\frac{r_k^2+\lambda_X\omega_k^2v_k^2}{2V_0a^4},
\quad
 L=\frac{A^3}{V_0a^6},\quad
 A_X=D_{X2}-\varepsilon L.
\tag{T10}
\]
下标 f 表示 ∫f(η)·dη。对于任意实紧支光滑 f,g，
\[
 \begin{aligned}
 N_{XY}^\pm(f,g)={}&
 \sigma^2\mu_2 L_fL_g
 +4p(1-p)A_{X,f}A_{Y,g}\\
 &+[16+(24\pm16)p]\operatorname{Re}(B_{X2,f}B_{Y2,g}^*)\\
 &+\sum_{k\ge3}4k^2\operatorname{Re}(B_{Xk,f}B_{Yk,g}^*).
 \end{aligned}
\tag{T11}
\]
所有四块都来自同一源。第一块与第二块不能由错误的零模/壳层独立假设重建。

对应平均交换子为
\[
 \langle[\bar T_X(f),\bar T_Y(g)]\rangle
 =2i(16+8p)\operatorname{Im}(B_{X2,f}B_{Y2,g}^*)
  +8i\sum_{k\ge3}k^2\operatorname{Im}(B_{Xk,f}B_{Yk,g}^*).
\tag{T12}
\]
两种符号相同。T11 是绝对噪声，T12 只是响应的 commutator 部分。

逐模方程给
\[
 D_{\rho k}'+3h(D_{\rho k}+D_{pk})=0,\quad
 B_{\rho k}'+3h(B_{\rho k}+B_{pk})=0,\quad L'=-6hL.
\tag{T13}
\]
因此 T11 两端满足完整齐次 Ward，保留密度—压力交叉相关。

## 7. 可显式控制的无限高模尾

设冻结实际轨道所在 Wiener E4 球半径 ρ=10^−25。其 V=U″+U′² 满足 ||V||E2≤ρ+ρ²。正频至少 s*>1.5，且
\[
 \|[\Theta(\Theta-2i\omega_k)]^{-1}\|_{E_2^0\to E_4^0}
 \le(1+1/s_*)^2<3 .
\]
由精确 Jost 方程，
\[
 \|F_k-1\|_{E_4}
 \le\frac{3(\rho+\rho^2)}{1-3(\rho+\rho^2)}<4\rho,
\quad v_k=e^{-i\omega_k\eta}F_k/\sqrt{2\omega_k}.
\tag{T14}
\]
故 F 的零阶偏差及 1–4 阶导数有上述界，G_k=F_k′−hF_k 的 0–3 阶导数≤6ρ。此处只需这有限阶；没有把旧任意阶 C_j 错改成 ρ。

对 S_j(f)=Σ_{l=0}^j binom(j,l)||f^(l)||1，直接 Leibniz 估计及二/三次分部积分给
\[
 |B_{\rho k}[f]|\le \frac{8\rho S_2(f)}{V_0A^4\omega_k^2},
\quad
 |B_{pk}[f]|\le \frac{2S_3(f)}{V_0A^4\omega_k^2}.
\tag{T15}
\]
记右边的 ω^−2 系数为 C_X(f)，K≥2 时
\[
 |\text{T11 的 }k>K\text{ 尾}|
 \le\frac{8 C_X(f)C_Y(g)}K.
\tag{T16}
\]
高模数目项在实际 incoming 真空 GNS 向量上消失。这里控制的是光滑测试；没有给瞬时 N00 一个有限值。

## 8. 完整 tensor NOON 差及其实际含义

k=2 的完整 SO(4) 壳满足
\[
 \sum_mY_m^2=d/V_0,\quad
 \sum_m\nabla_iY_m\nabla_jY_m=d\omega_2^2\gamma_{ij}/(3V_0),
\quad \sum_mY_m\nabla_iY_m=0 .
\]
令 s_ab=g_ab+n_an_b，并定义
\[
 {\cal B}_{ab}=B_{\rho2}n_an_b+B_{p2}s_{ab}.
\]
实际 vacuum–pair 矩阵元为 √(2d) B_ab。T1 的两个 off-diagonal coherence 因而给
\[
 \boxed{\Delta N_{abcd}(x,x')
 =32p\,\operatorname{Re}[{\cal B}_{ab}(x){\cal B}_{cd}(x')^*].}
\tag{T17}
\]
这是原非静态模式上的全部 tensor 差；momentum 差为零，density 与 density–pressure 差一般非零。coordinate ηη 分量含 a²，不能将物理 ρ 直接放进去。

对实 compact tensor 测试，
\[
 \Delta N(F,F)=32p\left|\int d{\rm vol}\,F^{ab}{\cal B}_{ab}\right|^2\ge0,
\]
实 rank 至多二。B_ab 由 T13 守恒，所以差的两端 Ward 精确成立。空间平均为零的标量谐波测试不读取这个 singlet 差。

若一个 h≠0 的连通区间上 Bρ2 恒零，T13 强迫 Bp2 恒零；但
Bρ2−Bp2=2ω2²v2²/(3V0a⁴)≠0，矛盾。因此真正非静态历史上存在密度测试差。DYNAMIC_WITNESS 还对当前指定正窗给数值包围。

然而同一组合的 incoming conserved charge pair 系数精确为零（静态过去 Bρ=0，加上 T13）。故
\[
 \Delta N(C_{\rm source},C_{\rm source})=0.
\tag{T18}
\]
新的局部密度噪声差不能被当成对缺失约束荷的补偿，更不能当成已经读出的引力信号。

## 9. 有限空间谐波的建设性截止界

令 b_L 是实 scalar harmonic，−Δb_L=λ_Lb_L，λ_L=L(L+2)。定义空间加权 T_X^b=V0^−1∫b_L T_X dΩ。其 covariant tensor 时间测试是
F^ab=f b_L n^a n^b/(V0a⁴)；pressure 则用 s^ab/3，保留 dvol=a⁴dηdΩ。

记
\[
 M_{km,ln}=\int b_LY_{km}Y_{ln}d\Omega,\quad
 R_{kl}=(\omega_k^2+\omega_l^2-\lambda_L)/2.
\]
积分分部给 ∫b_L∇Y_k·∇Y_l=R_kl M。Gaunt selection 为 |k−l|≤L，并有
\[
 \sum_{mn}|M_{km,ln}|^2\le\|b_L\|_\infty^2\min(k^2,l^2).
\tag{T19}
\]
有限带宽而非把所有 k,l 独立求和，是可和尾的关键。

高模 pair 矩阵精确为
\[
 \beta_{X;km,ln}
 =\frac{M_{km,ln}}{2V_0a^4}
      [r_kr_l+\lambda_XR_{kl}v_kv_l].
\tag{T20}
\]
取 K≥2L+4，在 max(k,l)>K 的非零项上，两频率可比。T14 的有限阶界及三次时间分部积分给
\[
 |\beta_{X;km,ln}[f]|
 \le |M_{km,ln}|\,\frac{C_f}{(\omega_k+\omega_l)^2},
\qquad C_f=\frac{40S_3(f)}{V_0A^4}.
\tag{T21}
\]
所有零模/k2 非 Gaussian 耦合此时已在截止中；遗漏的 creation 输出含至少一个 k>K 粒子，和保留输出正交。因此方差尾是非负的，且
\[
 0\le N_X^b(f,f)-N_{X,K}^b(f,f)
 \le\frac{4(2L+1)\|b_L\|_\infty^2C_f^2}{K}.
\tag{T22}
\]
更细常数是 32/9；上式作保守简化。交叉尾用 Cauchy–Schwarz。它不等于已经列出任意 tensor harmonic 的全部数值常数；一般 tensor 紧支测试的合法性由第5节承担。

## 10. 明确拒绝的三个错误替代

1. 把低模当 Gaussian：两态 W2 相同，会把 T17 错算为零。
2. 删除零模—壳层相关：实际 Var Hz=σ²μ2+4p(1−p)ε²、Var N=4p(1−p)、Cov(Hz,N)=−4p(1−p)ε，故 Var(Hz+εN)=σ²μ2；漏交叉项会多出 8p(1−p)ε²。
3. 用 ΔN 替代绝对 N：会删除严格正的共同 profile 块和无限真空尾。

新代码实际检查这些错误与正确结果不等。它检验代数和明确界；无限维分布、正常性与全部模式的解析证明由正文承担。没有执行旧科学代码、ODE 或重新计算旧静态常数。
