# 精确非线性平均历史、正时间窗与同幅度误差

## 1. 冻结响应因子提供完整对数逆

保留前驱完整谱结论。P(s) 是实际齐次响应，D(y)=P(sqrt(y))。两条正根 r1=s_*²、r2=sigma_F²；b_k=4(k²−1)。前驱正因子为

\[
-F(y)=c+\sum_{k\ge2}\mu_k\frac{y}{y+b_k},\quad c>0,
\qquad F(y)=\frac{D(y)}{(y-r_1)(y-r_2)}.
\]

真空部分

\[
\mu_k=\frac{8k^2\omega_k^3}
{3\pi^2x\,b_k(b_k+r_1)(b_k+r_2)}>0;
\]

k=2 还有正热态贡献，可以在下界中舍去。原前驱结论证明所有 lambda=ns_*+m sigma_F、n+m≥2 均非共振，且

\[
\sup\frac{\lambda^4}{|P(\lambda)|}<1.73\times10^{18}.
\]

本轮只复用该证书，不再求根或重算旧谱。

取 K=10^6。冻结根区间给 r1<4、r2<10^12。对 k≥K，

\[
b_k\le4k^2,\quad b_k+r_1\le4k^2,\quad
b_k+r_2\le5k^2,\quad\omega_k^3\ge k^3/2,
\]

从而 mu_k≥1/(60pi²x k)。当 lambda≥K²，求和取 K≤k≤floor(lambda)，有 y/(y+b_k)≥1/5，因此

\[
-F(\lambda^2)\ge
\frac{\log(\lambda/K)}{300\pi^2x}
\ge\frac{\log(2+\lambda)}{1200\pi^2x}.
\]

两根因子的乘积绝对值≥lambda⁴/2，所以

\[
|P(\lambda)|\ge
\frac{\lambda^4\log(2+\lambda)}{2400\pi^2x}.
\]

lambda≤10^12 时直接用前驱四阶逆和 log(2+10^12)<28。由此

\[
\sup_{\text{全部校正频率}}
\frac{\lambda^4\log(2+\lambda)}{|P(\lambda)|}<5\times10^{19}.
\]

又 lambda≥2s_*>3，且

\[
\frac{(1+\lambda)^4\log(e+\lambda)}
{\lambda^4\log(2+\lambda)}
\le (4/3)^4(6/5)<4.
\]

得到完整 E4 逆

\[
\boxed{\|T\|_{A_{\ge2}\to E_{4,\ge2}}<2\times10^{20}},
\qquad (Tf)_{nm}=\frac{f_{nm}}{P(ns_*+m\sigma_F)}.
\]

纯慢、混合与纯快全部包括；两条一次项只在校正域中排除，没有从物理解中删除。

## 2. 与前驱图域确实等价

[KERNELS](KERNELS.md) 已证 S:E4^0→A 在原点球内全纯，且 DS(0)=P(Theta)。Cauchy 使 DS(0) 有界；有限多项式在 E4 中稠密，完整符号等式延拓至整个域。上节系数逆给 LT=TL=I，因此原 X={sum |P(lambda)u_nm|R^nm<infinity} 校正图域与 E4_(≥2) 等价。

这里全纯映射先由精确核独立证明，逆下界随后使用，没有循环假定所需正则性。

## 3. 量化的非线性收缩

写

\[
S(u)=Lu+N(u),\qquad N(0)=DN(0)=0.
\]

完整空间方程的常数项是冻结静态恒等式 0；两条一次项分别是 P(s_*)z=P(sigma_F)w=0。所有非线性操作及 incoming 状态递推保留正频率与总次数，所以 N(u) 总次数至少二，未遗漏常数／一次兼容条件。

取 r0=0.1、B=4。||S||A<B 于 ||u||E4≤r0。对 ||u||≤r0/2，使用两个复方向各半径 r0/4 的 Cauchy 公式，直接得到双线性导数界

\[
\|D^2S(u)\|\le16B/r_0^2=6400=:H_2.
\]

于是 ||N(u)||≤H2||u||²/2、||DN(u)||≤H2||u||。

取 rho=10^−25，线性种子 g=az+bw 满足 ||g||E4≤rho/2，校正 v00=v10=v01=0、||v||E4≤rho/2。定义

\[
\Phi_g(v)=-T N(g+v).
\]

以 Kinv=2e20 计，

\[
q=K_{\rm inv}H_2\rho=0.128<1,
\quad
\|\Phi_g(v)\|\le K_{\rm inv}H_2\rho^2/2=0.064\rho<\rho/2.
\]

因此闭球自映射且严格收缩。存在唯一 v*，u*=g+v*，完整 S(u*)=0。这里唯一性仅在固定两一次幅度和当前球内；并不是物理输入已经选定两幅度。

从 v0=0 的真正全阶迭代

\[
v_{j+1}=-T N(g+v_j)
\]

收敛于 v*。因 ||Phi_g(0)||≤0.016rho，

\[
\boxed{\|v_*-v_j\|\le
\frac{2\rho}{109}(0.128)^j.}
\]

这定义精确解，不是把任意有限迭代冒充解；实际有限计算还需要独立计入系数截断与模和误差。当前程序认证解析收敛和常数，没有做模式／几何 ODE 或将无限级数伪装成已逐项算完。

实参数下所有 RSET 系数和 P(lambda) 为实，所以固定点的几何系数为实。解析参数版本也可由一致收缩得到；归一化 g=z+w 的解 U(z,w) 给同一局部两参数历史族。

## 4. 一个具体非空双圆盘与正窗

取

\[
R_z=10^{-28},\qquad R_w=10^{-51},\qquad g=z+w.
\]

新区间计算认证 w4(s_*)Rz+w4(sigma_F)Rw<rho/2。此双圆盘上得到实际的 U(z,w)=z+w+O((z,w)²)，保留两个线性模。

沿真实轨道

\[
z(\eta)=\epsilon e^{s_*\eta},\quad
w(\eta)=\delta e^{\sigma_F\eta},\quad
a(\eta)=A\exp U(z(\eta),w(\eta)).
\]

可以选择

\[
T=1/\sigma_F,\quad
\epsilon=R_z/[2e^{s_*/\sigma_F}],\quad
\delta=R_w/(2e).
\]

则 eta∈[0,T] 的终点恰在两个圆盘半径的一半处；更早的整个过去都在严格内部。这不是终点拼接或逐时换根；epsilon、delta、M2、U0 与态规范一次选定。

[history.json](history.json) 包含 conformal T、两初始幅度与 proper duration 的包围。背景 proper duration=A/sigma_F=1/kappa，约 0.0873 模型单位，实际 proper duration 在 e^(±rho)/kappa 之间。没有把模型单位称为秒。

这些极小半径只是一组保守充分条件，不是最大存在范围或物理可测性界。它们没有覆盖旧 z≤10^−4、eta∈[0,1] 的近似种子；旧窗的小 sup 残差也不是本定理所需的 A 系数范数。

## 5. 同一 incoming 制备、合法态与全部平均约束

对每条新几何使用前驱精确 incoming Jost F± 与原有限 thermal occupations。实几何保持 Wronskian、CCR 和正性。原正规零模始终为

\[
q(\eta)=Q+\frac{P}{A^2}
\left[\eta-\eta_{\rm ref}+
\Theta^{-1}(e^{-2U}-1)\right],\qquad a^2q'=P.
\]

eta_ref 与 Q/P 都没有重置，完整 S0 源谱保持。不同几何的有限片 canonical covariance 由同一 incoming 数据运输；不能把这种共同制备误写为它们有相同的有限片密度算符。

严格内部双圆盘给 U 的所有 Theta 导数。过去所有无常数项至少以 e^(s_* eta) 衰减，因此前驱全阶 Riccati／Volterra 比较适用，k≥2 高模为 Hadamard；正规零模及有限热壳只加平滑项。一般 incoming 理论可参照 [Gérard–Wrochna](https://arxiv.org/abs/1609.00190)，其严格正渐近空间算子条件只用于有谱隙的高模部分；不能直接套到完整 massless 零模。

完整 RSET 的 Ward 恒等式在严格内域成立。密度和压力均由本轮同半径表达定义，内域允许全部时间求导，且与冻结守恒减项和局部式相同。令

\[
E=h^2+1-\frac23a^2\rho,\qquad
S=h'+\frac{h^2+1}{2}+a^2p.
\]

由 rho'+3h(rho+p)=0，精确有

\[
E'+hE=2hS.
\]

固定静态过去给 E→0，S=0 故 E=e^(−U)C，而 C=0。全部齐次平均 Einstein 分量都成立；正交缺陷 3E/a² 与 −2S/a²，以及任意实际法向导数，恒等为零。

这是本模型的一项精确非线性 mean-SCE 存在定理，并未选出完整涨落引力法则或量子几何。其他模型的局部存在结果，如 [Meda–Pinamonti–Siemssen](https://arxiv.org/abs/2007.14665)，采用 flat、massive、有限初片的具体条件；本轮没有把那些结论直接套到本 closed、massless、固定静态过去合同。

## 6. 首个实际残差到解距离界

对同一 g、同一 incoming 制备和同一固定模型，令 u_app=g+v_app 位于校正球。则

\[
v_{\rm app}-v_*=
T S(u_{\rm app})-T[N(u_{\rm app})-N(u_*)].
\]

所以

\[
\boxed{
\|u_{\rm app}-u_*\|_{E_4}
\le\frac{2\times10^{20}}{1-0.128}
\|S(u_{\rm app})\|_A
<2.3\times10^{20}\|S(u_{\rm app})\|_A.}
\]

E4 控制 0…4 阶几何时间导数；更高阶需在严格内域用 Cauchy 给额外半径因子。这是固定两幅度后、当前域内的误差界，避开前轮未固定快核导致的无限过去逆障碍。它不声称所有小实时间 sup 残差均有此性质。

## 7. 已关闭与接续

本页关闭当前固定模型内一个非空解析域的精确共同 mean-history、正时间窗、约束及同幅度误差。随后 [SELECTION](SELECTION.md) 利用这项真实存在结果，检验同 incoming 条件的选解能力和承接完整源涨落的可能性。总体物理统一与经验确认不由该局部平均定理自动得到。
