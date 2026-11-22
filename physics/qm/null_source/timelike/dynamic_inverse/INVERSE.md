# 保留两条增长模的因果逆与解析系数逆

## 1. 两个不同的逆问题

本轮没有把快模删掉。已经证明的两个工具服务于不同的域：

| 问题 | 已闭合的结果 | 仍需承担的条件 |
|---|---|---|
| 从有限初片平滑开始的线性响应 | 完整因果 Green 函数、明确短窗增益、同步合法态 | 测试残差须光滑零过去；不是旧 seed 的全过去修正 |
| 两个过去衰减幅度的解析历史族 | 所有非线性组合频率无共振；系数逆有统一界并恢复四阶导数 | 完整非线性 AE/Jost 映射在 graph 域上的闭合尚未证明 |

两个工具都只使用当前完整响应和同一实际 incoming 态，没有改变物质、源强或重整化。
它们不将小方程残差直接等同于到精确非线性解的距离。

## 2. 正实部结构产生因果逆

沿用 [SPECTRUM.md](SPECTRUM.md)，r1=s_*²，r2=sigma_F²，

\[
 P(s)=(s^2-r_1)(s^2-r_2)F(s^2),\qquad
 c=-F(0)=-\frac{\mathscr D(0)}{r_1r_2}>0.
\]

取 mu_k=W_k/[b_k(b_k+r1)(b_k+r2)]>0。减去 F(0) 后的级数绝对局部一致收敛：

\[
 -F(y)=c+\sum_{k=2}^{\infty}\mu_k\frac{y}{y+b_k}.
\]

对 s=gamma+i tau、gamma>0，

\[
 \operatorname{Re}\frac{-F(s^2)}s
 =\frac{c\gamma}{|s|^2}
 +\sum_k\mu_k\frac{\gamma(|s|^2+b_k)}{|s^2+b_k|^2}
 \ge\frac{c\gamma}{|s|^2}.
\]

故 |1/F(s²)|<=|s|/(c gamma)。固定 gamma>sigma_F，设

\[
 \delta_j=1-r_j/\gamma^2>0.
\]

因为 |s²−rj|>=(1−rj/gamma²)|s|²，

\[
 \left|\frac1{P(\gamma+i\tau)}\right|
 \le\frac1{c\gamma\delta_1\delta_2|\gamma+i\tau|^3}.
\]

定义

\[
 G(t)=\frac1{2\pi}\int_{\mathbb R}
       \frac{e^{(\gamma+i\tau)t}}{P(\gamma+i\tau)}\,d\tau.
\]

1/P 与 s/P 在垂直线上均可积，因此 G 属于 C1，且

\[
 |G(t)|\le\frac{e^{\gamma t}}{\pi c\gamma^3\delta_1\delta_2},
 \qquad
 |G'(t)|\le\frac{e^{\gamma t}}{2c\gamma^2\delta_1\delta_2}.
\]

在有限宽右半平面矩形内，横边的被积函数分别 O(|tau|^-3)、O(|tau|^-2)，
所以可移动积分线。再令积分线向右无穷移动，得到

\[
 G(t)=0\quad(t<0),\qquad G(0)=G'(0)=0.
\]

Laplace 变换给 Ghat=1/P，定义唯一的具有某个有限指数增长阶的因果分布逆。
这里完整算子是同一 retarded 模响应；P 是它的 Laplace multiplier。
对光滑零过去函数，分布结果与原模式表达一致。

两个正实极点均保留。快极点 residue 非零，故没有任何 alpha<sigma_F 的
加权稳定卷积逆满足 \(\int_0^\infty e^{-\alpha t}|G(t)|dt<\infty\)。
否则 Ghat 在 sigma_F 解析，与 Ghat=1/P 冲突。有限时逆不要求这种长期稳定。

## 3. 正则域、实际态与短窗增益

对 f in C_c^infinity((0,infinity))，w=G*f 为光滑零过去响应，且 Lw=f。
所有导数可转移到 f：

\[
 w^{(j)}=G*f^{(j)}.
\]

这没有声称粗界保证 G'' 连续。连续 f 足以给下面 sup 增益，
但要据此连接全阶 Hadamard 几何—态，采用上述光滑平坦接入域。

对每条 \(a_\lambda=Ae^{\lambda w}\)，仍用相同 incoming Q/P、n 及高模正频归一化
作精确 KG/Jost 运输。一阶

\[
 \delta v_k(\eta)=\int_0^\eta
 \frac{\sin[\omega_k(\eta-t)]}{\omega_k}w''(t)v_{k0}(t)\,dt,
 \qquad
 \delta q(\eta)=-\frac{2P}{A^2}\int_0^\eta w(t)\,dt.
\]

这给合法 off-shell 族的一阶共同响应，没有冻结未来片上的 covariance，
也没有把数学 f 宣称为一个新增物理驱动。

取 gamma=24A，T=1/(24A)。完整参数区间给

\[
 T\in[5.098416013977445,\,5.098418426099144]\times10^{-7}.
\]

[causal_inverse.json](causal_inverse.json) 认证

\[
 \|w\|_{\infty,[0,T]}
 \le K_0\|f\|_{\infty,[0,T]},\quad
 K_0<4.20\times10^{-14},
\]

\[
 \|w'\|_{\infty,[0,T]}
 \le K_1\|f\|_{\infty,[0,T]},\quad
 K_1<1.30\times10^{-7},
\]

其中

\[
 K_0=\frac{e-1}{\pi c\gamma^4\delta_1\delta_2},\qquad
 K_1=\frac{e-1}{2c\gamma^3\delta_1\delta_2}.
\]

静态背景 proper duration 为 AT=1/24 个模型时间单位。
若 a=Ae^u，实际时长仅有 exp(−norm u)/24 至 exp(norm u)/24 的包围，
不是精确等于 1/24，更不是自动换算成秒。

对一般有限 T，将 e−1 换成 exp(gamma T)−1。
在旧 eta∈[0,1] 上这个界极大，不给旧近似历史有用的 shadowing 证书。

### 为何还不能从无限过去直接修正旧 seed

旧残差通常从 −infinity 按 exp(3s_* eta) 衰减，sigma_F>3s_*。
快极点对 G 贡献非零 exp(sigma_F t)/P'(sigma_F)，因此
从 −infinity 与这样的慢 forcing 直接做 retarded convolution 一般不收敛。
在有限初片突然截断旧残差又不满足平坦接入的兼容条件。

所以必须另行处理完整过去匹配或几何幅度；不能保持旧过去和旧片上态不动，
再单独选一个 a''' 根。后者还有 [STATE_MATCHING.md](STATE_MATCHING.md) 的 UV 障碍。

## 4. 所有纯慢谐波的统一非共振

令 q=sigma_F/s_*。本轮严格包围

\[
 468087.11913820513<q<468087.34103423485.
\]

因此 N=468087<q<N+1。没有选取该区间的中点作为真实参数。
由 F(y)<=F(0)<0 对 y>=0 成立，置 m=−D(0)>=m0>0，得到

\[
 |P(s_*\nu)|\ge m_0(\nu^2-1)|1-\nu^2/q^2|,\qquad \nu>1.
\]

对整数 n>=2，n<=N 部分在 t=n² 上的下界是凹二次函数；
n>=N+1 部分严格递增。因此无限项只需三个端点：

\[
 m_{\rm pure}=m_0\min\left\{
 3(1-4/q_L^2),\
 (N^2-1)(1-N^2/q_L^2),\
 ((N+1)^2-1)((N+1)^2/q_U^2-1)
 \right\}.
\]

[harmonics.json](harmonics.json) 给三个下界约为
11.99999999988、446136.19、2467636.95，所以

\[
 |P(ns_*)|>11.99\qquad\hbox{对全部整数 }n\ge2.
\]

没有扫描 468087 项，也没有把“只查少量系数非零”当成无限阶证明。

### 四阶时间导数的系数逆界

函数 \(t^2/[(t-1)|t-Q|]\)，Q=q²，
在 4<=t<Q 上严格增，在 t>Q 上严格降。
结合 q 的单调性，故

\[
 M_{4,\rm pure}=
 \frac{r_{1,\rm upper}^2}{m_0}
 \max\left\{
 \frac{N^4q_L^2}{(N^2-1)(q_L^2-N^2)},\
 \frac{(N+1)^4q_U^2}{((N+1)^2-1)((N+1)^2-q_U^2)}
 \right\}
 <1.73\times10^{18}.
\]

这界较大但有限，且保证 sup (ns_*)⁴/|P(ns_*)|<=M4。
精确证书上界约 1.7217054248991406×10^18。

单变量 u(z) 在 z=e^{s_*eta}=0 解析会排除非整数幂 fast 模 z^q；
这是一项额外选择，绝不是 incoming 态或 Hadamard 条件的推论。
本轮没有把它默认采用为物理法则。

## 5. 继续闭合：保留两个幅度的全部混合频率

为了不预先删掉快模，转向两个变量

\[
 z=\epsilon e^{s_*\eta},\qquad w=\delta e^{\sigma_F\eta},
 \qquad u=z+w+O((|z|+|w|)^2).
\]

两幅度只在初始选择一次，不逐时换根。总阶 n+m>=2 的频率为
lambda_nm=n s_*+m sigma_F。

m=0 已由上一节覆盖。m>=1 时 nu=n+m q>=q+1，
所以

\[
 |P(\lambda_{nm})|
 \ge m_0(2q+5+2/q)
 \ge m_0(2q_L+5+2/q_L)>m_{\rm pure}.
\]

四阶逆比值在 nu>q 上递减，最大只需 nu=q+1。再用 q 单调性，

\[
 M_{4,\rm mixed}
 =\frac{r_{1,\rm upper}^2}{m_0}
   \frac{q_U(q_U+1)^4}{(q_U+2)(2q_U+1)}
 <M_{4,\rm pure}.
\]

因此前面的 **11.99 和 1.73×10^18 同时覆盖全部二阶及以上纯／混合频率**。
此结论只需 q 非整数，不要求 q 无理。

## 6. 严格函数空间定理，以及不能省略的非线性门

给任意正 Rz,Rw，定义

\[
 \mathcal A=\left\{f=\sum_{n+m\ge2}f_{nm}z^nw^m:
 \|f\|_{\mathcal A}=\sum|f_{nm}|R_z^nR_w^m<\infty\right\},
 \qquad
 \Theta=s_*z\partial_z+\sigma_Fw\partial_w.
\]

系数逆

\[
 Tf=\sum_{n+m\ge2}\frac{f_{nm}}{P(ns_*+m\sigma_F)}z^nw^m
\]

是收敛的线性算子，并满足

\[
 \|Tf\|_{\mathcal A}\le m_{\rm pure}^{-1}\|f\|_{\mathcal A},
 \qquad
 \|\Theta^4Tf\|_{\mathcal A}\le M_{4,\rm pure}\|f\|_{\mathcal A}.
\]

精确的定义域用 graph norm：

\[
 X=\left\{u:\sum_{n+m\ge2}
 |P(ns_*+m\sigma_F)u_{nm}|R_z^nR_w^m<\infty\right\}.
\]

于是 L:X→A 是线性同构，T(A)=X 连续嵌入四阶导数系数空间。
零阶和两条一次项不在这个逆的域内；两线性幅度另行固定。

不能把裸四阶空间直接当成完整 L 的全域：
P(lambda) 的高频行为还含 lambda⁴ log(lambda)。
也不能由本线性同构推断完整 nonlinear AE/Jost map 已在 X→A 上闭合。
原慢窗的 UV 尾常数依赖其特定几何导数范围，不能原样搬到快方向。
[STATE_MATCHING 第7节](STATE_MATCHING.md#7-继续推进双变量精确-incoming-态的收敛构造)已给有限势能范数、零常数项下阶乘收敛的精确 incoming Jost 态族。下一项严格验收是这个包含完整态、AE 接触项、无限模的非线性映射及其余项界；
通过后才有资格使用收缩、隐函数或其他存在定理。

这已经把下一问题缩成保留两个真实线性自由度的、无频率共振的具体映射问题，
不再把“增加 Taylor 阶数”当成精确历史的替代。
