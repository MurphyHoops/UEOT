# 完整响应谱：两条增长根、正权重结构与无限尾认证

## 1. 固定的是同一个物理模型

本轮沿用 [dynamic_seed](../dynamic_seed/README.md) 的 exact unfiltered base：两场、闭 S3、massless minimal coupling，原 M2、常势 U0、canonical zero-mode Q/P 完整分布、两场完整 k=2 热壳，以及固定 AE mu=1、无额外有限曲率项。参数不是逐时选根，也没有重新选取旧区间中相互独立的浮点数。

令 x=A²，omega_k=sqrt(k²−1)，Jn=4 sqrt(3)n/pi²，
D0=3/(32pi²)，并定义

\[
 B(x)=\frac{S/4-3/160-[\log(x/4)+2\gamma_E]/64}{\pi^2},
 \qquad C_A=19+15[\log(x/4)+2\gamma_E].
\]

S 是冻结的前驱谱常数。本轮只读取证书，不重算旧谱和旧模式。

为消除变量歧义，用 P(s) 表示 eta 时间上的指数响应，用
\(\mathscr D(y)\) 表示同一函数的 y=s² 形式：

\[
 P(s)=\mathscr D(s^2),\quad
 \mathscr D(y)=y-4+\frac2x\left(\frac83B-D_0+\frac{Z(y)}{4\pi^2}\right)
 +\frac{4Jn}{3x}\frac{y+24}{y+12},
\]

\[
 Z(y)=D_{\rm num}(y)+\frac{C_Ay^2}{360}
       -\frac{(C_A-29)y}{180}-\frac1{24},
\]

\[
 D_{\rm num}(y)=-1+\frac y2-\frac{y^2}{12}
 +\sum_{k=2}^{\infty}
 \left[-\frac{4k^2\omega_k y}{3(y+4\omega_k^2)}
 +\frac{yk}{3}+\frac{y/6-y^2/12}{k}\right].
\]

代码中偶有 D(y)/Dnum 命名，均按此约定解释。包括 thermal pole 的所有局部 AE 项均保留。此前只在 1<s<3 认证根，未声称全正轴或复平面只有一个根。

## 2. 高频重排与快根的真实无限和

置 d=y/4−1，定义

\[
 H(d)=\sum_{k=2}^{\infty}\frac{d}{k(k^2+d)},\quad
 a_k=k^3-\frac k2-k^2\sqrt{k^2-1},\quad
 R(d)=\sum_{k=2}^{\infty}\frac{a_k}{k^2+d}.
\]

精确代数重排给

\[
 D_{\rm num}
 =-1+\frac y2-\frac{y^2}{12}
 -\frac y3(d+\tfrac12)H+\frac y3R.
\]

用有理化恒等式，

\[
 a_k=\frac1{4k[1-\frac1{2k^2}+\sqrt{1-\frac1{k^2}}]},
 \qquad \frac1{8k}<a_k<\frac1{6k}.
\]

所以 d>0 时 \(H/(8d)<R<H/(6d)\)。这不是截断忽略高模。

### H 的两套独立尾界

令 f_d(t)=d/[t(t²+d)]，K=256。f 正且递减，故

\[
 \sum_{2}^{K}f_d(k)+\frac12\log(1+d/(K+1)^2)
 \le H\le
 \sum_{2}^{K}f_d(k)+\frac12\log(1+d/K^2).
\]

这套粗界独立认证 P(11.45A)>0、P(11.47A)<0。

更紧的界也有完整余项符号。因为

\[
 f_d(t)=\int_0^\infty e^{-tu}[1-\cos(\sqrt d\,u)]\,du,
\]

以及 exact coth partial fractions

\[
 \frac1{e^u-1}-\frac1u+\frac12
 =2u\sum_{j=1}^{\infty}\frac1{u^2+4\pi^2j^2},
\]

用 \(1/a-u^2/a^2\le1/(a+u^2)\le1/a\) 得

\[
 u/12-u^3/720
 \le \frac1{e^u-1}-\frac1u+\frac12
 \le u/12.
\]

乘正的 Laplace 权重并积分，

\[
 I_K-\frac{f(K)}2-\frac{f'(K)}{12}+\frac{f'''(K)}{720}
 \le\sum_{k>K}f(k)
 \le I_K-\frac{f(K)}2-\frac{f'(K)}{12},
 \quad I_K=\frac12\log(1+d/K^2).
\]

这里

\[
 f'''(K)=-\frac6{K^4}
 +\frac{6(K^4-6K^2d+d^2)}{(K^2+d)^4}<0.
\]

在本快根区间 d/K²>3+2sqrt(2)，固定 d 的上下界宽不超过
1/(120K⁴)<2×10^-12。输入区间自身的依赖误差另行保留。

### 消除区间依赖，不改变物理参数

直接分别包围 log(x) 和 H 会丢失其高度相关性。令

\[
 L=C_A/30-1-H,\quad C=\frac1{2\pi^2x},\quad y=\kappa^2x,
\]

\[
 c_0(y)=-4+\frac{16B/3-2D_0}{x}-\frac{25C}{24}
       +\frac{4Jn}{3x}\frac{y+24}{y+12}.
\]

则严格恒等式为

\[
 \frac{\mathscr D(y)}y
 =1+\frac{\kappa^2L}{24\pi^2}
 +C\left(\frac{89}{180}-\frac L6+\frac R3\right)+\frac{c_0(y)}y.
\]

由上述尾界，L 可写成

\[
\begin{split}
 L={}&-\frac{11}{30}+\gamma_E-\sum_{k=2}^{K}\frac1k
 +\sum_{k=2}^{K}\frac{k}{k^2+d}+\log K\\
 &-\frac12\log\left[\kappa^2+\frac{4(K^2-1)}x\right]
 +\frac{f(K)}2+\frac{f'(K)}{12}+e_K,\quad
 0\le e_K\le-\frac{f'''(K)}{720}.
\end{split}
\]

这在同一个 x 变量上精确抵消 log(x)，不是调整 AE 常数。代码同时核对原式与重排式区间相交。

[fast_root.json](fast_root.json) 给出

\[
 11.45521916747093<\sigma_F/A<11.45521917819977,
\]

\[
 936174.2382721817<\sigma_F<936174.6820642408.
\]

区间端点是向外舍入的包围；精确值由共同参数决定。sigma_F/A 是静态背景固有时的增长率，单位是模型单位，不是秒^-1。

快根的导数/留数也由无限和认证。若 J=−R_d'，则
0<=J<=H/(6d²)，且中点积分与总变差给

\[
 \frac1{2(d+9/4)}-\frac9{16\sqrt3\,d^{3/2}}
 \le H_d'\le
 \frac1{2(d+9/4)}+\frac9{16\sqrt3\,d^{3/2}}.
\]

在根处利用根方程消去二次大项：

\[
 \mathscr D_y'
 =-p-\frac{2c_0}y+c_0'
 -C\left[\frac H6+\frac R3+\frac{y(y-2)}{48}H_d'
                         +\frac y{12}J\right],
\quad
 p=1+C[1/2-(C_A-29)/180],
\quad c_0'=-\frac{16Jn}{x(y+12)^2}.
\]

结果包括 \(-30<P'(\sigma_F)/A<-29\)，快极点留数严格非零。

## 3. 二阶差商证明完整复谱

取两个已认证、互不相交的正根
r1=s_*²、r2=sigma_F²；此时先不假设它们简单。冻结的慢根满足

\[
 1.9999999999909654<s_*<1.9999999999909663.
\]

有限截断可整理为二次多项式加正残数极点：

\[
 \mathscr D_N(y)=a_{2,N}y^2+a_{1,N}y+a_{0,N}
   +\sum_{k=2}^{N}\frac{W_k}{y+b_k},
 \quad b_k=4(k^2-1),
\]

\[
 W_k=\frac{8k^2(k^2-1)^{3/2}}{3\pi^2x}>0.
\]

k=2 的 W 再加 16Jn/x>0。原补偿求和在去掉负实极点的紧集上
O(k^-3) 局部一致收敛；对任意紧集，取 k 足够大后分母
1+(y/4−1)/k² 一致远离零，展开到补偿后的余项即可。更明确地，|y|<=M，D=M/4+1，
k²>=2 max(1,D) 时，令 u=1/k² 并二阶 Taylor 展开
sqrt(1−u)/(1+(y/4−1)u)，得到单项绝对值至多
M(1+3D+8D²)/(3k³)。这是紧集上的可求和 majorant。

定义

\[
 F(y)=\frac{\mathscr D(y)}{(y-r_1)(y-r_2)}
     =\mathscr D[y,r_1,r_2].
\]

两根处取可去延拓。对有限 N 的二阶差商，

\[
 \mathscr D_N[y,r_1,r_2]
 =a_{2,N}+\sum_{k=2}^{N}
 \frac{W_k}{(b_k+r_1)(b_k+r_2)(b_k+y)}.
\]

D_N(rj) 不必等于零；差商局部一致极限仍为 F。
置 alpha_k=W_k/[(b_k+r1)(b_k+r2)]>0，则

\[
 \operatorname{Im}F(y)
 =-\operatorname{Im}y\sum_k\frac{\alpha_k}{|b_k+y|^2}.
\]

虚部级数绝对局部一致收敛，严格异号，因此没有非实 y 零点。
实轴非极点上，

\[
 F'(y)=-\sum_k\frac{\alpha_k}{(b_k+y)^2}<0.
\]

又 \(\mathscr D(0)<0\)，所以 \(F(0)=\mathscr D(0)/(r_1r_2)<0\)。
于是 F 在 y>=0 全为负，原两根均简单，且没有第三个正根。
每两个相邻负极点之间，F 从 +infinity 严格降到 −infinity，恰有一个简单零点。
在 (−12,0) 同理恰有一个。

**完整结论：P 在开右半 s 平面恰有两个简单正实零点 s_*、sigma_F，没有非实右半平面根。**
其余有限零点是两负实对应根及由负 y 零点产生的纯虚根。
边界上的振荡指数不满足过去衰减合同，不能自动当作本 incoming 历史允许的齐次模式。

alpha_k/(b_k+y)=O(k^-1)，所以未重整的实部级数不能拆开单独求和。
必须与 a2_N 一同取极限。虚部、导数及 [INVERSE.md](INVERSE.md) 的减值形式均为绝对收敛级数。

## 4. 独立截断计数交叉证明

另一条证明使用

\[
 a_{2,N}=\frac{C_A/30-H_N}{24\pi^2x},\qquad H_N=\sum_{k=1}^{N}\frac1k.
\]

CA<400，N>=2^20 时 H_N>20log2>40/3>CA/30，故二次首项负。
D_N(0)<0，前驱统一小频界也对每个部分和成立，给 D_N(9)>5−8/x>0。
正残数产生 N−2 个 pole 间负根及 (−12,0) 的一个负根，再加两个正根，
共 N+1 个不同实根，恰好穷尽分子次数。无极点消去，因为 residue>0。
局部一致收敛和 Hurwitz 排除非实根。负根的唯一性和重数亦可由局部 Rouche 论证传递。

该证明不需要真的执行百万项截断。新代码检查系数与所需严格界；无限维论证是上述分析证明，并非声称已机器形式化。

## 5. 与数值小残差的关系

快模是完整固定 AE 方程的结果，不能按慢模区间外“没计算”而删除。
它也不能单独证明任何非线性历史不存在。其实际约束、态和曲率响应见
[STATE_MATCHING.md](STATE_MATCHING.md)，两个不同域上的逆见
[INVERSE.md](INVERSE.md)。
