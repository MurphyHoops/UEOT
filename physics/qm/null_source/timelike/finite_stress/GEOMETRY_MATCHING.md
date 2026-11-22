# 同一实际态的正窗残差、补偿应力与真实有限片修正

本页接着 FINITE_SLICE_UV 的合法初片态验收，直接回到原两个自由场、
原固定 M2/U0、原完整重整化平均方程。只读取冻结的 KERNELS、
EXISTENCE 和数值包围，不重跑旧求根、旧 checker 或任何 ODE。

先排除一条明确的 prescribed 曲线，再从已有精确平均历史中构造满足
a(0)=A、h(0)>0 的真实截面。这两项的幅度和定义域不同，不能把第一项
的误差界移植成第二项的大振幅存在定理。全部结果仍是原模型内 mean 层；
完整涨落几何、联合量子边界密度和装置并没有因此闭合。

## 1. 固定同一态的 off-shell 函数与可用常数

沿任一允许几何，原 incoming Jost/零模数据一次固定，由同一精确
KG 演化运输，使用同一 RSET 减项。记

\[
 a=Ae^u,\quad h=u',\quad
 E=h^2+1-\frac23a^2\rho,\qquad
 S=h'+\frac{h^2+1}{2}+a^2p.
\]

冻结材料已经证明在正频率 Wiener 空间

\[
 \|u\|_{E_4,R}=\sum_{n,m}
 w_4(ns_*+m\sigma_F)|u_{nm}|R_z^nR_w^m,\quad
 w_4(\lambda)=(1+\lambda)^4\log(e+\lambda)
\]

中，S 在半径 r0=0.1 的球上全纯且 ||S||A<4。
常数与系数圆盘半径无关。DS(0)=P(Theta)，||D²S||≤6400
于半径 0.05 球内。原实际同态 Ward 恒等式是

\[
 E'+hE=2hS,\qquad
 E=e^{-u}\Theta^{-1}[2e^u(\Theta u)S].                 \tag{103}
\]

这里 inverse 是正频率 incoming inverse，积分常数由同一静态过去
固定；不偷换成任意有限片自由常数。频率至少 s*>1.5，
故 ||Theta inverse||A≤1/s*，||Theta u||A≤||u||E4。
在半径 0.1 球上

\[
 \|E\|_A<
 2e^{0.2}(0.1)4/1.5<1.
\]

E 的零次、一次项都为零；沿单位 E4 方向作单变量 Cauchy，
在 N=||u||E4≤0.05 时给出实际余项

\[
 \|S-Pu\|_A\le3200N^2,\qquad
 \|E-E_2\|_A\le
 \frac{(10N)^3}{1-10N}\le2000N^3.                  \tag{104}
\]

这用的是已证明的完整 holomorphic RSET，不是形式级数的小量记号。

## 2. 一个固定正窗候选及其初片残差

取一次固定 c=10^-16、z=e^(s* eta)，

\[
 u_c=c(z^2-z),\quad
 0\le\eta\le T_p=\log(1.01)/s_*.
                                                               \tag{105}
\]

所有过去 eta≤0 都接到同一静态 incoming 数据。整个正窗
1≤z≤1.01 严格位于系数半径 R=1.02 内，因此可求全部实际时间导数。
这是明确给定的几何，不声称它自行满足 Einstein 方程。
冻结 s* 和 P2=P(2s*) 的包围蕴含

\[
 1.9<s_*<2.1,\qquad 11<P_2<13.
\]

直接按同一 E4 范数，

\[
 N=c[w_4(s_*)R+w_4(2s_*)R^2]<2000c=2\,10^{-13}.
\]

P(s*)=0，故

\[
 S_1=cP_2z^2,\qquad
 E_2=c^2P_2\left(z^4-\frac23z^3\right).             \tag{106}
\]

(106) 由 E2'=2hS1 与 incoming 常数零直接积分；在 eta=0，
E2=c²P2/3>0，而 S1=cP2>0。它不是沿 on-shell 线性核方向，
所以没有与 TOTAL_BOUNDARY_GATE 的二阶退化结论冲突。

(104) 给 ||S−S1||<1.28e-22、||E−E2||<1.6e-35。
由 z≥1 时 (106) 单增，整个正窗安全包含于

\[
 3.6\,10^{-32}<E<4.7\,10^{-32},\qquad
 1.09\,10^{-15}<S<1.33\,10^{-15}.                  \tag{107}
\]

相应 0≤u≤1.01e-18，
1.9e-16<h<2.164e-16。因此初片和正窗都没有满足原 mean-SCE，
不能因初片 a=A 或密度残差很小就签收。这项否决包含真实无限模
重整化余项；并非只看前两项。

## 3. 实际法向导数和补偿装置的必要应力

采用原 G=2T 归一化。如保持同一几何和同一原场平均泛函，
另加 homogeneous 应力，必要值唯一为

\[
 \rho_d=\frac{3E}{2a^2},\qquad p_d=-\frac{S}{a^2}. \tag{108}
\]

整个窗必须使用 a=Ae^u，不能在初片之外仍用 A。
由 (103)，(108) 自身满足

\[
 \rho_d'=-3h(\rho_d+p_d),\qquad
 n^\mu\nabla_\mu\rho_d=-\frac{3h}{a}(\rho_d+p_d).
                                                               \tag{109}
\]

严格保守界为

\[
 \frac{5.3\,10^{-32}}{A^2}<\rho_d<
 \frac{7.1\,10^{-32}}{A^2},
\]

\[
 -\frac{1.34\,10^{-15}}{A^2}<
 \rho_d+p_d<
 -\frac{1.06\,10^{-15}}{A^2},
\]

\[
 \frac{5.9\,10^{-31}}{A^3}<
 n^\mu\nabla_\mu\rho_d<
 \frac{8.8\,10^{-31}}{A^3}.                         \tag{110}
\]

因此必要补偿源在整个窗有正能密度、严格负 rho+p，并且能密度
沿未来单位法向增加。minimally coupled、正 canonical kinetic
的 classical scalar 有 rho+p=(n chi)^2≥0，任意势都不能改变此号。
它或此类场的和不能单独实现 (108)。

这只排除保持上述原场泛函的 additive、homogeneous 经典补偿方式。
重整化 quantum controller、其他明示的装置作用量、或者改变原场
演化的强相互作用，不在此排除结论中；后者必须重算完整总应力。
(108) 是必要应力，不是一台已构造的装置。

同一原场本身也有可计算的真实法向导数：

\[
 \rho+p=\frac{1+h^2-h'+S-\frac32E}{a^2},\qquad
 n\rho=-\frac{3h}{a^3}
       (1+h^2-h'+S-\tfrac32E)<0.                  \tag{111}
\]

检查器直接认证括号严格为正及完整正窗负导数界。
对于原零模，P 始终守恒，而

\[
 n\phi=P/a^3,\qquad n^2\phi=-3hP/a^4.             \tag{112}
\]

初片一阶速度 P/A³ 与静态值相同，二阶法向导数却非静态。
“保留 P 律”不能代替“保留原全部初片 jets”。

## 4. 在已有真实 mean-history 中修正初片条件

冻结 EXISTENCE 已构造精确
U(z,w)=z+w+v(z,w)，保留慢根 s* 与快根 sigma_F。
旧常数是 rho=10^-25、Kinv=2e20、H2=6400、
q=Kinv H2 rho=0.128<1；
旧双圆盘 Rz=10^-28、Rw=10^-51。
本节新增的是从该已存在族中选出一个非静态的 a(0)=A 截面，
不把旧 mean 存在性再次计作新发现。

现在另取 c_m=10^-55。用单位半径的形式变量 X,Y 和
g_w=-c_m X+wY，w∈[0.9c_m,1.1c_m]。
记 Ws=w4(s*)、Wf=w4(sigma_F)、W2=w4(2s*)，以及

\[
 r(w)=W_s c_m+W_f|w|,\quad
 C_0=\frac{K_{\rm inv}H_2}{2(1-q)}.
\]

r(w)<rho/2。唯一旧固定点给

\[
 \|v_w\|_{E_4}\le C_0 r(w)^2.                     \tag{113}
\]

所有操作保留正频率和二变量次数，故 v_w 的 m=0 部分就是 v_0；
其余含 m≥1，频率至少 sigma_F。系数投影不增 Wiener 范数。
因此实际点值校正可按各频率除权重：

\[
 |v_w(1,1)|\le
 \frac{C_0(W_s c_m)^2}{W_2}
 +\frac{C_0 r(w)^2}{W_f}=:\Delta<c_m/1000.         \tag{114}
\]

粗合并的 E4 点界在这里不足；保留慢／快频率权重是关键。
F(w)=-c_m+w+v_w(1,1) 在两端严格异号。
两参数固定点之差只含 m≥1，收缩估计又给

\[
 |v_w(1,1)-v_{\tilde w}(1,1)|
 \le\frac{q}{1-q}|w-\tilde w|,\qquad
 \frac{q}{1-q}<0.147.                             \tag{115}
\]

因此 F 严格递增，存在唯一 w*∈[0.9c_m,1.1c_m]，
且 |w*−c_m|≤Delta。也可由 w_next=c_m−v_w(1,1) 的严格
收缩定义同一根，有显式几何误差界；没有逐时重新选根。

lambda/w4(lambda) 在 lambda≥2s*>3 上严格下降。分开两频率扇区，

\[
 |\Theta v_w(1,1)|\le
 \frac{2s_*}{W_2}C_0(W_s c_m)^2+
 \frac{\sigma_F}{W_f}C_0r(w)^2=:\Delta_h.
\]

检查器认证

\[
 h(0)=-s_*c_m+\sigma_F w_*+\Theta v_{w_*}(1,1)
 \ge c_m(0.9\sigma_F-s_*)-\Delta_h>0.             \tag{116}
\]

## 5. 一次选参、同一合法态和真正正时间窗

取这一个 w*，固定整条历史

\[
 a_m(\eta)=A\exp U(-c_m e^{s_*\eta},
                         w_*e^{\sigma_F\eta}),\quad
 0\le\eta\le T_m=1/\sigma_F.                       \tag{117}
\]

单位半径 X,Y 的估计只直接评价初片 (1,1)，不延用到未来 X,Y>1。
逐系数结构及固定点唯一性给 u_w(X,Y)=U(-c_m X,wY)；
未来改用已冻结 normalized U 的原 Rz/Rw 双圆盘。
两物理坐标在整段及所有更早过去严格位于该双圆盘内部。
a_m(0)=A 严格成立，h_m(0)>0；
proper duration 在 A exp(±rho)/sigma_F 之间，使用模型单位。
原 incoming 零模数据、NOON/thermal 二点数据、固定 M2/U0 与
renormalization scheme 不重置；实际 finite-slice 量子态由同一
精确 KG 输运，并具有冻结定理证明的 CCR、正性与 Hadamard 正则性。
不同几何的 raw Cauchy 协方差并不相同，需满足 FINITE_SLICE_UV
导出的高频匹配；h0 虽然极小，只要非零，该要求仍在。

冻结完整平均方程和 Ward 现在直接给

\[
 S[U]=E[U]=0,\qquad
 n^j(3E/a^2)=n^j(-2S/a^2)=0
 \quad\text{对每个有限 }j.                        \tag{118}
\]

这里零残差是解析恒等式；程序没有数值展开全部无限级数或积分 ODE。
它并不表示实际物质密度静止：在初片，

\[
 \rho_m(0)=\frac{3(1+h_0^2)}{2A^2},\qquad
 p_m(0)=-\frac{h'_0+(1+h_0^2)/2}{A^2},\qquad
 n\rho_m(0)=-\frac{3h_0}{A}(\rho_m(0)+p_m(0)).
\]

这些是同一演化中的实际源量，不能由 static 数值账本替换。
(117) 是同一实际源、同一固定参数和同一正窗内的真实平均历史。
它既不是 (105) 的大幅度修复误差定理，也没有删除快根。

## 6. 反思与下一闭环

单独指定几何并用一个小的 density 残差判断可行，会漏掉一阶 pressure
残差与装置的必要能量条件。本页以真实 RSET 余项排除 (105) 的普通
标量修复，又用原已证明的 mean family 构造满足有限片尺度条件的
(117)，从而把“同步改变合法态”和“实际平均约束”接起来。

但 (117) 的两个幅度仍是明示选择，没有由唯一物理制备原则选出；
极小半径是充分条件，不是自然的可观测尺度。原 static 附近的 CTP
噪声／响应结果不能不经推导直接移植到这个非静态背景。

下一项因此具体变成：在 (117) 的同一实际有限片态上，计算原总作用量
的 lapse/density 和全部 momentum 初始约束映射、绝对噪声与交叉块，
审查能否由正常 geometry–matter–device 密度实现；再建立因果
正窗和误差。若改用 BOUNDARY_STATE 的薄层关联源，应先重算它在
此动态背景的实际完整噪声与制备总源，不能套用 static 数值预算。

完整 CTP、总装置、局域读出和经验引力校准仍 OPEN。
