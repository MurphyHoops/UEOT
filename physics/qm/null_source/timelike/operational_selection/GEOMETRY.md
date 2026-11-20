# 两项理想几何数据、误差控制与真正的零模编码差

## 1. 不改旧存在证书

采用冻结 U=z+w+v、Rz=10^-28、Rw=10^-51，
\[
\|v\|_{E_4}<4\times10^{-28}=:C,\qquad
D=\{|z|\le R_z/2,\ |w|\le R_w/2\}.
\]
v 只含总次数 n+m≥2。D 是实凸半矩形，严格位于已有解析域内部。
令 W(lambda)=(1+lambda)^4 log(e+lambda)、lambda=ns+m sigma。

## 2. 完整系数导数界

在 D 上，d=n+m≥2，
\[
|v_z|\le\frac C{R_z}\sup\frac{n2^{-(d-1)}}{W(\lambda)},\quad
|v_w|\le\frac C{R_w}\sup\frac{m2^{-(d-1)}}{W(\lambda)}.
\]
对 partial_z(Theta v)、partial_w(Theta v)，分子再乘 lambda。
这里确实是 partial(Theta v)；Theta(partial_z v) 少 s partial_z v，
Theta(partial_w v) 少 sigma partial_w v。

d/2^(d−1)≤1；W 单调增加，lambda/W(lambda) 在 lambda>1/3 严格递减。
含 z 导数的项有 lambda≥2s；含 w 导数的项有 lambda≥sigma+s。
冻结参数认证 W(2s)>1100、W(sigma+s)>10^25，故
\[
|v_z|<.004,\quad|\partial_z\Theta v|<.016,\quad
|v_w|<.04,\quad|\partial_w\Theta v|/\sigma<.041.
\]
这些是对无限系数和的界，没有截断 Taylor 级数。
若进一步按 m=1、m≥2 分组，w 两个 sup 实际可改为
1/[2W(sigma+s)]、(sigma+s)/[2W(sigma+s)]，但本轮保留上面的宽裕界。

## 3. 全域单射与显式逆误差

定义
\[
\mathcal G(z,w)=(U,\Theta U/\sigma)=(u,h/\sigma).
\]
其 Jacobian 的所有条目在同一个区间箱内：
\[
D\mathcal G=\begin{pmatrix}a&b\\c&d\end{pmatrix},\quad
a\in[.996,1.004],\ b\in[.96,1.04],\
|c|\le2.2\times10^{-6},\ d\in[.959,1.041].
\]
区间箱内任意矩阵均满足
\[
ad-bc\ge .996(.959)-1.04(2.2\times10^{-6})
=.955161712>.955.
\]
对 D 中任意两点，沿输入直线段平均 Jacobian：
Delta G=Jbar Delta p。Jbar 仍在同一区间箱，因而可逆。
所以 G 在整个 D 单射，无需假设像集 G(D) 凸。

显式逆矩阵给
\[
|\Delta z|\le1.091(|\Delta u|+|\Delta h|/\sigma),
\]
\[
|\Delta w|\le2.31\times10^{-6}|\Delta u|+
1.052|\Delta h|/\sigma,
\]
\[
\|\Delta p\|_\infty\le2.18\|\Delta\mathcal G\|_\infty.
\]
这是两个相容像集数据点的绝对误差界。任意有噪数据不自动属于像集；
Rw=10^-51 的相对快幅估计仍需极高精度。

在指定同一个物理时钟切片后，闭 S3 三曲率 6/a² 给 u=log(a/A)，
proper expansion H 给 h=aH。因此两项理想几何数据足以识别两幅度。
单个 a 读数不足：U_z,U_w>0 给 U 常值曲线，非零 determinant 保证 h 沿曲线改变。
在已标定的 proper T 上，先由 G 得 z,w，再由 eta=T−K(z,w) 得 eta，最后恢复 epsilon=z exp(−s eta)、delta=w exp(−sigma eta)。本页没有构造获得这些数据的 CP 仪器。

## 4. 原 incoming 零模相位不可重新归零

真实相位是
\[
\theta=\eta-t+B(z,w),\quad
B=\Theta^{-1}(e^{-2U}-1).
\]
proper time 的共同过去标定写作
\[
T=\tau_{\rm proper}/A=\eta+K(z,w),\quad
K=\Theta^{-1}(e^U-1).
\]
这是固定同一 incoming 原点的重整化差；不能在每条新几何的有限初片把 B 重置为零。

有精确积分
\[
B=\int_{-\infty}^0[e^{-2U(e^{s\xi}z,e^{\sigma\xi}w)}-1]\,d\xi,\quad
K=\int_{-\infty}^0[e^{U(e^{s\xi}z,e^{\sigma\xi}w)}-1]\,d\xi.
\]
D 在 xi≤0 的缩放下不变。又
\[
|v|\le C/[4W(2s)]<9.1\times10^{-32},\quad |U|<5.01\times10^{-29}.
\]
积分与其参数导数由 e^(s xi)、e^(sigma xi) 一致支配，故导数可交换。
e^(±U)、e^(±2U)、e^(±3U) 均在 [.999,1.001] 内，于是
\[
-2.08208/\sigma\le B_w\le-1.91808/\sigma,\quad
.95904/\sigma\le K_w\le1.04104/\sigma,
\]
\[
|B_z|\le2.010008/s,\qquad0<K_z\le1.005004/s.
\]

### 同 conformal time

同 epsilon、同 eta 时 z 相同，故
\[
|\Delta\theta|\le2.1|\Delta w|/\sigma\le2.1R_w/\sigma
<2.244\times10^{-57}.
\]
这是真正的跨几何编码差，绝不能将 1/sigma 本身当作该差。

### 同 proper time

两端 p_i=(z_i,w_i)∈D、同 epsilon，且 T1=T2。令
\[
\zeta=\int_0^1\epsilon e^{s[(1-t')\eta_1+t'\eta_2]}\,dt',
\]
则 Delta z=s zeta Delta eta，且 |zeta|≤Rz/2。
沿 D 内端点线段平均 K 的偏导，得到
\[
(1+s\zeta\overline K_z)\Delta\eta=-\overline K_w\Delta w.
\]
分母≥1−1.005004Rz/2>.999，故 |Delta eta|≤1.043|Delta w|/sigma。
同理
\[
\Delta\theta=(1+s\zeta\overline B_z)\Delta\eta+\overline B_w\Delta w,
\]
所以
\[
|\Delta\theta|<3.13R_w/\sigma<3.345\times10^{-57}.
\]
只使用两个端点与输入域的凸性，无需额外假定整条中间物理匹配族存在。
局部公式 partial_delta theta|T=e^(sigma eta)[B_w−e^(-3U)K_w] 的 leading 系数为 −3/sigma，也与有限差结果一致。

## 5. 接到实际可读资源

[CLOCK.md](CLOCK.md) 证明原零模 CQ 制备、全经典 p 标记下的
J<1.319×10^11，并且任意共同最终读取满足 Dtrace≤|Delta theta|sqrt(J)/2。
因此同 eta 的 Dtrace<4.08×10^-52，同 proper time 的 Dtrace<6.08×10^-52。

这些数值属于当前 Rw 与固定零模资源。它们不覆盖其他高模、额外探针、相干净化或编码中主动干预，
也不说明存在性认证域以外的快分支普遍不可观测。
几何可识别性与实际仪器分辨率是两项不同但已经可定量对接的责任。
