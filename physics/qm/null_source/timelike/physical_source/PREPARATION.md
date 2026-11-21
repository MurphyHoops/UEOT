# 固定旧静态过去的自由量子装置排除

## 合同

旧准备族在 eta<=-1/8 保持 A=sqrt(3)lambda，lambda=32768。原项目把该 S3 当作辅助 Cauchy 表示，未宣告它就是有限内球的物理外区。本定理只考察把整个静态 S3 过去提升为物理历史的特定完成。

保留原自由最小无质量量子场、正规零模、每个原初片根一次固定的 M2、AE mu=1 与额外曲率项零。只新增一个同参数自由标量设备；在整个静态过去，它独立守恒、没有交换或外驱。设备选择一个正规 Hadamard 态，零模二阶矩有限。允许非齐性、跨模相关、混合、非 Gaussian、coherent 与 squeezed；只使用两点函数。

## 绝对参考值

沿用 README 的 B(A^2)、E(A^2)。原完整参考 NEC 为 E/A^4，其正规零模贡献是 1/(4pi^2 A^4)。所以非零模静态真空及固定 AE 项的绝对基准为

\[
N_{\mathrm{nz},0}=\frac{E-1/(4\pi^2)}{A^4}.
\]

这是扣掉一个真实有限零模的值，未改变重整化。

设备零模按 [Q,P]=i、
phi_0=[Q+P eta/A^2]/sqrt(2pi^2) 定义，其 NEC 是

\[
N_{D,0}=\langle P^2\rangle/(2\pi^2A^6)\ge0.
\]

设备可任意正规挤压，不能假定它保留原参考 Var P=A^2/2，也不能假定存在静态振子零模真空。

## 全态的长时平均

取 V=2pi^2A^3，实正交谐函数 j=(k,alpha)，k>=2，
Omega_j=sqrt(k^2-1)/A。静态过去一次固定 annihilation operators，记

\[
n_j=\langle a_j^\dagger a_j\rangle\ge0,\quad m_j=\langle a_ja_j\rangle.
\]

定义空间平均

\[
\overline N_D(\tau)=V^{-1}\int_{S^3}
[T_{uu}+\tfrac13\sum_i T_{e_ie_i}]\,dV.
\]

空间正交消去跨模式项；coherent 位移已包括在 n,m 中。直接由最小场应力得到

\[
\overline N_D
=N_{\mathrm{nz},0}+\frac{\langle P^2\rangle}{2\pi^2A^6}
+\frac1{3V}\sum_j\Omega_j
[4n_j-2\Re(m_je^{-2i\Omega_j\tau})].
\]

同一背景两个 Hadamard 两点函数之差光滑。其 QQ、PP、QP Cauchy 核在紧 S3 x S3 上光滑，对 Laplacian 任意次分部积分使对角谱系数快速衰减。因此 sum|m_j| 与 sum Omega_j n_j 都有限。这一步使用 Hadamard 正则性，不从“有限能量”四字独自推出全部求和条件。

任意长度 L 的过去区间上，振荡项平均绝对值不超过

\[
\frac2{3VL}\sum_j|m_j|.
\]

所以

\[
\lim_{L\to\infty}\frac1L\int\overline N_D\,d\tau
=N_{\mathrm{nz},0}
+\frac{\langle P^2\rangle}{2\pi^2A^6}
+\frac4{3V}\sum_j\Omega_jn_j
\ge N_{\mathrm{nz},0}.
\]

该下界可以由高模真空和 Var P 趋零的正规高斯逼近；不宣称零模正规真空达到它。

## 与原静态总方程的矛盾

G=2T 在静态 S3 要求 rho+p=1/A^2。原 coherent 项为 M2/A^6；设备必须恒定地提供

\[
N_{\rm req}=A^{-2}-M_2/A^6-E/A^4.
\]

原 M2=27lambda^4-54lambda^2 Qrho，|Qrho|<=508。因此

\[
A^4(N_{\mathrm{nz},0}-N_{\rm req})
=2A^2-18Q_\rho+2E-\frac1{4\pi^2}.
\]

A^2=3221225472，而 2A^2-18*508=6442441800。
有向区间给严格 gap>6442441799，等价

\[
A^2(N_{\mathrm{nz},0}-N_{\rm req})>1.999997.
\]

恒定目标的长时平均仍等于目标，与下界矛盾。加一个常数势的 NEC 为零，若 A/M2/自由设备合同保持不变，也不能解除这个 NEC 矛盾。

## 负控：量子瞬时负 NEC 合法

单个实非零模取 n=1/8、m=3/8，有 |m|^2=n(n+1)，是纯 squeezed Gaussian，r=(log2)/2，有限秩修改保持 Hadamard。选相位后

\[
\Delta\overline N(0)=-\Omega/(12V)<0,\quad
\Delta E=\Omega/8>0,\quad
\overline{\Delta N}^{\,\rm long}=\Omega/(6V)>0.
\]

整壳同样挤压只乘 k^2 并保持各向同性。此例检查本定理没有偷用逐点 NEC。

## 未排除对象与文献

没有排除旧局部后释放存在定理、有限开始准备、不同外区、相互作用/交换、不同质量/耦合或另一个物理重整化模型；未证明原数学 driver 的一般量子实现不存在。

Hadamard 差的正则性背景见 Fewster, [The art of the state](https://arxiv.org/abs/1803.06836)，第2节。
静态能量时间平均的背景见 Pfenning–Ford, [gr-qc/9608005](https://arxiv.org/abs/gr-qc/9608005)。
本轮特定 NEC Cesaro 公式、零模处理和数值 gap 由上述直接推导及 static_source.py/constraint.py 承担，未把一般 QEI 当充分实现条件。
