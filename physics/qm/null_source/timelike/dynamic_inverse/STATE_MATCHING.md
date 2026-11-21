# 几何与实际量子态的同步匹配

## 1. 两个几何怎样共享 canonical Cauchy 数据

取共同坐标 I×S3、单位球度量 gamma，

\[
 g_\pm=a_\pm(\eta)^2(-d\eta^2+\gamma),\qquad
 h=a'/a,\qquad V=a''/a.
\]

canonical momentum 以固定 dmu_gamma 密度记为 pi=a² phi'，因此 Cauchy
辛形式不含 a。固定 a,h 后，用恒等映射识别实际 (phi,pi) covariance，
等价于固定 (v,v') covariance，因为

\[
 \phi=v/a,\quad \pi=a(v'-hv),\quad
 \begin{pmatrix}\phi\\\pi\end{pmatrix}
 =\begin{pmatrix}a^{-1}&0\\-ah&a\end{pmatrix}
  \begin{pmatrix}v\\v'\end{pmatrix}.
\]

该矩阵行列式为 1。记 X=|v|²,Y=Re(v* v'),Z=|v'|²，则

\[
 C_{\phi,\pi}=
 \begin{pmatrix}X/a^2&Y-hX\\Y-hX&a^2(Z-2hY+h^2X)\end{pmatrix}.
\]

把 v' 当成实际法向导数，会遗漏 h 项。

## 2. 冻结片上态、单独改变 jerk 的 UV 障碍

固定 a,h,V 与旧实际 covariance，改变 j=V' 和 ell=V''。
AE 模式减除为

\[
 e_k^{sub}=k+E_1/k+E_3/k^3,\qquad
 p_k^{sub}=k/3+P_1/k+P_3/k^3,
\]

\[
 E_3=[q^2-2(h^2-1)q+2hf]/8,\quad
 P_3=-q^2/8-q''/12-(3h^2+1)q/12+hf/4,
\]

其中 q=−1−V，f=−V'，q''=−V''。故

\[
 \Delta E_3=-h\Delta j/4,\qquad
 \Delta P_3=\Delta\ell/12-h\Delta j/4.
\]

冻结实际 covariance 时 bare e_k,p_k 不变。单场减除和的变化为

\[
 \Delta\rho_N=
 \frac{h\Delta j}{16\pi^2a^4}H_N+O(1),\quad
 \Delta p_N=
 \left[\frac{h\Delta j}{16\pi^2a^4}
       -\frac{\Delta\ell}{48\pi^2a^4}\right]H_N+O(1),
 \quad H_N=\sum_{k=2}^{N}\frac1k.
\]

两场同时冻结时系数加倍。有限零模、有限 thermal 壳和有限 AE 局部项不能抵消
log N 发散。因此 h Delta j 非零时，这种 jerk 修补不在当前有限 RSET/Hadamard 合同内。
这没有否定该 covariance 的抽象 CCR 正性。

h=0 时能量对数项确实消失，不能无条件宣称所有 stress 分量发散。
在固定 a,h,V 的本设置中，旧 covariance 已 Hadamard，两个新片上 cutoff sums
都收敛的必要充分条件仅是 h Delta j=0、Delta ell=0。
它显著弱于全阶 Hadamard。

一个明确反例：固定 J≠0，旧 a=A，新 a=A exp(J eta³/6)。在 eta=0，
a,h,V 相同，Delta V'=J、Delta V''=0。冻结旧静态 covariance 后，
两个片上 sums 有限，但缺失 J/(8omega³) 的 cross covariance，所以新态不是 Hadamard。
不能把单片有限值升级为邻域内完整 RSET 合法。

## 3. 同步态调整怎样消除对数项

高频 Hadamard 模有

\[
 |v|^2=\frac1{2\omega}+\frac{V}{4\omega^3}
       +\frac{3V^2-V''}{16\omega^5}+\cdots,
\]

\[
 \operatorname{Re}(v^*v')=\frac{V'}{8\omega^3}
       +\frac{6VV'-V'''}{32\omega^5}+\cdots.
\]

所以改变 V' 时至少须同步

\[
 \Delta Y=\Delta V'/(8\omega^3)+O(\omega^{-5}).
\]

bare energy \(e=Z-2hY+(h^2+\omega^2)X\) 的变化产生
−h Delta j/(4k³)，恰与 Delta E3/k³ 相消。
压力保留的 Delta V''/12 也由完整 covariance 相应匹配。
[state_matching.py](state_matching.py) 从纯态行列式
XZ−Y²=1/4 展开 Z，独立还原完整 E3/P3，而不是只比较这一项。
补 leading cross covariance 不等于构造全阶 Hadamard 态。

## 4. 当前模类的全阶 Hadamard 判据

限定本项目的光滑正闭 FLRW、minimal massless 模型，所有足够高 k 的模纯且
齐次各向同性；有限热壳和有限维零模保留。
两几何在初片 a,h 一致，一份完整 canonical covariance 对旧几何已 Hadamard。
则用同一个 covariance 在新几何作 Cauchy 传播，仍为 Hadamard，当且仅当

\[
 V_+^{(j)}(0)=V_-^{(j)}(0)\quad\hbox{对所有 }j\ge0.
\]

这是本模类的独立推导，不是任意时空/任意态的未证明推广。

证明：纯高模给

\[
 r=\frac{v'}v+i\omega=\frac{Y-i/2}{X}+i\omega,
 \qquad r'-2i\omega r+r^2=V.
\]

写 \(r\sim\sum_{j\ge1}r_j/(2i\omega)^j\)，则

\[
 r_1=-V,\quad
 r_{n+1}=r_n'+\sum_{\ell=1}^{n-1}r_\ell r_{n-\ell},
 \quad r_j=-V^{(j-1)}+\hbox{低阶 jets 多项式}.
\]

前六项为

\[
 -V,\quad -V',\quad V^2-V'',\quad 4VV'-V''',
\]

\[
 -V^{(4)}+5(V')^2+6VV''-2V^3,
 \quad -V^{(5)}+18V'V''+8VV'''-16V^2V'.
\]

Re r=Y/X、Im r=omega−1/(2X) 保留全部奇偶信息。
Hadamard Cauchy symbols 只能相差 smoothing，在紧 S3 的谱对角类意味着系数差
比任意 k^-N 都快。三角递推逐阶强制所有 V jets 一致。
反过来，所有 jets 一致给相同全 symbol；旧 covariance 与新几何任一全阶参考
covariance 只差 smoothing，Cauchy Hadamard 判据及传播给充分性。

该框架可参阅 [Gérard–Wrochna, 1209.2604](https://arxiv.org/abs/1209.2604)，尤其
Cauchy parametrices 与 Hadamard covariances 部分。本节 iff 是本模型的推导。
有限八阶符号核验只检查递推实现，不能替代全阶分析证明。

全部 jets 相同不要求两条 smooth 几何未来相同。
例如 a_+=a_- exp(chi)，chi 在 eta<=0 为零、eta>0 为 epsilon exp(−1/eta²)，
就具有相同初片 jets 而不同未来。这是合法 off-shell 构造，并不自动满足 SCE。
如果两几何另为实解析，全部 jets 相同才会强迫局部相同。
Hadamard 匹配也不等于新几何的 incoming Jost covariance 恰好与旧片上数据相同：
后者依赖完整过去。

## 5. 快模通过完整线性约束，且不是 gauge

静态共同背景满足 rho0=3/(2x)、p0=−1/(2x)。对同 incoming 态的真实几何响应，
守恒律和过去归一化给

\[
 \delta\rho'=-3(\rho_0+p_0)u'=-3u'/x,\qquad
 \delta\rho=-3u/x.
\]

E=h²+1−2a²rho/3 的线性化因此是

\[
 \delta E=-\frac23x(2\rho_0u+\delta\rho)=0.
\]

若 P(sigma)=0，u=c exp(sigma eta) 也满足空间线性方程。
各向同性的其他约束为零。因此新快根不是仅满足 trace 的伪根。

实际 Jost 响应为

\[
 \delta v/v_0=\frac{\sigma}{\sigma-2i\omega}u,
\]

\[
 \delta X=\frac{\sigma^2u}{\omega(\sigma^2+4\omega^2)},\quad
 \delta Y=\frac{\sigma^3u}{2\omega(\sigma^2+4\omega^2)},\quad
 \delta Z=-\frac{\omega\sigma^2u}{\sigma^2+4\omega^2}.
\]

它满足 \(Z_0\delta X+X_0\delta Z=0\)，且
delta Y=delta V'/(8omega³)+O(omega^-5)，与前面的同步匹配一致。
canonical zero mode 采用同 Q/P，delta q=−2P u/(A²sigma)；
热 occupation 也未重选。

曲率 \(\mathcal R=6a^{-2}(1+V)\) 给

\[
 \delta\mathcal R=\frac6x(\sigma^2-2)u.
\]

背景曲率恒定，这个非零变化不能由 infinitesimal time shift 消除。

sigma_F>2s_*，所以 fast 模在过去是 o(exp(2s_* eta))。
同静态极限、同 incoming 态、同慢幅度和 beta 没有固定其线性幅度。
在 exp(−5eta) 加权的半过去空间中，fast 指数属于非零核，普通
norm(w)<=K norm(Lw) 不可能成立。它不证明非线性精确解不唯一或无解。

## 6. 新因果逆与态的接缝

[INVERSE.md](INVERSE.md) 的 G 只直接保证 C1，但对
f in C_c^infinity((0,infinity))，w=G*f 的全部导数可转移到 f，
因此 w 光滑、零过去、所有初片 jets 为零。

对每个 a_lambda=A exp(lambda w)，用原 incoming 态精确作 KG/Jost 运输，
给一个合法的 off-shell 几何—态族，其切向量满足 Lw=f。
有限观察窗内 a_lambda 光滑正。这里 f 是校正算子的数学测试残差，
没有被偷偷添加为物理设备或改变源强。

原慢 seed 在 eta=0 一般有非零残差；既保持它的整个过去，又任意换一个 jerk
或把残差突然接入，都不属于上面的光滑零过去域。这个匹配责任继续保留。

## 7. 继续推进：双变量精确 incoming 态的收敛构造

这一步先关闭实际态构造，不宣称几何满足非线性 SCE。
本节 A 是包含常数项与一次项的完整双圆盘 Wiener 代数，区别于 INVERSE 第6节仅含总阶至少二的校正空间。
取 u00=0，Theta=s_* z partial_z+sigma_F w partial_w，
V=Theta²u+(Theta u)²∈A。所有非零单项式的 lambda_nm>=s_*>0。

令 F_{+,00}=F_{-,00}=1，定义

\[
 F_{\pm}=1+K_\pm(VF_\pm),\qquad
 (K_\pm f)_{nm}
 =\frac{f_{nm}}{\lambda_{nm}(\lambda_{nm}\mp2i\omega_k)}
 \quad(n+m\ge1).
\]

分母的模至少 2 omega_k lambda_nm，所以
norm(K_pm)<=1/(2omega_k s_*)。实际上不需要小范数假设。
令 T_k=K_pm M_V，a_k=norm(V)/(2omega_k s_*)。
每次乘 V 至少增加一个非零正频率。T_k^j 作用在任意 H∈A 时，
每条卷积路径的第 ell 个累计频率至少 ell s_*，故

\[
 \|T_k^j\|_{\mathcal A\to\mathcal A}\le a_k^j/j!.
\]

于是 Neumann 级数对任意有限 norm(V) 收敛，左右乘 I−T 都给恒等算子。
所以 F_pm 唯一，且为 V 的 entire Banach-space 函数，并有

\[
 \|F_{\pm,k}\|_{\mathcal A}\le e^{a_k},\quad
 \|\Theta F_{\pm,k}\|_{\mathcal A}
 \le\frac{\|V\|e^{a_k}}{2\omega_k},\quad
 \|\Theta^2F_{\pm,k}\|_{\mathcal A}\le\|V\|e^{a_k}.
\]

后两界分别使用 Theta K 的乘子 1/(lambda∓2iomega) 的模不超过 1/(2omega)，以及 Theta² K 的乘子 lambda/(lambda∓2iomega) 的模不超过 1。
V00=0 不可省略。u00=0、Theta²u∈A 已保证 V∈A，因为
norm(Theta u)<=norm(Theta²u)/s_*。
这是精确收敛模，不是有限阶截断。

沿 z=epsilon exp(s_*eta)、w=delta exp(sigma_F eta)，
v_k=exp(−iomega_k eta)F_+(z,w)/sqrt(2omega_k) 满足精确 KG，
并具有原 incoming 正频归一化。实系数几何上 F_−=conjugate(F_+)。
复 bidisc 上须把 F_+、F_−视为独立解析伙伴，不能把 abs(F)^2 误称为全纯函数。

\[
 \Theta[F_-\Theta F_+-F_+\Theta F_--2i\omega F_-F_+]=0.
\]

所有非零频率严格为正，故该 Wronskian 等于其常数项 −2iomega。
canonical 归一化及纯高模的正性因而保留。

零模也保持同一 Q/P：

\[
 q=Q+\frac{P}{A^2}
 \left[\eta-\eta_{\rm ref}+\Theta^{-1}(e^{-2u}-1)\right],
 \qquad (\Theta^{-1}f)_{nm}=f_{nm}/\lambda_{nm}.
\]

这严格给 q'=P/a²，并固定过去校正为零。eta_ref 保持前驱原值，不吸收到 Q 中重新选择态。完整 Q/P 分布、有限热壳 occupation
都没有重选。

具体非空例 u=z+w 可取 Rz=1/100、Rw=1/(100 sigma_upper²)。
新区间证书给 norm(V)<0.051、全 k 的收缩比<0.008。
它是明确的 off-shell 共同态族，尚不是精确 SCE 解。这个小范数只是定量例子，通用构造不要求小范数。

在每个严格内圆盘沿真实 eta 的历史上，解析函数给全阶几何导数。若 a=min(log(Rz/rz),log(Rw/rw))>0，则 norm(Theta^j V)_r <=sigma_F^j j! a^-j norm(V)_R；沿过去再乘 exp(s_*eta)，所以各阶导数都有过去 L1 界。
过去所有这些导数指数衰减。逐阶 Jost/WKB 余项的 Volterra 积分及反复分部积分
得到任意高阶 UV 展开，所以在每个有限观察窗为 Hadamard。
全阶正则性在严格内圆盘使用，不能从此跳到外圆盘边界上
完整重整化应力的 same-radius norm/Lipschitz 界。
后者正是下一非线性验收，仍未关闭。

相关 incoming-Hadamard 框架另见 [Gérard–Wrochna, 1609.00190](https://arxiv.org/abs/1609.00190)；其严格正渐近算子条件仅用于有谱隙的 k>=2 高模分析，不能无说明地套到本无质量零模。零模由上面的正规 Q/P 态另行补回；exact modes 从未假定在 1/k=0 解析。
