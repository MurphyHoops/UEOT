# 重叠窗的因果对数核、标量主部反演与 Hadamard 态差定理

[检查器](check.py) · [精确区间回执](result.json) · [共同合同](../CONTRACT.md) · [显式局域块](../resolvent/README.md)

基线：c57e2f411e58dc1dae60de8f3c97fbd680e46d8b。本节推进严格分离时间窗之外的响应，但区分三个对象：已定义的 UV 对数分布、其标量时间主部的精确逆、同背景光滑态差的完整一阶响应。尚未构造实际 prepared 最小无质量场的完整闭 FLRW baseline polarization。

## 1. 固定物理问题与指标约定

保留 a_lambda=λ√(3cos2η)、λ=32768、原始制备及参考量子态。继承物理 μ=1、α=0、无额外有限曲率项，相对于同一固定参考处方 c_extra=0。下文标量 normal form 的参数 c 是数学参数，其数值例不为原项目另选耦合。

额外有限项为零，不表示固定参考 RSET 的接触项为零。参考减除的 metric 变分、显式指标变分和定义推迟分布所需的局域补项都须保留。定义
\[
\mathcal R_{\rm eff,cov}[h]_{ij}
=a_\lambda^2\gamma_{ik}\delta\langle T^k{}_j\rangle^{TT},
\qquad \Pi_{\rm ref}^{TT}=a_\lambda^{-2}\mathcal R_{\rm eff,cov},
\]
\[
D_T h-4\mathcal R_{\rm eff,cov}[h]=f,\qquad f=4a_\lambda^2F.
\]
F 是外加 mixed TT 应力。raw covariant δTij 的压力乘 h 项在升指标后抵消，不能再加第二次。前驱分离窗 susceptibility 只冻结为已有证据，不充当重叠反馈范数。

## 2. 非零 UV 系数与合法的因果有限部分

一个实无质量标量的平直 spin-2 谱为
\[
\rho_T(s)=\theta(s)s^2/(960\pi^2),\qquad
\beta_T=1/(1920\pi^2)>0.
\]
该系数与曲率耦合 xi 无关。用 beta_T 避免与局部 R² 参数 b 混淆。与 delta HC=−Box²h 的约定一致，
\[
\delta T_{\rm nl}^{TT}
=-\beta_T(K^2)^2
\log[(K^2-i0\,{\rm sgn}\omega)/\mu^2]\,h^{TT}. \tag{1}
\]
谱与因子来自 [AMM 2009, (2.1), (2.4b), (2.5b), (2.6)](https://arxiv.org/pdf/0907.0823)；同文 HC=−A 的约定固定符号。这只识别 UV 主部，不把完整共形 de Sitter 或平直真空核移植到本 prepared 最小场。Hadamard 态的光滑改变不能消去共同领先奇性；实际背景的曲率次主项仍需控制。

对平直空间 Fourier 参数 k≥0、μ>0，定义 t>0 上的普通局部可积函数
\[
q_{k,\mu}(t)=-2\left[\gamma_E+\log(\mu t)
+\int_0^t\frac{\cos(kr)-1}{r}dr\right],
\quad K_{k,\mu}=D_t[\theta(t)q_{k,\mu}(t)]. \tag{2}
\]
先定义局部可积 q 的零延拓，再取分布导数；没有把未经延拓的奇异应力核直接乘不连续 theta。k 不是闭三球的 TT 模式编号。

右半平面 Laplace 变换为
\[
\mathcal LK_{k,\mu}(p)=\log[(p^2+k^2)/\mu^2],\quad {\rm Re}\,p>0. \tag{3}
\]
用 L(logt)=−(γE+logp)/p 与 Frullani 恒等式
\[
\int_0^\infty e^{-pr}(\cos kr-1)dr/r
=-\tfrac12\log(1+k^2/p^2)
\]
即可验证；后式对 k 求导、再用 k=0 的值证明。对数取由 p>0 连续延拓的解析分支。

等价的截止公式是
\[
(K*f)(t)=-2\lim_{\epsilon\downarrow0}
\left[(\gamma_E+\log(\mu\epsilon))f(t)+
\int_\epsilon^t\frac{\cos kr}{r}f(t-r)dr\right]. \tag{4}
\]
有限 epsilon 的误差满足
\[
2\epsilon\|f'\|_\infty+(k^2\epsilon^2/2)\|f\|_\infty. \tag{5}
\]
减去 f(t)，用 |f(t−r)−f(t)|≤r||f'|| 与 |coskr−1|≤k²r²/2 即得。
这与 [AMM 2009 Appendix A, (A3), (A7)–(A9), (A13)](https://arxiv.org/pdf/0907.0823) 的因果有限部分一致。

检查器对 f=t⁴、k=3、μ=1、t=1/8，独立比较 primitive 卷积展开与截止式的三个 epsilon；两边都有解析 Taylor 余项和70位有向区间，没有用浮点求积差充当误差。一般单项式的 primitive 展开是
\[
K*t^m=2t^m(H_m-\gamma_E-\log\mu t)
-2m!\sum_{n\ge1}\frac{(-1)^nk^{2n}t^{2n+m}}{2n(2n+m)!}.
\]

### 2.1 尺度变化和时间域映射

\[
K_{k,\nu}-K_{k,\mu}=-2\log(\nu/\mu)\delta. \tag{6}
\]
因此 (c_W+beta_T K)deltaHC 在 c_W(ν)=c_W(μ)+2beta_T log(ν/μ) 的共同变换下不变。这是一般记账恒等式；本轮物理 μ 保持1。共形时间缩放还会给局域位移，normal form 的 μ 不自动等于物理标尺数值。

在有限时间上
\[
\|q\|_{L^1(0,T)}\le Q
=2T[1+|\gamma_E+\log(\mu T)|]+k^2T^3/6. \tag{7}
\]
用 log(μt)=log(μT)+log(t/T)、∫|log(t/T)|dt=T 和余弦余项得到。
对 W^(1,p) 中只要求左端 f(0)=0 的输入，
\[
K*f=q*f',\qquad \|K*f\|_p\le Q\|f'\|_p,\quad1\le p\le\infty. \tag{8}
\]
没有右端条件。若 f(0)≠0，须补 f(0)q(t)。
P4=(∂t²+k²)² 的因果输入若 h^(j)(0)=0（0≤j≤4），则
\[
\|\beta_TK*P_4h\|_p\le\beta_TQ
(\|h^{(5)}\|_p+2k^2\|h^{(3)}\|_p+k^4\|h'\|_p). \tag{9}
\]
它是明确分布的 Sobolev 映射，不宣称 K 本身为普通 L1 核，也不认证完整曲时空核。

## 3. 标量时间对数主部的精确因果逆

令 L_mu=K_0,mu/2，Laplace 符号为 log(p/μ)。对 κ>0、μ>0、c实数，
\[
\mathsf L=c\delta+\kappa L_\mu,\qquad p_*=\mu e^{-c/\kappa}>0.
\]
将反馈方程乘 a_lambda²/4 后，冻结系数的纯时间 UV 主部中 logp 系数为 κ=2beta_T；二倍来自 log(p²)=2logp。这里没有把常数 c 等同于尚未完整计算的参考接触项。

精确因果逆为
\[
\boxed{r(t)=\frac1\kappa\int_0^\infty
\frac{p_*^u t^{u-1}}{\Gamma(u)}du},\quad t>0. \tag{10}
\]
所有被积项为正。令 ν(q)=∫0∞ q^u/Γ(u+1)du，则 Tonelli 给
\[
\|r\|_{L^1(0,T)}=\nu(p_*T)/\kappa<\infty.
\]
rho>p* 时再次交换正积分，
\[
\int_0^\infty e^{-\rho t}r(t)dt
=\frac1\kappa\int_0^\infty(p_*/\rho)^u du
=\frac1{c+\kappa\log(\rho/\mu)}. \tag{11}
\]
右半平面的解析延拓证明 L*r=delta，属于指数阶因果分布的逆。于是
\[
\|r*F\|_{L^p(0,T)}\le[\nu(p_*T)/\kappa]\|F\|_p.
\]
对 ∂t⁴ L h=F 的零初值问题，h=I⁴(r*F)，再乘 T⁴/24 即为响应界。它给未来余项接入的接口，不代表当前曲背景余项已被界住。

主对数分支的谱表示为
\[
r(t)=\frac1\kappa\left[
p_*e^{p_*t}+\int_0^\infty
\frac{e^{-xt}}{\log^2(x/p_*)+\pi^2}dx\right]. \tag{12}
\]
负实轴分支切口贡献为正，正实极点留数为 p*/κ；检查器分别核对。增长极点被保留，因此这里没有宣称稳定逆，也没有暗中换边界条件删除极点。t→0 时由 1/Γ(u)=u+O(u²) 得
\[
r(t)\sim[\kappa t\log^2(p_*t)]^{-1},
\]
奇性局部可积。

### 3.1 有严格尾界的质量常数

设 Λ(q)=(q−1)/logq，Λ(1)=1。写 u=n+v、0≤v≤1，
\[
e^{-1}n!\le\Gamma(n+v+1)\le(n+1)!.
\]
下界来自 Γ(v+1)≥∫1∞e^−x dx=e^−1 和递推；上界来自整数端点间的对数凸性。因此
\[
\Lambda(q)(e^q-1)/q\le\nu(q)\le e\Lambda(q)e^q. \tag{13}
\]
q<N+1 时 u≥N 的尾不超过
\[
e\Lambda(q)\frac{q^N}{N!}[1-q/(N+1)]^{-1}. \tag{14}
\]
检查器认证 κ=μ=1、c/κ=−1,0,1、T=1/8、N=16 的辅助例及 rho=2p* 时的精确权重范数1/log2。这些例不是新的物理耦合选择。定理和有理区间决定结论，显示浮点上界另向上取一格。

## 4. 同一实际背景上的重叠 Hadamard 态差

设同一 prepared 背景上的两 Hadamard 态分别在共同过去保持各自初始数据；两态不要求相同。S=W1−W0 是光滑、实对称 bisolution。共同 Hadamard 奇性和 CCR 消去奇异部分；复合场 metric 响应和显式变分的框架见 [Hollands–Wald 2005 §4.3、Appendix A](https://arxiv.org/pdf/gr-qc/0404074)。

令
\[
P=\partial_\eta^2+2\mathcal H\partial_\eta-\Delta_\gamma,\quad
V_h=\delta P=D_i(h^{ij}D_j)=h^{ij}D_iD_j,\quad B_h=-V_h.
\]
空间 TT 条件使 determinant 一阶变分为0，V_h 形式自伴。
ER(t,s) 是 P 的零初位移、单位初速度传播子：ER(s,s)=0、∂tER(s+,s)=Id。Duhamel 积分采用共形 dη，不另乘 a² 测度。固定过去数据的准确恒等式是
\[
\boxed{\delta S=E_R B_h S+(E_R B_h S)^{\rm transpose}}. \tag{15}
\]
transpose 交换两组时空变量及各自的推迟积分。作用在光滑输入上，无奇异分布相乘。

若两态的空间核均 SO(4) 不变（全三球齐性各向同性），定义 [DiDj'S]_diag=σSγij。共同 state-independent 反项在态差中消去，但有效反馈保留局域态项：
\[
\boxed{\Delta\mathcal R_{\rm eff,cov}[h]
=[D_iD_{j'}\delta S]_{\rm diag}^{TT}-\sigma_Sh_{ij}}. \tag{16}
\]
证明：记 Sij=[DiDj'S]、X=−S00+γijSij，covariant stress 差是 Sij−γijX/2。变分并升一指标后，−hijX/2 与升指标中的 +hijX/2 抵消，留下 δSij−h_i^k Skj；TT 消去纯迹。若非各向同性，保留矩阵项，不用标量 σ。

### 4.1 可核验的 Volterra 界

取时间窗 [1/16,3/16]，长度 T=1/8；输入 h 在此前为零、两态均按各自固定过去 Cauchy 数据运输，并定义
\[
J=1-\Delta_\gamma,\quad
M_S=\sup_{s,t}\|J S(s,t)J\|_1,\quad
M_8=\sup_{s,t}\|J^2S(s,t)J^2\|_{HS}. \tag{17}
\]
空间紧和 S 光滑使二者有限。J 本征值 k²、简并度 k²，因此
\[
{\rm Tr}J^{-2}=\pi^2/6,\qquad M_S\le(\pi^2/6)M_8.
\]
后式用 JSJ=J^-1(J²SJ²)J^-1、Schatten Hölder 以及 operator norm≤HS norm。

Bochner 恒等式 ||HessYk||²=(k²−1)²−2(k²−1)≤k⁴ 给
\[
\|V_\tau J^{-1}\|,\ \|J^{-1}V_\tau\|\le\|\tau\|_\infty.
\]
张量 sup 范数取点态 Hilbert–Schmidt 范数。波能量 E²=||u'||²+||J^1/2u||² 满足
\[
(E^2)'\le(4\sup|\mathcal H|+1)E^2,\quad
\|E_R(t,s)\|\le C_E(t-s),\quad
C_E=e^{LT},\quad L=\tfrac12+2\tan(3/8).
\]
最后一步先界 u'，再对初位移0的 u 积分。

观察配对分部积分为 −Tr(V_tau δS)，与 B_h=−V_h 两个负号抵消：
\[
\langle\tau,\Delta\mathcal R_{\rm nonlocal}[h]\rangle
=2\int {\rm Tr}(V_\tau E_R V_h S)ds.
\]
合法因子分解是
\[
{\rm Tr}(V_\tau E_R V_h S)
={\rm Tr}[(JSJ)(J^{-1}V_\tau E_R V_hJ^{-1})].
\]
只需有界 V_tau/J、ER、V_h/J 和 trace-class JSJ；不交换未经证明的 Hessian 与 ER。因此
\[
|\mathcal K_S(t,s)[\tau,h(s)]|
\le2C_E(t-s)M_S\|\tau\|_\infty\|h(s)\|_\infty.
\]
在光滑 TT sup 范数空间的完备化 X 及其对偶 X* 上，非局域范数≤CE T²MS。
若 V=VolS³，3VσS=Tr(−ΔS)，故 |3VσS|≤MS，局域配对范数≤MS/3。合起来
\[
\boxed{\|\Delta\mathcal R_{\rm eff,cov}[h]\|_{L^\infty X^*}
\le\frac{\pi^2}{6}(C_ET^2+1/3)M_8\|h\|_{L^\infty X}}. \tag{18}
\]
检查器给几何系数的有向区间。该空间配对不是前驱含时间权重的仪器 O；转换时仍需按 O=4∫A²ψ τ:T 的定义积分，粗权重4A²≤12。

本轮没有数值认证实际 prepared-reference difference 的 M8，也没有借更换参考态宣布共同 baseline polarization 已解。旧 E5/k5 的有限阶 WKB 界、均值尾或分离窗噪声界不能直接填入 M8。

### 4.2 齐性调源的完整有效 TT 盲性

对同一 prepared 参考态上的任意齐性相干位移及其混合，
S(s,x;t,y)=q f(s)f(t) 对 x、y 分别为空间常数，是纯空间零模差；一般 SO(4) 不变的二点核仍可含非零球谐，不属于此特例。于是 V_h S=0、σS=0，(15)–(16) 精确给
\[
\boxed{\Delta\mathcal R_{\rm eff,cov}[h]=0}
\quad\text{对任意光滑空间 TT 输入，包括重叠窗。} \tag{19}
\]
混合不必 Gaussian：二次自由应力的一阶响应只依赖二点函数，亦可由齐性经典场的一阶 TT forcing 为零直接证明。

raw covariant δTij 仍可含 a_lambda²Δp hij，升指标后才抵消。因此零差是反馈所需的有效 mixed-index 各向异性响应，不能写成原始 covariant 响应处处为零。齐性 S 的粗 MS 可非零，(19) 用的是精确零模恒等式。

闭球面用于既定辅助 Cauchy 表示与范数估计。应用于原有限物理内球时，输入及相关因果域须在冻结合同允许的共同内域内；没有据此改变全局物理拓扑。

## 5. 当前闭合范围与完整反馈的剩余责任

仅反演局域四阶块后，平直 UV 主部仍有 log(p)。若 e^−rho t k(t)∈L1，则其 Laplace/Fourier multiplier 沿 rho+iω 有界；log(rho+iω) 无界，故这个主部不是普通 L1 卷积余项。有限局域常数不能消去对数增长。标量对数逆 (10) 说明如何将其纳入主部，但不是实际非平稳闭 FLRW 逆的替代。

真正剩余输入是：当前最小无质量 prepared 态、同一固定处方的完整非齐性 baseline kernel；全部固定接触项；扣除正确主部后的曲率、非平稳和全局传播余项的实际界；与初值空间相容的完整反馈逆。M8 条件定理只控制光滑态差，不能替代共同 Hadamard 主部。

本轮已完成有限部分定义、标量 normal-form 逆和重叠态差定理；完整量子反馈、全量子噪声的几何传播、非线性 SCE 仍开放。检查器只做精确代数、解析余项和有向区间，不运行旧科学入口，不新增模式 ODE、硬件或 Lean 数据，Core 只读。
