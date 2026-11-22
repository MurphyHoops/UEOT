# 同一实际历史上的齐次因果逆与独立伴随逆

本页关闭一个比“响应算子已定义”更强、但范围明确的门：
在QUIET_WINDOW一次选参的实际U上，固定同一incoming态和AE处方，
构造有限窗、零初始扰动的齐次确定性压力因果逆。
任意L² forcing的输出是声明graph域中的H4线性响应闭包，
不自动是新的非线性Hadamard几何，也不等于完整量子几何态。

## 1. 固定窗口、背景和函数空间

I=[0,T]，T=1/50，a=Ae^U，γ=24A。
沿用同一c=e⁻²⁰⁰⁰⁰和已一次求得的b(c)，不是在每个时刻换参。
QUIET_WINDOW给全过去至T的加权解析背景范数
\[
 \varepsilon=\|U\|_{E_4,T}<e^{-1158}<10^{-3}.
\]
定义Y=L²(I,e⁻²γηdη)，X为H4(I)且w(0)…w‴(0)=0，
范数||w||X=||w⁽⁴⁾||Y。
这不是把任意forcing放进正频Wiener空间。

CAUSAL_DOMAINS的完整静态G0满足
\[
 G_0:Y\to X,\qquad \|G_0\|<M_0,\quad M_0=10^{15}.    \tag{I1}
\]
其已证区间上界小于1.833×10¹⁴；这里用更保守M0。
快根保留在G0中，γ大于快根，不是无权稳定性结论。

取D0=Ran(G0:Y→X)，L0(G0f)=f，graph范数||L0w||Y。
这是明确的闭图定义域，不能写成“L0在所有H4上都有定义”；
原P含四阶log增长。

有限窗估计无需任意cutoff：
若f初片0…r−1阶为零，初片前补零，T后接r−1次Taylor多项式，
则D^r f_ext=1_I f^(r)，没有δ项。
因果multiplier在I上的值不依赖未来延拓，且
\[
 \|w^{(j)}\|_Y\le\gamma^{j-4}\|w^{(4)}\|_Y,\quad j\le4. \tag{I2}
\]
χ0的每个H1输入分别接常数，G0的H4输入接三次多项式；
不需要延拓实际背景h至远未来。

## 2. 背景界与 forcing 域严格分开

令
\[
 \mu_J=\sum_{r=0}^3\|V^{(r)}\|_{L^1(-\infty,T]},\quad V=U''+h^2.
\]
它不是旧KERNELS里名为M的E2范数。
所有非零背景频率λ≥s*>1，积分降一阶，故
\[
 \sup|U^{(j)}|\le\varepsilon\ (j\le4),\quad
 \|U^{(j)}\|_1\le\varepsilon\ (j\le5),\quad
 \mu_J\le4\varepsilon+15\varepsilon^2<5\varepsilon.  \tag{I3}
\]
最后一个U五阶L¹界来自积分的1/λ，不是声称E4控制五阶sup。

## 3. 共同χ0的有界性

ACTION_RESPONSE的静态Q响应为
\[
 K_0(z)=-z^2\sum_{k\ge2}{k^2\over4\omega_k^3(z^2+4\omega_k^2)}
       +{K_3-1\over4}+{8n\over\omega_2(z^2+4\omega_2^2)}.
\]
z=γ+iτ，q=|z|，γ≥2。对τ≥0，|z+i2ω|≥q。
ω≤q的和使用k²/ω³≤8/(3√3k)、Cauchy–Schwarz以及
频率2ω_k间距>2，得到
\[
 \sum {1\over k|z-i2\omega_k|}<\sqrt{6/\gamma}.
\]
这里packing bound由两侧单调积分及两个峰值给
Σ[γ²+(τ−2ωk)²]⁻¹≤2/γ²+π/γ<6/γ。
所以低段<q/√γ。ω>q用|z²+4ω²|≥3ω²、Σ_{k>q}k⁻³≤2/q²，
高段<1。固定local和thermal项保留后
\[
 |K_0(z)|\le3|z|/\sqrt\gamma,\qquad
 \|K_0 f\|_Y\le3\|f'\|_Y/\sqrt\gamma.               \tag{I4}
\]
τ<0由共轭处理。每个零初值f按第1节常数延拓，故I4在I上有效。

## 4. 实际χ差：全部模式的显式 Schur 界

F_k=e^{iωη}√(2ω)v_k，满足
F=1+Kω*(VF)，Kω(τ)=(e^{2iωτ}−1)/(2iω)，τ≥0。
ω≥√3且μJ≤.1。Volterra与Gronwall逐次给
\[
 |F|\le2,\quad |F-1|\le2\mu_J/\omega,\quad
 |F'|\le4\mu_J/\omega,\quad |F''|\le8\mu_J/\omega,\quad
 |F'''|\le16\mu_J/\omega.
\]
令J(η)=∫_-∞^ηV。将Kω分成常数与振荡部分并分部积分一次，
对j=0,1,2得到
\[
 |F^{(j)}-\delta_{j0}-iJ^{(j)}/(2\omega)|
 \le4\mu_J/\omega^2.                               \tag{I5}
\]
非振荡差的系数可分别取(1,3,9)μJ²/ω²；
振荡边界及积分系数可分别取(1.1,1.5,2.7)μJ/ω²，
因此共同4是有效的。只用I3列明的四个L¹范数。

令D+=∂t+∂s、τ=t−s、I_V=∫_s^tV。
D+不打二倍频相位。展开四个F因子，用8μJ/ω<1/2，
对j≤2有
\[
 D_+^j(\chi_{U,k}-\chi_{0,k})
 =-{D_+^jI_V\cos(2\omega_k\tau)\over2\omega_k^3}
   +r_{j,k},\quad |r_{j,k}|\le500\mu_J/\omega_k^4.   \tag{I6}
\]
这是所有k≥2的界，没有遗漏低壳。
|D+^j I_V|≤μJτ，由V,V′,V″的sup≤μJ得到。

条件和的领先项也明确控制：
\[
 \sum_{k\ge2}{k^2\over\omega_k^3}\cos(2\omega_k\tau)
 =-\log(2\sin\tau)+E(\tau),\quad |E|<4,\quad0<\tau\le T.
\]
证明从Σ_{k≥1}cos(2kτ)/k闭式减去k=1项，再用
|k²/ω³−1/k|≤4/k³、相位差≤2τ/k。
差额绝对收敛；原和可先按L²或Abel极限取值。
余项Σk²/ω⁴<2。

设R=K_U−K_0、R_j=D+^jR。
共同δ/(4ω³)及(K3−1)/4接触精确相消。
每个真空R_j的加权row/column积分小于
\[
 \mu_J[1000T+T^2(-\log T+4.5)/4]<21\mu_J.
\]
另直接加真实k=2 thermal项，不对条件和任意乘比例：
其积分<.16μJ[T²/(4ω2³)+500T/ω2⁴]<.18μJ。
因此三个核的weighted Schur范数统一有
\[
 \|R_j\|_{Y\to Y}<23\mu_J,\qquad j=0,1,2.           \tag{I7}
\]
权重贡献e⁻γτ≤1。

## 5. 同一作用量行的差算子预算

由ACTION_RESPONSE，
Lhat_U=H_U/(3V0A²)，B_U=Lhat_U−L0。
对初片f=f′=0，
\[
 D T_Rf=T_Rf'+T_{D_+R}f,\quad
 D^2T_Rf=T_Rf''+2T_{D_+R}f'+T_{D_+^2R}f.
\]
先finiteK/smooth core，再以I7闭包，没有省略初片项。

|h|…|h‴|≤ε以及I2给D_U†R D_U块<500ε。
静态χ0的三个变系数块为
D²K0(2hD)−2D[hK0D²]−4D[hK0hD]；
I4逐项给48ε+12ε+72ε²<61ε。

固定背景Qbar差按冻结Born核给
||Qbar_U−Qbar_0||C¹<2ε、|Qbar_0|<1，
故−2D[(Qbar_U−Qbar_0)D]块<8ε。
其中linear Qren的E2→E1常数≤9/20，Born尾≤.27||V||E1²，
固定conversion≤||V||E1/4、thermal≤.008||V||E1。
这些背景界没有对forcing另加Wiener假设。

全部AE局部项可精确化成
\[
\begin{split}
t_{\rm an}={}&-1/32-CU^{(4)}/480+(C-29)U''/240\\
&+(3C-59)h^2U''/240+h^2/16-hU'''/8
 -3(U'')^2/32+3h^4/32,\\
&C=C_{A0}+30U,\quad C_{A0}=19+15\ell_0<400 .
\end{split}                                                     \tag{I8}
\]
δtan_U−δtan_0的w⁽ʲ⁾系数绝对值分别小于
(.188,.261,.318,.125,.0625)ε，和<ε。
于是AE块<4ε。所有matter/action块实际还要除3V0A²>1，
此处保守地不使用这个有利因子。

|A²ρz0|<.6、A²U0<1.01，归一gravity、零模和U0差分别<17ε、3ε、30ε。
总和<623ε，统一保守声明
\[
 \boxed{\|B_Uw\|_Y\le1000\varepsilon\|w\|_X.}        \tag{I9}
\]

## 6. 真正收敛的全场逆

B_U从smooth同态方向唯一连续延拓X→Y；取R_U=B_U G0。
由I1/I9，
\[
 \|R_U\|<q_{\rm inv}:=10^{18}e^{-1158}<e^{-1100}<1.
\]
因此
\[
 \boxed{\widehat G_U=G_0(I+R_U)^{-1}
       =G_0\sum_{n=0}^\infty(-R_U)^n:Y\to D_0.}     \tag{I10}
\]
Lhat_U=(I+R_U)L0，是D0上的闭算子，I10为其唯一逆。
每项因果；时间截断投影下取operator-norm极限保持因果。
这是实际full-field算子直接构造，不宣称FINITE_CAUSAL的G_K已经强收敛。

余项受控：
\[
 \|\widehat G_U-\widehat G_U^{[m]}\|_{Y\to X}
 \le {M_0q_{\rm inv}^{m+1}\over1-q_{\rm inv}}.       \tag{I11}
\]
极小q表示本窗口算子相对静态逆的接近程度，
不是几何噪声、初态制备精度或无权时间稳定性。

## 7. 从 action 行精确回到压力行

实际E=S=0且零初始约束扰动时，Ward给
\[
 Lhat_U=M_U L_U,\quad
 M_Uf=e^{2U}f+e^U\int_0^\eta e^Uhf,
\]
\[
 M_U^{-1}g=e^{-2U}\left[g-\int_0^\eta hg\right].      \tag{I12}
\]
两者Y范数≤e^{2ε}(1+ε/γ)。因此
\[
 G_U=\widehat G_U M_U,\quad
 \|G_U\|_{Y\to X}\le
 {M_0e^{2\varepsilon}(1+\varepsilon/\gamma)\over1-q_{\rm inv}}.
                                                               \tag{I13}
\]
若初始e(0)≠0，另有列½e^{U+U(0)}e(0)；
真实source/准备决定它，不能由零初值逆自动补齐。
全场应使用合法平滑约束荷，不能把e(0)替成未定义尖片密度。

## 8. 独立的 advanced 证明，及其准确含义

在I上以反向权重e^{+2γη}和terminal 0…3阶零迹重做同一估计。
总action的gravity、−2D(Qbar D)和乘法项形式自伴。
I8局部变分系数满足
\[
 a_3=2a_4',\qquad a_1=a_2'-a_4''' .
\]
因此δtan的形式转置与自身相同，高阶背景jets精确消掉。
非局部项只将χ_ret转置为χ_adv；三个Schur范数不变。
于是独立得到advanced H4 inverse，预算仍为I9/I10。

对smooth初/终边界core作Green恒等式，再连续延拓，可知
这个advanced inverse就是unweighted测试配对中的Ghat_U^*。
这里的星不是省略权重变换的weighted Hilbert adjoint；
也不是从forward smoothing自动推断adjoint smoothing。

pressure pullback为
\[
 G_U^*F=M_U^*\widehat G_U^*F,\quad
 M_U^*q=e^{2U}q+he^U\int_\eta^T e^Uq.               \tag{I14}
\]
它保持H3和terminal0…2阶零迹。与实际应力GNS域的接合、
原初片块与截断误差见PREPARED_READOUT。
完整tensor inverse、正常联合几何态、真实装置及物理统一仍OPEN。
