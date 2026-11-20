# 固定态动态历史：二阶修正、无限模与有限窗

## 1. 一次选定的物理数据

使用 [前驱实际历史](../joint_history/history.json) 的 unfiltered case。其 x=A²、n、M2、U0、x0、nu0 是相关的精确定义量；JSON 区间仅包围它们。不能任意独立抽取区间内数值后仍使用静态等式。

两相同自由 minimal massless 实场，闭 S3，G=2T，AE mu=1，无额外有限曲率项。原固定 M2、U0 保持。零模 centered VarP=x0/4、desheared VarQ=1/x0；实际完整 S0 律保持，mu=E(S0)=L+1/nu0。完整两组 k=2 壳在同一 incoming 态中有每振子 n，其余高模为 incoming vacuum。正规零模的应力在静态过去恒定，整个零模密度算符不因此被称为静态振子真空。

前驱静态恒等式为 rho0=3/(2x)、p0=-1/(2x)。本轮没有改变制备预算，没有新增源强参数。

## 2. 精确 off-shell 族及同一实际初片

固定 s>0、beta，令

\[
u(z)=z+\beta z^2,\quad z=\epsilon e^{s\eta},\quad a=Ae^u,\quad h=u',
\]
\[
V=a''/a=s^2[z+(1+4\beta)z^2+4\beta z^3+4\beta^2z^4].
\]

这是精确几何族，不是已经解出的 SCE。对每个 k≥2，omega=sqrt(k²−1)，精确模式由

\[
v(\eta)=\frac{e^{-i\omega\eta}}{\sqrt{2\omega}}
+\int_{-\infty}^{\eta}\frac{\sin\omega(\eta-t)}{\omega}V(t)v(t)\,dt
\]

定义。固定 incoming 边界条件，V 的所有时间及有限参数导数在过去一致指数衰减，Volterra 构造唯一。实参数时实势保持精确 Wronskian。实际 Cauchy 数据为

\[
\phi_k=v_k/a,\quad \pi_k=a(v_k'-hv_k),\quad
n^\mu\nabla_\mu\phi_k=(v_k'-hv_k)/a^2.
\]

零模始终使用同一 Q/P 态：

\[
q(\eta)=Q+P\left[(\eta-\eta_{\rm ref})/A^2+
\int_{-\infty}^{\eta}(a^{-2}-A^{-2})dt\right],\qquad a^2q'=P.
\]

故完整 \(S_0=(P_1^2+P_2^2)/(2\pi^2M2)\) 谱律保持，
\(\rho_z=p_z=M2\,E(S_0)/(2a^6)\)。有限维零模及有限 thermal 壳只改变平滑二点函数部分。

Hadamard 性使用高模全阶 positive-frequency 渐近。令 lambda=2i omega，
r1=−V，r_{j+1}=r_j'+sum_{l+m=j} r_l r_m。任意阶 Riccati 截断的缺陷通过 Volterra 比较给任意阶高频渐近及有限参数导数控制；因此高频协方差与全阶 Hadamard 构造的差为 smoothing。这里只在有谱隙的 k≥2 子空间应用该论证，再补有限零模。相关背景定理是 Gérard–Wrochna [arXiv:1609.00190](https://arxiv.org/abs/1609.00190)，其严格正渐近空间算子条件不能无说明地直接套到完整无质量零模。

机器中二阶模式是这些精确模式的 jet，不是替代精确模式的量子态。未来可在观察窗之后平滑延拓为正常正度量；过去的 retarded 构造不受该延拓影响。

## 3. 二阶 KG 与全部 AE 项

写 v=e^{-i omega eta}F(z)/sqrt(2omega)。精确递推为

\[
f_0=1,\quad
f_n=\frac{f_{n-1}+(1+4\beta)f_{n-2}+4\beta f_{n-3}+4\beta^2 f_{n-4}}
 {n(n-2i\omega/s)},\qquad f_{n<0}=0.
\]

于是

\[
f_1=\frac{s}{s-2i\omega},\qquad
f_2=\frac12 f_1+\beta\frac{s}{s-i\omega}.
\]

以真实法向导数计算裸能量／压力。beta=0 时

\[
e_2=\frac{2\omega s^2}{s^2+4\omega^2},\qquad p_2=-p_1/2.
\]

固定 AE 数值减除为
e^d=k+E1/k+E3/k³，p^d=k/3+P1/k+P3/k³，其中

\[
q=-1-V,\quad f=q',\quad
E1=(h^2-1)/2,\quad E3=[q^2-2(h^2-1)q+2hf]/8,
\]
\[
P1=q/3+h^2/2+1/6,\quad
P3=-q^2/8-q''/12-(3h^2+1)q/12+hf/4.
\]

[jet.py](jet.py) 从 a1…a4 重新构造全部 AE H1/H3 和 trace 局部项；固定 trace= rho−3p，保留 log(a²/4)+2 gamma 的时间变化。没有删除高阶导数项，也没有改变有限项处方。AE 背景公式沿用 [Anderson–Eaker](https://arxiv.org/abs/gr-qc/9906055) 及冻结的 [前驱代数](../evolution/review_algebra.py)。

令 C_A=19+15[log(x/4)+2 gamma]，

\[
D_{\rm num}(s)=-1+s^2/2-s^4/12+
\sum_{k\ge2}\left[
-\frac{4k^2\omega_k s^2}{3(s^2+4\omega_k^2)}
+\frac{s^2 k}{3}+\frac{s^2/6-s^4/12}{k}
\right],
\]
\[
Z(s)=D_{\rm num}(s)+C_A s^4/360-(C_A-29)s^2/180-1/24.
\]

对每个含标准正规零模的参考场，完整系数为

\[
p_{q,1}=-4p_{q,0}+Z/(4\pi^2x^2),
\]
\[
p_{q,2}=8p_{q,0}+
[-9Z/2+23/48-s^2/4+3s^4/8]/(4\pi^2x^2),
\]
\[
\rho_{q,1}=-4\rho_{q,0}-9/(32\pi^2x^2),\qquad
\rho_{q,2}=8\rho_{q,0}+[-3Z/2+63/16]/(4\pi^2x^2).
\]

实际替换必须减去每场标准零模 1/(8 pi² x²) exp(−6u)，再加实际零模。thermal 项令 Jn=4 sqrt(3)n/pi²，r_s=s²/(s²+12)，则

\[
p_{{\rm th},1}=-\frac43\rho_{{\rm th},0}(1+r_s),\qquad
p_{{\rm th},2}=(8/3+6r_s)\rho_{{\rm th},0}.
\]

## 4. 一次选根，消去动态一阶和二阶

定义实际各向同性空间方程

\[
\mathcal S=u''+(h^2+1)/2+a^2p.
\]

利用精确静态约束后，

\[
\mathcal S=D_{\rm new}(s)z+
[\beta D_{\rm new}(2s)+Q_2(s)]z^2+O(z^3),
\]
\[
D_{\rm new}(s)=s^2-4+\frac2x
\left[\frac{8B(x)}3-D_0+\frac{Z(s)}{4\pi^2}\right]
+\frac{4Jn}{3x}\frac{s^2+24}{s^2+12},
\]
\[
Q_2=\frac{s^2}{2}+2+\frac1x\left[
-8B-6D_0+Jn(-4+10r_s/3)
+\frac{-5Z/2+23/48-s^2/4+3s^4/8}{2\pi^2}\right].
\]

这里 B、D0 使用前驱固定定义，所有 stiff zero 项均通过静态关系显式消入，不能据此省略实际零模。

[bounds.py](bounds.py) 新证无限和：1≤s≤3 每项尾 <27/(2k³)，3≤sigma≤5 每项尾 <525/(2k³)；导数尾 <36/k³。由此 D_new'(s)>2−10/x>0，根在 (1,3) 中唯一，且 |s−2|<8/(3x)。D_new(2s)>11，|Q2−4|<24/x，|beta+1/3|<6/x。

选定精确根 s 以及精确 beta=−Q2/D_new(2s)，然后固定整条历史。这保证 S0=S1=S2=0；展示的小数只包围这些精确量。若数值演化使用舍入后的参数，须另外保留一、二阶系数的舍入残差。

## 5. 从 jet 到真实有限窗：统一 UV 与两次 Cauchy

### 5.1 复参数只用于误差估计

取 |z|≤R=1/16、1≤s≤3、|beta|≤1。定义两独立解析 partner

\[
v_\sigma=e^{-i\sigma\omega\eta}F_\sigma(z)/\sqrt{2\omega},
\quad F_-(z)=\overline{F_+(\overline z)}.
\]

实 z 时才是物理共轭。令 A_sigma=(sz partial_z−i sigma omega−h)F_sigma，则裸压力解析延拓是
[A_+A_-−omega² F_+F_-/3]/(2omega)，能量把 −1/3 改为 +1。不能把复 z 代入绝对值平方。AE 对数用 C(z)=C_A+30u(z)，固定解析分支。

### 5.2 实频率的 exact-minus-WKB 控制

使用加权系数范数 ||P||_R=sum |p_j| R^j。对无常数项多项式，沿过去 z(t)=z_* exp(st)，

\[
|P(z(t))|\le ||P||_R e^{st},\qquad
\int_{-\infty}^0|P(z(t))|dt\le ||P||_R/s.
\]

这不是任意 supnorm 都具有的性质。完整 V 的第 0…5 阶时间导数范数上界为

| j | 0 | 1 | 2 | 3 | 4 | 5 |
|---|---:|---:|---:|---:|---:|---:|
| ||V^(j)|| | 3/4 | 3 | 13 | 61 | 343 | 2160 |

同时 ||V||_L1<7/32、|h|<1/4。Riccati 五阶为

\[
r_1=-V,\ r_2=-V',\ r_3=V^2-V'',\ r_4=-V'''+4VV',
\]
\[
r_5=-V^{(4)}+5V'^2+6VV''-2V^3.
\]

令 R5=sum r_j/(2i omega)^j、w5=e^{-i omega eta}exp(int R5)/sqrt(2omega)。其缺陷从 (2i omega)^−5 开始；六项加权范数由
(3300,1288,4648,17444,62720,200704) 控制。对 omega≥7，

\[
||R5||_{L^1},\,|R5|<2/25,\qquad
||\delta_5||_{L^1}<108/\omega^5.
\]

Volterra 比较给去除平面波后的模式差 <130/omega^6、实际 v' 的相应差 <124/omega^5。计入 −hv 后，两裸应力与 WKB5 的差统一 <600/k^5，k≥8。该步骤仅使用真实 k/omega，不要求精确模式在 1/k²=0 解析。

### 5.3 仅对有限局部 WKB 表达做 delta-Cauchy

令 delta=1/k²、b=1−delta，选择从 delta=0 延拓的 sqrt(b)。定义

\[
T=\frac{V\delta}{2b}+\frac{(2V^2-V'')\delta^2}{8b^2},\quad
A_*=\frac{V'\delta}{4b}+\frac{r_4\delta^2}{16b^2},
\]
\[
J_*=\frac{V\delta}{2b}+\frac{r_3\delta^2}{8b^2}
-\frac{r_5\delta^3}{32b^3}.
\]

有限 WKB 裸能量除以 k 为

\[
F_e=\frac{e^T}{2\sqrt b}
\{\delta(A_*-h)^2+b[(1-J_*)^2+1]\};
\]

压力 F_p 把最后 +1 改为 −1/3。在 |delta|≤1/4 有 |F_e|<6、|F_p|<5。fresh exact algebra 核对它们前三项恰为固定 AE k、k^−1、k^−3 减除。Cauchy 给剩余 <410/k^5、342/k^5。

因此对整个复 z 圆盘，

\[
|e_k-e_k^d|,\ |p_k-p_k^d|<1100/k^5,\qquad k\ge8.
\]

含 k² 简并度的 K 之后尾 ≤550/K²。取 K=8，低模亦由精确 Volterra 界控制，未进行旧模式传播。Weierstrass 一致收敛给真实无限模 RSET 在 z 圆盘内全纯。完整精确模式通常不在 delta=0 解析；证明没有使用这一错误假设。

### 5.4 完整总压力及圆盘界

去除参考零模后，真实总压力精确为

\[
p=\rho_{z,0}e^{-6u}-U_0+
\frac{1}{2\pi^2a^4}
\left[-\frac13-P1-P3+\sum_{k\ge2}k^2(p_k-p_k^d)+4P_{\rm an}\right]
+\frac{4n}{\pi^2a^4}p_{k=2},
\]

P_an=pi² a⁴ p_an 是一个参考场的全部 AE 局部压力。k=1 减除保留，两个完整 thermal 壳由最后一项保留。

[window.py](window.py) 使用 x rho_z0<3/5、xU0<101/100，以及全部有限模、尾和局部项，得到 |S| 的圆盘上界 <3.171，故可选 M=4。

对一次选定的精确 s、beta，S 的前三系数严格消失。第二次 Cauchy 作用于实际 S(z)，于是

\[
|\mathcal S(z)|\le M\frac{(|z|/R)^3}{1-|z|/R}.
\]

## 6. 正时间窗、约束和实际法向导数

取 r=10^−4、epsilon=r exp(−s)，固定 eta∈[0,1]，则全过程 0<z≤r。这是一条同态同参数的实际历史。

定义

\[
E=h^2+1-\frac23a^2\rho,\quad C=a^2E,\quad
B_{\rm acc}=a''+a-\frac{a^3}{3}(\rho-3p).
\]

[review.py](review.py) fresh 精确验证每个 AE 减除及所有 AE 局部项的完整 conservation 恒等式；统一解析尾允许在内圆逐项求导。故真实应力满足 Ward：

\[
C'=2a'B_{\rm acc},\quad B_{\rm acc}/a=S+E/2,\quad
E'+hE=2hS.
\]

静态过去给 E(0)=0，因此

\[
E(z)=2e^{-u(z)}\int_0^z u_\zeta e^{u(\zeta)}S(\zeta)d\zeta.
\]

令 g=r+r²，得到

\[
|E|\le
\frac{M e^{2g}(1+2r)r^4}{2R^3(1-r/R)}.
\]

正交标架下的 Einstein 缺陷为

\[
\mathcal E_\rho=G_{nn}-2\rho=3E/a^2,\qquad
\mathcal E_p=G_{\hat i\hat i}-2p=-2S/a^2.
\]

它们不是直接的共形坐标 covariant 分量。认证界为

\[
|S|<1.642\,10^{-8},\quad |E|<8.209\,10^{-13},
\]
\[
x|\mathcal E_\rho|<2.465\,10^{-12},\qquad
x|\mathcal E_p|<3.284\,10^{-8}.
\]

Cauchy 还给
|S'|≤3M(r/R)^3[3−2r/R]/(1−r/R)^2。
利用真实 n·∇=a^−1 partial_eta，

\[
a^3|n\cdot\nabla\mathcal E_p|
\le2(|S'|+2|hS|)<3.0\,10^{-7},
\]
\[
a^3|n\cdot\nabla\mathcal E_\rho|
\le |h|(6|S|+9|E|)<3.0\,10^{-11}.
\]

这些界包含初片以及整个正时间窗。proper-time 长度约在 [81716.5,81732.91] 模型单位；它不是实验秒。初态规范 Q/P 和高模 Jost 条件都没有在初片重置。

## 7. 已完成与仍开放的区别

本轮已完成完整同态 RSET、实际法向数据、固定源强和指定正窗的受控近似共同历史。小残差不证明附近存在精确非线性 SCE 解；下一步需要相应函数空间、线性逆估计／稳定性和非线性余项控制，不能用 D_new(2s) 的单一非零数代替完整线性化算子的可逆性。

本族也不能吸收新的随机零模能量。若保持同一静态过去 A，却改变 deltaM=delta(M2 E(S0))，则

\[
C(-\infty)=-\delta M/(3A^2),\qquad
B_{\rm acc}(-\infty)=\delta M/(3A^3).
\]

过去趋零的增长种子无法消去这些常数。承接完整源涨落需要新的联合约束初值与明确引力法则。齐次 mean 响应、初始几何涨落和噪声驱动涨落的责任不同；参见 Hu–Roura–Verdaguer [gr-qc/0402029](https://arxiv.org/abs/gr-qc/0402029) 的具体框架，不能不带其假设直接当作本双场模型的完成。
