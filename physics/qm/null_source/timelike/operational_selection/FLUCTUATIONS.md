# 正时间窗、任意高态的动态能量界与完整联合约束缺口

## 1. 定理范围

固定闭 S3 FLRW、两个自由 minimal massless 实场、G=2T、同一个 incoming A、
原 M2、U0、AE mu=1 与有限曲率项。令
\[
a=Ae^u,\quad h=\Theta u,\quad u_{00}=0,\quad
\|u\|_{E_4}\le r.
\]
E4 是 [冻结全阶核](../nonlinear_history/KERNELS.md) 的正频强范数：
sum (1+lambda)^4 log(e+lambda)|u_nm|Rz^n Rw^m，
lambda=ns+m sigma。候选观测窗留在解析内部，所有量在同一实际几何上演化。
r 控制几何及导数，不能仅改述为 |u| 的界。
本定理不要求这些候选已经是平均 SCE 解，也不重新证明在更大球中的解存在。

允许经典中央几何标签与量子态任意关联；
高模可非平稳、挤压、跨模、跨场纠缠，零模与高模也可纠缠。
条件高态可以改变，但必须属于同一物质代数的正规 Hadamard 类，
保留完整非选择 S0 边缘及所有记录。几何标签是 CQ 中央变量，
不包含非交换量子几何或额外添加的装置物质。

取下文的共同 g≥0、g∈Cc∞(0,T)、integral g=1，T=1/sigma>10^-6。
以 proper-normal 密度的全空间平均 rho_bar 定义
\[
\widehat{\mathcal H}_g=\int ga^6\widehat{\bar\rho}\,d\eta,\quad
\mathcal G_g=\frac32\int ga^4(1+h^2)\,d\eta>0,\quad
\widehat{\mathcal C}_g=\mathcal G_g-\widehat{\mathcal H}_g.
\]
正式结论是：在 r=1/5000，
\[
\boxed{\left\langle
(\widehat{\mathcal C}_g/\mathcal G_g)^2
\right\rangle^{1/2}
>\frac{123753}{1250000\sqrt2}>0.07.}
\]
平均包括全部中央记录与各支量子态。
普通 RMS 要求 smeared residual 本身二阶矩有限；否则按扩展非负值解释。
Hadamard 两点条件不自动保证有限四阶矩。

这是完整源／约束残差，不是几何 RMS，也不是每支都超过7%。
平均约束可以成立；本定理并不推翻前驱精确 mean-SCE 历史。

## 2. 单模归一化，包含所有高态

实球谐 k≥2，简并度 k²，omega=sqrt(k²−1)，
\[
v_k=e^{-i\omega\eta}F_{+,k}/\sqrt{2\omega},\quad
Y_k=v_k'-hv_k,\quad
e_k=|Y_k|^2+\omega^2|v_k|^2,\quad
d_k=Y_k^2+\omega^2v_k^2.
\]
每场、每实振子的空间平均密度为
\[
[\,e_k(2N+1)+d_kb^2+\bar d_kb^{\dagger2}\,]/(4\pi^2a^4).
\]
a6 加权后正常序贡献为 q_k/(4pi²)，
\[
q_k=2A_kN+B_kb^2+\bar B_kb^{\dagger2},\quad
A_k=\int ga^2e_k,\quad B_k=\int ga^2d_k.
\]
双场共有 2k² 重数。原两个 k=2 热壳的八振子贡献正好是4n e2/(pi²a⁴)，
现在已包含在任意正常序高态中，不能额外再加一次原热项。

全片平均的零模—高模交叉项由球谐正交精确消失，不依赖态独立。
局部交叉噪声并未被删除。

## 3. Jost 控制与异常系数恒等式

V=Theta²u+h²，||V||E2≤r+r²。
冻结 Jost 方程 F+=1+Komega(VF+) 的乘子为
1/[lambda(lambda−2i omega)]。
使用 lambda≥s>1.99，整个 r≤.1 球有
\[
\|K_\omega M_V\|_{E_2\to E_2}
\le(r+r^2)/s^2\le r/3.
\]
E2 仍含 log 权重，乘法常数为1。Neumann 给
||F+||E2≤(1−r/3)^−1≤e^r；
最后不等式可由 e^r(1−r/3) 在[0,.1]上递增且起点为1直接证明。

KG 精确给 Y'=−hY−omega²v，因此
\[
(a^2d_k)'=4a^2h\omega^2v_k^2.
\]
令 Dk=e^(2i omega eta)a²dk，
\[
(\Theta-2i\omega)D_k=2\omega a^2hF_{+,k}^2.
\]
Dk 是无常数项的正频解析函数，且
|2omega/(lambda−2i omega)|≤1，于是
\[
\boxed{\|D_k\|_{E_2}\le xr e^{4r},\quad x=A^2.}
\]
同一常数控制 Dk、Dk'、Dk''。

## 4. 一个真实平滑正时间窗

令 L=T/2，在[T/4,3T/4]取
\[
g_0(\eta)=30q^2(1-q)^2/L,\quad q=(\eta-T/4)/L,
\]
区间外为零。g0非负、C1、积分1；端点函数与一阶导数均为零。
弱二阶导数没有额外 delta 项，并有
\[
\|g_0'\|_1=15/(2T),\quad
\|g_0''\|_1=160\sqrt3/(3T^2)<96/T^2.
\]
与支撑在(−T/8,T/8)的任意非负归一 Cc∞ mollifier 卷积，
得到支撑在[T/8,7T/8]的平滑 g；L1 导数界不增加。
故
\[
C_g=\|g''\|_1+2\|g'\|_1+1
<96/T^2+15/T+1<10^{14}.
\]

## 5. 直接界与两次分部积分必须结合

直接估计给 |Bk|≤xr e4r。
两次分部积分没有边界项，并给精确 Fourier 因子
\[
B_k=-\frac1{4\omega^2}\int e^{-2i\omega\eta}(gD_k)''d\eta.
\]
于是
\[
\boxed{|B_k|\le xr e^{4r}
       \min(1,C_g/(4\omega^2)).}
\]
Wronskian 给 e_k²−|dk|²=omega²、e_k≥omega，故
Ak≥x e^-2r omega。
g≥0 同时保证 Ak>|Bk|；也可使用直接比值
|Bk|/Ak≤r e6r/omega<1。
不能用低模中过粗的 Cg/omega² 界来判定稳定性。

单模谱底为
\[
\inf q_k=\sqrt{A_k^2-|B_k|^2}-A_k
=-|B_k|^2/[A_k+\sqrt{A_k^2-|B_k|^2}]
\ge-|B_k|^2/A_k.
\]
所以任意高态统一有 Hnormal≥−Qg，其中
\[
\boxed{Q_g(r)\le\frac{xr^2e^{10r}}{2\pi^2}
\sum_{k\ge2}\frac{k^2}{\omega_k}
\min(1,C_g^2/(16\omega_k^4)).}
\]
这已经允许挤压造成的负正常序能量，不是假设局部或正常序能量非负。

## 6. 无限和无需逐模重算

取 Kcut=5,000,000、Cbar=10^14。
由 omega≥sqrt3 k/2，
\[
S_{\min}\le\frac2{\sqrt3}[K_{\rm cut}(K_{\rm cut}+1)/2-1]
+\frac{C_{\rm bar}^2(4/3)^{5/2}}{32K_{\rm cut}^2}.
\]
用 sqrt3>17/10 即得纯有理上界
\[
S_{\min}<
\frac{20}{17}[K_{\rm cut}(K_{\rm cut}+1)/2-1]
+\frac{10C_{\rm bar}^2}{153K_{\rm cut}^2}
<4.1\times10^{13}.
\]
结合两种频段，比只用两次分部积分的 Cg² 全模估计明显收紧。
在 r=1/5000、x<7e9，e10r<101/100、pi²>9，得
\[
Q_g<6.442\times10^{14}<7\times10^{14}.
\]

为严化无限算符和，令 ck=Ak−sqrt(Ak²−|Bk|²)≥0。
qk+ck是正闭二次型，其含双场重数的 ck 和≤Qg。
有限模式正型的递增和仍闭；有限粒子有限模式向量的真空尾型值仅为可和的 ck 和，
故定义域稠密。减去有限常数得到半有界自伴 Hnormal。
它作用于高模张量因子，与 S0 强交换，不要求态乘积。
这是具体模式证明；一般量子能量不等式的背景见
[Fewster 的原论文](https://arxiv.org/abs/gr-qc/9910060)，没有把一般 worldline 定理当作本数值界的替代。

## 7. 完整固定 AE 真空项

冻结的双场、已剔除参考零模的真空为
\[
\rho_{\rm vac}=R/(2\pi^2a^4),\quad
R=-1-E_1-E_3+\sum k^2(e_k-e_k^d)+4r_{\rm an}.
\]
实际零模另为 M2 S0/(2a6)。参考 k=1 减项仍保留在−1−E1−E3。

冻结 norm_bounds.json 已认证整个 E4≤.1 上完整 |R|<7，
可直接覆盖本轮。独立审计的宽裕逐项界为：

- |E1|≤.505，|E3|≤.1320375；
- renormalized density 模和≤.0121+.011+.00175+.5+.0025+.009075=.536425<1；
- 包含动态2u的 ell=log(x/4)+2gamma+2u 有范数<24；
- 完整 H1≤19.0926、H3≤3.0603，代入局域式给 |r_an|<.466204<1。

因此 |R|<1+.51+.14+1+4<7。
omega 到原 k 减项的有限差、动态 log、实际双场、参考零模剔除均未遗漏；
旧谱常数没有重算，固定重整化处方未变。
故
\[
\mathcal V_g=\int ga^6\rho_{\rm vac}
\ge-7x e^{2r}/(2\pi^2).
\]

## 8. 从能量界到完整约束 RMS

完整源算符精确分解为
\[
\widehat{\mathcal H}_g
=\frac{M_2}2S_0+U_0\int ga^6+\mathcal V_g+\widehat H_{\rm normal}.
\]
另一方面
\[
\mathcal G_g\le G_{\max}(r)=\frac32x^2e^{4r}(1+r^2).
\]
定义
\[
\mu_{\rm cap}(r)=\frac2{M_2}
[G_{\max}-U_0x^3e^{-6r}+7xe^{2r}/(2\pi^2)+Q_g].
\]
于是 H_g−G_g 可写成 (M2/2)(S0−mu_cap) 加一个与 S0 强交换的非负算符。
在共同谱上逐点使用 (y+h)²≥y_+²、h≥0，得
\[
\widehat{\mathcal C}_g^2\ge(M_2/2)^2(S_0-\mu_{\rm cap})_+^2.
\]
这是强交换的正部谱论证，不能把一般算子不等式直接平方。
CQ 中 Gg 是正中央量，故
\[
\mathrm{RMS}\ge\frac{M_2}{2G_{\max}}
[\mathbb E(S_0-\mu_{\rm cap})_+^2]^{1/2}.
\]
没有把随机比值的平均换成平均的比值。

完整记录保留原源边缘。它已知是 R=1、R+=1+sqrt3/2 各一半的非中心 chi² 混合，
E(S0|R)≥R。对凸正部平方用 Jensen：
\[
\mathbb E(S_0-\mu_{\rm cap})_+^2
\ge\tfrac12(R_+-\mu_{\rm cap})_+^2.
\]
这仅是固定谱积分的数学分解，不要求新联合态里有可读 R 标记；
也没有使用错误的 P(S0≥R+)=1/2。

## 9. 主门的独立有理认证

在 r=1/5000 使用
\[
e^{4r}\le1250/1249,\quad
e^{-6r}\ge2497/2500,\quad
e^{2r}\le2500/2499,\quad \pi^2>9.
\]
冻结宽参数盒中，正项取上界、负项取下界，加上 Qg<7e14，
[review.py](review.py) 用精确 Fraction 得
\[
\mu_{\rm cap}<1.439949914<36/25,\quad
M_2/(2G_{\max})>.2324236362>581/2500.
\]
又 R+>933/500，所以
\[
\mathrm{RMS}>
(581/2500)(213/500)/\sqrt2
=\frac{123753}{1250000\sqrt2}>.07.
\]
最后严格比较的整数余量为
123753²·10000−98·1250000²=23050090000>0。

[fluctuations.json](fluctuations.json) 另以180位有向区间输出连续半径公式
\[
L(r)=\frac{M_2}{2G_{\max}(r)}
       (R_+-\mu_{\rm cap}(r))_+/\sqrt2
\]
在1e−25、.0001、.0002、.001、.005的包围。
这些是同一候选域内必要下界；粗界减弱或变零不构成解存在证明。

## 10. 这项闭环迫使下一任务改变

现在不能再以“允许非平稳高模、挤压或更复杂零高纠缠”作为没有核算的补偿出口。
此类态的负正常序能量能力已经被算入，仍留正时间窗缺口。

下一共同历史须明确选择一个尚未被本合同排除的模型：
例如放宽固定 incoming A／正频强范数类，给出有限初片的合法联合数据及其传播；
或加入具有明确总应力的新物质和装置；或建立非交换几何的约束与概率法则。
后两者不能只换术语，前者也不能逐时换根或冻结态后单独改几何 jets。

平均历史的存在已闭合；完整随机或量子引力法则、局域仪器与物理统一没有由此自动导出。
