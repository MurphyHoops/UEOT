# 同一新历史的完整记录、噪声及实际态响应

## 1. 实际零模谱与两支 CP instrument

令 \(\kappa_P^2=2\pi^2M_2\)、\(v_P=x_0/4\)、\(\nu=\kappa_P^2/v_P=2\nu_0\)。给定相干标签 \((y,z)\)，两个动量的中心化协方差为 \(v_PI\)。于是
\[
\nu S_0\mid R\sim\chi^2_2(\nu R),\quad R=y^2+z^2.
\]
在共同最低预算处 R=1、1+d 各占一半。

对 s≥0，完整输入谱的 Laplace 变换为
\[
Z(s)=\frac1{1+2s/\nu}
\mathbb E_R\exp[-sR/(1+2s/\nu)].
\]
取 q=1/2 和 t=10^-12，定义
\[
K_1=\sqrt q\,e^{-tS_0/2},\quad
K_0=\sqrt{1-qe^{-tS_0}},\quad
K_0^\dagger K_0+K_1^\dagger K_1=I.
\]
根号内统一大于等于1/2，所以两个动量乘子都光滑、保持本准备的 Schwartz 零模波函数。两支正常归一、正，有限模改变保持 Hadamard 性。若用 q=1，则失败乘子在动量原点像 |P|，不能用同一个光滑性论证。

设 c=1+2t/ν、α=t/c，则
\[
Z(t)=c^{-1}e^{-\alpha}(1+e^{-d\alpha})/2,\quad
p_1=qZ(t),\quad p_0=1-p_1.
\]
完整成功与失败谱分别为
\[
L_1(s)=Z(t+s)/Z(t),\quad
L_0(s)=\frac{Z(s)-qZ(t+s)}{1-qZ(t)}.
\]
它们确定完整概率律，不是仅凭有限矩猜测。

成功支的径向高标签权重 \(w=(1+e^{d\alpha})^{-1}\)，其均值和方差为
\[
\mu_1=\frac{1+dw}{c^2}+\frac2{\nu c},\quad
v_1=\frac{d^2w(1-w)}{c^4}+
\frac{4(1+dw)}{\nu c^3}+\frac4{\nu^2c^2}.
\]
写 \(\delta=\bar\mu-\mu_1>0\)，则
\[
\mu_0=\bar\mu+\frac{p_1}{p_0}\delta,\quad
v_0=\frac{\bar v-p_1v_1-(p_1/p_0)\delta^2}{p_0}.
\]
最后的 \(v_0\) 是失败支 S0 方差，与先前动量方差 vP 不同。全方差严格满足
\[
\bar v=p_1v_1+p_0v_0+p_1p_0(\mu_1-\mu_0)^2.
\]
[algebra.py](algebra.py) 验证 \(d\mu_1/dt=-v_1\)、完整记录的两条矩恒等式。[instrument.py](instrument.py) 使用无大数相消的 δ 表达式生成实际区间。

## 2. 量子态不是只有一个改权标签

给定成功的原标签，动量均值变为 \(\kappa_P(y,z)/c\)，中心化 Var(P)=x0/(4c)。去剪切 canonical frame 的 Var(Q)=c/x0，不确定度乘积仍为1/4。若实际片上已有 \(Q=\widetilde Q+\beta[g]P\)，则必须使用
\[
\operatorname{Var}Q=c/x_0+\beta[g]^2x_0/(4c),\quad
\operatorname{Cov}(Q,P)=\beta[g]x_0/(4c).
\]
这里 \(\beta[g]=\int a_g^{-2}d\eta\)。失败态一般非 Gaussian，以上完整谱公式仍成立，但不将成功 Gaussian 协方差套到失败支。

成功筛选后旧第一场的相干二阶系数为 \((1-d+2dw)/c^2\)，新第一场为 \(1/c^2\)；旧／新储备分别为 \(d(1-w)/c^2,dw/c^2\)。总和相同，但原场完整边缘已改变。原先的“第一场边缘保持”合同不能继承到本轮新准备。

## 3. 非选择筛选和后续联合准备是两项不同操作

在同一个固定背景上，minimal massless 应力只依赖零模 P、不依赖常数 Q；高模与 P 独立。包括交叉项的应力代数在动量表示中对 P 可分解，因此 S0 与其有界效应强交换。对每个允许的总应力效应 E，
\[
\sum_iK_i^\dagger E K_i=E.
\]
这是筛选本身在保留全部记录时的完整律不变性。

新模型还按 i 指定几何和热壳。该额外 CQ 准备并不处在同一个固定背景，也改变高模能量边缘。因此上述不变式不能直接覆盖整个新准备过程。完整设备能量和工作成本也没有由此归零。

这些全局算子尚未由局域设备实现。[Fewster–Verch 的局域测量框架](https://arxiv.org/abs/1810.06512) 需要明确的系统—探针耦合和因果散射映射；只写出 CP 算子不满足那项责任。

## 4. 完整总能量是连续谱与热壳谱的卷积

在第 i 个静态历史中，令
\[
A_i=\sqrt{x_i},\quad V_i=2\pi^2A_i^3,\quad
E_{s,i}=\pi^2M_2/A_i^3,\quad \Omega_i=\sqrt3/A_i,
\]
\[
E_{c,i}=2V_i\rho_q(A_i)+U_0V_i-\frac1{2A_i}.
\]
减去 \(1/(2A_i)\) 正好扣除两个参考零模总能量，再插入实际条件零模。

八个独立热振子的总占据 N_i 为负二项分布：
\[
\Pr(N_i=k)=\binom{k+7}{7}(1+n_i)^{-8}
[n_i/(1+n_i)]^k.
\]
其均值为8n_i，方差为8n_i(1+n_i)。零模条件态与该热态为乘积。完整算符与 Laplace 变换为
\[
H_i=E_{c,i}+E_{s,i}S_0+\Omega_iN_i,
\]
\[
\mathbb E e^{-sH_i}
=e^{-sE_{c,i}}L_i(sE_{s,i})
[1+n_i(1-e^{-s\Omega_i})]^{-8}.
\]
不能继续把 H_i 说成单独的非中心 χ²。

完整方差为
\[
\operatorname{Var}H_i=E_{s,i}^2v_i+24n_i(1+n_i)/x_i,
\]
\[
\operatorname{Var}\rho_i=M_2^2v_i/(4x_i^6)
+6n_i(1+n_i)/(\pi^4x_i^4).
\]
[response.json](response.json) 单独保存正的热项，以免它在大零模方差的浮点显示中消失。实际两支完整密度 RMS／各自总平均密度均在约[0.10072287,0.10072345]内。所有数值沿用本模型单位，不换称 SI 实验灵敏度。

## 5. 完整局部噪声，包括非 Gaussian 失败支

在各支自己的几何上，以单位零模解
\(f_0=\eta/(\sqrt{2\pi^2}x_i)\) 和高模场 ψ_j 定义
\[
T[\psi_j+P_jf_0]=Q_{h,j}+P_jL_{h,j}+P_j^2C_i,\quad
C_i=T[f_0].
\]
这一定义固定 L_h 的因子2，避免交叉项系数歧义。两个 high species 为相同零均值 Gaussian 热真空混合，并与零模条件态为乘积。Gaussian 三阶矩、独立 species 的 connected cross 及线性高模均值都为零。于是完整对称 connected 噪声为
\[
\boxed{
N_{{\rm tot},i}
=2N_{h,i}+2\pi^2M_2\mu_i N_{L,i}
+(2\pi^2M_2)^2v_i\,C_i\otimes C_i.
}
\]
公式不要求零模条件态 Gaussian，也不要求两个零模之间独立。它保留高模二次噪声、零模—高模交叉噪声和共同径向项。U0 与 AE 减项是 c 数，不进入 connected 方差。

这里给出完整分解及全局能量的精确出口，没有宣称已数值求出新背景上的所有局部核或其引力传播。各个 i 的核位于不同几何；不能把它们无说明地当成一个背景上的 bitensor 相加。

## 6. 旧／新完整不变记录仍同律

两场相同的 Gaussian 零模参考、相同热壳及相同静态高模真空都保持内部 O(2)。原旧／新标签的径向 R 律一致，滤波 K_i 与 O(2) 交换。记录概率、μ_i 及由它们唯一决定的 x_i,n_i 也相同。

对任意允许保留 i 这个几何标签、其场效应保持 O(2) 的完整记录 A，
\[
\mathsf P_{\rm old}(i,A)=\mathsf P_{\rm new}(i,A).
\]
这是包括热噪声的完整总源记录结论。非不变的第一场记录不在该结论内；某个还未构造的引力通道也不能仅凭名称被判定是否满足合同。

## 7. 实际热态的响应，未把旧真空符号原封搬来

取固定入射态的扰动 \(\delta a/A=\epsilon e^{s\eta}\)，1≤s≤3。热占据是入射态参数；变分时随 KG 自由演化，不在每一时刻重新热化。k=2 有 ω²=3，完整有限模变分给
\[
\delta p_{\rm th}/\epsilon
=-\frac43\rho_{\rm th}\left(1+\frac{s^2}{s^2+12}\right).
\]
任意固定 canonical 零模态都有
\(\delta p_z/\epsilon=-6\rho_z\)，而 \(\rho_z+p_z=2\rho_z\)；故
\(3(\rho_z+p_z)+\delta p_z/\epsilon=0\)。这一消去与零模是否 Gaussian 无关。

线性守恒给 \(\delta\rho/\epsilon=-3(\rho+p)=-3/x\)。线性 trace 方程化为
\[
s^2-1+x\,\delta p/\epsilon=0.
\]
用背景 \(\rho+p=1/x\) 消去实际零模密度后，新增热贡献是
\[
x[3(\rho_{\rm th}+p_{\rm th})+\delta p_{\rm th}/\epsilon]
=\frac{4Jn}{3x}\frac{s^2+24}{s^2+12}.
\]
因此
\[
\mathcal D_{\rm new}(A,s)=\mathcal D_{\rm vac}(A,s)
+\frac{4Jn}{3A^2}\frac{s^2+24}{s^2+12}.
\]
\(\mathcal D_{\rm vac}(A,s)\) 是前驱已认证、适用于2λ<A<3λ的完整真空／固定 AE 表达式，在新 A 上取值；不是旧动态核硬移植。

前驱括号绝对值 <3.326006048。新有限热补项在括号中 <0.01801，合计 <4。因此 D_new(1)<0、D_new(3)>0，连续性给正增长根，且
\[
|s-2|<8/(3x)<3.992659\times10^{-10}
\]
对实际两支均成立。其固有时间增长率约2.44724×10^-5（模型单位）。这不是非线性不稳定定理，但足以阻止把本平均解称为稳定终点。

原固定入射态的一阶 FLRW Hamiltonian 噪声障碍也未消失：平均背景静态、总 \(\rho+p=1/x\)，其线性几何项和诱导密度相消，无法承接这里严格正的实际能量源噪声。改变初态相关或采用非线性／更大几何模型时，必须重新求完整约束及传播。
