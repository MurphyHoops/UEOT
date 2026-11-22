# 完整总源记录与平均预算—共同噪声前沿

## 1. 态与固定预算

d=sqrt(3)/2，sigma=±1。旧 Y=(sigma±sqrt(3))/2 各半；等价把
y_l=sigma(1-sqrt(3))/2、y_h=sigma(1+sqrt(3))/2 各半。
Y^2 分别为 1-d、1+d。新 Y=epsilon=±1 的概率是
(2+sigma epsilon)/4。两者 E Y=sigma/2，E Y^2=1。

两份相同的正规静态参考态作乘积，两个 Weyl 位移是 (Y u_cl,Z u_cl)。同一几何和同一 u_cl 上的源 M2 一次固定。允许有限随机化和 Y,Z 相关，定义

\[
R=Y^2+Z^2,\quad
\mathbb E_{\rm old}Z^2=\mathbb E_{\rm new}Z^2=b.
\]

Z^2>=0，E R=1+b。b 是同形 coherent 平均源预算，不是所有物质、重整化能量或硬件成本的普遍界。

## 2. 尖锐径向 TV 下界与达到构造

令 f(r)=min(1,|r-1|/d)。0<=f<=1，Lipschitz 常数 1/d。旧 f(Y^2)=1，新 Y^2=1，所以

\[
\mathbb E_{\rm old}f(R)\ge1-b/d,\qquad
\mathbb E_{\rm new}f(R)\le b/d.
\]

有界测试直接给 TV>=1-2b/d。

对 0<=b<=d/2，令 t=b/d。显式联合分布为：

| 旧 Y | Z^2 | 概率 |
|---|---:|---:|
| y_l | 0 | 1/2-t |
| y_l | d | t |
| y_h | 0 | 1/2 |

新 Y 完全保留原概率，独立选择 Z^2=0、d，概率分别 1-t、t。旧/新边缘、预算均严格满足合同。取 Z 非负平方根即可定义每个实际 coherent 分支。

径向律是

\[
\mu_o=(1/2-t)\delta_{1-d}+t\delta_1+\tfrac12\delta_{1+d},
\quad
\mu_n=(1-t)\delta_1+t\delta_{1+d}.
\]

共同质量为 2t，故

\[
\inf {\rm TV}(\mu_o,\mu_n)=(1-2b/d)_+.
\]

最低完全同律预算 b*=d/2，两者 R=1、1+d 各半。
旧 b>=d 定理要求单一固定半径，本轮放宽条件后并不撤销旧定理。

## 3. 完全同律后的共同方差最优界

任何共同径向律都满足 R>=1 且 P(R>=1+d)>=1/2。设均值 m=1+b<1+d=h，p=P(R>=h)>=1/2。对两组条件 Jensen，

\[
\operatorname{Var}R\ge\frac p{1-p}(h-m)^2\ge(d-b)^2.
\]

当 d/2<=b<=d，可达到：旧低支 Z^2=2b、高支 Z^2=0；新独立取 Z^2=2b-d、d 各半。共同 R=1+2b-d、1+d 各半，方差 (d-b)^2。b>=d 则取固定 R=1+b，旧补 Z^2=b±d，新补 Z^2=b。

因此 min Var R=(d-b)_+^2。b=d/2 的支持/均值条件还强迫唯一共同律，Var R=3/16。相干径向 CV=sqrt(3)/(4+sqrt(3))≈0.30216948；增大 lambda 不能压低此项。

要求同律且径向 CV<=epsilon 的必要且可达预算为
max[d/2,(d-epsilon)/(1+epsilon)]。
它不包含仍需加上的量子能量方差，也不直接认证半经典近似有效性。

## 4. 从径向律到完整 O(2) 不变记录

参考乘积态全部协方差在两场旋转下不变。相同 r=y^2+z^2 的分支属于同一 O(2) 轨道；总应力、两个相同 AE 减项和常势 U 不变。

任意有界旋转不变记录效应 E_A 都有
Tr(rho_yz E_A)=k_A(r)。完整记录律是同一个 Markov 核对径向律的作用。因此

\[
{\rm TV}(\mathsf P_o,\mathsf P_n)\le {\rm TV}(\mu_o,\mu_n).
\]

同径向律给所有此类记录严格同律。没有使用有限矩或无限矩决定性。对称性破缺的测量与记录准备标签的仪器不在此不可辨识结论中。

自由 multiplet 内部自同构背景：
[Fewster 1201.3295](https://arxiv.org/abs/1201.3295)。
此处只需显式两场旋转，不依赖一个额外未验证的自然态选择定理。

## 5. 完整 connected noise 与推迟交换子

令 Q_i 为单场参考的中心化二次应力，L_i 为沿 u_cl 位移的线性 cross stress，C=T[u_cl]。每支 Weyl 拉回后

\[
T_{\rm tot}=2\langle T\rangle_0+T^U+Q_1+Q_2+yL_1+zL_2+RC.
\]

L_ab=grad_a u grad_b phi+grad_b u grad_a phi-g_ab grad^c u grad_c phi。中心 Gaussian 的三次矩为零，两参考场独立，故作为合法分布/平滑涂抹有

\[
N_{\rm tot}=2N_0+(1+b)N_1+\operatorname{Var}R\,C\otimes C.
\]

包括 reservoir 的全部参考噪声和位移噪声，以及标签的场—reservoir cross noise。U 是同一真实常数物质参数，其 c-number 应力没有 connected noise。

低预算构造满足

\[
\operatorname{Var}_o R=d^2-db-b^2,\quad
\operatorname{Var}_n R=db-b^2,
\]

\[
N_o-N_n=d(d-2b)C\otimes C.
\]

均值相同，固定背景推迟交换子核也相同：
chi_tot=2chi_0+(1+b)chi_1。
这并未自动构造完整 metric response 的 contacts、约束或逆。

## 6. 实际静态量子总能量

V=2pi^2 A^3，canonical Var P_i=A^2/2，
mean(P_1,P_2)=sqrt(2pi^2M2)(y,z)。完整 Hamiltonian 是

\[
H=E_c+\frac{P_1^2+P_2^2}{2A^3}
+\sum_{i,k\ge2,\alpha}\frac{\sqrt{k^2-1}}A\,N_{ik\alpha},
\quad E_c=2V\rho_q+VU-\frac1{2A}.
\]

两个完整 rho_q 已包含每个 1/(4A) 的零模参考能量，最后一项避免重复计数。当前高模真空只使全空间 Hamiltonian 的高模项确定；其局部应力噪声没有消失。

令 Es=pi^2 M2/A^3，S_H=(H-Ec)/Es，nu=4pi^2 M2/A^2。
则条件 R=r 时，nu S_H 是非中心 chi-square(df=2, noncentrality=nu r)，密度与 Laplace 变换为

\[
k_\nu(s;r)=\frac\nu2e^{-\nu(s+r)/2}I_0(\nu\sqrt{sr}),\quad s\ge0,
\]

\[
\mathbb E(e^{-tS_H}\mid R)=
(1+2t/\nu)^{-1}
\exp[-tR/(1+2t/\nu)].
\]

故 E S_H=1+b+2/nu，Var S_H=Var R+4(1+b)/nu+4/nu^2。

若能量谱相等，径向 Laplace 变换在 (0,nu/2) 相等。右半平面解析性及 Laplace 唯一性推出径向律相等；反向由共同核显然成立。因此 b*=d/2 也是真实量子模型全部不变记录同律的尖锐平均 coherent 阈值。

## 7. 有限 nu 的实际记录界

把量子零模动量测量写为标准 Gaussian G_1,G_2，则

\[
S_H=R+2\sqrt{R/\nu}\,G_\parallel+(G_1^2+G_2^2)/\nu.
\]

因此

\[
\mathbb E|S_H-R|\le
2\sqrt{2(1+b)/(\pi\nu)}+2/\nu.
\]

用同一个 f 有

\[
{\rm TV}(\mathsf P_o^H,\mathsf P_n^H)\ge
[1-2b/d-\tfrac4d\sqrt{2(1+b)/(\pi\nu)}-\tfrac4{d\nu}]_+.
\]

对低预算显式构造，概率律差还严格分解成
(1-2b/d)[(K_(1-d)+K_(1+d))/2-K_1]。故能量 TV=(1-2b/d)D_nu，其中

\[
1-\tfrac4d\sqrt{2/(\pi\nu)}-\tfrac4{d\nu}\le D_\nu\le1.
\]

这是该构造的精确式，没有证明它在所有可能量子完成中全局最小。隐含径向 TV 与实际量子能量 TV 始终分开登记。

所有所用预算 0<=b<=d 的新平均历史上 nu>10^11。
b=0 的实际能量 TV>0.9999921476；
b=d/4 的通用下界>0.4999909043；
b=d/2 时两者完整概率律精确同一。

## 8. 明确的 CP 合法性和实现边界

有限制备映射 P_alpha(rho)=sum_j w_j W_j rho W_j^dagger，
Kraus sqrt(w_j)W_j，故 CP 且保迹。它保留原场边缘的完整概率，不靠逐时选择 squeezing 或参数根。

能量效应 E=f(S_H)，0<=E<=I。instrument 为
I_1(rho)=sqrt(E)rho sqrt(E)，
I_0(rho)=sqrt(I-E)rho sqrt(I-E)。辅助 qubit 的抽象 unitary dilation 是

\[
U_E=\begin{pmatrix}\sqrt{I-E}&-\sqrt E\\
\sqrt E&\sqrt{I-E}\end{pmatrix}.
\]

这些全局场的抽象合法映射没有实现紧支局域耦合、制备驱动、钟或引力探针；未知控制器成本未被称为零。局域系统—probe 实现责任参见
[Fewster–Verch 1810.06512](https://arxiv.org/abs/1810.06512)。

正规零模 Hilbert 空间 L2(R2) 中 P1^2+P2^2 的精确能量壳是 Lebesgue 零测集，没有正规可归一化本征态。不能通过非零概率的“精确能量后选择”免费删除最后量子方差；窄窗筛选和几何—物质联合相关是不同且尚需计算的合同。
