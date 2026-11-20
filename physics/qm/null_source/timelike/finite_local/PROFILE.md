# 新几何的光滑辅助过去与合法高态

本节只构造一个明示的 Hadamard 参考态族。它不是从实际局域测后高态到新几何的
设备实现，也不声称辅助过去满足 Einstein 方程。

## 1. 改半径时不能原封搬旧高频协方差

旧静态 canonical (q_k,pi_k) 高频协方差主项为
Var q_k~1/(2A^2 omega_k)、Var pi_k~A^2 omega_k/2。
新初片半径 a0 对应的主项必须换为 a0。
只把原数字硬搬过去时，Bogoliubov beta_k 趋于非零常数；
即使补半径 rescale，漏掉 pi=a(v'-hv) 的 canonical shear，
也会有 beta_k~h/(2omega_k)。S3 简并度 k^2 使两者都不 Hilbert-Schmidt。
有限阶 adiabatic 改正并不自动给 Hadamard 全阶短距离结构。

零模是有限维例外；可以保留正常条件 Q/P 态，按同一新几何运输，
但不能用这个例外替代无限高模匹配。

## 2. 统一的辅助过去存在

对 EVOLUTION 的 b_cl，记 z=b_cl^3。由能量恒等式

|z'|<=3 sqrt(z^2+beta)。

从 z(0)=1 积分，s∈[-2/5,0] 上

z(s)>=cosh(6/5)-sqrt(1+3/20)sinh(6/5)>(4/7)^3。

另一方面 b_cl''<=b_cl，反向 Duhamel 与非负初速给
b_cl(s)<=cosh(2/5)<13/12。正窗 tau<=1/10 上
b_cl<=exp(sqrt(23/20)/10)<9/8。
凸函数 b^2+(3/20)b^-4 的两个端点都小于 (4/3)^2，
故整个所用区间 |b_cl'|<4/3。这些都是有向区间或有理不等式，不依赖 ODE 采样。

## 3. 一个完全确定的 C-infinity 切换函数

先取 Beta(6,6) 概率密度 2772 x^5(1-x)^5 在 [0,1] 上的 CDF，
线性拉到 [-3/4,-1/20]，区间外为 0/1，记 chi0。
以固定 even C-infinity 概率核 j_eps 卷积，eps=1/20；
例如 j_eps(x)=Z^-1 exp[-1/(1-(x/eps)^2)]，|x|<eps，外为零。
令 chi=chi0*j_eps。

chi 真实为 C-infinity、0<=chi<=1，tau<=-4/5 时为0、tau>=0时为1。
中心对称使 integral_-4/5^0 chi=2/5。
卷积的 L-infinity 收缩给前五阶导数界
(4,23,316,3939,61850)；profile.py 用精确多项式临界根隔离及有向 Horner 验证，
没有把有限阶 chi0 误称为光滑无限阶函数。

定义 s(tau)=integral_0^tau chi，b_ext(tau)=b_cl(s(tau))。
辅助过去静态，未来与领先阶历史完全相同。这里 lapse 仍为1；
它是另造的尺度函数，不是把原物理解换个坐标。

## 4. 模态与有限导数证书

令 D=b d/dtau、h=b_tau、V=b_tau^2+b b_tau_tau。
使用变量 b=b_cl、v=b_cl'、zeta∈[0,3/20]、c_j=chi^(j)，有

V=c0^2(v^2+b^2-2zeta/b^4)+b v c1，

D=b[c0 v partial_b+c0(b-2zeta/b^5)partial_v
    +sum c_(j+1)partial_cj]。

全区间 tau∈[-4/5,1/10] 的直接区间展开给

|D^j V| < (10,95,1615,32568,811690)，j=0,...,4。

总 scaled conformal 长度 <=63/40，|h|<4/3。
这些界用于真实高频尾，不假定旧正频 E4 小范数。

## 5. 高态与低频能量

在辅助静态过去选择每个 k>=2 的 in-vacuum；正规零模另行给定。
光滑全局双曲演化保持 Hadamard；可把原 n_old 保留为新 in-basis 中两场 k=2
共八个振子的热占据，这只是有限模光滑修改。相同 n 不代表相同高态协方差。

令 p=sqrt(kappa)omega_k，scaled mode w 满足 w''+(p^2-V)w=0。
设 X=w/b，E=|X_tau|^2+(p^2/b^2)|X|^2，则

E_tau=-6Hbar |X_tau|^2-2Hbar(p^2/b^2)|X|^2。

领先阶 b_cl 在所用外侧允许支至多有一个极小值；chi>=0 保持这个顺序。
因此 E<=p b_-^2/b_min^6，且
b_-^2/b_min^6<(13/12)^2(7/4)^6=19882681/589824<34。
这避免低 p 下错误使用 exp(const/p) 的非可积估计。

背景参考：Junker–Schrohe, math-ph/0109010（有限 adiabatic 阶与 Hadamard 的区别）；
Olbermann, arXiv:0704.2986（光滑取样的 Hadamard 态选择）。
本构造与数值有限导数界由本节直接承担，未声称这两篇文献给出当前完整半经典存在。
