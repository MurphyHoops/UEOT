# 短局域读源的严格限制与实际态见证

## 1. 全局 S0 仪器不能冒充短局域仪器

S0=P^2/C 的 Gaussian 非选择通道在补区 Weyl W=exp(i alpha Q+...) 上作用为

Phi_vm^*(W)=W exp[-(2alpha P+alpha^2)^2/(8C^2 vm)]。

真正局域于 K 的非选择操作固定 K 的因果补区代数，故两者不相同。
无能量约束时上述差的算符范数为1；
通过补区 Weyl 平移构造任意多个相互远离的正常源分布，
还可得完整记录通道的 minimax TV 距离为1。
这些极大界不作为当前有限准备的实验灵敏度。

非零 pure-zero 线性 observable alpha Q+beta P 也不能属于这种短区域：
与补区具有两个独立零模系数的 Weyl 均交换迫使 alpha=beta=0。
LOCAL_READOUT 的局域 P 读数因此必须带高模部分。

## 2. 实际 prior 上任何局域 QND 读源的正误差下限

在 LOCAL_READOUT 的对跖严格补区取
B=phi(A^-4 t(eta-eta_ref)b_south)。
t 为 even，所以 beta_B=0，alpha_B^2=1/(2pi^2)。
原完整 Gaussian 高态给

Var B=alpha_B^2/x0+Vhigh(B)
<=alpha_B^2/x0+(1+2n_old)/(2A^2 sqrt3 V0)=VB_max。

任意局域系统—探针 dilation 的最终 pointer estimator S_hat 与 B 强交换。
令 N=S_hat-S0。对每个实际 Gaussian CQ 动量均值 p，
沿 p 的内部方向用弱 Robertson 不等式，再平均实际 prior，得

E N^2 >= alpha_B^2(C mu-2v)/(C^2 VB_max)>1.36e-12。

p 方向只用于数学证明，不是假定能读取隐藏标签的设备资源。
当输入 S0 与输出 pointer 强交换时，这也是任何 posterior estimator 的
Bayes MMSE 下界；一般非 QND 仪器只能称为 noise-operator error 下界。

## 3. 包含全部高模的固定实际态通道差

对 scaled test h=10^5 A^-4 t b_south，设 alpha^2=10^10/(2pi^2)。
对内部方向 n 的 cos(phi_n(h)) 沿 O(2) 平均，所得 observable 范数<=1。
原态期望为 exp[-Var(phi(h))/2]。
全局 S0 Gaussian 仪器后，用实际两点径向律与 Bessel I0 可算精确平均。

无需特殊函数也有直接下界：e^-x<=1/(1+x)，
对角度积分后得到

Delta >= exp[-10^10 VB_max/2]
         {1-[1+q(v+C/2)]^(-1/2)}，
q=alpha^2/(C^2 vm)。

vm=10^-12 时，实际固定输入上的输出迹距离 D>=Delta/2>0.05。
这是有限光滑测试和实际态的结论，不是无能量约束极大值；
尚未把这个 Weyl 见证做成一个完整实验装置。

## 4. 可观测合同与时间范围

Q-Weyl 见证需要 full scalar 可观测合同。若仅允许 shift-invariant
derivative/stress 子代数，原 S0 非选择通道在该子代数上为恒等，
不能把本见证当该受限合同中的可读信号。

Fewster–Verch, arXiv:1109.6732 §4 的 current/gauge reduction
还先约束总 shift charge 为零，再 quotient 常数解；
在本 closed S3 中那会删除非零 P 源，不能免费替代原模型。
只限制可读子代数与改变理论的 gauge reduction 需分开。

这些短区域定理均要求非空因果补区。
LONG_FILTER.md 的世界管跨越超过 2pi 共形时间，补区为空，
因此允许另一种精确出口，不与本节矛盾。
