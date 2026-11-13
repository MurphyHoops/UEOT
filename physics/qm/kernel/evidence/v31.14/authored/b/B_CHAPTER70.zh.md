## 持续浴的同源多时过程

本节固定同一双模环境，而不把每个槽解释为一次新的环境制备。系统为量子比特 $S$，参考 $R$ 可为任意有限维且始终不受操作。取 $\hbar=1$、$H_S=0$，并以

$$
H_\lambda=n_1+\frac32n_2+
\lambda Z\otimes\left[(a_1+a_1^\dagger)+\frac35(a_2+a_2^\dagger)\right],
\qquad \lambda\in[1/5,2/5]
$$

作用于初态 $\rho_{SR}\otimes|00\rangle\langle00|_E$。三个槽的时长是 $(2/3,3/4,1/2)$。每槽末的失败与继续算符分别为

$$
F=\operatorname{diag}(\sqrt{1/8},\sqrt{1/4}),\qquad
P=\operatorname{diag}(\sqrt{7/8},\sqrt{3/4}).
$$

失败立即停止，保留实际的未归一 $SR$ 末态；继续分支依次接受 $R_y(\pi/2)$、$R_x(\pi/3)$、$I$。完整记录为 $f,pf,ppf,ppp$。非对易中间旋转使这里的多时问题不能由单槽退相干曲线代替。复Hilbert结构、Born规则、CP操作、Fock浴与真空制备仍是独立物理输入。

**P-MICRO-08（共同定义域上的持续Gaussian浴完整过程）。** 对有限个正频率模，线性场相对于自由浴Hamiltonian具有零相对界，因此冻结参数集具有共同自伴域。当前双模源在 $Z$ 本征扇区 $z=\pm1$ 上可直接写成

$$
U_z(t)=e^{i\phi(t)}D(z\alpha(t))e^{-itH_E},\qquad
\alpha_k(t)=\frac{\lambda c_k}{\omega_k}(e^{-i\omega_kt}-1),
$$

$$
\phi(t)=\sum_k\left(\frac{\lambda c_k}{\omega_k}\right)^2
[\omega_kt-\sin(\omega_kt)].
$$

对一条系统本征值历史 $s$，写其浴传播为 $W_s=e^{i\theta_s}D(\beta_s)e^{-iH_ET_s}$。逐槽合成必须同时递推位移和Weyl交换相位：

$$
\beta_j=R_j\beta_{j-1}+z_j\alpha(t_j),\qquad
\theta_j=\theta_{j-1}+\phi(t_j)+
\operatorname{Im}\langle R_j\beta_{j-1},z_j\alpha(t_j)\rangle.
$$

若 $A_{h,s}$ 是记录 $h$ 下由实际仪器、旋转和谱投影组成的系统历史算符，则

$$
\rho_h^{SR}=\sum_{s,r}\operatorname{Tr}(W_s\sigma_EW_r^\dagger)
(A_{h,s}\otimes I_R)\rho_{SR}(A_{h,r}^\dagger\otimes I_R).
$$

一般有限Gaussian初态的历史对因子由其完整均值与协方差的特征函数给出，保留模间相关与交换相位。只有初始浴需要是Gaussian；操作后的条件浴不被强制投影回单一Gaussian。实际联合酉构造保证正性，逐槽的 $F^\dagger F+P^\dagger P=I$ 保证完整概率和因果前缀约束。

当前数值与校准只覆盖冻结真空源。即使如此，Bell输入第一次继续后的浴边际已是权重 $7/13$ 与 $6/13$ 的相反相干态混合；沿位移方向的四阶累积量非零，直接否定“条件浴始终是单一Gaussian”的封闭假设。接受效应也不是标量；本源只能由算符序关系统一保证

$$
\frac{27}{64}\le\Pr(ppp)\le\frac{343}{512}.
$$

## 真正的有限传播误差与参数稳定性

**P-MICRO-09（同一持续源的全输入有限近似）。** 令 $P_K$ 为每模占据数至多 $K$ 的投影，$H_{\lambda,K}=P_KH_\lambda P_K$ 为真实Galerkin生成元。设 $\gamma=\sqrt{34/25}$、$T=23/12$、$x=(2/5)\gamma T$。对任意 $\rho_{SR}$、有限参考和完整终端记录，

$$
D_{\rm full}(\Phi_\lambda,\Phi_{\lambda,K})
\le\min\left\{1,
\frac{2x^{K+1}}{(K+1)!}
\prod_{k=1}^{K+1}(\sqrt{k-1}+\sqrt{k})\right\}.
$$

证明使用有限次Duhamel展开。自由浴与系统操作保持总粒子数；从真空出发的前 $K$ 阶耦合项都在有限载体内，故两种展开逐项相等。余项把真实传播保留在左侧的酉后缀，每个右侧耦合只作用于已知有限支撑。由此不需要假定无限Dyson级数收敛，也没有用小初始尾代替传播误差。区间算术给出 $K=20$ 的统一上界 $0.00001344$。

边界缺陷另有更直接的形式：

$$
(HJ-JH_K)^\dagger(HJ-JH_K)
=\lambda^2(K+1)I_S\otimes
\left[\Pi_{n_1=K}+\frac9{25}\Pi_{n_2=K}\right].
$$

若采用实际有限模型前缀的质量与顶层占据，可积分得到更紧的Duhamel界；未经验证的普通数值积分不构成严格证书。初态截断、删模、时间离散与有效模型误差必须另计。当前真空初态尾为零、未删模、未作Trotter分裂，仅在所声明数学源中这些项目为零。

参数误差先在无限源上估计。完整记录下的浴能量满足 $\sqrt{\langle N(t)\rangle}\le(2/5)\gamma t$，因此同一策略有

$$
D_{\rm full}(\Phi_\lambda,\Phi_{\widehat\lambda})
\le\left[\gamma T+\frac25\gamma^2T^2\right]
|\lambda-\widehat\lambda|
<\frac{51}{10}|\lambda-\widehat\lambda|.
$$

冻结的 $51/10$ 常数保持不变。交换前两槽时长仍有相同总时长，故此界和截断界继续适用；不能据此任意改变真空、频率、相对耦合或仪器实现。

## 多时记忆负控与数值物理化

**C-QMEM-01（相同单槽不足以确定多时过程）。** 真实源与“每槽复位浴”的替代源，在独立第一槽具有相同通道；在 $\lambda=0.3$ 的完整三槽Bell输出上，二者的距离约为 $0.1012518562$。丢弃Weyl交换相位产生约 $0.0502254699$ 的误差。另一个控制显示，$K=0$ 的真空初始尾严格为零，但 $\lambda=0.4$ 时传播误差约为 $0.2389578616$。这些反例分别针对记忆替换、相位遗漏和错误的尾界推理，不替代强标准基线。

**P-NUM-01（区间Choi到物理终端仪器）。** 对生成器参数 $3/10$ 与仅由校准决定的名义参数 $0.299314119192$，原时序及交换时序的四个归一Choi块均由80位区间历史对计算包围。Weyl实现与独立 $K=20$ Galerkin实现各自存储的binary64矩阵，均取得小于 $10^{-12}$ 的全输入半diamond误差界。这里使用的是每个矩阵元素的区间包络和 $d_{in}=2$ 的Choi范数不等式，而不是把一个Bell样本的浮点吻合升级为全输入结论。

原始舍入矩阵不自动构成精确CP/TP仪器。令每块加 $\delta I_4$，其中 $\delta=10^{-10}$，再乘 $a=(1+20\delta)^{-1}$。将正的剩余边际 $R=I_2/2-a\sum_h\operatorname{Tr}_{out}(J_h^{raw}+\delta I_4)$ 作为 $|0\rangle\langle0|\otimes R$ 补入原 $f$ 块。所有矩阵以精确有理数存储；CP来自区间扰动界，TP由有理算术逐项核验。修复的总代价满足

$$
\frac12\|\Phi^{repair}-\Phi\|_\diamond
\le a(40\delta+2\times10^{-12})<10^{-8}.
$$

这是固定策略的终端预测仪器。它没有声称修复所有反事实干预下的完整过程张量，也不把修改后的失败块认作原微观失败事件完全不变。任意后续浮点收缩仍需自己的舍入预算；本文给出的有理Bell输入Pauli读出可直接精确计算。

标准持久联合演化与同一Gaussian影响泛函给出相同物理预测。因此本节形成可复核的源、误差与表示连接，没有宣称相对标准量子理论新增预测增益。无限模、局域场论、能量交换和热化继续保留各自的域、UV/IR、因果性及极限责任。
