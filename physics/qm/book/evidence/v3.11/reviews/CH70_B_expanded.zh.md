## 持续浴的同源多时过程

### 源、记录与结论的量词

本节保留同一个双模环境，直到各分支真正停止。系统为量子比特 $S$；初态 $\rho_{SR}$ 任意，参考 $R$ 可为任意有限维且在动力学中不受操作。取 $\hbar=1$、$H_S=0$，并固定以下源：

$$
\begin{aligned}
H_\lambda&=I_S\otimes H_E+\lambda Z\otimes B,
&H_E&=n_1+\frac32n_2,\\
B&=(a_1+a_1^\dagger)+\frac35(a_2+a_2^\dagger),
&\lambda&\in[1/5,2/5],\\
\rho_{SRE}(0)&=\rho_{SR}\otimes|00\rangle\langle00|_E,
&(t_1,t_2,t_3)&=(2/3,3/4,1/2).
\end{aligned}
$$

每槽的联合演化后，执行完整二分支仪器 $F=\operatorname{diag}(\sqrt{1/8},\sqrt{1/4})$、$P=\operatorname{diag}(\sqrt{7/8},\sqrt{3/4})$。失败立即停止，并保留实际的未归一 $SR$ 末态；继续分支依次接受 $R_y(\pi/2)$、$R_x(\pi/3)$、$I$。所有终端记录 $f,pf,ppf,ppp$ 均保留。距离为各记录块迹范数差之和的一半，环境只在终端按合同迹去。复Hilbert空间、Born规则、CP操作、振子源和真空制备仍是独立物理输入；本节没有从Core唯一导出它们。

**P-MICRO-08（共同定义域上的持续Gaussian浴完整过程）。** 下文首先构造合法的共同源，再推导其完整多时响应。一般有限Gaussian初态只用于明确解析公式的范围；本节执行、校准及数值认证的初态始终是上述冻结真空。

### 场算符界与共同自伴域

对有限正频率模，令 $a(g)=\sum_k g_k^*a_k$、$b_g^2=\sum_k|g_k|^2/\omega_k$。在有限Fock向量上，Cauchy–Schwarz与CCR给出

$$
\begin{aligned}
\|a(g)\psi\|&\le b_g\|H_E^{1/2}\psi\|,\\
\|a(g)^\dagger\psi\|^2
&=\|a(g)\psi\|^2+\|g\|_2^2\|\psi\|^2,\\
\|(a(g)+a(g)^\dagger)\psi\|
&\le2b_g\|H_E^{1/2}\psi\|+\|g\|_2\|\psi\|.
\end{aligned}
$$

谱不等式 $\sqrt{x}\le\epsilon x+(4\epsilon)^{-1}$ 将最后一行化为任意小的 $H_E$ 相对界加有界项。因此线性场的相对界为零；有限系统算符有界，Kato–Rellich定理给出自伴实现，定义域为 $\mathbb C^2\otimes D(H_E)$。有限耦合的紧参数集与正频率下界使这些估计一致。在当前模型中，还可直接完成平方。令 $\omega=(1,3/2)$、$c=(1,3/5)$，在 $Z$ 本征扇区 $z=\pm1$ 上得到

$$
\begin{aligned}
U_z(t)&=e^{i\phi(t)}D(z\alpha(t))e^{-itH_E},\\
\alpha_k(t)&=\frac{\lambda c_k}{\omega_k}(e^{-i\omega_kt}-1),\\
\phi(t)&=\sum_k\left(\frac{\lambda c_k}{\omega_k}\right)^2
[\omega_kt-\sin(\omega_kt)],\\
D(\zeta)&=\exp\!\left[\sum_k(\zeta_ka_k^\dagger-\zeta_k^*a_k)\right].
\end{aligned}
$$

位移关系 $a_kD(\zeta)=D(\zeta)(a_k+\zeta_k)$ 表明有限位移保持 $D(H_E)$；新增一次场项的范数正由前述界控制。这个显式酉与共同自伴源一致，并非用未证收敛的形式级数定义动力学。

### 含完整停止记录的能量界

将仪器扩张到有限记录寄存器；已停止分支在剩余时段只让浴自由演化。如此补齐到共同终点 $T=23/12$ 不改变它的终端记录或 $SR$ 输出。系统与记录操作均保持总粒子数 $N=n_1+n_2$，存活分支上的控制耦合算符范数至多为1。取 $\gamma=\|c\|_2=\sqrt{34/25}$。从真空出发，有限条位移历史具有所需数矩；在这个实际定义域上求导并用Cauchy–Schwarz，可得

$$
\left|\frac{d}{dt}\langle N\rangle\right|
\le2|\lambda|\gamma\sqrt{\langle N\rangle},
\qquad
\sqrt{\langle N(t)\rangle}\le|\lambda|\gamma t.
$$

零初值可先以 $\sqrt{\langle N\rangle+\epsilon}$ 正则化，再令 $\epsilon$ 趋于零。这是完整记录、未后选择的能量界；条件分支除以小概率后不能无代价沿用它。对另行声明的有限能量Gaussian初态，右侧改为 $\sqrt{\langle N(0)\rangle}+|\lambda|\gamma t$；这不自动赋予非真空输入当前的截断或数值证书。

### 一般相关Gaussian初态的完整历史对

在一条系统本征值历史 $s=(z_1,\ldots,z_n)$ 上，令 $R_j=\operatorname{diag}(e^{-i\omega_kt_j})$。从 $\beta_0=0,\theta_0=0$ 逐槽递推

$$
\begin{aligned}
\beta_j&=R_j\beta_{j-1}+z_j\alpha(t_j),\\
\theta_j&=\theta_{j-1}+\phi(t_j)
+\operatorname{Im}\langle R_j\beta_{j-1},z_j\alpha(t_j)\rangle,\\
W_s&=U_{z_n}(t_n)\cdots U_{z_1}(t_1)
=e^{i\theta_s}D(\beta_s)e^{-iH_ET_n}.
\end{aligned}
$$

第二行保留Weyl乘法产生的交换相位。它在非对易中间操作之后通常不能被删除。

取正则坐标 $r=(q_1,p_1,q_2,p_2)$，其中 $q_k=(a_k+a_k^\dagger)/\sqrt2$、$p_k=(a_k-a_k^\dagger)/(i\sqrt2)$，且 $\Omega=\bigoplus_{k=1}^2\begin{pmatrix}0&1\\-1&0\end{pmatrix}$。均值为 $d$，对称协方差为 $V$，要求 $V+i\Omega/2\succeq0$。这里的 $V$ 是完整矩阵，允许模间相关。Gaussian特征函数与历史对因子为

$$
\begin{aligned}
\xi(\zeta)&=\sqrt2(\operatorname{Im}\zeta_1,-\operatorname{Re}\zeta_1,
\operatorname{Im}\zeta_2,-\operatorname{Re}\zeta_2)^T,\\
\chi_\sigma(\zeta)&=\operatorname{Tr}[\sigma D(\zeta)]
=e^{i\xi(\zeta)^Td-\frac12\xi(\zeta)^TV\xi(\zeta)},\\
F_{s,r}&=\operatorname{Tr}(W_s\sigma_EW_r^\dagger)\\
&=e^{i[\theta_s-\theta_r+\operatorname{Im}\langle\beta_r,\beta_s\rangle]}
\chi_\sigma\!\left(e^{i\omega T_n}(\beta_s-\beta_r)\right).
\end{aligned}
$$

此式由迹循环性、$D(-\beta_r)D(\beta_s)$ 的Weyl相位和自由旋转直接得到。它没有把初始相关浴拆成产品态，也没有假定操作后的条件浴仍是Gaussian。

对终端记录 $h$，以 $M_{h,j}$ 表示该槽实际的失败或旋转后继续算符，定义 $A_{h,s}=M_{h,n}\Pi_{z_n}\cdots M_{h,1}\Pi_{z_1}$。完整输出为

$$
\rho_h^{SR}=\sum_{s,r}F_{s,r}
(A_{h,s}\otimes I_R)\rho_{SR}(A_{h,r}^\dagger\otimes I_R).
$$

它正是实际联合算符 $\sum_sA_{h,s}\otimes W_s$ 作用后迹去环境的展开，所以是CP映射；$(F_{s,r})$ 也构成正半定Gram矩阵。逐层求和并使用 $F^\dagger F+P^\dagger P=I$，得到总迹为1和因果前缀约束。全过程保留参考。由 $(3/4)I\preceq P^\dagger P\preceq(7/8)I$ 对存活质量递推，可得 $27/64\le\Pr(ppp)\le343/512$；这不意味着实际接受效应是标量，也不使归一后选择成为线性通道。

即使真空初态也不维持单Gaussian条件闭合。Bell输入首次继续后，浴边际是权重 $7/13,6/13$ 的相反相干态混合；令 $\mu=\sqrt2|\alpha_1(t_1)|$，其位移方向四阶累积量为 $\mu^4(-2+8/169-6/28561)$，非零位移时严格非零。Gaussian初态与完整Gaussian条件动力学因此是不同前提。

## 真正的有限传播误差与参数稳定性

### 有限Duhamel展开与全输入提升

**P-MICRO-09（同一持续源的全输入有限近似）。** 令 $P_K$ 为每模占据数至多 $K$ 的投影，$J_K$ 为嵌入，使用真实压缩 $H_{\lambda,K}=J_K^\dagger H_\lambda J_K$。自由浴与全部记录扩张操作保持总粒子数。在包含这些操作的相互作用绘景中，场算符记为 $\widetilde V(s)$；它在总粒子数至多 $k-1$ 的子空间上的范数至多为 $\gamma(\sqrt{k-1}+\sqrt{k})$。

关键是选择真实传播留在左侧的Duhamel取向：

$$
W(T,0)=I-i\lambda\int_0^T W(T,s)\widetilde V(s)\,ds.
$$

将左侧后缀继续展开有限次。第 $j$ 阶余项中，真实酉仍在所有场因子的左侧，而右端是从真空开始的有限支撑向量。每作用一次场，总粒子数至多增加1。故 $j\le K$ 的所有项均位于 $N\le K$，并包含在矩形投影 $P_K$ 内；无限源与有限源的前 $K$ 阶项完全相同。有限源余项中的投影不能增大范数。令 $\lambda_{\max}=2/5$，利用有序时间单纯形体积，可分别控制两个 $K+1$ 阶余项：

$$
\begin{aligned}
x&=\lambda_{\max}\gamma T,
&c_j&=\frac{x^j}{j!}\prod_{k=1}^j(\sqrt{k-1}+\sqrt{k}),\\
\|(W-J_KW_KJ_K^\dagger)\psi_{\rm vac}\|
&\le c_{K+1}+c_{K+1},
&d_K&=\min\{1,2c_{K+1}\}.
\end{aligned}
$$

这里没有无限Dyson级数的收敛假设，也没有让未受控的无限演化状态站在场算符右侧。对任意输入先纯化，将所有仪器记录保留在扩张中；上述算符估计对附加参考恒等映射不变。归一纯态的迹距离不超过相应向量差，再迹去环境和不用的扩张寄存器，得到

$$
\sup_{\rho_{SR},\,\dim R<\infty}
\frac12\sum_h\left\|
(\Phi_{\lambda,h}\otimes\operatorname{id}_R)(\rho_{SR})-
(\Phi_{\lambda,K,h}\otimes\operatorname{id}_R)(\rho_{SR})
\right\|_1\le d_K,
\qquad d_{20}<0.00001344.
$$

因此这是任意 $SR$ 输入的解析结论，而非Bell输入数值吻合的外推。只要保留同一总暴露时间和合法的系统操作，交换前两槽时长仍适用同一界。

### 真实有限前缀上的边界残差

初态尾小并不证明压缩生成元传播准确。对于当前矩形截断，只有升算符穿越上边界，两个模式的出射面相互正交，故

$$
\begin{aligned}
\mathcal R_K&=H_\lambda J_K-J_KH_{\lambda,K},\\
\mathcal R_K^\dagger\mathcal R_K
&=\lambda^2(K+1)I_S\otimes
\left[\Pi_{n_1=K}+\frac9{25}\Pi_{n_2=K}\right].
\end{aligned}
$$

令 $\sigma_h$ 是同一有限模型在存活节点的实际未归一前缀，质量为 $m_h$；其局部有限演化为 $\sigma_h(s)$。对子归一态作纯化，Duhamel给出的向量缺陷积分需要再乘其范数 $\sqrt{m_h}$，才能成为迹距离界。随后以真实完整后缀的收缩性沿树求和，得到

$$
r_h(s)=\operatorname{Tr}\!\left[
(\mathcal R_K^\dagger\mathcal R_K\otimes I_R)\sigma_h(s)\right],
\qquad
D_{\rm full}\le\sum_{h\,\mathrm{live}}\int_0^{t_h}\sqrt{m_h r_h(s)}\,ds.
$$

这些占据和质量必须来自真实有限前缀；不能偷换成无限源的占据。该式可给出更紧界，但本节没有把普通数值求积当作区间证书。实际采用的统一认证是前面的 $d_K$。

当前真空初态尾为零，未删模、未作Trotter分裂。若改变初始浴，投影尾与有限传播缺陷须分开支付；相关模不能被重新制备为产品真空。删模应在同一Hilbert空间上关闭相应耦合，并对实际保留初态及有限域的耦合差作Duhamel估计。真实器件的准备、控制、泄漏、有效模型与读出误差仍须独立确定。

### 先在无限源上证明参数稳定性

对 $\lambda,\widehat\lambda\in[1/5,2/5]$，比较同一控制器与停止规则。参数Duhamel公式中的差为 $(\lambda-\widehat\lambda)Z\otimes B$；其右端前缀是无限源的真实演化。因此应使用已经证明的无限源能量界，而不是假定有限压缩继承某个不变量。对归一纯化前缀有

$$
\begin{aligned}
\|B\psi(t)\|&\le\gamma\left(\sqrt{\langle N\rangle}
+\sqrt{\langle N\rangle+1}\right)
\le\gamma(1+2\lambda_{\max}\gamma t),\\
D_{\rm full}(\Phi_\lambda,\Phi_{\widehat\lambda})
&\le|\lambda-\widehat\lambda|
\int_0^T\gamma(1+2\lambda_{\max}\gamma t)\,dt\\
&=|\lambda-\widehat\lambda|
[\gamma T+\lambda_{\max}\gamma^2T^2]
<\frac{51}{10}|\lambda-\widehat\lambda|.
\end{aligned}
$$

括号中的实际常数约为 $4.2336426708$；以 $\gamma<7/6$ 即可完全有理地界为 $38111/9000<51/10$。本节保留先前冻结的 $51/10$。这一参数估计先成立，再组合有限截断与数值表示的误差。它不允许静默改变频率、相对耦合、浴制备或控制权限。

## 多时记忆负控与数值物理化

### 固定三槽的严格记忆见证

**C-QMEM-01（相同单槽不足以确定多时过程）。** 将环境在每槽后重新制备为真空，会得到另一过程。其孤立单槽通道对任意输入和参考都与真实源相同，因为这一槽仍从同一真空作同一演化。但同一三槽Bell输入在 $\lambda=3/10$ 时，事件“记录为 $ppp$ 且 $X_S\otimes X_R=+1$”有严格区间见证：

$$
p_{\rm reset}-p_{\rm persistent}
>0.03164037538529123569>\frac3{100},
\qquad
D_{\rm full}(\Phi_{\rm reset},\Phi_{\rm persistent})>\frac3{100}.
$$

这里使用80位区间历史对与独立的逐槽复位Schur通道计算，并保存准确dyadic端点。事件概率差下界直接给出迹距离下界，不需要对迹范数作区间特征值求解，也没有借用另一个因果断开协议。完整迹距离约 $0.1012518562$ 另列为浮点诊断。漏交换相位的误差约 $0.0502254699$；$K=0$ 的真空初始尾严格为零，但 $\lambda=0.4$ 时传播误差约 $0.2389578616$。这些控制说明不同缺项的实际后果，不替代强标准基线。

### Choi区间包络为何控制任意参考输入

**P-NUM-01（区间Choi到物理终端仪器）。** 使用归一Bell向量 $|\Omega_2\rangle=(|00\rangle+|11\rangle)/\sqrt2$，按“输出 $S$、输入参考”的顺序定义四个归一Choi块：

$$
J_h=(\Phi_h\otimes\operatorname{id}_2)
(|\Omega_2\rangle\langle\Omega_2|),
\qquad
J_h\succeq0,
\qquad \sum_h\operatorname{Tr}_{\rm out}J_h=I_2/2.
$$

对生成参数 $3/10$、仅由校准决定的名义参数 $0.299314119192$，原时序与交换时序的全部矩阵元素均由独立80位区间公式包围。各时序分别认证Weyl实现和 $K=20$ Galerkin实现的实际binary64存储矩阵，共八份证书。将存储矩阵转为精确有理数并Hermitian化，记为 $Q_h$。从元素区间得到Frobenius误差界，而每块维数为4，故

$$
\begin{aligned}
e&:=\sum_h\|Q_h-J_h\|_1
\le2\sum_h\|Q_h-J_h\|_F<10^{-12},\\
\frac12\|\mathcal Q-\Phi\|_\diamond
&\le\frac{d_{\rm in}}2\sum_h\|Q_h-J_h\|_1=e,
\qquad d_{\rm in}=2.
\end{aligned}
$$

第二行可直接由向量化核对。任意参考维数上的归一秩一输入 $|u\rangle\langle v|$ 可写成 $(I\otimes A)|\Omega_2\rangle\langle\Omega_2|(I\otimes B^\dagger)$，其中 $\|A\|,\|B\|\le\sqrt2$；两侧乘法至多把每块迹范数放大2。再对任意迹类输入作奇异值分解并求和，即得到diamond界。因此这里认证的是存储线性映射对所有参考输入的误差，不是把一个Bell样本的浮点吻合外推。

区间认证直接比较精确无限源与实际存储矩阵。对Galerkin后端，这个固定名义参数下的差已经包含其截断与浮点矩阵指数误差；不能把它仅称为舍入误差。此前 $d_{20}$ 则是独立的、对整个冻结参数区间一致的解析界。

### 精确CP/TP修复及其逐项成本

原始 $Q_h$ 不自动为正或迹保持。取有理数 $\delta=10^{-10}$、$a=(1+20\delta)^{-1}$，定义

$$
\widetilde Q_h=Q_h+\delta I_4,
\qquad
R=I_2/2-a\sum_h\operatorname{Tr}_{\rm out}\widetilde Q_h.
$$

每块算符误差至多为 $e<\delta$，所以 $\widetilde Q_h\succeq0$。偏迹对Hermitian输入的迹范数收缩给出总边际误差至多为 $e<2\delta$。四块的 $\delta I_4$ 经偏迹贡献 $8\delta I_2$，于是

$$
a\sum_h\operatorname{Tr}_{\rm out}\widetilde Q_h
\preceq a(1/2+10\delta)I_2=I_2/2,
\qquad R\succeq0.
$$

对所有块先取 $J_h^{\rm rep}=a\widetilde Q_h$，再仅向原 $f$ 块加入 $|0\rangle\langle0|_{\rm out}\otimes R$。所有块为正，且总输出偏迹严格等于 $I_2/2$，因而定义一个CP/TP终端仪器。矩阵、$a,\delta,R$ 均以精确Fraction保存；TP与Hermitian性逐项有理核验。独立审查还精确核查了八证书中全部块和 $R$ 的504个主子式。

为明确修复代价，记 $\Delta_h=Q_h-J_h$、$s=\sum_h\operatorname{Tr}\Delta_h$，则 $|s|\le e$。利用 $R\succeq0$、$\sum_h\operatorname{Tr}J_h=1$，逐项三角估计为

$$
\begin{aligned}
\sum_h\|J_h^{\rm rep}-J_h\|_1
&\le ae+(1-a)+16a\delta+\operatorname{Tr}R,\\
\operatorname{Tr}R&=1-a(1+s+16\delta),\\
\sum_h\|J_h^{\rm rep}-J_h\|_1
&\le ae+2(1-a)-as\\
&\le2ae+40a\delta
=a(40\delta+2e)<10^{-8},\\
\frac12\|\Phi^{\rm rep}-\Phi\|_\diamond&<10^{-8}.
\end{aligned}
$$

其中 $16a\delta$ 来自四个四维块，$2(1-a)=40a\delta$ 来自归一化缩放；没有遗漏输入维数因子。这是已计成本的物理化，不是把原始“近CP”矩阵直接认作CP。

修复对象只是一项固定策略的终端预测仪器。这里不声称它可在原来的每个早停时刻逐槽插入，也不声称它修复了所有反事实干预下的完整过程张量；修改后的失败块与原微观失败事件的差已经进入上界。若随后以浮点方式对任意输入收缩这些矩阵，还需新增该收缩的舍入预算；本文固定Bell输入的Pauli读出可从有理矩阵精确计算。

在冻结校准证书中，保守预算继续采用

$$
\varepsilon_{\rm CQ}
=\frac{51}{10}r_\lambda+d_{20}+\varepsilon_{\rm phys},
\qquad
\varepsilon_{\rm tester}
=\varepsilon_{\rm CQ}+\frac12r_\eta,
\qquad \varepsilon_{\rm phys}=10^{-8}.
$$

由于当前名义参数的区间证书已直接控制无限源到修复预测器的差，额外再付 $d_{20}$ 是保守预留，不是将同一误差伪装成两次独立发现。$r_\eta/2$ 只适用于声明的完整二值终端读出模型，不是任意器件SPAM的统一上界。

标准持久联合演化和同一Gaussian影响泛函预测相同物理结果。本节连接了明确前提、完整记录、实际有限传播和可审计数值表示，没有宣称相对标准量子理论的新增经验优势。无限模、局域场论、能量交换与热化仍分别需要UV/IR条件、表示选择、因果组合和极限证明。
