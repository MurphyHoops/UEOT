# 《UEOT物理学》v3.0 高级章节完整修订块

基准为原 v2 Markdown，SHA256 `2fa47d663bb212153a2829e816444e99805348266eefd5a27882e8dbbf4e58a1`。未在下表列出的正确正文原样保留；第 33–35、47–48 章及新内核章由总编辑负责。本文件不替代总著。

装配文件：同目录 `advanced_replacements.json`，每项 `old` 是原 v2 中逐字精确且唯一的片段；按列表顺序断言 `count(old)==1` 后替换。插入项同时绑定前段末尾及后一标题。完整顺序干运行已检查旧章节和命题 HTML 锚点不丢失。

## ADV-14

操作：replace。开始锚点：`## 14.1 Wigner 与生成元`。结束锚点：`## 14.4 时间反演与标准基准`。

来源与理由：v25.2 sections Wigner / common smooth domain / Bargmann massive branch; v2 chapter 14; v31.3 kernel scope ledger。

<!-- BEGIN ADV-14 -->

本章及第 15–32、36–46 章以标准量子扇区和各章明列的领域输入为起点。文中的纸面命题、采用的外部重定理、精确算术回归、浮点计算和 Lean 定理按不同证据登记。有限 Kraus 内核使其中若干操作合同可以机器复查；它不自动证明本章开始使用的无限维表示、自伴域、场论或热力学极限。具体覆盖以形式化命题登记和冻结回执为准。

## 14.1 Wigner 与生成元

**K-QSYM-01：Wigner。** 保持全部射线转移概率的双射由酉或反酉算符实现，唯一到相位。这是针对已经给定复 Hilbert 射线空间的标准定理。它不从一般状态集合、对象名称或有限个角度的测试重建全部量子理论。

若一个群的射线作用适当连续，且选定单位元附近的连续实现，连通单位元分支由酉射影表示实现；射影乘子仍须处理，不能据此断言整个群已有单值普通酉表示。适用时可转到覆盖群或中心扩张。离散时间反演可以反酉。

无界生成元不是任意可交换的矩阵。对每个强连续酉单参数子群，Stone 定理给自伴生成元；对有限维 Lie 群的强连续酉表示，可在稠密光滑向量空间上定义共同的无穷小表示并讨论 Lie 括号。以下含 $P,J,K,H$ 的对易式首先在这样的共同不变域上使用，随后再处理相应算符的闭包与域；形式对易式并不单独证明全局群表示存在。

有限维可逆 CPTP 动力学若其逆也 CPTP，则为酉共轭。对连续参数微分得到
$$
\dot\rho=-i[H,\rho]/\hbar.
$$
这个标准量子序同构结果不包含反酉转置通道，也不决定具体 $H$。例如复矩阵转置虽然保持单系统正性，但其 Choi 算符是交换算符，反对称子空间有负本征值，故它不是完全正映射。反酉是对称操作对射线的实现类别，不能因此列入任意系统上可实施的 CPTP 控制库。

## 14.2 旋转与自旋

角动量代数
$$
[J_i,J_j]=i\hbar\epsilon_{ijk}J_k
$$
的有限维不可约酉表示由 $s=0,\tfrac12,1,\ldots$ 标记，并满足
$$
J^2=\hbar^2s(s+1),\qquad J_z=\hbar m,
\qquad m=-s,-s+1,\ldots,s.
$$
令 $J_\pm=J_x\pm iJ_y$，由代数得到
$$
\|J_\pm|s,m\rangle\|^2
=\hbar^2[s(s+1)-m(m\pm1)].
$$
范数非负、最高与最低权的终止及相邻权相差一，要求 $2s\in\mathbb N$。这是离散表示标签的来源。轨道单值标量球谐对应整数 $\ell$；内禀自旋属于另外声明的内部表示。

半整数自旋的向量在 $2\pi$ 转动下变号，而射线不变；$SO(3)$ 的相应射影表示由 $SU(2)$ 覆盖处理。空间中的半扭转图形不替代表示论证明。仅给 $SU(2)$ 表示也不决定粒子的质量、磁矩大小或磁矩中的 $g$ 因子；这些仍需 Hamiltonian、物质模型或实验输入。

## 14.3 Galilei 中心扩张与有质量粒子

采用生成元 $P_i,J_i,K_i,H$，并在共同光滑域上写
$$
[K_i,P_j]=i\hbar\delta_{ij}M,\qquad
[K_i,H]=i\hbar P_i,\qquad [P_i,H]=0,
$$
其中 $M$ 与群表示的全部生成元对易。不可约性使中心算符取标量 $M=mI$。本节明确选择 $m>0$ 的自由 massive 分支；零质量或其他奇异 Galilei 表示不由下面除以 $m$ 的推导覆盖。

定义
$$
Q_i=K_i/m,\qquad
\mathbf S=\mathbf J-\mathbf Q\times\mathbf P,
\qquad C_E=H-\frac{P^2}{2m}.
$$
第一式给轨道 CCR。由完整的 Galilei 对易关系，$\mathbf S$ 与 $\mathbf Q,\mathbf P$ 对易，并自身满足角动量代数。又
$$
[K_i,P^2/(2m)]=i\hbar P_i,
$$
所以 $C_E$ 与 boosts 对易；它也与空间平移、旋转和时间平移对易。对所声明不可约表示应用 Schur 论证，得 $C_E=E_{\rm int}I$。在正则轨道表示与有限自旋因子下，因而有
$$
\mathcal H_1=L^2(\mathbb R^3)\otimes\mathbb C^{2s+1},\qquad
H=P^2/(2m)+E_{\rm int}.
$$
这里分类标签是 $(m,s,E_{\rm int})$，不是从拓扑绕数算出的质量谱。整体粒子不可约性属于中心扩张后的对称群；Weyl 位移只作用于轨道因子，故其在含自旋的整个空间上可约并不矛盾。

中心扩张还有可直接检查的后果：boost 与空间平移的两种次序相差与 $m\mathbf v\cdot\mathbf a/\hbar$ 成比例的相位，具体正负号由指数约定决定。历史基准分别作用两条算符序列检验该相位，而不是只把同一目标式代入两次。它验证已采用的表示，不能反向决定 $m$ 或 $\hbar$ 的数值。

<!-- END ADV-14 -->

## ADV-15A

操作：replace。开始锚点：`## 15.1 不可区分性不单独选择 Bose/Fermi`。结束锚点：`## 15.2 Fock 构造`。

来源与理由：v25.2 sections permutation representations / complete invariance / NR spin-statistics countermodels; v2 section 15.1。

<!-- BEGIN ADV-15A -->

## 15.1 不可区分性不单独选择 Bose/Fermi

标号张量积是辅助表示。若可观测代数与 $S_N$ 的置换表示对易，可将载体分解为
$$
\mathcal h^{\otimes N}\simeq\bigoplus_\lambda V_\lambda\otimes M_\lambda,
\qquad U_\pi=\bigoplus_\lambda U_\lambda(\pi)\otimes I.
$$
置换不变可观测量在这些因子上具有交换代数的形式。对密度矩阵本身施加置换不变性时，Schur 论证给
$$
\rho=\bigoplus_\lambda\frac{I_{V_\lambda}}{\dim V_\lambda}\otimes\tau_\lambda,
\qquad \tau_\lambda\succeq0,\qquad\sum_\lambda\operatorname{Tr}\tau_\lambda=1.
$$
$N\ge3$ 时 $S_N$ 不只具有平凡和符号两种不可约表示。因此“交换标签不改变可观测量”不能单独排除其他表示扇区，也不能独自强迫状态只落在 Bose 或 Fermi 子空间。

标准 Bose/Fermi 选择采用额外的物理扇区条件
$$
P_\pm=\frac1{N!}\sum_{\pi\in S_N}
(\operatorname{sgn}\pi)^{(1\mp1)/2}U_\pi.
$$
群乘法与符号乘法给 $P_\pm^2=P_\pm=P_\pm^\dagger$。被采用的态支撑应明确写入其中一个子空间。历史文献还研究对所有辅助扩展的更强置换不变性、量子控制的置换等选择条件；那些定理的量词和许可操作不同于普通置换不变性，也不同于纯化仅在辅助可逆变换意义下唯一。不能把它们压成一个无需前提的“不可区分原则”。

三维非相对论理论中，自旋与统计仍是独立标签：形式上可以构造自旋 $1/2$ 的 Bose 多体扇区或自旋 $0$ 的 Fermi 多体扇区。这些是对非相对论推导能力的反例，不是自然界存在这些基本粒子的主张。相对论自旋—统计联系需要局域性、正能量、正度量及相应域条件。二维交换配置的拓扑以编织群取代普通置换群，还允许任意子；本章的三维对称化公式不能排除它们。

<!-- END ADV-15A -->

## ADV-15B

操作：replace。开始锚点：`## 15.3 超选的操作类型`。结束锚点：`<a id="ch-16"></a>`。

来源与理由：v25.2 sections algebraic SSR / Bargmann / Fock boundary; v2 section 15.3。

<!-- BEGIN ADV-15B -->

## 15.3 超选的操作类型

超选是相对于可观测代数和允许操作定义的。若 $\mathcal A$ 的中心投影给出互斥扇区，且全部允许操作不能访问其间相干，便得到该实现中的超选结构。必须区分中心 $Z(\mathcal A)$ 与交换子代数 $\mathcal A'$：一般 $\mathcal A'$ 中的投影可能只选择一个不可观测重数因子，不自动定义新的基本电荷。代数量子场论中的超选还可表现为不等价表示，不能被某个预先固定 Hilbert 空间的中心投影列表穷尽。

扩大参考系、允许操作或边界自由度可能改变操作超选。Bargmann 质量超选的推论依赖采用的 Galilei 表示与参考框架；它不说明任何涉及不同质量的形式叠加都在所有扩展理论中被禁止。Fock 构造自身也不强迫普适粒子数超选。只有在固定同一种质量 $m$ 的粒子、采用相应质量超选并使总质量为 $mN$ 等条件下，才得到与粒子数相连的结论。

有限模式 Fock 空间和无限模式场表示还需区分：有限个 canonical DOF 的 Stone–von Neumann 唯一性不能直接控制无限模 CCR 的全部表示。量子场中的真空、热态和其他相的表示问题在第 21 章另立合同。

<!-- END ADV-15B -->

## ADV-16

操作：replace。开始锚点：`## 16.3 相关、纠缠与相分类`。结束锚点：`<a id="ch-17"></a>`。

来源与理由：v26.3 sections finite vs thermodynamic / MPS / predictive certificate / QD / N=2 Fermi benchmark; v2 sections 16.3–16.4。

<!-- BEGIN ADV-16 -->

## 16.3 相关、纠缠与相分类

关联长度、谱隙、序参量、纠缠熵和拓扑指标分别回答不同问题。有限系统的能级交叉或局部涨落峰不是自动的热力学相变证明。自发对称破缺通常按
$$
\lim_{h\to0^\pm}\lim_{|\Lambda|\to\infty}
$$
选择无限体积态；交换次序可恢复对称态。有限尺寸外推因此要同时说明边界、破缺场、初态及所用观测量，不能以一张有限链曲线替代极限定理。

MPS 表示
$$
|\psi\rangle=\sum_{i_1\cdots i_L}
 v_L^\dagger A_1^{i_1}\cdots A_L^{i_L}v_R
 |i_1\cdots i_L\rangle,
$$
键维限制各切割的 Schmidt 秩。对单个切割，若归一化纯态丢弃的 Schmidt 权重为 $\delta<1$，归一化截断态与原态的保真振幅为 $\sqrt{1-\delta}$，所以纯态迹距离恰为 $\sqrt\delta$。这一单切割结论不能直接当作整条链、全部时刻的统一误差；顺次压缩、时间离散、Trotter、有限体积和初始近似仍需组合。

一维、有限局域维数、受控局域相互作用与统一谱隙等条件可支持面积律及 MPS 近似结果。近似存在、找到该近似的算法复杂度、任意高纠缠实时态能否低键维表示是三种不同命题。不能仅因某低能基态可用 MPS，就宣布一般多体动力学高效。

数值基准也应有区分力。单粒子 hopping 不涉及交换两费米子的符号；验证 Fermi 后端须使用真正多粒子 CAR 或显式反对称 Fock 基，例如固定 $N=2$ 的链，并对照独立的二次量子化构造。

## 16.4 多体对象证书

对象候选可以是局域激发、逻辑子空间、序参量有效态或空间区域。必须先冻结目标未来、初态/环境类、允许干预、持续窗和资源尺度，再声明各证书的距离与估计方法。一个可继承的登记形式为
$$
(\epsilon_{\rm pred},\epsilon_{\rm mem},\epsilon_{\rm leak},
\Pi_{\rm pers},R_\delta,C_{\rm glob}).
$$
这些分别记录指定协议中的预测误差、已选记忆模型后的剩余误差、泄漏、持续性、可访问记录冗余及全局相干等信息；没有跨平台通用的未定义数值。$\epsilon_{\rm mem}$ 衡量遗漏了多少记忆，不要求真实物理过程本身 Markov。

共同相关不证明父对象因果不可约。若从多体 Hamiltonian 推有效对象动力学，必须给投影、可达输入类和记忆控制；能带图或相关图本身不完成 Core 接口。一个响应充分的泛对象也未必是具有内部修复和资源维持能力的强 $\Omega$ 对象，后者要另加合法破坏、修复和持续性合同。

同样，环境片段的 Holevo 信息 plateau、总互信息、获得给定记录精度所需的最小片段大小和可独立访问的冗余片段数不能互相替代。强客观性需要相应的操作条件；多个片段可携带同一公共记录，而联合父系统仍保留不可由公共读出看见的全局相干。第 6–8 章与第 41 章的不识别性界在多体情形继续适用。

<!-- END ADV-16 -->

## ADV-17

操作：replace。开始锚点：`## 17.3 Davies 接口`。结束锚点：`## 17.4 量子轨迹与计算`。

来源与理由：v26.3 GKSL/Davies weak coupling / KMS / nonunique Gibbs; v2 section 17.3。

<!-- BEGIN ADV-17 -->

## 17.3 Davies 接口

GKSL 是有限维连续 CPTP 半群的结构刻画；要从一个具体浴推导该半群，必须给微观条件。设
$$
H_S=\sum_\epsilon\epsilon\Pi_\epsilon,\qquad
H_{
\rm int}=\lambda\sum_\alpha A_\alpha\otimes B_\alpha,
$$
并声明浴的平稳态、相关衰减/混合、耦合算符的条件，以及弱耦合 $\lambda\to0$、宏观时间按 $\lambda^{-2}$ 缩放的极限。有限但长的时间、耦合强度和误差范围另需估计，不能把极限生成元写成所有耦合强度下的精确方程。

定义 Bohr 频率分量
$$
A_\alpha(\omega)=
\sum_{\epsilon'-\epsilon=\hbar\omega}
\Pi_\epsilon A_\alpha\Pi_{\epsilon'},
\qquad [H_S,A_\alpha(\omega)]=-\hbar\omega A_\alpha(\omega).
$$
在相容的 Fourier 约定下，浴谱矩阵 $\gamma_{\alpha\beta}(\omega)$ 半正定，使每个频率块的耗散项
$$
\sum_{\alpha\beta}\gamma_{\alpha\beta}(\omega)
\left[A_\beta(\omega)\rho A_\alpha(\omega)^\dagger
-\tfrac12\{A_\alpha(\omega)^\dagger A_\beta(\omega),\rho\}\right]
$$
具有 GKSL 形式。热 KMS 关系为
$$
\gamma_{\alpha\beta}(-\omega)
=e^{-\beta_T\hbar\omega}\gamma_{\beta\alpha}(\omega),
\qquad \beta_T=(k_BT)^{-1}.
$$
该标准弱耦合极限中的 Lamb shift 与 $H_S$ 对易；简并或等频跃迁须整体处理，不能先任意删去同一 Bohr 块中的交叉项。

利用 $A_\alpha(\omega)\rho_T=e^{-\beta_T\hbar\omega}\rho_T A_\alpha(\omega)$ 与正负频率的热关系，可以逐块验证 Gibbs 态驻定。驻定只意味着 $\mathcal L(\rho_T)=0$；唯一性、混合速率和任意初态热化还需不可约性/遍历性等条件。额外守恒量或无噪声子空间可留下多个驻定态。

对于 gap $\Delta>0$ 的二能级系统，热 Bose 占据
$$
n_T=(e^{\beta_T\Delta}-1)^{-1}
$$
给 $\gamma_\downarrow=\kappa(n_T+1)$、$\gamma_\uparrow=\kappa n_T$，二者比值为 $e^{-\beta_T\Delta}$。这把速率连到声明的浴模型，不是把预先期望的平衡态反填进任意速率。

<!-- END ADV-17 -->

## ADV-18A

操作：replace。开始锚点：`## 18.1 为什么单时刻通道不够`。结束锚点：`## 18.2 一个完全可执行的记忆反例`。

来源与理由：v26.3 process Markov / causal-break contract; v31.2–31.3 fixed-library scope; v2 section 18.1。

<!-- BEGIN ADV-18A -->

## 18.1 为什么单时刻通道不够

CP-divisibility 要求：对 $t\ge s$，存在 CPTP $V_{t:s}$ 使 $\Lambda_t=V_{t:s}\Lambda_s$。它约束单时刻映射族；这些映射通常是在固定初始系统—环境制备下测得的。干预会改变中间的系统—环境关联，因此单时刻可分解性不能自动确定全部多时刻干预的统计。

过程张量将一串 CP interventions 映为末态或记录概率。相对于明确的输入/输出腿排序、Choi 归一化和转置约定，它由正 Choi 算符与逐级因果迹约束刻画；消去最后输出腿得到“相应输入单位算子 × 前一级 comb”。对历史依赖的 instrument，保留每个结果，最后再取所需的完整记录事件。把输出腿当输入腿或漏掉转置，会得到不同的配对，并非一个无害记号差。

**K-QMEM-01。** 在完整 instrument 协议下，操作 Markov 性要求当前因果断开之后，未来条件统计不再依赖更早的操作和结果；在相同 Choi 约定下，Markov 过程对应初态与逐段通道 Choi 的时间乘积。这是多时刻操作判据，采用其原始定理条件，不能用 CP-divisibility 替换。[原始研究](https://arxiv.org/abs/1512.00589)

“完整”是一个量词：若只准许一小类被动读出，相同数据可能掩盖环境记忆；某些扩大的主动干预才能区分历史。有限 Kraus 内核对固定时齐操作库的全部有限词与完整有限自适应树所证明的充分性，也不能自动扩展到新增的环境接入、漂移、非时齐库或未声明的过程插槽。

<!-- END ADV-18A -->

## ADV-18B

操作：replace。开始锚点：`## 18.3 记忆核和模拟选择`。结束锚点：`<a id="ch-19"></a>`。

来源与理由：v26.3 Nakajima–Zwanzig / revival and process memory; v2 section 18.3。

<!-- BEGIN ADV-18B -->

## 18.3 记忆核和模拟选择

设联合线性演化 $\dot R=\mathcal LR$，选投影超算符 $\mathcal P$ 与 $\mathcal Q=1-\mathcal P$。在算符与半群定义合法的范围内，先解
$$
\mathcal QR(t)=e^{t\mathcal Q\mathcal L}\mathcal QR(0)
+\int_0^t e^{(t-s)\mathcal Q\mathcal L}
\mathcal Q\mathcal L\mathcal PR(s)\,ds.
$$
代回 $\mathcal P$ 方程，得到 Nakajima–Zwanzig 恒等式
$$
\frac d{dt}\mathcal PR(t)=\mathcal P\mathcal L\mathcal PR(t)
+\int_0^t\mathcal P\mathcal L e^{(t-s)\mathcal Q\mathcal L}
\mathcal Q\mathcal L\mathcal PR(s)\,ds
+\mathcal P\mathcal L e^{t\mathcal Q\mathcal L}\mathcal QR(0).
$$
在具体系统投影下，它可写成
$$
\dot\rho_S(t)=\mathcal L_0\rho_S(t)
+\int_0^t\mathcal K(t-s)\rho_S(s)\,ds+\mathcal I(t).
$$
核与非齐次项依赖所选投影和初始相关，不是一个普适、唯一的“非 Markov 数值”。原始恒等式也不保证任意截断的近似核保持 CP；这必须通过可用的结构条件或真实协议概率单独检验。

系统与单个环境的激发交换给 $G(t)=\cos gt$，激发区分度 $D(t)=\cos^2gt$ 可复苏。时间局部率 $2g\tan gt$ 在映射不可逆时奇异；不能跨零点把它当普通光滑半群生成元。区分度复苏是该模型的一个证据，不能代替对全部可允许干预的过程判据。

HEOM、pseudomode、链映射与张量网络可作为模拟后端。其误差来自浴谱逼近、辅助层截断、时间积分和初态假设，须换算到共同的目标响应后再比较。过程张量提供操作比较语言，不保证永远比其他算法便宜。

<!-- END ADV-18B -->

## ADV-19

操作：replace。开始锚点：`## 19.4 驻定、平衡化与热化`。结束锚点：`## 19.5 Spohn 与物理熵产生`。

来源与理由：v26.3 diagonal ensemble / exact degeneracy / persistent fluctuations; v2 section 19.4。

<!-- BEGIN ADV-19 -->

## 19.4 驻定、平衡化与热化

有限闭系统的长时间平均保留完整的简并能量块：
$$
\overline\rho=\lim_{T\to\infty}\frac1T\int_0^T
 e^{-iHt/\hbar}\rho_0e^{iHt/\hbar}\,dt
=\sum_E P_E\rho_0P_E.
$$
在能量基底展开后，$E\ne E'$ 的平均系数为
$T^{-1}\int_0^T e^{-i(E-E')t/\hbar}dt\to0$；同一能量块中的系数恒为一。因此简并块内部的相干不能任意删除，选择一组能量本征向量并只保留其对角元会给错误结果。

时间平均存在也不意味着逐时态收敛。例如 $H=\hbar\omega Z/2$、初态 $|+x\rangle$ 时，$\langle X\rangle_t=\cos\omega t$；它的时间平均为零，但晚时振荡始终存在。有限谱还允许复现。要得到“多数晚时局域观测接近平衡”或某种均方偏差界，须增加有效维数、能隙结构、观测类和初态条件。

ETH 是针对特定非可积系统局部矩阵元结构的假设，不是所有 Hamiltonian 的定理。可积性和额外守恒量可能要求广义 Gibbs 或其他稳态描述。有限系统 Gibbs 态的变分存在性、开放热浴中的驻定、动力学平衡化及 Gibbs 热化应分别登记。

<!-- END ADV-19 -->

## ADV-21

操作：replace。开始锚点：`## 21.1 场论实现的物理输入`。结束锚点：`## 21.3 三种闭合状态`。

来源与理由：v27.1 Poincaré/field domain / Shale / Type III / split / Reeh–Schlieder / Haag; v2 21.1–21.2。

<!-- BEGIN ADV-21 -->

## 21.1 场论实现的物理输入

**H-QFT-1。** 声明闵可夫斯基背景、强连续的 Poincaré 酉实现、能动量联合谱位于前向闭光锥、局域性、正定物理态空间，以及所用真空的存在、生成性、正则性和必要的唯一性条件。相互作用模型还要给场内容、作用量、调节与重整化条件。这些是进入该场论扇区的物理和数学输入，不是一般对象闭合的后果。谱条件本身不保证真空唯一。

场 $\phi(x)$ 通常是算符值分布。对 Schwartz 测试函数等指定函数类定义
$$
\phi(f)=\int d^4x\,f(x)\phi(x),
$$
并在共同不变稠密域上讨论可闭性、乘积与矩阵元的分布性质。点处场、同点场乘积和时序乘积不能被默认当成处处有界矩阵；后两者还可能需要独立的延拓或重整化。

对有界区域 $\mathcal O$，局域可观测代数 $\mathcal A(\mathcal O)$ 满足包含单调性、协变性和类空交换性。自由 Bose 场可从有界 Weyl 算符生成局域代数；费米场具有分次局域性，物理偶可观测量满足通常的类空交换性。一个物理对象接口可记录区域、代数、限制态与允许局域 instruments：
$$
(\mathcal O,\mathcal A(\mathcal O),\omega|_{\mathcal A(\mathcal O)},\mathfrak I_{\mathcal O}).
$$
其中再附时间/能量分辨率和近似误差，不预先强迫尖锐区域拥有独立的 Hilbert 张量因子。

## 21.2 无限自由度、表示与局域代数

有限 canonical DOF 的正则不可约 CCR 表示唯一性不延伸到无限模。以 Bose Fock 表示为例，对适当的线性正则 Bogoliubov 变换，是否可在原 Fock 空间由酉算符实现，受其产生—湮灭混合部分 $\beta$ 的 Hilbert–Schmidt 条件控制：
$$
\|\beta\|_{\rm HS}^2<\infty.
$$
对独立模式的相容对角变换，$\beta_n=1/n$ 的平方和收敛，而 $\beta_n=1/\sqrt n$ 发散。这是同样逐模合法的变换在无限系统中可能具有不同实现状态的明确诊断；不是把每个模式截断后再悄悄交换无限极限。真空、热态及不同相因此可能需要不等价表示。

在通常连续相对论模型的标准条件下，区域局域代数具有 Type III 等不同于有限矩阵代数的结构。即使整个 Fock 空间上的 $\mathcal B(\mathcal H)$ 是 Type I，也不能据此把每个局域代数写为 $\mathcal B(\mathcal H_{\mathcal O})\otimes I$。尖锐区域限制态不自动有相对于普通局域迹的密度矩阵，普通约化纠缠熵也不自动有限。

因此，“迹掉区域外”必须说明其实现：可以使用格点或能量截断，也可在附加 split/nuclearity 等条件下，对有间隔的内外区域引入中间 Type I 因子。这样的 split 选择有条件且通常不唯一。一般始终可讨论代数态限制
$$
\omega\longmapsto\omega|_{\mathcal A(\mathcal O)},
$$
并在适用框架内使用相对熵或模理论量，而非宣称一个不存在的有限局域配分函数或普通局域迹。

Reeh–Schlieder 的局域循环性结论需要谱、真空与适当生成性等定理条件。循环性不允许远端自由控制：若类空两域的 $B$ 与全部局域 Kraus $K_\mu$ 交换，且 $\sum_\mu K_\mu^\dagger K_\mu=I$，则
$$
\sum_\mu K_\mu^\dagger B K_\mu=B.
$$
故非选择局域操作不改变另一域的期望；依赖具体测量结果的条件态必须同时计入概率与经典结果通信。

Haag 定理在其真空、协变性及场条件下限制了自由场与相互作用场之间天真的全局酉等价。它不证明相互作用不可能，而是要求区别有限调节模型、微扰相互作用图像与移除调节后的严格场论。Core 的响应和限制语言可以接收这些实现；有限维密度、熵、diamond 范数或矩阵算法若要延伸，仍需明确拓扑、能量约束和极限合同。

<!-- END ADV-21 -->

## ADV-23A

操作：replace。开始锚点：`**K-QSTAT-01：自旋—统计。**`。结束锚点：`## 23.2 Maxwell 约束与横向模式`。

来源与理由：v27.1 massive Dirac anticommutator and spin-statistics boundary; v2 P-QDIR-01 and K-QSTAT-01。

<!-- BEGIN ADV-23A -->

从同一模式展开还可以检验 Dirac 场的分次因果性。令
$$
D_0(x)=\Delta^+(x)-\Delta^+(-x)=i\Delta(x),
$$
并保持第 22 章的归一化与符号约定，则
$$
\{\psi_\alpha(x),\bar\psi_\beta(y)\}
=\bigl[(i\not\partial_x+m)D_0(x-y)\bigr]_{\alpha\beta}.
$$
证明是分别用 $u\bar u=\not p+m$ 与 $v\bar v=\not p-m$ 的自旋求和；$i\partial$ 在正、负频率项上产生相反的动量符号。$D_0$ 的因果支撑在取导数后仍成立，故类空分离的费米场反对易；由偶数个费米场构成的适当局域可观测量通常交换。检验有质量模型须保留 $m$ 项，不能以无质量核的数值替身宣称已验证整个 massive 接口。

**K-QSTAT-01：自旋—统计。** 在相对论局域、正能谱、正定态空间及相应真空/域等定理条件下，整数/半整数自旋分别服从 Bose/Fermi 统计。这里采用标准重定理，不声称由 Core 独立证明。它不等于第 15 章的普通不可区分性，也不能原样搬到未经检查的二维编织统计或其他超出定理域的模型。

<!-- END ADV-23A -->

## ADV-23B

操作：replace。开始锚点：`## 23.2 Maxwell 约束与横向模式`。结束锚点：`## 23.3 带电对象、Gauss 定律与边界`。

来源与理由：v27.1 Maxwell helicity / covariant-potential obstruction / physical F locality; v2 section 23.2。

<!-- BEGIN ADV-23B -->

## 23.2 Maxwell 约束与横向模式

取
$$
\mathcal L_M=-\tfrac14F_{\mu\nu}F^{\mu\nu},\qquad
F_{\mu\nu}=\partial_\mu A_\nu-\partial_\nu A_\mu,
\qquad A_\mu\sim A_\mu+\partial_\mu\alpha.
$$
$A_0$ 无独立动能，其正则共轭为零；要求约束随时间保持产生 Gauss 约束。每个非零动量上的四个势分量经过约束与规范冗余，只剩两个物理横向偏振。它们给 Maxwell 光子的 helicity $\pm1$。选择偏振向量的具体相位与局部标架是表示选择，不能把标架变化当作新增物理偏振。

在库仑规范下，横向投影为
$$
P^T_{ij}(\mathbf k)=\delta_{ij}-k_i k_j/|\mathbf k|^2.
$$
它在位置空间非局域；这不证明可观测信号超光速。物理电磁场 $F_{\mu\nu}$ 的因果代数仍需按第 21 章处理。规范势的辅助传播子、物理场强的交换子及可制备/探测的光子态不是同一个对象。

不能无条件同时坚持非平凡 $A_\mu$ 具有点局域、Lorentz 协变、严格 Maxwell 方程和正定 Hilbert 描述。标准 Maxwell 势的 no-go 结果解释了为何协变规范通常采用辅助不定度量空间，再用 subsidiary condition 或 BRST 商得到物理正态空间；另一路是在物理空间直接使用横向模式或局域规范不变场。四个 $A_\mu$ 模式都被当成正范数光子，会重复计算非物理自由度。

<!-- END ADV-23B -->

## ADV-24

操作：replace。开始锚点：`## 24.1 带调节的 $\lambda\phi^4$ 基准`。结束锚点：`## 24.2 Wick 展开与 Feynman 规则`。

来源与理由：v28.1 both witnesses: bare-renormalized field factors / counterterm vertices / perturbative scope; v2 24.1 bookkeeping repair。

<!-- BEGIN ADV-24 -->

## 24.1 带调节的 $\lambda\phi^4$ 基准

必须先固定裸参数与重整化参数的记法。裸拉氏量可写成
$$
\mathcal L_0=\tfrac12(\partial\phi_0)^2
-\tfrac12m_0^2\phi_0^2-\frac{\lambda_0}{4!}\phi_0^4.
$$
它本身不再额外加一份独立反项。若在 $d=4-\epsilon$ 的 dimensional regularization 中改用重整化场和无量纲耦合，定义
$$
\phi_0=Z_\phi^{1/2}\phi,\qquad
Z_\phi m_0^2=m^2+\delta m^2,\qquad
Z_\phi^2\lambda_0=\mu^\epsilon(\lambda+\delta\lambda),
\qquad Z_\phi=1+\delta Z_\phi.
$$
同一个裸式于是被分解为
$$
\begin{aligned}
\mathcal L={}&\tfrac12(\partial\phi)^2-\tfrac12m^2\phi^2
-\frac{\mu^\epsilon\lambda}{4!}\phi^4+\mathcal L_{\rm ct},\\
\mathcal L_{\rm ct}={}&\tfrac12\delta Z_\phi(\partial\phi)^2
-\tfrac12\delta m^2\phi^2-\frac{\mu^\epsilon\delta\lambda}{4!}\phi^4.
\end{aligned}
$$
这是一套参数重写，不是新增两组独立质量和耦合。四维极限下二点反项顶点为 $i(\delta Z_\phi p^2-\delta m^2)$，四点反项顶点为 $-i\delta\lambda$；尚未取 $\epsilon\to0$ 时四点顶点须保留 $\mu^\epsilon$。第 27 章 QED 使用 $d=4-2\epsilon_{\rm DR}$，其 pole 记法应另行换算，不能把两个 epsilon 直接混用。

经典实标量势的全局稳定性要求适当的正四次项；微扰方案中的裸/重整化参数关系与全局稳定性不是同一陈述。第 25 章的 Euclidean 硬截止质量基准使用其明确的减除方案；从不同调节得到的参数需要匹配后再比较物理量。

相互作用图像记号为
$$
U_I(t,t_0)=T\exp\left[-i\int_{t_0}^{t}H_I(s)\,ds\right].
$$
其第 $n$ 阶是时间有序积分；改成全区域积分时出现 $1/n!$。在有限调节与适当算符条件下可以先定义动力学；对四维连续理论，Dyson 级数通常按微扰阶使用。调节移除、渐近态极限和级数求和不得凭一个指数符号交换，也不能据此避开第 21 章的 Haag 边界。

<!-- END ADV-24 -->

## ADV-25

操作：insert_before。开始锚点：`<a id="ch-26"></a>`。插入于此标题之前，原标题保留。

来源与理由：v28.1 finite scheme transformations / normalized WF / independent Wilson-CS check; preserve original 25.1–25.3。

<!-- BEGIN ADV-25 -->

## 25.4 方案匹配、展开参数与独立 RG 检验

leading beta 系数的相同性有自己的合同。若两种无质量、质量无关方案只作显式尺度无关的有限重定义
$$
\lambda'=\lambda+c\lambda^2+O(\lambda^3),
$$
则链式法则给
$$
\beta_{\lambda'}=(1+2c\lambda+\cdots)\beta_\lambda
=b\lambda'^2+O(\lambda'^3)
$$
当 $\beta_\lambda=b\lambda^2+\cdots$。若 $c$ 本身依赖 $\mu/m$，显式 $\mu\partial_\mu c$ 已在同一阶增加项；这正是带质量 MOM 阈值不必等于全尺度 MS beta 的原因。物理比较应同时转换耦合、质量和外腿归一化，并固定匹配条件。

Wilson–Fisher 展开用
$$
g=\frac{\lambda}{16\pi^2},\qquad
\beta_g=-\epsilon g+3g^2+O(g^3)
$$
更直接显示圈展开参数，所以 $g_*=\epsilon/3+O(\epsilon^2)$。固定点附近还须调到临界质量面；$\beta_g'(g_*)=\epsilon+O(\epsilon^2)$ 描述这里选定的 RG 参数方向，不能脱离 UV/IR 方向解释稳定性。$\epsilon=1$ 的应用仍需高阶与重求和分析，不能把小 $\epsilon$ 证明当成无误差的三维数值。

第 26 章向 IR 的薄壳积分给
$$
\int_{\rm shell}\frac{d^4q}{(2\pi)^4q^4}=\frac{ds}{8\pi^2},
\qquad\delta\lambda=-\frac32\lambda^2\int_{\rm shell}\frac{d^4q}{(2\pi)^4q^4}.
$$
它由三通道的组合因子和独立径向积分产生。第 25.2 节减除泡图对 $\log\mu$ 的导数则从另一计算得到对应 UV 系数。在匹配的无质量方案下二者相合，方向符号相反。历史回归用独立求导/积分与阶数缩放检查这一关系；直接把一条已知 beta 公式复制到两边不构成独立验证。两系数在一阶相合也不证明完整 Wilsonian action flow 与 Callan–Symanzik 的所有非微扰数据同一。

<!-- END ADV-25 -->

## ADV-26A

操作：insert_before。开始锚点：`## 26.3 三种 RG 的类型`。插入于此标题之前，原标题保留。

来源与理由：v28.1 (1) heavy-exchange scattering, complemented by unsuffixed quadratic stability / matching boundary。

<!-- BEGIN ADV-26A -->

### 同一重尺度的散射匹配检验

二次混合中的 $\kappa$ 具有质量维数二。另一个有区分力的匹配基准采用重场交换顶点 $-g\chi\phi^2/2$，其中 $g$ 的质量维数为一；这里须声明局部稳定真空及所需的完整势，以下只计重 $\chi$ 的树级交换贡献，不把它当作完整全局稳定势的证明。

标准顶点和传播子给
$$
\mathcal M_\chi(s,t,u)=g^2\left[\frac1{M^2-s}+\frac1{M^2-t}+\frac1{M^2-u}\right].
$$
当各 $|z|/M^2\le r<1$，逐通道展开为
$$
\mathcal M_\chi=
\frac{3g^2}{M^2}+\frac{g^2(s+t+u)}{M^4}
+\frac{g^2(s^2+t^2+u^2)}{M^6}+\cdots.
$$
截到每通道 $z^n$ 后，总余项绝对值至多
$$
\frac{3g^2}{M^2}\frac{r^{n+1}}{1-r}.
$$
对质量为 $m$ 的相同外粒子，壳上有 $s+t+u=4m^2$；低维局域项和导数项须在这个运动学约束下匹配，而不是把三个独立变量任意设置。例 $M=10,g=2,m=1,s=9,t=u=-2.5$ 给交换振幅约 $0.12200482444$。这是完整树图与 EFT 级数的比较，独立于上一节仅修改二点核的 Schur 补。

把重场从低能活跃场表移除后，需要匹配 Wilson 系数并在相应理论中运行。一个完整理论的 MOM 耦合在阈值处平滑减弱，不等于已经自动完成这项 EFT 匹配，更不等于所有重场效应精确为零。

<!-- END ADV-26A -->

## ADV-26B

操作：replace。开始锚点：`## 26.3 三种 RG 的类型`。结束锚点：`<a id="ch-27"></a>`。

来源与理由：v28.1 real-time influence-functional bridge and three distinct RG domains; preserves P-QEFT-02。

<!-- BEGIN ADV-26B -->

## 26.3 三种 RG 的类型

| 变换 | 输入与输出 | 保持的内容 |
|---|---|---|
| Core 对象粗化 | 声明协议响应及其预测因子之间的映射 | 指定未来任务的响应或有界误差 |
| 量子过程粗化 | 多时 instrument 插槽、初态与记忆过程 | 允许干预下的记录概率 |
| Wilsonian RG | 带调节的作用量、场与耦合 | 低能相关函数或匹配振幅至声明精度 |

它们可以构造桥接，但定义域、陪域和应保持的数据不同。尤其固定点、谱隙、Markov 阶数、对象最小性是各自的概念，没有一般定理把它们无条件一一对应。

<a id="p-qeft-02"></a>

**P-QEFT-02：受限的实时桥。** 给定同一个系统—环境划分、初态、联合酉演化、允许插槽干预和末端读出，直接部分迹与将环境积分为 Schwinger–Keldysh influence functional 的计算，如果均精确且相应求和/积分与极限合法，则给出相同的协议概率。

**证明。** 在有限维、有限调节实现中，完整记录 $\mathbf o$ 的概率可先写成联合算符的线性配对：在同一个初态上，按时间次序插入每一步联合酉演化和相应的系统 CP 分支，最后对全部终态求迹。将矩阵元展开，演化振幅与其共轭分别形成闭时路径的两条腿；环境初态和末端迹提供相同的环境指标缩并。先缩并环境得到 influence functional，最后再求系统指标，或先组成联合算符再部分迹，只是同一有限和的不同顺序。受控的连续极限要求额外收敛与换序条件，然后才能把该等式传到极限。∎

相同响应可以再按 Core 的预测等价关系取商。若近似 influence functional、截断记忆或丢弃某些干预，须给相应概率误差，不能继续使用精确相等。Euclidean 快模式积分自身不是一般 CPTP 时间演化；初始相关、外部算符插入、规范约束和非局域记忆都可能使天真的通道解释失败。共享一种“粗化”直觉不替代这些物理接口。

<!-- END ADV-26B -->

## ADV-27

操作：replace。开始锚点：`## 27.3 一圈 UV 闭合基准`。结束锚点：`<a id="ch-28"></a>`。

来源与理由：v29.2 self-energy UV / direct-vs-multiplicative mass / independent vertex UV contraction / photon pole; v2 27.3。

<!-- BEGIN ADV-27 -->

## 27.3 一圈 UV 闭合基准

这里冻结 Feynman 规范、一个单位电荷 Dirac 费米子及 MS-bar 的一圈 UV pole 记法：
$$
a=\frac{\alpha}{4\pi\bar\epsilon},\qquad
\frac1{\bar\epsilon}=\frac1{\epsilon_{\rm DR}}-\gamma_E+\log4\pi.
$$
目标是独立计算反项的一致性，不是给任意规范下的全部有限自能和顶点。

费米自能分子先用
$\gamma_\mu\gamma_\alpha\gamma^\mu=(2-d)\gamma_\alpha$
化简；Feynman 参数平移后，UV 系数积分为
$$
\Sigma_{\rm UV}(p)=a\int_0^1(-2x\not p+4m)dx
=a(-\not p+4m).
$$
若逆传播子约定为
$$
\Gamma^{(2)}=\not p-m+\delta Z_2\not p
-\delta m_{\rm direct}\,m-\Sigma_{\rm loop},
$$
则分别消掉 $\not p$ 与 $m$ 的 UV 残差给
$$
\delta Z_2=-a,\qquad\delta m_{\rm direct}=-4a.
$$
乘法质量重整化 $m_0=Z_m m$ 满足
$$
1+\delta m_{\rm direct}=Z_2Z_m,
\qquad\delta Z_m=\delta m_{\rm direct}-\delta Z_2=-3a.
$$
所以 direct mass coefficient 与 $Z_m-1$ 并不相同；把它们混用会制造并不存在的 Ward 冲突。

顶点的 logarithmic UV 部分还有一条独立检查。对称 loop-momentum 张量积分给度规缩并，在 pole 的四维留数上
$$
\frac14\gamma_\alpha\gamma_\rho\gamma^\mu
\gamma^\rho\gamma^\alpha=\gamma^\mu.
$$
两次使用四维的 $\gamma_\rho\gamma^\mu\gamma^\rho=-2\gamma^\mu$ 即得此式。$d-4$ 的差别可影响有限部分，不能用该四维留数替代完整维数依赖顶点。它给出一圈 UV 顶点修正 $\Lambda^\mu_{\rm UV}=a\gamma^\mu$，故 $\delta Z_1=-a$。与从自能独立得到的 $\delta Z_2$ 相比，确认此规范、此阶的 $\delta Z_1=\delta Z_2$。

光子 UV 系数来自
$$
\frac{2\alpha}{\pi\bar\epsilon}\int_0^1x(1-x)dx
=\frac{\alpha}{3\pi\bar\epsilon},
$$
因此 $\delta Z_3=-\alpha/(3\pi\bar\epsilon)$。再由完整 Ward 关系 $Z_e=Z_3^{-1/2}$ 得对应 charge pole。历史回归分别积分自能系数、缩并顶点 Dirac 张量和检查 photon 系数，不能把“先设 $Z_1=Z_2$ 再比较”当成独立圈图计算。

以上不覆盖任意 $\xi$ 的全部 finite parts、壳上 $Z_2$ 的红外结构或多圈精密 QED。树级 Ward、此处一圈 UV checkpoint 与第 27.2 节采用的完整 Ward–Takahashi 定理是三种证据，必须分别登记。

<!-- END ADV-27 -->

## ADV-28

操作：insert_before。开始锚点：`**K-QQED-01。** 标准一圈顶点积分经 Feynman 参数与 Pauli 投影给出有限积分`。插入于此标题之前，原标题保留。

来源与理由：v29.2 one-loop vertex integral to simplex, explicit reduced-calculation evidence boundary; v2 K-QQED-01 retained。

<!-- BEGIN ADV-28 -->

这里的标准一圈来源是在外腿壳上、以 $-ie$ 从完整顶点提出之后，按固定动量流向写出的修正积分，例如
$$
\Lambda^\mu(p',p)=-ie^2\int\frac{d^d\ell}{(2\pi)^d}
\frac{\gamma_\rho(\not p'-\not\ell+m)\gamma^\mu
(\not p-\not\ell+m)\gamma^\rho}
{[\ell^2+i0][(p'-\ell)^2-m^2+i0][(p-\ell)^2-m^2+i0]}.
$$
dimensional regularization 中还须保留相应的 $\mu^{2\epsilon_{\rm DR}}$，需要时先引入相容的红外处理。Feynman 参数化、loop shift、Gordon 分解和 Pauli 结构投影把 $q^2\to0$ 的有限 $F_2$ 部分化为下式。这个解析 reduction 是标准 QED 输入；后面的二维数值积分不等于机器重新证明了这里的全部换序、正则化和极限。

<!-- END ADV-28 -->

## ADV-31

操作：insert_before。开始锚点：`<a id="ch-32"></a>`。插入于此标题之前，原标题保留。

来源与理由：v31.3 Selector/Spectrum actual source; G3 selector refinement and physical adapter; v2 chapter 31。

<!-- BEGIN ADV-31 -->

## 31.6 与已验证内核的准确对应及永久反模型

第 31.3 节条件选择器的整数内容已在有限 UEOT-QM 内核中实现为 `Selector.selects_three_without_atomicity`。其输入明确包括自然数 $N_c,N_f,k$、$N_c\ge3$、$N_f>0$、$k\le N_f$、给定立方方程及严格弱预算。它没有从一般 Core 产生这些物理前提。

`Spectrum.spectrum_selects_three` 进一步从有限谱行求和接到该选择器。接口要求轻子朝向同质、非零异常单位、每行普通轻子与夸克双重态在同一弱窗口活跃、非负额外 screening、完整弱系数为正；未列普通行之外的异常补偿总和也须单独等于零。这些都是有实质内容的合同。它没有构造 $SU(3)_L$ 的量子场、证明额外补偿机制有效，或在改变阈值后继续使用原窗口。

例如放宽同质轻子模板，令 $l$ 代轻子取 $R$、其余取 $\bar R$，则立方式变为
$$
(2l-N_f)+N_c(2k-N_f)=0.
$$
$(N_c,N_f,l,k)=(3,2,1,1)$ 使其为零，并有 $N_f(N_c+1)=8<22$。这是对“谱朝向无关紧要”的具体反例。内核验证了相应的行计数与弱系数；在另行声明的一般化 331 电荷表、$\beta_8=0$ 等条件下，Python 精确算术还核对了六项局域异常。后者不因此成为 Lean 的完整六异常定理，也不构成已可行的全部粒子模型。

同样，额外二十个复 Higgs 双重态可把三代普通点的弱系数压到零；所以普通必要预算通过不保证加入任意标量后的完整系数仍为正。若允许额外立方补偿抵消普通行的非零异常，单代等其他点也可能进入更宽模型类。相反例与正例应永久一起保存，防止把物理前提在摘要中删掉。

第 31.4–31.5 节的完整六局域异常求和、第 32 章 framing/指标路线，以及第 36 章正确高能规范群上的分类，是不同的数学对象，仍按各自纸面证明和精确回归登记。一个形式化定理数量不能代替这些具体覆盖关系。

<!-- END ADV-31 -->

## ADV-37

操作：insert_before。开始锚点：`<a id="ch-38"></a>`。插入于此标题之前，原标题保留。

来源与理由：v31.0 flavor adapter and permanent equal-diagonal counterexample; v2 chapter 37。

<!-- BEGIN ADV-37 -->

## 37.6 轻子普适性必须是完整矩阵条件

若某个重中性矢量在三代普通轻子上确实具有相同表示耦合，且忽略 exotic 混合后保持酉的轻子质量旋转，那么弱基底耦合应为
$$
G_\ell=g_\ell I.
$$
对任意质量基底旋转 $U$，$U^\dagger G_\ell U=g_\ell I$，于是该项没有由这种旋转产生的树级味改变中性流。这是一项可用的候选区分条件，不是所有 HGP、flipped 331 或含显著重轻混合模型的结论。

检查各对角元相同还不够。以两维子块为例，取 $G=\operatorname{diag}(g_1,g_2)$，用
$$
U=\frac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}
$$
旋转后得到
$$
U^\dagger GU=
\begin{pmatrix}
(g_1+g_2)/2&(g_1-g_2)/2\\
(g_1-g_2)/2&(g_1+g_2)/2
\end{pmatrix}.
$$
两个对角元相等，但只要 $g_1\ne g_2$，非对角耦合仍存在。三维中嵌入这个子块即可得到同类反例。因此“普适”应检验整个矩阵是标量单位阵，或检验其谱与所有相关矩阵元，不能只对角拟合后宣称味改变消失。低能过程的 running、算符混合与其他介子/重矢量贡献仍按第 37.5 节的合同处理。

<!-- END ADV-37 -->

## ADV-40A

操作：replace。开始锚点：`## 40.2 一个规范保持、无条件线性的随机候选`。结束锚点：`有限维取 Hermitian $A$、$\gamma>0$，采用 Itō 方程`。

来源与理由：v2 title terminology: norm-preserving, not a new gauge theorem。

<!-- BEGIN ADV-40A -->

## 40.2 一个范数保持、无条件线性的随机候选

<!-- END ADV-40A -->

## ADV-40B

操作：insert_before。开始锚点：`## 40.4 一个可计算的有限时间闭合率`。插入于此标题之前，原标题保留。

来源与理由：v2 C-03 bounded multiplicative SDE; explicit finite-time vs asymptotic scope。

<!-- BEGIN ADV-40B -->

这里“谱分支吸收”是 $t\to\infty$ 的几乎处处极限，不是有限时刻精确投影。事实上对 $p_a(0)>0$，令 $b_a(t)=2\sqrt\gamma[a-\bar a_t]$，则
$$
p_a(t)=p_a(0)\exp\left[
\int_0^t b_a(s)dW_s-\frac12\int_0^t b_a(s)^2ds\right]>0
$$
在每个有限时间几乎处处成立，因为有限谱使 $b_a$ 有界。零初权重保持零，而多个非零初权重通常只在无限时极限分离。有限实验需要下面的误差或置信界，不能把 C-03 的渐近陈述读成精确有限时坍缩。

<!-- END ADV-40B -->

## ADV-40C

操作：replace。开始锚点：`## 40.4 一个可计算的有限时间闭合率`。结束锚点：`## 40.5 新物理候选必须同时支付能量代价`。

来源与理由：v2 C-04 exact proof preserved; degeneracy indices and simulation-vs-innovation Brownian clarified。

<!-- BEGIN ADV-40C -->

## 40.4 一个可计算的有限时间闭合率

<a id="c-04"></a>

**C-04：成对不确定性衰减。** 继续采用第 40.3 节的有限谱与 $[H,A]=0$ 条件，则
$$
\mathbb E\sqrt{p_a(t)p_b(t)}
=\sqrt{p_a(0)p_b(0)}
 e^{-\frac\gamma2(a-b)^2t}.
\tag{40.9}
$$
因而
$$
\mathbb E[1-\max_a p_a(t)]
\le\sum_{a<b}\sqrt{p_a(0)p_b(0)}
 e^{-\frac\gamma2(a-b)^2t}.
\tag{40.10}
$$

**证明。** 对 $q_{ab}=\sqrt{p_ap_b}$ 使用 (40.5) 与 Itō 公式。两种乘法噪声的差为 $2\sqrt\gamma(a-b)$，由二阶项得到漂移
$-\frac\gamma2(a-b)^2q_{ab}$；有界随机积分均值为零。于是其均值解一阶线性方程，得到 (40.9)。正初概率在有限时间保持正；零初概率恒为零，边界可分别处理。对任意概率向量，把最大项记为 $p_{\max}$，与该项组成的成对最小值已给 $1-p_{\max}$，故
$$
1-p_{\max}\le\sum_{a<b}\min(p_a,p_b)
\le\sum_{a<b}\sqrt{p_ap_b}.
$$
取均值得 (40.10)。∎

若 $A$ 有简并，选共同本征基 $|a,\alpha\rangle$，使
$$
A|a,\alpha\rangle=a|a,\alpha\rangle,
\qquad H|a,\alpha\rangle=E_{a\alpha}|a,\alpha\rangle.
$$
无条件主方程相应给
$$
\bar\rho_{a\alpha,b\beta}(t)=
 e^{-i(E_{a\alpha}-E_{b\beta})t/\hbar}
 e^{-\frac\gamma2(a-b)^2t}
\bar\rho_{a\alpha,b\beta}(0).
$$
一个 A 的谱标签不必指定唯一 H 能量；同一谱子空间中的相干可以继续酉演化。模型关联的是不同谱分支的确定化与非选择相干损失速率，不能据此宣布简并子空间内也已经选出唯一纯态。

可用无需 Euler 时间步的精确过滤表示模拟这些权重。先按 $p_a(0)$ 抽取标签 $A_*$，在该模拟空间取独立标准 Brownian 过程 $B_t$，生成
$$
Y_t=2\sqrt\gamma\,a_{A_*}t+B_t,
$$
并用 Bayes 公式给
$$
p_a(t)=
\frac{p_a(0)e^{2\sqrt\gamma aY_t-2\gamma a^2t}}
{\sum_b p_b(0)e^{2\sqrt\gamma bY_t-2\gamma b^2t}}.
\tag{40.11}
$$
在由观察记录生成的过滤中，创新过程
$$
W_t=Y_t-2\sqrt\gamma\int_0^t\bar a_s\,ds
$$
是物理混合测度下的 Wiener 过程，权重满足 (40.5)。这里的 $B_t$ 与创新 $W_t$ 承担不同角色；抽标签只是同一过滤律的模拟表示，不是以“预先选结果”替代 C-03 的动力学吸收证明。

<!-- END ADV-40C -->

## ADV-40D

操作：replace。开始锚点：`## 40.5 新物理候选必须同时支付能量代价`。结束锚点：`## 40.6 记录依赖可以合法加入，但须放在物理系统里`。

来源与理由：v2 40.5 preserved energy relations; fix 5.3→40.3; v24.4 / v31.2 finite-CCR boundary。

<!-- BEGIN ADV-40D -->

## 40.5 新物理候选必须同时支付能量代价

由 (40.4) 及合法的迹循环，额外噪声对能量的贡献为
$$
\frac{d\langle H\rangle}{dt}\bigg|_{\rm noise}
=-\frac\gamma2\langle[A,[A,H]]\rangle.
\tag{40.12}
$$
这条恒等式本身不要求 $[H,A]=0$。若在一维非相对论延拓中取 $A=X$、$H=P^2/(2m)+V(X)$，则要另行给无界算符的共同域、状态能量条件及交换迹与生成元的正当性。在这些条件下
$$
[X,[X,H]]=-\hbar^2/m,
\qquad\frac{d\langle H\rangle}{dt}=\frac{\gamma\hbar^2}{2m}.
\tag{40.13}
$$
位置表象的两个点相距 $d\ne0$，该附加双交换耗散的相干衰减率为 $\Gamma(d)=\gamma d^2/2$，故
$$
\boxed{\frac{d\langle H\rangle}{dt}
=\frac{\hbar^2}{md^2}\Gamma(d).}
\tag{40.14}
$$
这是同一个线性位置噪声模型的双观测约束；不是所有 CSL、耗散或有色噪声模型的普适加热公式。这里没有使用第 **40.3** 节的 $[H,A]=0$：自由粒子位置噪声可以持续加热，不能同时被描述成固定位置本征态的永久吸收。有限矩阵的精确全域 CCR 不成立，所以数值位置截断也不能未经误差分析直接继承 (40.13)。

若独立实验给附加加热上界 $\dot E_{\max}$，该具体模型必须满足 $\gamma\le2m\dot E_{\max}/\hbar^2$，并限制相应的额外干涉衰减。若一个记录触发模型拟合了更大衰减却没有匹配能量效应，它必须明确改变 $A$、噪声谱或耗散结构，随后接受新模型的检验；不能把同一噪声参数的另一个后果从合同中删去。

<!-- END ADV-40D -->

## ADV-40E

操作：replace。开始锚点：`## 40.6 记录依赖可以合法加入，但须放在物理系统里`。结束锚点：`<a id="ch-41"></a>`。

来源与理由：v2 40.6 physical register / nonlinearity boundary; correct typography and coherent-record scope。

<!-- BEGIN ADV-40E -->

## 40.6 记录依赖可以合法加入，但须放在物理系统里

若记录 $R$ 是真实的局部寄存器，有固定投影 $Q_r$，可以在联合空间定义
$$
L_r=\sqrt{\gamma_r}\,A\otimes Q_r,\qquad\gamma_r\ge0,
$$
并采用标准 Lindblad 方程。对已经经典条件化到记录值 $r$ 的分支，系统获得相应速率；在全部记录结果上平均，整体演化仍是线性 CPTP。

这里 $\gamma_r$ 是固定模型参数，$Q_r$ 是可实施物理变量；若寄存器尚处于相干叠加，就应继续用联合模型计算，而不是先把记录强行当经典标签。它不等价于把分析者根据未观测全局态算出的熵、冗余或“对象程度”任意代入一个非线性单系统速率。

怎样从资源、自维持、实际可访问记录和目的任务中独立选出 $A,Q_r,\gamma_r$，仍是新增物理桥的责任。允许记录反馈的标准量子模型、基本随机场候选以及某个设备的校准控制是不同实现；它们需要共同响应和可区分的实验条件才能比较。

<!-- END ADV-40E -->

## ADV-42A

操作：replace。开始锚点：`## 42.2 本组前沿推导独立检验`。结束锚点：`## 42.3 对“新物理”和旧问题的明确回答`。

来源与理由：v2 verification suites; v31.3 actual kernel CI and audit distinction; current book rerun evidence attached by root。

<!-- BEGIN ADV-42A -->

## 42.2 本组前沿推导的独立检验与形式化边界

附录保留从头编写的数值/有理数验证程序、冻结输入和结果。主要比较相互独立的表达：

- 从全左手表示表求六种异常，再与解析因式比较；
- 对有限整数域穷举，与正文的全整数分类证明对照；
- 由酉质量旋转直接构造矩阵，检验秩一和式、CKM 共轭关系和 FCNC 下界；
- 从复 Lindblad 向量构造生成元，再独立计算三角正性及 Poisson 饱和；
- 直接构造 Kraus、环境扩张、四维 $W$ 及实际统计效应；
- 检查锐见证的饱和点、随机相位、混合与校准距离界；
- 通过同一联合纯态的两种远端测量复核分解依赖反例；
- 用精确 QND 过滤采样检查鞅均值、成对衰减和有限时吸收误差上界。

历史保存结果与本版重新运行分别登记，以程序 SHA、输入、运行环境和实际退出状态绑定；不能用旧 JSON 的成功标记替代本次执行。整数/有理数等式、有限维浮点残差和 Monte Carlo 覆盖也属于不同证据。

这些高级前沿的全称数学结论依靠正文的解析论证及所引用外部定理，抽样或有限搜索不替代它们。有限 Kraus 内核已经采用 Lean，并有独立 build、公理审计、实例正反控与远端 CI 回执；但不能把这项进展表述成 G-01、F-03、M-04、Itō 吸收、Berry/SSH 或历史依赖统计等全部高级命题都已形式化。具体有源码映射的选择器和谱行合同按第 31.6 节与形式化登记处理。

目前这些程序提供模型回归和算术复核，不是新硬件数据。实际设备必须执行预注册的物理和统计合同；模拟通过不构成经典噪声、基本坍缩、五色或新粒子模型的经验确认。

<!-- END ADV-42A -->

## ADV-42B

操作：replace。开始锚点：`本组前沿推导直接使用原始三份附件的研究定位、上一完整量子主文及其中 SRN、HGP、QFT 接口；相关历史检索未成功取得更多完整对话，因此没有声称重读全部旧对话。外部技术依赖只引用原始研究或作者材料。`。结束锚点：`- 331表示、跨代异常、FCNC：`。

来源与理由：replace obsolete source-acquisition narrative with actual book-maintenance provenance; preserve source/prior-art bullets。

<!-- BEGIN ADV-42B -->

本组前沿推导继承原始研究定位、既有完整量子主文与综合 v2 总著，以及其中的 SRN、HGP、QFT 接口。本次维护还核对了可读的 v23–v30.11 历史文本、两份互补 v28.1 来源、正式 Core–Physics 合同及 v31 系列内核报告。材料身份和实际取得范围见附录 C；缓存可读文本、完整原件和已运行验证分别标识，不把其中一种冒充另一种，也不声称掌握未取得的全部历史对话。外部技术依赖保留其原始研究或作者材料的来源。

<!-- END ADV-42B -->

## 原样保留的主要命题

第 29–30 章的异常解、Higgs、Yukawa 计数与 seesaw；第 31–32 章原有 P-QG3/P-QFR 指标链与退役表；第 36 章 G-01/G-02 及全部五色计算；第 37 章 F-01–03；第 38 章 M-01/M-02 及 Poisson 反例；第 39 章 M-03–05、E-01/E-02；第 40 章 C-01–03 的完整证明（仅修范数术语并追加有限时边界），C-04 已给完整等价重写；第 41 章 C-05；第 43–46 章全局环谱、Berry/SSH、有限格点与 P-UST-01/02，均保留数学思想和原命题 ID。
