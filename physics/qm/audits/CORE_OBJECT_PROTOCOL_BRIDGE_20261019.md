# UEOT Core → UEOT-QM：理论桥接审计与可执行合同

审计日期：2026-10-19。范围：完整逐段阅读附件 Core v3 3983 行、开放端口矩阵 346 行、科学闭合纲领 210 行、Roadmap v2 198 行；并核对已抽取的原始 PDF §4.2.1–4.2.2 文本。本文是规划分析，不是新增 Lean 通过记录；不修改冻结 Core、106 计数或四生成器。

## 1. 正确的依赖方向

Core §0、§28.7 明确排除量子专属公理。因而合法目标是把已有 QM 结果接成 `Quantum model / reconstruction premises → operational record process → Core object / transport / realization / control certificates`。如果要反向重构 QM，必须另列量子重构的额外前提与独立性；Core 定理不能替代这些前提。

Core 的规范对象不是某个绝对本体标签，而是固定声明未来、协议族、历史支撑与参考律下的嵌入预测因子。§4.1–4.2 的精确公式是

$$
C_{\mathcal I}(h)=(K_i(h,\cdot))_{i\in\mathcal I},\qquad
K_i(H,\cdot)=L_i(S,\cdot)\;\mu\text{-a.s.}
\Rightarrow C_{\mathcal I}=\varphi(S)\;\mu\text{-a.s.}
$$

这里 $\mathcal I$ 有限/可数并采用共同版本。它不证明有限维记忆存在、不证明量子 Hilbert 空间存在、不保证唯一物理载体。不可数协议需共同点态结构核或稠密协议与共同连续性，不能把逐个 a.s. 改成同时 a.s.。

## 2. 已有通用成果可合法提供什么

| Core 入口 | QM 中可复用的严格内容 | 仍需量子/领域前提 |
|---|---|---|
| P-PRED-01/02/03，§4 | 协议响应最小因子、协议细化、在续接封闭及正概率分支上的递归更新 | 实验 instrument 的物理语义、量子状态/过程到记录的表示；一般可测更新另证 |
| P-DYN-01–04，§7 | 受控闭合、同协议路径误差、跨尺度 intertwining | 量子 instrument 在所选商纤维上相容；Markov 性不是自动属性 |
| P-OMG、P-CAR、P-RES，§12–14 | 固定失败族的裕量、有限向上充分族与 blocker、访问分辨率 | 物理擦除/恢复/量子可解码性；no-cloning 与量子纠错约束不由集合论输出 |
| P-COMP，§15 | 父层自己的未来、声明切割的干预差异、额外预测信息 | 纠缠/非局域性/物理张量分解须独立定义，经典相关不是纠缠 |
| P-STAT/P-INV，§16–17 | 真实记录的有限抽样、相同误差事件复用、实验等价类与识别边界 | SPAM、漂移、后选择、ancilla 可用性、协议覆盖 |
| P-QUO、P-CTL，§18–20 | 有目标、动作、奖励、合法策略和闭合后，价值/策略运输 | 自然动力学和指定实验控制目标之间的 faithfulness；自然 Hamiltonian 不自动是 GOD |
| P-GOA/P-QSD，§10、21 | 指定长期集合、占据、不变、条件生存之分型 | 幺正 不产生一般吸引性；CP/Lindblad 谱/不可约条件须独立给出 |
| P-KL，§22 | 正概率记录路径的 KL、事件下界与可实施性边界 | 振幅不是正概率；KL 不是 $iS/\hbar$；热力学功需单位和模型桥 |
| P-DDH，§23 | 目标分解 gauge、已给共同 latent 的必要秩条件、带误差的维数拒绝 | Π/Φ 独立机制锚；两驱动不是复数振幅的实虚部 |
| P-API-01，§28.3 | $C_\# P_A^{Ju}=P_B^u$，接口复合及 TV 缺损加和 | 真实协议 lift、读出、初态、时域，不能靠同名 RG 代替 |

四生成器是注册推导系统中的商下降 M-QD、有限定量运输 M-TC、正特征结构 M-PE、占据不变闭合 M-OI。所给 2026-10-07 纲领记录 `11 generated + 89 retained_adapter + 6 retained_boundary = 106`。这并非所有 106 个结果从四公理无额外数学导出，更不是四条物理定律。固定基线 `195ebb06fb8afcc592c69671dabfd2250e9d1989` 的实际状态与声明见 [Lean 证据审计](CORE_LEAN_TO_QM_AUDIT_20261019.md)。

## 3. 必须隔离的七类旧推论

### 3.1 Ω 不等于物理闭曲线或非平凡同调

Core §12.2 先冻结证书和时域，$\chi_{O,T}(D)=1$ 表示删除后仍通过证书。若失败单调，$\Omega_T=(\mathcal M,\min\{D:\chi(D)=0\})$。§9.4 明示可缩空间上的 $\dot x=-x$ 也有稳定结构、中性旋转不严格收缩也能持续。

**资料纠错：** 附件科学闭合纲领 §3.4 用文字把 χ 描述为“删除后失败”，与冻结 Core 的 1=通过相反。新增 QM 文档应采用 Core 原约定，或显式定义 `fail = 1 - χ`，不能复制此符号反转。

### 3.2 Fisher/CR 与量子不确定性有独立桥

原 PDF §4.2.1（30–31/43）从信息有限直接跳到 $\Delta x\Delta p\ge\hbar/2$。CR 约束指定统计模型和估计量的估计方差；Robertson 约束指定量子态和算子的内禀方差。由一个到另一个需要显式位置分布、动量作用、波函数正则性/定义域及 Fisher–动量方差恒等式或界。两者不是同一变量换名。

### 3.3 圈绕数不能独自产生 CCR

$\oint d\theta=2\pi n$ 只约束一个已给 U(1) 相位映射的 winding。将相位识别成 $S/\hbar$、定义量子平移表示、给出算子与公共定义域，是独立义务。有限维负对照尤其明确：

$$
\operatorname{Tr}[Q,P]=0,\qquad
\operatorname{Tr}(i\hbar I_d)=i\hbar d\ne0
$$

所以 $d>0,\hbar\ne0$ 的有限矩阵不能精确满足 canonical CCR。有限截断的模拟通过不能升级为完整 CCR 形式化。

### 3.4 正主特征向量平方不证明普适 Born

Core §10.2 的 Doob 占据是 $\varpi_i=q_i h_i$；对称特例才成为 $u_i^2$。§30.6 的纯经典 killed Brownian 例已经给 $q(x)\propto\sin(\pi x/L)$、$\varpi(x)\propto\sin^2(\pi x/L)$。这说明“出现平方”可由经典条件过程产生，尚无任意复振幅、相位干涉或所有测量的 Born 法则。

### 3.5 GOD 与最小作用不是自动等同

Core §18 N-TEL-01 用同对象两个相反目标证明目的不由对象唯一给定。§19.5 定义 $\mathcal A^*(x)=\arg\max_a Q^*(x,a)$，仅在附加漂移结构下变成方向族。Hamiltonian 方程/Schrödinger 流并非耗散最陡下降；稳定轨道不是最大化一个事后定义目标的机制证据。

### 3.6 GOA 不等于唯一基态或终极吸引点

Core §21 分别定义 $\omega$-limit、Cesàro 占据、不变律、多复归类、QSD 等。封闭量子幺正演化保持 trace distance，因此一般不能把两不同初态吸引到同一态。有限 Hamiltonian 的时间平均可给谱分块退相干，但逐时态一般振荡。实时间、虚时间、条件后选择和耗散 Lindblad 是不同机制。

### 3.7 维数、群和世代数需独立选择机制

Π/Φ gauge 是 $\Pi'=\Pi+\lambda\chi,\Phi'=\Phi+\chi$；不是量子 ray 的 U(1) gauge，也不是 Yang–Mills local gauge。共同二维响应只给同一预算点跨环境堆叠秩≤2，不推出 complex field、规范群或三代。原 PDF §4.2.2（32–33/43）的 `Index(D)=β₁=3` 不是通用指标定理；指标依赖具体流形、丛、算子、边界与特征类。固定 anomaly-free multiplet 的任意整数复制也保持局域 anomaly 相消；由相消到唯一三代必须新增并独立验证排除其它数目的机制。

## 4. Bridge B0：有限量子 instrument → Core 记录过程

**输入类型：** 给定有限维复 Hilbert 空间、正迹一 $\rho$、有限动作族，每动作的 CP trace-nonincreasing maps $\mathcal I^a_y$，且 $\sum_y\mathcal I^a_y$ trace-preserving；时间顺序与 causal policy 明确。所有这些是已有 QM 结果或明确额外前提，不能装作由 Core 推出。

对确定 causal policy（随机策略再并入动作记录），定义

$$
p_\rho^\pi(y_{1:T})=
\operatorname{Tr}\bigl(\mathcal I^{a_{T-1}(y_{<T})}_{y_T}\circ\cdots\circ
\mathcal I^{a_0}_{y_1}(\rho)\bigr).
$$

**证明义务：** 每路径非负；叶质量总和=1；允许续接下柱集一致；动作只读取已发生记录；分支更新 $\rho' =\mathcal I^a_y(\rho)/\operatorname{Tr}\mathcal I^a_y(\rho)$ 只在正分母上认证。零概率观察输出模型冲突/未认证扩展，不把它当实证后验。

**输出：** Core 的实际记录历史、概率核、protocol family，以及 `record law = quantum trace law` 的有前提 theorem。它不构造全部不相容测量结果的共同非情景 hidden-variable 分布，只构造每次实际可实施协议的记录。

**内存边界：** 初版对给定 Markov instrument 模型证明。系统–环境有记忆时，须增广真实 joint state 或用 process tensor/comb，再从合法 testers 输出记录律。单时刻 reduced $\rho_S$ 相同不保证未来所有干预响应相同。不得把 CPTP-divisibility 当作全多时刻操作 Markov 性。

## 5. Bridge B1：可观测子空间闭包 → 协议预测商

这是可以优先实现的有限数学切片；它需要先与已有 QM 版本去重。它复用成熟 quantum model reduction 方向，不宣称新原创。

设 $\mathsf H_d$ 为 Hermitian 矩阵的实向量空间，维数 $d^2$。从

$$
W_0=\operatorname{span}_{\mathbb R}\{I\},\qquad
W_{n+1}=\operatorname{span}_{\mathbb R}
\left(W_n\cup\bigcup_{a,y}(\mathcal I_y^a)^*(W_n)\right)
$$

出发。每个严格细化增加维数，故最多 $d^2-1$ 次严格增长后稳定为 $W_*$。如果保留额外终端 observables，将它们加入 $W_0$。固定有限全局动作字母表；若动作约束依协议状态变化，将该协议状态一同保留。

定义

$$
\rho\sim_{W_*}\sigma
\iff\operatorname{Tr}[(\rho-\sigma)E]=0\quad\forall E\in W_*.
$$

**精确结论与证明路线：** 每条 finite word 的概率是某个 Heisenberg effect 对初态的 pairing；递归 closure 包含所有这样的 effects。于是等价状态给所有 words、因果树同样的记录律。反向，所有 word 概率相同则对其线性 span 相同。因为 $I\in W_*$ 且 $(\mathcal I^a_y)^*W_*\subset W_*$，同等价类的分支概率相同；分母>0 时归一化后的分支仍等价。由 Core P-PRED-01 与 P-PRED-03 对接规范最小性及递归。

**可执行输出：** 一组 exact basis、每个 instrument adjoint 的闭包矩阵、商坐标、协议反例 witness、闭包残差（近似版才需要）。若全部密度矩阵允许，扣除迹常数后最多 $\dim W_*-1$ 个实坐标；限制 reachable preparations 时，应再按可达差分空间计算 rank，不能从全空间维数虚报最小记忆。

**正负基准：** 仅 Z-projective instrument 时 $W_*=span\{I,Z\}$，$|+\rangle,|-\rangle$ 对全部 Z 记录等价；增加 H-unitary 动作后 Z 读出区分二者。若只增加实矩阵操作，可能得到 $span\{I,X,Z\}$；再加允许的相位操作可揭示 Y。由此分别验证协议细化与漏掉可用控制的失败。

**物理实现限制：** 最小线性响应商不自动是更小 Hilbert 空间的全部 density state，也不自动有 CP realization。后者须 operator-algebra/conditional-expectation 等独立条件。将其命名为“预测坐标”而非未证明的“最小物理量子系统”。

## 6. Bridge B2：误差从量子层运输到真实记录

先固定 norm conventions：$d_{tr}(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1$、$d_\diamond(\mathcal E,\mathcal F)=\tfrac12\|\mathcal E-\mathcal F\|_\diamond$。

任一合法完整 measurement channel $\mathcal M$ 应证明

$$
D_{TV}(\mathcal M\rho,\mathcal M\sigma)\le d_{tr}(\rho,\sigma).
$$

受限协议一般只给不等式；等号需要该协议族能实施 Helstrom optimal measurement。对于相同 adaptive 策略、相同初态、按时间替换通道并允许所声明 ancilla 的模型，hybrid argument 给

$$
D_{TV}(P^\pi,\widehat P^\pi)\le
\min\{1,\epsilon_{init}+\textstyle\sum_t\delta_t\}.
$$

通道 diamond 缺陷不能直接套出 Core 更强的 $1-\prod_t(1-\epsilon_t)$；后者需另证在相同已发生经典记录上的条件核 TV 界。非 Markov memory model 要 tester/strategy norm 或 joint state 比较，一时刻 channel norm 不足。

后选择单独登记成功率。全记录界不能无损变成条件存活/筛选记录界；若成功概率有共同下界 $p_{min}>0$，可使用保守 $2\epsilon/p_{min}$ 条件化界（并 cap 1），同时保留未筛选失败记录。没有成功率下界就不宣称 uniform conditional guarantee。

统计端沿用 Core §16 的 `model defect / sampling uncertainty / implementation / drift / postselection` 分账，只有度量兼容时才加总；同一 simultaneous good event 复用不重复加 α。

## 7. Bridge B3：量子载体、纠错与 Ω

先区分两任务：经典记录访问充分性，可直接调用 Core D-CAR；未知 logical quantum state 的恢复，需另定义 CPTP decoder，并包含任意 reference 的纠缠保真。

对编码 $\mathcal E$ 与保留子系统 S，量子充分性可定义为存在 decoder $\mathcal D_S$，使

$$
\mathcal D_S\circ\operatorname{Tr}_{S^c}\circ\mathcal E=\mathrm{id}_L
$$

（完整 channel equality 等价于所有 reference 上一致）。保留更多子系统可先丢弃多余部分再恢复，因此 sufficient family 向上，有限 blocker 组合结论可复用。但是 disjoint classical backups 与 disjoint arbitrary-quantum recovery 不同，后者受 no-cloning/no-broadcasting 约束。

最低反例用 repetition/GHZ 编码 $\alpha|000\rangle+\beta|111\rangle$：局部读取足以恢复 Z 统计，却不恢复未知相位 coherence。载体报告必须指定是“预测 Z 记录”还是“完整 logical qubit”。

物理损坏需要明示 erasure/loss channel、剩余耦合、补偿与修复时域、资源预算。Ω 根据完整冻结证书重测，不能把 access blocker 当成真实器件失效谱。

## 8. Bridge B4/B5：量子控制与三个尺度操作

量子控制首轮选有限时域、有限动作、已知 instruments 与明示 reward；在 B1 的商上要求同类动作可行性、branch law、奖励都闭合，再复用 P-QUO。若奖励不在 preserved observable space，把它加入闭包后重算；否则预测商可能失去 value。

无限时域和 GOA 单独验收。CPTP/Lindblad 稳态存在、唯一、mixing、gap 及各类 QSD 需要量子适配。M-PE 的标量正矩阵结果不能无条件作用于任意 CP superoperator；正锥类型不同，初版可先做 commutative diagonal sector，或明确引用另证的 cone spectral theorem。

尺度分三种，不建立万能 RG：

1. Object resolution：固定目标/底载体/时域的 closure、blocker、微观实现区间。
2. Process coarse-graining：$C_\#P_A^{Ju}=P_B^u$ 的协议与记录映射，必要时有残差。
3. Wilsonian RG：具体场论、cutoff、action、integration/truncation、matching 与低能 observables；只有完成 response naturality/误差桥，才接 Core。振荡复权 path integral 不是经典概率 pushforward。

## 9. Bridge B6：Π/Φ 在量子应用中的可失败主张

Π 可选独立可测收益/能量/时间预算，Φ 可选协议预测 KL、memory rate 或明确 decision cost；若混入目标，$\lambda_\Phi$ 需承担单位转换。两参数拟合不能验证宇宙仅有两驱动。

若宣称跨环境共同 $z(B)\in\mathbb R^2$，应冻结至少三预算方向、三总响应维数，并在同一点 B 堆叠 $S(B)=(J_e(B))_e$。有 $\|\hat S-S\|_2\le\eta$ 时，`σ̂₃−η>τ₀` 拒绝 $\sigma_3\le\tau_0$。支持阈值意义 effective dimension 2 须同时 `σ̂₂−η>τ` 和 `σ̂₃+η<τ`。不同 B 的切空间可旋转，不得随意跨点堆叠。

若秩三被确认，输出“该共同二维 bridge 被拒绝”；保留 Core、已有 QM 与其它物理拟合结果。没有锚时只报告低维响应，不称 Π/Φ 机制。

## 10. 规划的建议验收记录

每条 QM claim 独立保存 mathematical statement、来源版本、Core P-ID / Lean 名、QM 额外假设、proof implementation、compiled commit、physical calibration、protocol coverage、positive and negative witnesses、status。至少将 `MATHEMATICS / MACHINE / PHYSICS / REAL_DATA` 分列，避免 simulation pass 导致无条件“已证明”。

首轮应先补 B0/B1/B2 的一个精确可执行小链；其价值是把已有量子论变成可检验对象证书。重构 Born/complex field/ħ/gauge/generations 保持各自既有路线，审查假设是否隐含结论，不为追赶版本号加新公设。

### 10.1 与 v23 已有成果去重

已核对 v23.0 完整可读正文中的 Quantum FFIPS uniqueness、Instrument Conditioning–FFIPS、Coherent Parent Completion、公有稳定交换代数、Public-Record Blindness，以及 conservative extension 段落。B0 的基本解析内容已有；新增目标应是 frozen Core v3 的精确 source→Lean adapter、支持/零概率/误差类型核对，不能将其再包装成首次 instrument→FFIPS theorem。B1 的非 tomographically-complete、受控 observable-space closure 给一个可执行的受限协议切片；它亦应复用已有 model-reduction 文献。

v23 已声明标准分支保持 states/effects/Born/channels/instruments/tensor law，只添加对象 predicates，因此其 outcome probabilities 与标准 QM 相同。这条 conservative-extension theorem 应保留，不能要求定义性 standard branch 额外产生新物理偏离；QBX 的非平凡 SRN kernel 或 HGP 新sector需另列物理前提。

### 10.2 v30.11 selector 的独立实质改进：atomicity 为冗余前提

已完整核对 v30.11 text view（不是原件字节核验）与 unified mainline / deep audit / regression JSON。其整除方程为

$$
2N_c k=(N_c-1)N_f,\quad
d=\gcd(2N_c,N_c-1)=\gcd(2,N_c-1),\quad
N_f=t\frac{2N_c}{d},\ k=t\frac{N_c-1}{d},\ t\ge1.
$$

**加强定理：** 假设 $N_c\ge3,N_f>0,k\in\mathbb Z,0\le k\le N_f$，上述 cubic anomaly 方程成立，且 $N_f(N_c+1)<22$。不假设 primitive/atomicity，仍唯一得到

$$
(N_c,N_f,k)=(3,3,1).
$$

**证明：** 若 $N_c$ 奇，$N_f=tN_c$。$N_c\ge5$ 时左侧至少30，矛盾；故 $N_c=3$，于是 $12t<22$ 且 $t$ 正整数，只能 $t=1$。若 $N_c$ 偶，$N_c\ge4$、$N_f=2tN_c$，左侧至少40，矛盾。证毕。

因此 primitive 不是另一个宇宙选择公理，而是此条件组合的推论。水平异常式本身是齐次的，仍对 $(N_f,k)\mapsto(mN_f,mk)$ 封闭；新路线中排除整包复制的是 weak-screening 上界。正确叙事是“anomaly 整除下界 + weak coefficient 上界 → 3”，不是 anomaly 自身打破所有 replication。

**保留的物理前提不止 HGP 一句：**

- 具体 chiral horizontal/extended-weak gauge group 与带非零 cubic coefficient 的 R；所有 leptons 取同一 R、quarks 按 k/(Nf−k) 分为 R/$\bar R$ 的 spectrum。
- 所检验 support 的总 anomaly 正好是该方程；若有 spectator chiral fields、counterterm/Green–Schwarz/inflow，它们必须计入，不能继续强制裸 matter 系数为零。
- color class 已限定为 complex fundamental $SU(N_c)$ 且 $N_c\ge3$。这不是 generic Core 选择所有可能色群。
- 存在 ordinary families 全 active、弱 $SU(2)_L$ 仍为适用 gauge factor 的 perturbative matching window，并要求其一环 $b_2>0$。若 UV gauge group 已扩大，不能把这个窗口的符号称为全能标弱SU2 asymptotic freedom。
- 非负额外 screening 只对声明的额外 fermion/scalar matter 成立；额外 gauge vectors/改变 gauge group 时应重新算完整 beta coefficient。

对普通 Weyl 双重态和 complex scalar 内容，采用 $\mu\,dg/d\mu=-b_2g^3/(16\pi^2)+\cdots$ 约定，$b_2=22/3-N_f(N_c+1)/3-s$、$s\ge0$，故 $b_2>0\Rightarrow N_f(N_c+1)<22$。这个必要界不保证已列候选的完整 field content 必然 AF；仍需具体 witness 的 scalars/thresholds。

### 10.3 GOIT 只消费标准 anomaly 障碍，不反向替代它

v30.11 正确把原始 `β₁=3→index=3` 退役，并将 determinant-line 放在标准 QFT [K]。进一步应避免把“Core 的操作响应表示不变”说成自行推导总 anomaly line 平凡化。受限公共响应可能看不到相位，v23 Public-Record Blindness 正是此类边界。GOIT 的输入应包含完整 QFT consistency theorem；所需 trivialization 应适用于 gauge redundancy、equivariant 且与 connection/global holonomy 相容。局域 anomaly polynomial/cubic cancellation 与 global torsion anomalies/inflow 检验分列。

### 10.4 已运行的精确小基准

[`qm_bridge_benchmarks.py`](../benchmarks/qm_bridge_benchmarks.py) 使用 Python 标准库 Fraction，无浮点容差。4 组均通过：

1. Z-only W*维数2、H+Z W*维数3；$|+\rangle,|-\rangle$ 的 Z-TV=0、H再Z的TV=1，且每组 adjoint closure 直接验证。
2. 成功率分别取 $10^{-1},10^{-2},10^{-3},10^{-6}$，两完整记录 TV 等于成功率，而后选择条件 TV 恒为1。
3. 两个2×2有理 Hermitian矩阵的 commutator trace=0，对比 $\operatorname{Tr}(i\hbar I_2)=2i\hbar$；一般迹论证另在文中证明。
4. 由正整数 bound 严格推出 $3\le N_c\le20$，穷尽全部89个 $(N_c,N_f,k)$ 候选，不加入primitive filter，唯一留下 $(3,3,1)$。移除complex color有 $(2,4,1)$，移除weak bound有 $(3,6,2)$。

这些是精确有限反例/回归；不计入新的 Lean 证明或现实数据支持。

## 11. 直接相关的原始文献（核实于 2026-10-19）

- Pollock et al., *Operational Markov condition for quantum processes*, Phys. Rev. Lett. 120, 040405 (2018): https://arxiv.org/abs/1801.09811 。操作 Markov 判据的范围，应与一般 CP-divisibility 区分。
- Taranto et al., *Quantum Markov Order*, Phys. Rev. Lett. 122, 140401 (2019): https://arxiv.org/abs/1805.11341 。有限记忆性质依赖 instrument 族，不能把受限协议结果外推到全部 interventions。
- Grigoletto et al., *Exact Model Reduction for Continuous-Time Open Quantum Dynamics*, Quantum 9, 1814 (2025): https://arxiv.org/abs/2412.05102 ；https://quantum-journal.org/papers/q-2025-07-29-1814/ 。区分 minimal linear reduced model 与保持物理结构的 quantum reduced model。
- Grigoletto, Viola, Ticozzi, *Model Reduction for Controlled Quantum Markov Dynamics* (2025): https://arxiv.org/abs/2510.25546 。受控时变 Lindblad 的 observable-preserving reduction 可作为已有技术来源。
- Adhikary et al., *Expressiveness and Learning of Hidden Quantum Markov Models*, AISTATS 2020: https://proceedings.mlr.press/v108/adhikary20a.html 。HQMM 与 observable operator models 的关系，可用于区分记录表示与可实现 quantum model。

上述新桥的公式与限定是对 Core 的独立组合推导/规划，不以文献 abstract 替代完整证明，也不声称已在 Lean 中实现。
