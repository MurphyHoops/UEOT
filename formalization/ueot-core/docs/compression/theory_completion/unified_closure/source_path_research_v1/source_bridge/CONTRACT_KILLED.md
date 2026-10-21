# 从同一实际闭环到 killed restriction 与条件生存

状态：`MATHEMATICAL_CONTRACT_NOT_FORMALIZED`。这是下一条来源桥的准确命题与书面证明路线，不是新增 Lean 通过收据。本文不修改当前七个生产候选，不启动 Lean，不扩展到完整最优值或 Cesàro 实例。

## 0. 首步私有桥的再次复核

复核输入为本目录 `SourcePolicyPathBridge.lean`，SHA256：

`108500fc13229b8faffc9829d886313167142075112bc3f6c023a086c074ae91`。

本次静态复核未发现数学或量词错误，没有修改该文件；实际编译状态仍为 `WRITTEN_NOT_COMPILED`。

其来源链是：`sigma : Y → PMF A` 在每个时间、每个完整观察历史上按当前观察取行动；微观转移直接使用 `M.transitionPMF`；`liftedStationaryPolicy` 的实数概率直接取同一个 sigma 的 `toReal`。因此 `actual_next_state_eq_stationary_row` 的有限 bind 展开，与 `Model.policyTransition` 的有限行动和逐项一致；两个 PMF 的质量都有限，可通过 `toReal` 的单射性返回 PMF 相等。完整路径归纳用已证明的行等式、既有 `risk_map_extend_right` 和 `coverage_map_extend_reference`，没有另假定 Markov 来源身份。

它只擦除动作，保留全部微观状态记录。故不需要观察 q 的强可聚合性，也不推出观察过程 Y 自身 Markov。平稳性来自实际策略定义，并非由零概率历史上的条件概率臆测。一般历史依赖策略没有被该候选覆盖；时间依赖的当前观察策略只能直接得到时间非齐次核，不能悄然替换成一个固定 policyMatrix。

本次不在缺少编译日志时调整 tactic。潜在 elaboration 问题只影响实现验收，不改变下面的数学契约；仍须以 root 后续聚焦编译结果确定候选状态。

## 1. 一次定义全部来源

固定有限微观状态 X、有限非空共同动作类型 A、任意观察类型 Y、观察映射 o:X→Y，以及一个既有有限控制模型 M。记原始真实转移为

\[
P(x,a)=M.\mathrm{transitionPMF}(x,a),\qquad
p(x,a,z)=M.\mathrm{transition}(x,a,z).
\]

已有 `transitionPMF_apply_toReal` 给出 `(P(x,a)(z)).toReal=p(x,a,z)`。固定 `sigma:Y→PMF A`，定义全部历史上的实际策略

\[
\pi_n(h)=\sigma(\operatorname{last}h),\qquad
w(x,a)=(\sigma(o(x))(a)).\mathrm{toReal}.
\]

这里 h 是观察历史。实际微观核仍通过 `riskMicroControlKernel o (fun _ => M.transitionPMF) π` 构造，不能另给一个转移表代替它。

定义

\[
L:=\mathrm{policyMatrix}\ M\ (\mathrm{liftedStationaryPolicy}\ o\ \sigma),
\qquad L(x,z)=\sum_a w(x,a)p(x,a,z).
\]

L 是同一实际源的平稳闭环矩阵。非负性与行和为一直接由 M、sigma 的归一化和 `policyMatrix_rowStochastic` 得出。首步私有桥的目标正是证明实际带动作路径擦除动作后的律等于 `policyPathKernel` 的完整状态路径律；此等式不列作本定理的调用者假设。

取任意安全集 K⊆X，令 S={x:X // x∈K}，j:S→X 为包含映射。**按定义**构造 killed 核

\[
Q(u,v):=L(j(u),j(v)),\qquad u,v\in S. \tag{1}
\]

没有第二个自由 Q，也没有额外 `Q=L|K` 假设。Q 不重新归一化；其缺失行质量是实际下一步离开 K 的概率：

\[
Q(u,v)\ge0,\qquad
\sum_{v\in S}Q(u,v)\le1,\qquad
1-\sum_{v\in S}Q(u,v)
=\sum_a w(j(u),a)\Pr_{P(j(u),a)}(K^c). \tag{2}
\]

右端 PMF 事件概率取实值。有限字母表可直接用有限质量和定义；若使用现有 `toMeasure.real` 记法，则给 X、A 离散可测结构，或保留其单点可测实例。Y 的可测性仍不参与这条 PMF 来源桥。

## 2. 生存事件必须包括哪些时刻

任意初始 PMF p0:X。实际长度 n 的带动作路径律记为 νn。定义

\[
S_n=\{X_0\in K,\ldots,X_n\in K\},\qquad
\eta_0(u)=p_0(j(u)).\mathrm{toReal}. \tag{3}
\]

这里 η0 是安全子类型上的**未归一化**初始行；一般只有总质量 p0(K)≤1。这样允许 K 为空，允许初态已经失败，并使 n=0 的命题准确。若额外知道真实 p0 支持于 K，η0 才是概率行，且 S0 的概率为一。

实现上，Sn 可以直接定义成已有

`¬ riskEverFailure (fun x => x ∉ K) n h`。

它包含初始状态与 n 次转移后的所有状态，与当前风险接口的时域约定一致。原四状态研究固定初始 `(true,false)∈K`，所以写成只检查第 1 至 n 步在该实例中概率相同；一般定理不能省略初始检查。

令真实存活终端质量为

\[
\kappa_n(v):=\nu_n(S_n\cap\{X_n=j(v)\}),\qquad
s_n:=\nu_n(S_n). \tag{4}
\]

只检查 `Xn∈K` 不够。原过程可能先离开、再返回；killed 核应丢弃所有这类路径，而不是在返回时重新加入。

## 3. 核心一般定理：未归一化质量的精确身份

**定理 K1。** 在上述按定义共享的 M、o、sigma、p0、K 下，对所有 n∈ℕ、v∈S，

\[
\boxed{\ \kappa_n(v)=(\eta_0Q^n)(v)\ },\qquad
\boxed{\ s_n=\sum_{v\in S}(\eta_0Q^n)(v)\ }. \tag{5}
\]

其中行乘法使用既有 `QSDPerron.rowApply` 或等值的 `Matrix.vecMul`。定理不需要 QSD、特征向量、不可约性、正存活假设、闭合安全域或独立采样假设。Q 与真实路径的来源身份由构造和证明提供。

**证明路线。**

1. 擦除动作保持每一个微观状态，故把 Sn 与终端状态事件分别表示为完整纯状态历史事件的精确原像。对 n 归纳证明这个集合等式。复用首步的完整路径推前定理，得到对应真实事件质量相等。
2. n=0 时，κ0(v)=η0(v)，且 Q⁰ 为 S 上单位矩阵；空 S 的求和同样合法。
3. 使用同一个 `policyPathKernel` 展开一次 PMF extension，并用 `policyTransitionPMF_apply_toReal` 把下一状态质量改写为 L。按末个安全状态 u 分组，得到
   \[
   \kappa_{n+1}(v)=\sum_{u\in S}\kappa_n(u)L(j(u),j(v))
   =\sum_{u\in S}\kappa_n(u)Q(u,v).
   \]
   无需在零概率历史上做条件化或除法；所有项均为未归一化有限质量。
4. 由归纳假设与 `rowApply_mul`、`pow_succ` 得第一式。Sn 内的末状态必在 K，对终端原子作互不相交的有限分解，求和得第二式。

也可直接展开实际动作—状态核的双重 pmfExtend，把行动和化成 L；但在已经建立首步桥后，应复用那条来源证明，避免重新维护两套相同展开。

**直接后果。**

\[
0\le s_{n+1}\le s_n\le1,\qquad
\nu_n(\mathrm{EverFailure}_K)=1-s_n. \tag{6}
\]

单调性由 Q 的非负性及行和≤1得出；风险等式由已定义的互补事件得到。它是同一实际有限实验的等式，不是对另一个独立 killed 模型的预测。

## 4. 条件终端律：严格保留正分母

**定理 K2。** 若 s_n>0，则

\[
c_n(v):=\frac{(\eta_0Q^n)(v)}{s_n} \tag{7}
\]

是 S 上概率行，且实际路径条件于 Sn 后的末状态分布，恰为 cn 经 j 推前得到的 PMF。

证明只使用 K1、各质量非负及分母正。Lean 可先用 `FiniteProbabilityRow.ofRealRow` 构造 S 上 PMF，再证明其 `map j` 等于 `(νn.filter Sn ...).map (riskLastState n)`。过滤的非空支持证据从真实 s_n>0 推出；不能另给一个未经连接的“成功条件分布”。

若 s_n=0，条件于 Sn 的概率分布没有由本实验唯一确定。Lean 对零分母的代数约定不能把 `0/0` 解释为 QSD。未归一化等式 K1 仍然有效。

## 5. 从同一 Q 接入现有 QSD：能推出什么

给同一个按 (1) 定义的 Q 一个概率行 r，以及真实证明

\[
rQ=\rho r,\qquad \rho>0. \tag{8}
\]

这是一项明确的条件特征数据，不是来源身份。Q 的非负与 substochastic 性已由 (2) 推出，因此现有 `KilledQSDGOA` 可直接复用，并可推出 ρ≤1。一般 Q 并不自动满足 (8)。

**定理 K3。** 用 r 构造真实初始 PMF

\[
p_0:=(\mathrm{ofRealRow}\ r).\mathrm{map}\ j.
\]

先证明按 (3) 得到的 η0 就是 r，再由现有 `leftPerron_pow` / `qsd_survival_mass_pow` 和 K1 推出

\[
\nu_n(S_n)=\rho^n>0,\qquad
\mathcal L(X_n\mid S_n)=j_*r \quad(n\ge0). \tag{9}
\]

这里 p0 按定义取自 r，不是对任意实际初态偷加 `η0=r` 作为未核验的来源假设。对实际初始 δx，要么直接使用一般 K1/K2，要么另外证明它经过若干 killed 步如何到达 r。四状态模型恰需证明任意安全初始**概率行** η（η≥0，且 `∑u η(u)=1`）在一步后变成 `(1−θ)r`；若 η 只是总质量 m 的非负行，相应结果应是 `m(1−θ)r`。该实例在 θ<1 时的 r 条件终端结论从 n≥1 开始，n=0 仍是原概率行 η。

QSD 条件只说明从指定 QSD 初始律出发的条件终端稳定。它不推出任意初始律的正存活、QSD 唯一性、向 QSD 收敛，或未条件化过程安全。

## 6. 正右特征向量给出的实际正存活条件

设同一个 Q 满足 `RightEigenData` 的条件

\[
Qh=\rho h,\qquad h(u)>0\ (u\in S),\qquad \rho>0. \tag{10}
\]

若 η0 的总质量严格为正，则 S 非空。令 hmin、hmax 是 h 在有限 S 上的最小与最大值，两者均正。由右特征关系的幂次推广、K1 及非负性，

\[
h_{\min}s_n\le\rho^n\langle\eta_0,h\rangle
\le h_{\max}s_n,
\]

从而

\[
0<\frac{\rho^n\langle\eta_0,h\rangle}{h_{\max}}
\le s_n\le
\frac{\rho^n\langle\eta_0,h\rangle}{h_{\min}}. \tag{11}
\]

这是适用于每一个非零安全初始行的有限时域正存活条件，明显强于只存在一个左 QSD。已有正特征结构的一般代数继续复用；新贡献是通过 K1 把这些量真正识别为原控制过程的存活概率。

## 7. 有限生存条件化与 Doob 变换的区别

设

\[
g_r(u):=(Q^r\mathbf1)(u),\qquad g_0(u)=1.
\]

本节讨论真实初始 p0 的有限生存条件实验时，明确要求全局 `s_T=ν_T(S_T)>0`。再给定一个真实、正概率且尚存活的完整微观前缀，当前安全状态为 u，时间 t<T，且 `g_{T-t}(u)>0`；这些前缀条件也保证该前缀与 S_T 的联合概率为正。条件于最终活到 T 的下一状态核为

\[
Q^{[T]}_t(u,v)=
\frac{Q(u,v)g_{T-t-1}(v)}{g_{T-t}(u)}. \tag{12}
\]

若保留行动记录，真实下一动作—安全状态的条件质量为

\[
\frac{w(j(u),a)\,p(j(u),a,j(v))\,g_{T-t-1}(v)}
     {g_{T-t}(u)}. \tag{13}
\]

初始条件律为 `η0(u) gT(u) / sT`。这些式子由实际路径质量因子分解得到；它们一般改变行动分布，也可能改变初始分布。不能把条件实验仍标成原来的未条件化策略。若只给观察前缀而没有实际微观当前状态，还必须对真实后验与未来存活权重作混合；不能把当前观察纤维直接当作该后验。

另一方面，(10) 导出的 Doob 核是

\[
Q^h(u,v)=\frac{Q(u,v)h(v)}{\rho h(u)}. \tag{14}
\]

它对一条安全状态路径的乘积满足

\[
\prod_{t<n}Q^h(x_t,x_{t+1})
=\rho^{-n}\frac{h(x_n)}{h(x_0)}
 \prod_{t<n}Q(x_t,x_{t+1}). \tag{15}
\]

取 S 上非负初始行 η，明确要求 `η(u)≥0` 对所有 u 成立，且 `⟨η,h⟩>0`。按 `η^h(u)=η(u)h(u)/⟨η,h⟩` 初始化就得到概率行。Doob 路径律是原 killed 路径质量（以 η 初始化）的终点 h 权重倾斜，归一化常数为 `ρ^n⟨η,h⟩`。若 η 本身归一化为概率行，原 killed 路径质量对应一个真实初始概率实验；η 未归一化时，以上恒等式按有限非负路径测度理解，η=η0 时即对应已截去初始失败质量的真实路径测度。该权重倾斜一般不是仅条件于生存的路径律。

**可精确合并的特殊情形。** 若 `Q1=ρ1` 且 ρ>0，则可以取 h≡1，`gr=ρ^r1`，(12) 对所有时刻都成为 Q/ρ；从任意安全概率初始 η 出发，有限生存条件下的纯状态路径正是初始 η、转移 Q/ρ 的路径。条件行动分布仍应由 (13) 推出，不能省略。四状态源的 `Qθ=(1−θ)H` 属于该常危险率情形；θ<1 时条件行动全部为安全动作，这与原 πθ 的无条件部署律不同。

## 8. 必须保留的反例

下面每个反例都分别从一个明确的有限控制模型产生：动作只有一个，奖励为零、折扣为 1/2；各例自己的原闭环、路径事件与 killed restriction 共享这一来源，并非五例共用同一矩阵。§8.1、§8.2、§8.4、§8.5 可在各自给定的 substochastic Q 之外增加吸收墓地状态，把缺失行质量送入墓地。§8.3 则保留可以返回 K 的域外状态 d，d 不是吸收墓地。两种构造的 Q 都按 (1) 取自各自真实 stochastic 模型的 K 限制；killed restriction 不要求原模型的域外状态吸收。

### 8.1 安全域非空，一步可以存活，但不存在正存活 QSD

\[
Q=\begin{pmatrix}0&1\\0&0\end{pmatrix}.
\]

实际安全状态 a 确定转移到 b，b 下一步确定离开 K。p0=δa 时 `(s0,s1,s2)=(1,1,0)`。若存在归一化非负 r、ρ>0 满足 rQ=ρr，第一坐标强制 ra=0，第二坐标再强制 rb=0，矛盾。因此有限 K、非零 Q、某个正时刻存在生存路径，都不足以保证正存活 QSD。

### 8.2 全支撑 QSD 仍不能保证实际初态正存活

\[
Q=\begin{pmatrix}0&0\\1/2&1/2\end{pmatrix},\qquad
r=(1/2,1/2),\quad\rho=1/2.
\]

直接算得 rQ=ρr，r 对每个安全状态都为正；但实际 p0=δa 从首状态出发，s1=0。QSD 的初始混合中一部分质量从 b 补入 a，并不保证单独从 a 出发能再活一步。此例不存在满足 (10) 的严格正右特征向量，因为首行迫使 `0=ρh(a)`。

### 8.3 返回安全域不恢复此前已失去的生存事件

原状态 a 与非吸收的域外状态 d 确定交替 `a→d→a`，K={a}，p0=δa。T=2 时终端落在 K 的概率为一，但始终留在 K 的概率 s2=0，且 Q=(0)。实际原过程允许 d 返回 a；killed restriction 在首次离开 K 时即不再计入该路径，所以必须区别于最终安全事件。

### 8.4 正 QSD 与正右特征向量也不使 Doob 等于有限窗条件化

\[
Q=\begin{pmatrix}1/4&1/8\\1/2&1/4\end{pmatrix},\qquad
h=(1,2),\quad\rho=1/2.
\]

Qh=ρh，且 r=(2/3,1/3) 满足 rQ=ρr。Doob 核 (14) 的每行都是 `(1/2,1/2)`，但只条件于下一步存活的核 (12) 每行都是 `(2/3,1/3)`。所有分母都为正，差别来自真实终点权重，而非零概率例外。

### 8.5 正存活并不保证 QSD 唯一

`Q=(1/2)I` 在两个安全状态上，任意概率行 r 都是 ρ=1/2 的 QSD；条件终端律始终保留自己的初始行。要推出唯一或吸引，需要额外真实结构，不能从 (5)、(8) 或 (10) 单独推出。

## 9. 最小实现次序与验收

本阶段仅建议依次实现：

1. 对首步 `SourcePolicyPathBridge.lean` 执行聚焦编译，保留真实失败与修复身份。
2. 从同一 `policyMatrix` 定义安全子类型上的 Q，证明 (2)。不把 Q 或来源相等另设为外层输入。
3. 定义实际 Sn、κn，证明事件擦除动作的原像身份、一次质量递推及 K1。
4. 由 K1 给出 K2 的真实条件终端律；只有正存活分支允许归一化。
5. 再以明确构造的 QSD 初始律接入现有 QSD 结论，并在四状态源中另做实际 δ 初态的一步适配。

第 7 节的完整有限窗条件核与 Doob 路径倾斜可作为后续证明目标，避免本阶段一下扩到整套 Q-process 理论。即使暂不形式化，它们的数学边界也必须保留，以免把条件终端不变误写成同一未条件化策略的完整路径不变。

当前候选与本契约不证明完整同源 GOA 实例、无限期存活、全部 P-ID 重推导或经验世界的统一理论；它们补的是一条可检查、能实际消除独立来源假设的有限概率桥。

## 实际源码依据

- `SourcePolicyPathBridge.lean`：本目录私有候选，状态见 `STATUS.json`。
- `UEOT/V3/CoreOperationalAssembly.lean`：`policyMatrix`、`policyTransitionPMF`、`policyPathKernel`。
- `UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/MicroscopicFailureRisk.lean`：`riskEverFailure` 包含初始时刻。
- `UEOT/V3/QSDPerron.lean`：`rowApply_mul`、`leftPerron_pow`、`qsd_survival_mass_pow`、`qsd_all_steps`。
- `UEOT/V3/Compression/PositiveEigenstructure.lean`：`RightEigenData`、`BiEigenData`、`qsdDoob_bundle`。
- `UEOT/V3/Compression/TheoryCompletion/GOA.lean`：`KilledQSDGOA` 及其正生存、rho 上界语义。

以上生产路径均相对于 `ueot-integration/formalization/ueot-core/`；本次只读这些来源。
