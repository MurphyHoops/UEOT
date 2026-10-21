# 有限窗生存条件路径与齐次 Doob 路径：同源边界与最小接口

## 结论与研究状态

**一般 K2 与左 QSD 足以确定实际条件终态律，不能推出完整有限窗条件路径等于某个固定齐次 Doob 路径。即使同一个 killed 核同时有严格正右特征向量，这个推论仍然不成立。** 下面的三状态同源反例在一步就分开两种路径律；相应一般有限窗核需要剩余生存函数 \(H_m=Q^m\mathbf 1\)。

这不是宣称 Core 缺少 QSD 或 Doob 理论。生产 `QSDPerron`、`PositiveEigenstructure` 和 `GOA` 已证明左特征、右 Doob 随机性、配对不变律及相关代数后果；已审 `CONTRACT_KILLED` §7–8.4 已写明有限窗条件化的区别。本报告复用这些结果，给出本次指定实际源的完整数字、一般路径量词及下一条来源适配的最小范围。[QSDPerron.lean](sandbox:/workspace/scratch/9a8d58b21e30/ueot-integration/formalization/ueot-core/UEOT/V3/QSDPerron.lean)、[PositiveEigenstructure.lean](sandbox:/workspace/scratch/9a8d58b21e30/ueot-integration/formalization/ueot-core/UEOT/V3/Compression/PositiveEigenstructure.lean)、[CONTRACT_KILLED.md](sandbox:/workspace/scratch/9a8d58b21e30/tmp/finite-encoding-20261021/resume-source-bridge/CONTRACT_KILLED.md)。

**本报告新增的反例和完整有限窗核为数学推导，未运行 Lean。** 有理数计算使用 `fractions.Fraction`，其结果保存在 [RATIONAL_COUNTEREXAMPLE.json](sandbox:/workspace/scratch/9a8d58b21e30/tmp/interface-next-review/finite-window-doob/RATIONAL_COUNTEREXAMPLE.json)，不是抽样实验或 Lean 证明。一般 K2 与 QSD 特化已有各自私有聚焦 PASS 和独审，尚未进入当前七模块生产发布；QSD 实际编译增量见本目录 [QSD_COMPILE_DELTA_CLEAR.md](sandbox:/workspace/scratch/9a8d58b21e30/tmp/interface-next-review/finite-window-doob/QSD_COMPILE_DELTA_CLEAR.md)。

## 1. 一份真实的三状态源

取状态空间 \(X=\{0,1,\Delta\}\)，安全集 \(K=\{0,1\}\)，行动类型为单点。观察映射取常值，策略永远选择该唯一行动。令实际模型转移为

\[
L=\begin{pmatrix}
3/8&3/8&1/4\\
1/8&1/8&3/4\\
0&0&1
\end{pmatrix},
\qquad p_0=(1/2,1/2,0).
\]

每行非负且和为 1，墓地吸收。若需满足现有有限控制模型的全部字段，可取奖励恒为零、奖励界为 1、折扣为 \(1/2\)；这些字段不改变转移或生存事件。单行动使同一模型的 `policyMatrix` 就是 \(L\)，完整风险历史记录中的行动也没有额外随机性。安全事件始终是 \(S_T=\{X_0,\ldots,X_T\in K\}\)，不是仅要求终态落在 K。

唯一 killed 核来自这份 \(L\) 的安全限制：

\[
Q=\begin{pmatrix}3/8&3/8\\1/8&1/8\end{pmatrix},
\quad r=(1/2,1/2),\quad \rho=1/2,\quad h=(3,1).
\]

逐项计算得到

\[
rQ=(1/4,1/4)=\rho r,
\qquad Qh=(3/2,1/2)=\rho h.
\]

因此本例同时有归一化全支撑左 QSD 和严格正右特征向量，且真实初态正是 \(r\) 的包含映射推前。并未在分析中替换另一个既定初态。

Doob 核为

\[
R_{ij}=\frac{Q_{ij}h_j}{\rho h_i}
=\begin{pmatrix}3/4&1/4\\3/4&1/4\end{pmatrix}.
\]

这里 \(\langle r,h\rangle=2\)，自然的倾斜初态为
\(r^h_i=r_i h_i/2=(3/4,1/4)\)，也就是 R 的不变律。生产 `BiEigenData` 的字段要求左右配对等于 1；直接适配时应使用 \(\bar h=h/2=(3/2,1/2)\)。此缩放不改变 R，不能把原配对 2 当作 1。

### 1.1 真实一步条件路径

原源在安全初末态上的联合质量是

\[
\Pr(X_0=i,X_1=j,S_1)
=p_0(i)Q_{ij}
=\begin{pmatrix}3/16&3/16\\1/16&1/16\end{pmatrix}.
\]

它的总质量为 \(s_1=1/2\)。除以这同一个真实事件概率后，条件路径联合分布恰为

\[
C_1=\mathcal L(X_0,X_1\mid S_1)
=\begin{pmatrix}3/8&3/8\\1/8&1/8\end{pmatrix}=Q.
\]

这个矩阵在此处是四个路径原子的联合概率表，不是声称原 Q 的每行已归一化。行边缘与列边缘分别为

\[
\mathcal L(X_0\mid S_1)=(3/4,1/4),\qquad
\mathcal L(X_1\mid S_1)=(1/2,1/2)=r.
\]

终态确实服从 QSD，初态却因未来生存条件而改变。实际条件下一步转移的每行均为 \((1/2,1/2)\)，与 R 的每行不同。

以 r 或 \(r^h\) 启动同一个 R，得到的路径联合分布分别为

\[
D^r_1=\begin{pmatrix}3/8&1/8\\3/8&1/8\end{pmatrix},
\qquad
D^{r^h}_1=\begin{pmatrix}9/16&3/16\\3/16&1/16\end{pmatrix}.
\]

它们都不是 \(C_1\)，两者与 \(C_1\) 的路径 TV 均精确为 \(1/4\)。更强的是，R 的两行相同，所以**任意概率初态**乘 R 后的终态都是 \((3/4,1/4)\)，不可能等于 \(C_1\) 的终态 r。更换 Doob 初态也无法修复这个一步完整路径等式。

## 2. 一般有限窗的实际条件公式

固定同一有限模型 M、观察 q、当前观察平稳随机策略 sigma，以及任意真实初态 \(p_0\)。由已经通过的私有来源桥，擦除行动后的完整微观状态路径等于同一 `policyPathKernel` 的路径；这一步不把一般历史策略自动变成 Markov 策略。[SourcePolicyPathBridge.lean](sandbox:/workspace/scratch/9a8d58b21e30/tmp/finite-encoding-20261021/resume-source-bridge/SourcePolicyPathBridge.lean)。

令 \(L\) 为这个同源闭环，\(Q=L|_{K\times K}\)，以及未归一化的初始安全行

\[
\eta_0(i)=p_0(i),\qquad i\in K.
\]

它的总质量为 \(p_0(K)\)，不应先除掉初始失败质量。定义

\[
H_0(i)=1,\qquad H_{m+1}(i)=\sum_{j\in K}Q_{ij}H_m(j),
\quad H_m=Q^m\mathbf 1,
\]

\[
s_T=\sum_i\eta_0(i)H_T(i)=\Pr_{p_0,L}(S_T).
\]

这里 Q 的非负次随机性与 \(s_T\) 的实际生存意义，均来自同一模型和 K1 已证接口。[SameSourceKilledPath.lean](sandbox:/workspace/scratch/9a8d58b21e30/tmp/finite-encoding-20261021/resume-killed-formalization/SameSourceKilledPath.lean)。以下条件实验明确要求 \(s_T>0\)。

### 2.1 路径与前缀质量

对一条安全状态路径 \(x_0,\ldots,x_T\)，实际未条件质量为

\[
w_T(x_{0:T})=\eta_0(x_0)\prod_{t=0}^{T-1}Q_{x_t x_{t+1}},
\]

故实际条件路径原子为

\[
C_T(x_{0:T})=\frac{w_T(x_{0:T})}{s_T}. \tag{1}
\]

对 \(t\le T\) 的安全前缀 \(x_{0:t}\)，把后续安全路径求和可得

\[
\Pr(X_{0:t}=x_{0:t},S_T)
=\eta_0(x_0)\prod_{k<t}Q_{x_kx_{k+1}}\,H_{T-t}(x_t). \tag{2}
\]

证明不需要另加“来源质量等式”前提：`causalLaw` 以 `pmfExtend` 递推，已有 `pmfExtend_apply` 给出原子乘积；再按同一随机核对后缀作有限求和，归纳得到 H 的递推。既有完整状态路径来源桥把这一计算送回含行动记录的真实风险实验。[PathError.lean](sandbox:/workspace/scratch/9a8d58b21e30/ueot-integration/formalization/ueot-core/UEOT/V3/PathError.lean)。

### 2.2 初始律和时变核

由式（2），真实条件初始律为

\[
\eta^{[T]}(i)=\Pr(X_0=i\mid S_T)
=\frac{\eta_0(i)H_T(i)}{s_T}. \tag{3}
\]

若安全前缀在条件实验中有正质量，当前状态 i、剩余步数 \(m=T-t\ge1\)，则其原前缀质量正且 \(H_m(i)>0\)。将子前缀与父前缀的质量相除，得到

\[
R^{[T]}_t(i,j)=
\frac{Q_{ij}H_{m-1}(j)}{H_m(i)}.
\tag{4}
\]

非负性直接来自 Q 和 H；求和为 1 正是 \(H_m=QH_{m-1}\)。条件路径由（3）与（4）生成，乘积中的 H 因子望远镜消去，最后 \(H_0=1\) 恢复式（1）。

**全局 \(s_T>0\) 不表示每一个状态的 \(H_m(i)>0\)。** 式（4）在正分母行上才是条件概率；若某状态在该条件时间没有质量，不能把实数 0/0 宣称为一行概率。若形式化的完整 PMF 核接口需要在全部状态上给值，应明确提供零质量行的回退，或在正未来生存的子类型上定义行，并证明这些补值不影响实际条件路径律。

### 2.3 保留行动时，策略也会被条件化

写 \(w(i,a)=\sigma(q(i))(a)\)，\(p(i,a,j)\) 为同一模型的行动后转移质量。在相同正条件前缀上，实际下一动作—状态质量为

\[
\Pr(A_t=a,X_{t+1}=j\mid X_{0:t},S_T)
=\frac{w(i,a)p(i,a,j)H_{m-1}(j)}{H_m(i)},\qquad j\in K.
\tag{5}
\]

对 j 求和可见，条件行动边缘通常不再等于原 sigma。对 a 求和则得到（4）。因此即便纯状态条件核恰好齐次，也不能自动宣称条件实验沿用原未条件化行动政策。

若只有观察历史而没有当前微观状态，公式还须对真实后验按未来生存权重再混合；当前观察纤维不能替代真实历史后验。这里不新增一般观察过程的 Markov 性主张。

### 2.4 必须保留的边界

- \(T=0\)：\(H_0=1\)，\(s_0=p_0(K)\)。若正，则条件初态为原初态限制于 K 后归一化；没有转移核需要应用。
- K 为空或 \(p_0(K)=0\)：所有 \(s_T=0\)，不存在所需条件 PMF。若 Q 只允许有限寿命，某些后续 \(s_T\) 也可以为零。
- 从 QSD 初态 r 出发时，\(s_T=\rho^T\)；\(\rho=0\) 仅在 \(T=0\) 可条件化。这个精确边界已由私有 QSD 特化证明。
- 一般 killed restriction 不要求原 K 外状态吸收；曾退出后返回的路径仍不属于 \(S_T\)。本例选择吸收墓地只是实现方便。

## 3. 齐次 Doob 路径实际表示什么

现在另有同一 Q 的正右特征数据：\(\rho>0\)、\(h_i>0\)、\(Qh=\rho h\)。已有生产接口给出

\[
R^h_{ij}=\frac{Q_{ij}h_j}{\rho h_i},\qquad \sum_jR^h_{ij}=1.
\]

令 \(c=\langle\eta_0,h\rangle>0\)，以 \(\eta_0^h(i)=\eta_0(i)h_i/c\) 启动 R。对安全路径，直接展开并消去内部 h 得

\[
D^h_T(x_{0:T})
=\frac{\eta_0(x_0)\prod_{t<T}Q_{x_tx_{t+1}}\,h_{x_T}}
       {\rho^T c}.
\tag{6}
\]

所以 Doob 路径是原 killed 路径测度的**终点 h 权重倾斜**。它与纯生存条件路径（1）的比值为

\[
\frac{D^h_T}{C_T}(x_{0:T})
=\frac{s_T h_{x_T}}{\rho^T c}
\quad\text{在正质量安全路径上}. \tag{7}
\]

对固定初态及固定 T，使用上述自然倾斜初态时，二者相等的精确条件是

\[
h(X_T)=\frac{\rho^T c}{s_T}
\quad C_T\text{-几乎处处}. \tag{8}
\]

有限支持下就是所有实际可达且有正条件质量的终态拥有相同的 h 值。这比“存在正右特征向量”强，且只要求相关可达支持上的条件；不能把全局 h 常数误说成所有退化例子中的必要条件。

若比较转移行而非完整路径，准确条件为：对正条件前缀、\(m\ge1\) 以及 \(Q_{ij}>0\)，

\[
\frac{H_{m-1}(j)}{h_j}
=\frac{H_m(i)}{\rho h_i}. \tag{9}
\]

此外必须匹配真实条件初始律（3）。只核对某个时刻的转移行不足以推出完整路径相同。若 Q 的所有安全条目都严格为正且实际初态非零，正时刻条件终态支持包含全部 K；这时（8）迫使 h 全局为常数。指定反例正属于这一情况，非恒定 h 不能被忽略。

### 3.1 常危险率的可靠充分条件

若同一个 Q 满足

\[
Q\mathbf1=\rho\mathbf1,\qquad \rho>0,
\]

则可以取 \(h\equiv1\)，从递推得 \(H_m=\rho^m\mathbf1\)。于是（4）在所有时刻都是 \(Q/\rho\)，（3）为 \(\eta_0/p_0(K)\)，与 T 无关。若原初态已全在 K 内，则初态保持不变；若含初始失败，则仍需限制并除以 \(p_0(K)\)。

这一条件表示每个安全状态的一步生存概率相同，是所有初态都可直接使用的充分条件。一般稀疏核或受限可达支持上也可能有其他相等情形，其精确判断应回到（8）或（9）。

在已有四状态研究稿中，\(Q_\theta=(1-\theta)H\)、H 每行和为 1，\(0\le\theta<1\) 给 \(\rho=1-\theta>0\)、\(h=1\)。故有限窗条件**状态**核确实为 H。其更强状态—行动路径等于安全策略 \(\pi_0\) 的结论，还使用该具体源“生存迫使每步动作都为安全动作”的事实：所有存活路径的原质量恰为 \((1-\theta)^T\) 乘对应 \(\pi_0\) 质量。它是该源的额外论证，不是从一般左 QSD 自动推出。\(\theta=1,T>0\) 为零事件，不能继续归一化。[SAME_SOURCE_STATIONARITY_QSD_RISK.md §3–4.1](sandbox:/workspace/scratch/9a8d58b21e30/tmp/books-next-20261021/SAME_SOURCE_STATIONARITY_QSD_RISK.md)。

指定三状态反例的 Q 行和为 \(3/4,1/4\)，不满足常危险率。直接把 h 换为 1 会破坏 \(Qh=\rho h\)；若改变 Q 来获得常行和，就是改变了原模型。

## 4. 反例在较长有限窗中的准确形状

本例 \(Q^2=\rho Q\)，故对 \(m\ge1\)，

\[
H_m=\rho^{m-1}(3/4,1/4)=\rho^m h/2.
\]

从真实 QSD 初态 r 出发，任意 \(T\ge1\) 的条件初态均为 \(r^h\)。剩余 \(m\ge2\) 时，式（4）恰好等于 R；**最后剩余一步**却为每行 r 的核。也就是：

- 第一个至倒数第二个转移使用 R（若 T=1，则没有这一段）；
- 最后一个转移使用每行 \((1/2,1/2)\) 的核；
- 终态为 r，所有更早时刻的条件边缘为 \(r^h\)。

这种“前缀已是 Doob、末步仍不同”的精确例子说明，远离终点的阶段相等不能扩大成整个有限窗相等。从（7）还得到，以 \(r^h\) 启动的 Doob 路径与实际条件路径的 TV 对每个正 T 都为 \(1/4\)。报告中的 T=1、2、3 枚举只作有理数核对；全 T 结论来自 \(Q^2=\rho Q\) 与上述公式的数学推导。

不同 T 对应不同条件事件，故这些完整条件路径律也不能未经证明拼成同一个无限过程的前缀族。例如 \(C_2\) 的前两时刻联合为 \(r^h R\)，而 \(C_1=Q\)；二者不同。这不否定实际原过程的前缀一致性，只是说明“按各自终点生存重新条件化”通常不保留该一致性。

## 5. 已有 Core 覆盖与最小待适配端点

下表来自实际源码检索和声明读取。它区分现有理论、已通过私有桥和本次尚待形式化的完整有限窗适配，不作项目全域缺失断言。

| 已有位置 / 端点 | 可直接复用的内容 | 仍需本来源适配的内容 |
|---|---|---|
| `CoreOperationalAssembly.policyTransitionPMF`、`policyTransitionPMF_apply_toReal`、`policyPathKernel`、`policyMatrix` | 同一模型和平稳策略生成 PMF、实数矩阵与历史核 | 不能换成一个无来源相等证明的自由 Q |
| `PathError.pmfExtend_apply`、`causalLaw` | 真实有限路径的递推与逐原子乘积 | 安全后缀求和得到 H、真实前缀圆柱与最终生存的联合质量（2） |
| 私有 `SourcePolicyPathBridge.actual_state_path_eq_stationary_path` | 同一风险实验擦除行动后的完整状态历史身份，已聚焦 PASS | 条件化后继续保留完整路径，而不是只取终态 |
| 私有 K1 两个 `actual_survival_*_eq_killed_pow*` | 实际终端联合质量与总生存质量，已聚焦 PASS | 所有中间前缀与剩余未来的联合质量，不只是终态 |
| 私有 K2 `actualConditionedTerminal`、`actual_conditioned_terminal_eq_normalized_killed_map` | 真正过滤实际生存事件再取末态的归一化律，已聚焦 PASS | 完整条件历史的时变核分解；K2 的终态投影不包含此完整等式 |
| 私有 QSD `actual_qsd_survival_mass`、当前正存活条件律 | 从实际 `r.map` 初态复用 K1/K2，已聚焦 PASS 并通过本次增量独审 | 不能升级为全路径 Doob 恒等式 |
| `QSDPerron.leftPerron_pow`、`qsd_survival_mass_pow`、`qsd_all_steps` | 左特征幂、质量、归一化终态不变 | 把代数对象绑定实际源由 K1/K2/QSD 桥完成；无完整路径等同结论 |
| `QSDPerron.doobTransform_row_sum`、`doobInvariant_stationary`；`PositiveEigenstructure.RightEigenData` / `BiEigenData` / `qsdDoob_bundle` | 正右特征归一化、左/右配对不变律 | 真实路径的 h 倾斜（6）和有限窗比较（7），配对归一化不能省略 |
| `GOA.KilledQSDGOA`、`killedQSDGOA_all_steps` | 次随机、概率左行、正因子和左特征语义及 all-step 比值 | 谓词本身不记录原控制实验，也不包含右 h 或完整路径身份 |
| `QSDTVLimit.KilledSemigroup.conditioned`、`conditioned_shift_eq_mass_smul`、`p_qsd_01` | 连续时间 killed 半群中实际演化边缘的归一化、时间平移与 TV 极限到 QSD | 它要求自己的半群与生存条件；不是本离散控制历史的有限窗路径分解 |
| `CompositionPathSource.sourceConditionalPathLaw_disintegrates` / `sourceConditionalPathLaw_isCondKernel` | 同一联合路径测度的真实条件核来源 | 条件的是给定源参数；不自动给出本安全事件的 H 公式 |
| `PositiveEigenInvariantLimit.stationary_limit_of_convergent_positiveEigenstructure` | 变化 Doob 核及不变权重的收敛传递为极限不变性 | 已假设所需收敛；不自动证明生存条件路径的 Q-process 极限 |

名称相近的 `HilbertMeanDoobCore` 等模块处理条件期望 Doob 鞅，不能仅因名称相同就把它们充作 killed 核的 h 变换来源桥。它们的既有概率成果仍然有效，只是接口责任不同。

### 最小实现建议

下一条若选择完整有限窗适配，先证明（2）的**实际前缀质量**，并把 H 定义为同一 Q 的剩余生存函数；然后在正条件前缀上推出（3）–（5）。使用 `pmfExtend_apply` 和原生 `PMF.filter_apply`，不要复制一整套已完成的 K2 终态证明，也不要把（2）放进新结构的假设来跳过来源桥。

Doob 的有限乘积望远镜等式（6）是独立的短代数引理；接上（1）后才能得到（7）与相等条件。当前只需要有限窗，不需要为这项比较新增无限路径体系、重新审计全部 Core 或扩大正在发布的冻结范围。

## 来源身份

精确文件摘要、实际反例计算脚本及本报告摘要由同目录 `REVIEW.json` 绑定。本报告不修改任何生产、消费者、书稿、Git 或原历史收据，不运行 Lean/build/native。
