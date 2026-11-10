# 同一可再生源的两项边界与可选任务分类

核验对象：`main de8efdd7d9009d48cd64c005e209b158f2c66d42` 的本地绑定副本；实际读取六个 `CoreRegenerative*.lean` 源文件、`API_BOUNDARIES.md`、`S0_FREEZE.md` 和当前数学书。六文件 SHA-256 见 `boundary_math_check.json`。没有修改生产源码，没有新增或编译 Lean 定理，也没有访问 Mac、GI 或远端。

结论：第二期严格新生期望差成立；同一健康 θ0 的实际内部程序给出三个公开响应 `(s,b,bq)`，在整个合法参数开放集上秩为三；指定的 2/3/4 层分类成立，但第三层必须是**所有有限未来新生计数联合记录再加入首期真实修复费**。仅 `(B1,R1)` 是三类。

## 可直接并入总论的短证明

### 一次新生响应不足以决定全部未来新生响应

固定任意满足 `Valid p` 的参数

\[
p=(s,\delta,b,\gamma,q),\qquad
0<\delta<s<1,\quad 0<b,\quad b+\gamma<1,\quad
\delta<\gamma,\quad 0<q<1,\quad s+b>1.
\]

从一个 canonical 创始体开始，静默标签固定为 false。每个体此后始终执行自己的真实内部程序，后继忠实继承该程序。令 \(\mathcal P_0\) 为这个单元素初始人口，并定义

\[
B_{t+1}=\sum_{u\in\mathcal P_t}
\mathbf1\{(\operatorname{programStep}(u.\mathrm{body},Z_{u,t})).\mathrm{newborn}
\ne\mathrm{none}\},\qquad t\ge0.
\]

这里 \(B_{t+1}\) 只计该次普查的严格新生槽；续存不计为新生。新生到下一次普查才执行。因此 \(B_1\in\{0,1\}\)、\(B_2\in\{0,1,2\}\)；\(B_2\) 包含第一期所有实际后继在第二次普查产生的新生，既不是第二期总人口，也不是仅由原创始体产生的新生。

记 \(\nu=(1-q,q)\)、\(k_c=s+b\)。三个初态 \(\theta_0H,\theta_0D,\theta_1D\) 的首次内部动作均为 care，故

\[
\mathcal L(B_1\mid\theta_0H)
=\mathcal L(B_1\mid\theta_0D)
=\mathcal L(B_1\mid\theta_1D)
=\operatorname{Bernoulli}(b).
\]

首次实际输出在两种身体类型上的均值行均为 \(k_c\nu\)。θ0 的两行下一次新生概率都是 \(b\)；θ1 的 H 行为 \(b+\gamma\)，D 行为 \(b\)。由同一原始噪声及真实后继的条件期望，

\[
\begin{aligned}
\mathbb E_{\theta_0H}B_2
&=\mathbb E_{\theta_0D}B_2=(s+b)b,\\
\mathbb E_{\theta_1D}B_2
&=(s+b)\bigl((1-q)(b+\gamma)+qb\bigr),\\
\mathbb E_{\theta_1D}B_2-\mathbb E_{\theta_0D}B_2
&=(s+b)(1-q)\gamma>0.
\end{aligned}
\]

严格性由 \(s+b>1\)、\(q<1\) 和 \(\gamma>\delta>0\) 得到。于是相同的一次新生响应不能推出所有有限未来新生计数联合律相同。本结论对每个合法 p 成立，不以存活或修复后成功为条件，也不以外部控制替换内部程序。

### 同一程序的三个公开响应排除共同光滑二维因子

固定同一个健康初态 \(x=\operatorname{programBody}(\mathrm{false},\mathrm{false},\mathrm{false})\)，只运行其内部 care 程序。对同一实际公开收据取三个事件：

1. retained 槽非空；
2. newborn 槽非空；
3. newborn 槽非空，且该 newborn 的公开诊断为 D。

第三项直接可读：`PublicReceipt.newborn : Option Observation` 保存输出身体的两组三位码、主门和 bootstrap；`diagnostic_observedBody` 保证由该观察算出的诊断等于原身体诊断。它不读取静默标签或审计身份。

由实际 36 原子和式，三个事件的概率组成响应

\[
F(p)=(s,b,bq).
\]

以 \((s,\delta,b,\gamma,q)\) 为参数坐标，

\[
DF(p)=
\begin{pmatrix}
1&0&0&0&0\\
0&0&1&0&0\\
0&0&q&0&b
\end{pmatrix},\qquad
\det D_{(s,b,q)}F(p)=b>0.
\]

故 F 在整个合法参数开放集上具有局部秩三。具体合法内点为

\[
p_*=(3/4,1/8,3/8,1/4,1/3),\qquad
F(p_*)=(3/4,3/8,1/8),\qquad
\det D_{(s,b,q)}F(p_*)=3/8.
\]

例如固定 \(\delta=1/8,\gamma=1/4\)，令 \(s,b,q\) 分别在距 \(3/4,3/8,1/3\) 小于 \(1/32\) 的开区间内变动，仍全部满足 `Valid`。

若在 p* 的某个开邻域存在共同 \(C^1\) 映射 \(z:U\to\mathbb R^2\) 和 \(g:V\to\mathbb R^3\)，其中 \(z(U)\subset V\)，使 \(F=g\circ z\)，链式法则将给 \(\operatorname{rank}DF\le2\)，矛盾。对三个分别解码的 \(g_j\circ z\) 亦然，将 \(g_j\) 堆叠即可。

这里排除的是**这一源参数邻域内，同时保持三个响应的共同 C1 光滑二维局部因子**。它不声称排除任意不连续编码，也不否定只保留少数响应、限制在低维参数子族、或近似阈值意义的二维表示；参数变化本身也未被冒称为现实实验已经能独立干预的物理轴。该推导是现有第 23.4 节链式秩必要条件的具体同源实例。

## 可选补充：同一四初态上的 2/3/4 个任务等价类

此段可作为简短例子纳入现有总论，不构成新的本版必过门，也不需要新通用平台。固定合法 p，令

\[
X=\{\theta_0H,\theta_0D,\theta_1H,\theta_1D\}.
\]

每层的等价定义都是“该层要求保留的**完整联合记录律**相等”，并固定上述内部程序协议。

| 要求保留的任务记录 | 精确等价类 | 类数 |
|---|---|---:|
| 仅 \(B_1\) | \(\{\theta_0H,\theta_0D,\theta_1D\},\{\theta_1H\}\) | 2 |
| 对每个有限 \(T\ge1\)，全部 \((B_1,\ldots,B_T)\) 联合律 | \(\{\theta_0H,\theta_0D\},\{\theta_1D\},\{\theta_1H\}\) | 3 |
| 上一层再加入创始体首期真实修复费 \(R_1\)，即全部 \((R_1,B_1,\ldots,B_T)\) 联合律 | 四个单点类 | 4 |
| 加入完整初始公开观察 | 四个单点类 | 4 |

**第一层。** θ1H 的下一次新生概率为 \(b+\gamma>b\)，另外三者为 b，所以恰为两类。

**第二层的合并。** 对同一个原始噪声原子 z，θ0H 和 θ0D 都实际执行 care，且恢复后的代码和主门完全相同。因此

\[
\bigl(\mathrm{retained},\mathrm{newborn}\bigr)
\bigl(\operatorname{programStep}(\theta_0H,z)\bigr)
=
\bigl(\mathrm{retained},\mathrm{newborn}\bigr)
\bigl(\operatorname{programStep}(\theta_0D,z)\bigr).
\]

这里等号比较两个 `Option Body`，并没有比较收费和退款。把同一深度 T 的原始二叉噪声树分别交给两个初态，首次两个槽一致；每个实际存在的槽随后面对相同身体、相同子树和相同内部程序。按 `Population.descendants` 的两槽递归，逐个有限 T 有

\[
(B_1,\ldots,B_T)(\theta_0H,w)
=(B_1,\ldots,B_T)(\theta_0D,w)
\quad\text{对每棵同一噪声树 }w.
\]

同一树律的推前于是相等。这是全部有限联合记录的逐点耦合证明，不只是各时刻均值相同。θ1H 用 \(B_1\) 已与其余分离；θ1D 用上述 \(B_2\) 期望严格差与 θ0 分离，故恰为三类。

“逐点相同”限定为身体后继与所声明的出生记录。完整 `Member` 祖先记录首条边的 `sourceKind`、初始公开 `before`、首期付款及退款并不相同，不能把此证明升级为完整审计或控制商。

**第三层的分离及钱包核对。** 实际内部程序在四初态上的动作／预付 cap／首期修复费为

| 初态 | 动作 | cap | \(R_1\) |
|---|---|---:|---:|
| θ0H | care | 3 | 0 |
| θ0D | care | 6 | 3 |
| θ1H | bloom | 4 | 0 |
| θ1D | care | 6 | 3 |

四者都用同一“旧资本 1＋环境供给 5”的六单位账户实际接受执行。损坏体先付三单位恢复费，再按**恢复前的原诊断行**执行 care；不会在恢复后改读 H 行而请求不可支付的 D/bloom。费用在读生存／出生噪声前已经支付，故即使随后零输出，R1 仍为三。

θ0H 和 θ0D 在相同噪声下退款相差三，但每个实际输出都只携带同样一单位资本，余款归环境，下一期各旧体仍显式获得五单位。这解释了为何首期真实费用可区分它们，而这些不同费用不破坏第二层的后续出生耦合。若改成共享总钱包或让退款差留在后继账户，必须重新分析；那不是本源。

第三层已有的三类中，唯一非单点类 \(\{\theta_0H,\theta_0D\}\) 被 \(R_1=0/3\) 分开，故恰为四类。完整初始公开观察也直接区分四者：H 行备份位区分 θ，主门区分 H/D；已有 `physicalReadout_full_injective` 正是此事实。

特别地，仅保留 \((B_1,R_1)\) 得到的是

\[
\{\theta_0H\},\quad\{\theta_0D,\theta_1D\},\quad\{\theta_1H\},
\]

仍为三类，不能写成四类。全未来分类只适用于固定内部程序的出生计数任务；例如外部请求 bloom 能使 θ0H 出生而 θ0D 被拒绝，因而不能沿用第二层等价为完整允许控制的等价。

## 当前已有 Lean 端点及未新增部分

| 本文所用事实 | 当前准确源码／端点 | 状态 |
|---|---|---|
| 内部请求按原诊断执行，并接受实际付费事务 | `CoreRegenerativeSource.program_request_affordable`, `program_step_executes`, `actual_program_reads_restored_code` | 已有 Lean |
| 允许损伤恢复、输出程序忠实，修复费 H=0／D=3 | 同模块 `restore_programBody`, `repairCost_programBody`, `copied_code_faithful`, `executed_retained_faithful`, `executed_newborn_faithful` | 已有 Lean |
| 原始噪声为合法概率，严格续存／新生均值 | 同模块 `noiseWeight_pos`, `noiseWeight_sum`, `retainedMean_eq`, `newbornMean_eq`, `eventMean_eq_row` | 已有 Lean |
| 实际下一次新生事件律 | `CoreRegenerativeFormation.sourceResponse_true`，及 `sourceResponse_probability` | 已有 Lean |
| 健康体的实际原身份续存概率 | `CoreRegenerativeOneStep.healthy_retainedProbability` | 已有 Lean |
| 实际身份及新生下期执行 | `CoreRegenerativePopulation.descendants`, `newborn_actual_parent`, `descendants_length` | 已有 Lean；`descendants_length` 是总人口，不能叫新生数 |
| 收据公开标记输出及其诊断 | `CoreRegenerativeControlPopulation.PublicReceipt`, `publicReceipt`, `diagnostic_observedBody`；`CoreRegenerativeQuotient.Observation`, `observe` | 已有定义／Lean 桥 |
| 四初态的完整物理读出可区分 | `CoreRegenerativeFormation.physicalReadout_full_injective` | 已有 Lean |
| 第二期严格新生数的期望差及整套 2/3/4 分类 | 上述书面证明与独立 Fraction 核验 | **没有新增专门 Lean 端点** |
| 本源 `(s,b,bq)` 的 Jacobian 秩三与 C1 二维因子阻碍 | 上述书面链式证明与 SymPy 精确计算；复用书第 23.4 节必要性 | **没有新增本源专门 Lean 端点** |

不要把 `treeMean_program_succ` 的后代总数公式或静默标签的合法商定理登记成这里新生计数分类的专门形式证明；也不要把固定任务的三类与连续参数的三维秩混为同一结论。

## 修订前查重与整合建议

1. 初次审阅时，总论第三部分已有形成桥，但没有上述同源第二期差公式；第六部分已有标签商和删诊断反例，但没有精确 2/3/4 任务分类。
2. 第 23.4 节已有共同可微二维因子的秩必要条件及抽象堆叠秩三反例，第 39.60 节已有有限线性分类；新增 `(s,b,bq)` 仅作为当前真实源的具体消费者，不重建通用平台。
3. 初次审阅时形成段的“不同实际程序的未来新生概率不同”宜精确改为“两个程序的健康初态具有不同的下一次新生概率 b 与 b+γ”，避免读成 θ0D 与 θ1D 的下一次响应也不同。
4. 两项必要边界可分别紧接形成桥与表示段。2/3/4 表格和耦合论证作为可选有限例，不升级为本版必过门；正文状态明确标为“书面证明及精确计算；未新增专门 Lean 端点”。

### 修订后复核

协调者随后将有限分类写入同一路径数学书总论第三部分、将 `(s,b,bq)` 写入第 23.4 节。本报告作者重新读取了这两个修订段落：参数范围、全未来联合记录量词、身体槽耦合、审计 ancestry 的首边差异、R1 的真实付款、第三响应的可观察性以及“未新增对应 Lean 端点”的状态均准确，数学复核通过。

仅建议两处措辞精化：“输出资本也都为一”改成“每个实际输出的资本均为一”；第三响应处可点名 `PublicReceipt.newborn` 与 `diagnostic_observedBody`，并将共同因子的正则性明确写为 C1。二者不改变所证结论。

## 独立精确核验

运行 `python boundary_math_check.py > boundary_math_check.json`，退出码 0。脚本按真实位恢复、原诊断执行、36 原子和六单位付款重建本次有限核验，并使用 Fraction 计算有限联合律。

在合法内点 \(p_*\)：

| 初态 | \(\mathbb E B_1\) | \(\mathbb E B_2\) |
|---|---:|---:|
| θ0H | 3/8 | 27/64 |
| θ0D | 3/8 | 27/64 |
| θ1H | 5/8 | 65/96 |
| θ1D | 3/8 | 39/64 |

差为 \(3/16\)。枚举前 1、2、3 次普查的完整出生计数联合律得到 2、3、3 类；再加入 R1 得四类。全部 36 原子上的 θ0H／θ0D 身体槽逐点相等及 0／3 付款均已核对。全部有限时域的结论来自前述递归证明，不以枚举到第三期替代无限量词。

三个公开响应在内点为 `(3/4,3/8,1/8)`，符号 Jacobian 的指定子式恰为 b。精确输入、源码哈希、有限联合律和断言状态均保存在结果 JSON 中。
