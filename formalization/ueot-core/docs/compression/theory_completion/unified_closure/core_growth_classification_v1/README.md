# Core 严格正概率域的增长参数分类

本单元完成用户授权的五项出口后停止。原 Core 的内容状态继续为 **CLASSIFIED_CORE_CLOSED**，经验状态继续为 **UNVERIFIED**。PR #446 的定本冻结与旧 Valid 合同保留；本目录是其后的有限数学扩展，未重开 S0—S6。

基线为实际 main 的 827be44cd14c63d9d13e33493eee07c5f1afa5fe（tree 829283dc24c71826537bd4e1698625220878097d）。新结果使用相同的原始程序、身体、公开观察、六单位事务、人口普查时钟、stop、真实拒绝、身份与忠实遗传。

## 1. 精确结果

仅要求原 36 个原子全部严格为正的概率条件：

\[
0<\delta<s<1,\quad b>0,\quad\gamma>0,\quad
b+\gamma<1,\quad0<q<1.
\]

这里不包含零概率、q=0 或 q=1 等退化端点。旧 Valid 精确等于此基本域再加 \(\delta<\gamma\) 与 \(s+b>1\)，旧定义未修改。

设
\[
k_c=s+b,\quad k_b=s-\delta+b+\gamma,\quad
\lambda_0=k_c,\quad\lambda_1=(1-q)k_b+qk_c.
\]
对任意有限非空 canonical 初始人口，原完整允许历史策略类的最优期望人口指数因子为
\[
\boxed{\rho_*=\max\{1,\lambda_0,\lambda_1\}.}
\]

完整菜单中的 D/bloom 行仍是实际拒绝的 \((0,1)\)，stop 仍为零。确定达到策略在 H 选择总产出较大的动作；当 \(\max(\lambda_0,\lambda_1)\ge1\) 时 D/care，否则 D/bloom 原拒绝。该策略只读已有公开诊断，是旧 Policy 的一个成员。

两个既有遗传内部程序分别从自己的受损 canonical 创始体付费修复，达到边界恰为：

| 既有程序 | 达到原全策略最优因子的充要条件 |
|---|---|
| θ0=(care,care) | \(\gamma\le\delta\) 且 \(k_c\ge1\) |
| θ1=(bloom,care) | \(\gamma\ge\delta\) 且 \(\lambda_1\ge1\) |

优势平手与增长临界等号均保留。两程序都亚临界时，它们均未达到原拒绝基准1；这不排除先真实修复一次、再使用允许历史控制达到1。两个不同程序的字面 Body 不相同；各自的修复与增长判断绑定同一具体身体、原账本和原程序。

## 2. 形式合同与完整比较类

HasExpectedGrowth 是“存在正常数 lo、hi，对全部自然数 n 有
\(lo\,\rho^n\le E N_n\le hi\,\rho^n\)”的有限双边合同。

UniformExpectedUpper 的一个常数同时覆盖全部原 Policy 和全部 n。原 Policy 继续允许全部公开收据历史、实概率及同代成员之间相关的联合请求；当前请求仍在当前世界噪声之前选定。没有假定每个竞争策略都存在增长极限或双边指数界。

实际人口消费者直接复用原 State、generation、next、branchWeight 和 populationExpectation。新证明只更换正权重与参数条件，没有创建替代人口过程。正权重的全菜单行界和所选行等式经原有限历史工具给共同上界和正双边界；正幂比无界进一步证明 rho 是共同上界的最小正底数。

正文的正 n 次根极限与任意策略 limsup 上界是这些有限合同的书面分析推论。没有另称专门的 Lean 根极限端点；没有新的无限路径空间或 Mathlib Martingale 实例。

### 新增生产端点

以下文件位于同一 UnifiedClosure 源目录，均由原公共入口 CoreTheoryClosure 导出。

| 模块 | 本轮承担的结论 |
|---|---|
| CoreRegenerativeGrowthClassification | ProbabilityValid；旧 Valid 的精确条件拆分；原36原子正性；最优率公式；分段正势；全部实际请求行界与达到；两个率的代数 iff |
| CoreRegenerativeGrowthPopulation | 原完整 Policy 上界；公开可执行达到策略；两个程序各自的指数界；继承程序逐分支执行桥；各自受损创始体及实际收费 |
| CoreRegenerativeGrowthAttainment | 正指数唯一性；全策略共同上界的最小底数；两个程序达到 iff；同一受损身体的真实修复与增长绑定；亚临界失败；旧 Valid 特例 |

关键可检索端点：

- valid_iff_probability_advantage_supercritical
- optimalRate_formula、actual_one_step_value_le、actual_selected_one_step_value_eq
- optimal_population_upper、optimal_hasExpectedGrowth
- programPolicy_positive_branch_is_internal、damaged_founder_paid_repair
- optimalRate_isLeast_uniform_upper
- false_program_attains_iff、true_program_attains_iff
- same_damaged_program_repairs_and_attains_iff
- subcritical_existing_programs_do_not_attain、old_valid_damaged_program_attains

任意 canonical State 上的 programPolicy 首先是公开选择器。称为实际遗传内部程序时，使用 founder_program、原 reachable_program 与 programPolicy_positive_branch_is_internal 串接；受损创始体端点已固定这一应用。原 CoreTheoryClosure 的旧声明未改，只新增导入及范围说明。

## 3. 验证证据及范围

- [最终验证](VALIDATION.json)与[源绑定](SOURCE_BINDING.json)：三个新增模块、原公共入口及[边界消费者](GrowthClassificationCheck.lean)的实际 Mac Lean 检查；工具链与依赖复用原冻结环境，未重跑历史全工程。
- [检查回执目录](checks/)：实际命令、源码 SHA-256、退出码、耗时和公理输出。15个关键端点仅依赖 propext、Classical.choice、Quot.sound，未出现 sorryAx 或 Lean.ofReduceBool。该结论限定于列出的端点，不改写旧 PR443 已披露的数值信任。
- [独立数学推导](BOUNDARY_REVIEW.md)与[形式接口交叉审查](GROWTH_ATTAINMENT_REVIEW.md)：分别登记作者责任、读取身份与实际检查层次。
- [精确探针](check_growth.py)及[有理数结果](results.json)：哈希锁定原字面事务检查器和六个原来源文件。八组参数、6,912个完整菜单局部事务、另2,304个内部程序事务、T=0—12的精确有限递推。协调端独立重跑结果逐字一致。该 Python 运行不是新的 Lean 原生执行或自然经验验证。
- [数学独立读者](INDEPENDENT_MATH_READER.md)与[哲学独立读者](INDEPENDENT_PHILOSOPHY_READER.md)：只依据对应主文，列明阅读范围、最终指纹和必要局部修订；不是外部学术同行评议。
- [PDF 导航核对](PDF_NAVIGATION.json)及[新增页面审查](VISUAL_REVIEW.json)：两书更新对应段落并重新导出；只声称记录内实际选页的目视检查，不声称整书逐页重审。
- [交付清单](MANIFEST.json)：绑定本次产物，不改写旧冻结包的历史清单。

### 精确反例

在 p=(3/5,1/10,3/10,1/2,1/5) 上，care 本身的因子为9/10，θ1与全策略最优因子为61/50。D起点两期全策略最优为279/250，固定θ1为549/500；二者不能混记。

在 p=(2/3,1/8,1/4,1/4,1/3) 上，θ1与全策略的因子均为1，但同一D起点的内部期望人数在每个正期限恒为11/12，拒绝策略逐路径为1。因此指数达到不等于逐期人数最优。

## 4. 两书与停止条件

数学书在定本核心总论第四部分增加“严格正概率域上的精确增长与内部达到”，并限定第五部分仍用原反馈合同。哲学书仅在第七、十一章及对应脚注说明恢复、机制排序、评价期限和规范责任；没有把增长最优化替代全部目的论。

| 五项出口 | 交付 |
|---|---|
| 参数责任拆分 | 新 ProbabilityValid 与旧 Valid 的等价拆分 |
| 完整实际源菜单精确界 | 真实拒绝、stop、两种正势与 max 公式 |
| 原全历史人口消费者 | 共同上界、可执行达到与最小统一底数 |
| 两个内部程序的达到／失败 | 两个 iff、真实程序桥与各自受损创始体修复 |
| 两书消费和相称验证 | 对应正文、独立读者、正式检查与PDF选页证据 |

五项完成即停止。没有扩大选择反馈常数、加入共享钱包或新遗传程序，没有启动未知机制学习、动作特有损伤律、几乎处处增长、无限谱系存活或一般可约 Perron 平台。相对既有分枝控制研究的完整新颖性评议仍属于外部学术工作；本单元的具体贡献是同一实际来源约束下的准确适用域、达到与失败分类。
