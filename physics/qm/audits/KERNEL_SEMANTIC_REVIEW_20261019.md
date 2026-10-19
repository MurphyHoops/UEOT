# UEOT-QM 内核：Lean 与 Python 语义交叉审查

审查日期：2026-10-19（UTC）  
审查快照时间：2026-10-19T14:19:27.986475+00:00  
范围：五个 QM Lean 模块、五个 Python 包文件、统一 Lean 入口、公理审计脚本、工具链/依赖清单及独立测试源码。  
审查性质：源码语义交叉审查与本地精确回归复核；未修改被审产品或 Lean 文件。实际 GitHub CI、精确提交对应关系及公理输出由主线程 root 确认并另存回执。  
透明性说明：本审查者参与了四个 Python runtime 模块的实现；Lean、certificates.py 和独立测试由其他协作者提供。此文是跨实现的语义复核，不应描述成完全独立于所有实现作者的第三方审计。

## 1. 验收结论及可发布表述

**在已声明的有限维操作量子扇区内，当前 Lean 证明源码与 Python 的计算语义一致；没有发现新的数学阻塞。Python 已通过本审查者独立重跑的 32 项测试，但 Python 实现没有经过 Lean 的程序正确性验证。**

五个 Lean 模块已经给出具体数学定义和证明体，覆盖密度算子合法性、Kraus 分支、任意有限辅助系统的放大正性、所有有限词的响应商、正概率后验、零证据的 Option 更新以及条件式标量 transport。它们不含一个“假定未来更新已经成立”的量子结构字段。可接受的机器证明状态仍须以匹配本报告源码快照的 Lean 构建和公理回执为准。

Python 提供可实际执行的 Gaussian-rational 矩阵、完整 weighted Kraus instruments、精确 W* 闭包、有限基坐标更新、固定词与有限因果树记录律以及有限覆盖证书。当前没有以下程序细化定理：

- Python 的 Fraction/QComplex/Matrix 运算与 Lean ℝ/ℂ 运算逐项对应；
- Python 的 principal-minor PSD 判定器与 Mathlib PosSemidef 等价；
- Python 的高斯消元、闭包循环、有限基及 pullback 矩阵正确实现 Lean 的 all-word response；
- Python 的 finite-tree 解释器、指纹或错误处理经过 Lean 验证。

建议的发布措辞：

> 已实现一个有明确物理输入和范围的有限维精确操作内核，并提供相应量子操作、全有限词响应商及条件式 transport 的 Lean 证明源码。实际机器通过状态附精确提交和公理回执；可执行 Python 部分通过独立物理例、负例和有限回归。W* 算法与 Python 实现的 Lean 细化验证仍是后续工作。

不应使用“全部 Python 已由 Lean 验证”“QM 全理论已形式化”“通过少量协议即认证 diamond 距离”等表述。

## 2. 逐模块数学审查

| Lean 源与关键声明 | 证明源码实际支持 | Python 对应及边界 |
|---|---|---|
| Basic.lean：Density、mass_nonneg、mass_eq_zero_iff、normalize | 所有有限复矩阵中的 PSD、trace-one 密度算子；PSD 的质量非负；PSD 质量为零当且仅当矩阵为零；正质量归一化仍为合法密度算子 | algebra.py 在 Q(i) 上计算，并通过全部 principal minors 检查 PSD；支持状态维数为 1–4。该判定算法的细化证明尚未建立 |
| Instrument.lean：krausMap_posSemidef、trace_krausMap、sum_probability、probability_le_one、posterior、zero_probability_iff_zero_branch | 从 Kraus 算子和完整性等式推出分支 PSD、归一化概率、概率上界、合法正概率后验及零概率/零分支等价 | instrument.py 从非负有理权重与精确完整性检查构造操作；需要第 3 节的 weighted-to-unweighted 和标签/索引适配 |
| Instrument.lean：ancillaKrausMap_posSemidef、ancillaKrausMap_entry | 对任意有限辅助索引 ν 和任意联合 PSD 输入，K⊗I 的 Kraus 放大保持 PSD；逐项等式确认这确实是原映射的 identity amplification | Python 测试了支持维数内的 Bell 态、非 CP 的 partial-transpose 负例及纠缠输入上的 damping；测试不是对任意辅助维数的枚举证明 |
| Operational.lean：recordOperator、totalRecordMass_density、existsUnique_responseDecoder、response_posterior、existsUnique_closedReachableUpdate | 实际 Kraus 词响应非负；固定有限控制序列的总记录质量为 1；全有限词响应商上的唯一下降；正概率条件继续律；Option 更新的纤维相容与同一 reachable 状态类型内的闭合下降 | predictive.py 使用有限 W* 基坐标实现该语义的候选有限表示；有限维张成、basis 求解与程序细化没有出现在当前 Lean 文件中 |
| Transport.lean：scalarBudget、scalar_transport_certificate | 在明确非负性、初值和逐步递推前提下，实际误差被递推预算覆盖；实际调用 Core weighted_chain_bound | certificates.py 计算同一形式的有理递推，并可检查给定有限数值轨迹；没有从有限协议比较自动建立量子距离的 uniform recurrence |
| Selector.lean：selects_three_without_atomicity 及反例 | 明确整数方程和弱筛选预算下的 (Nc,Nf,k)=(3,3,1)，无需 atomicity；若移除相关整数前提，有展示的反例；整包复制仍保留异常方程 | 属于并行的条件整数定理，不是 W* 运行算法的正确性证明，也没有构造物理 gauge parent 或完整粒子模型 |

Basic 的 Density.positive 和 Instrument.complete 是合法扇区与操作输入的规格条件。待证目标是由这些条件推出的概率、后验和继续律；不是把目标本身作为输入假设。运行时则实际检查矩阵和完整性条件，不要求调用者填入“已证明 CP/已证明递归闭包”等结论字段。

## 3. Python 与 Lean 的数域及索引适配尚未形式化

### 3.1 非负权重的 Kraus 表示

Python 的一个 outcome 使用

\[
\Phi_o(X)=\sum_k w_{o,k}K_{o,k}XK_{o,k}^{\dagger},
\qquad w_{o,k}\in\mathbb Q_{\ge0},
\]
并检查
\[
\sum_{o,k}w_{o,k}K_{o,k}^{\dagger}K_{o,k}=I.
\]

Lean 的 Instrument 使用普通复 Kraus 家族
\[
\Phi_o(X)=\sum_k L_{o,k}XL_{o,k}^{\dagger},
\qquad \sum_{o,k}L_{o,k}^{\dagger}L_{o,k}=I.
\]

正确数学桥是先把 Q(i) 嵌入 ℂ，再取
\[
L_{o,k}=\sqrt{w_{o,k}}\,K_{o,k}.
\]
这同时保持 branch 和 completeness。零权重给零算子。平方根不必仍在 Q(i) 内；Lean 允许一般复数，而 Python 用有理 weight 直接计算相同结果，避免不必要的无理数近似。

此桥在数学上成立，但当前没有对应的 Lean weighted adapter、Python 数据反射器或程序细化证明。Hadamard 的整数矩阵配 weight=1/2 是有效实例，不意味着该实例已经自动被导入并由 Lean 核心检查。

### 3.2 动作、结果和 Kraus 项的类型

Python 每个动作有自己的有限字符串 outcome 集合，每个 outcome 的 Kraus 项数也可以不同；还允许显式空项 outcome 表示不可能事件。

Lean 使用共同的有限 O 和 κ，所有动作的 instruments 具有同一个类型。嵌入 Python 库时需要固定共同结果/项索引，补零到共同 O、κ，并明确 Python 实际记录与补零后 Lean 记录之间的对应。补出的非法动作/结果组合只应有零权重，不应增加真实实验结果。

这是实现适配问题，不是现有 Lean 命题的错误；但没有补齐它之前，不能直接声称两个程序对象是同一个 Lean 值。Lean 的动作类型 A 本身不要求有限；W* 的可计算闭包算法另外要求有限动作/结果字母表。

## 4. 全有限词响应商与运行时 W* 的关系

### 4.1 Lean 已给出的语义

Operational.lean 定义了时间顺序一致的实际 Kraus 词作用：

\[
\operatorname{recordOperator}([e_1,\ldots,e_n],\rho)
 =\Phi_{e_n}\circ\cdots\circ\Phi_{e_1}(\rho),
\]
\[
r_\rho(w)=\operatorname{ReTr}(\operatorname{recordOperator}(w,\rho)).
\]

responseSetoid 以完整函数相等 \(r_\rho=r_\sigma\) 定义不可区分性。existsUnique_responseDecoder 实际使用 Core 的 quotient descent；它证明的是响应对商的唯一下降，没有声称复 Hilbert 空间来自这个商。

所有有限词对 prefixing 封闭。由实际 posterior 定义和线性 trace 推出的 response_posterior 为

\[
r_{\rho|e}(w)=\frac{r_\rho(e::w)}{p_\rho(e)},\qquad p_\rho(e)>0.
\]

这提供了 recursive congruence 所需的原因。当前文件没有把充分性或输入纤维相容直接存成待调用的“真值字段”。

### 4.2 W* 是这个语义的候选有限表示

Python 以
\[
W_0=\operatorname{span}_{\mathbb R}\{I\},
\quad
W_{n+1}=\operatorname{span}_{\mathbb R}
\left(W_n\cup\{\Phi_e^*(E):E\in W_n,e\}\right)
\]
迭代。它每轮固定现有基，实际求出新 pullback，以 Fraction 高斯消元决定是否增维；不把“闭包成立”当成调用者输入。

需要用于连接两层的一般数学论证是：

1. 有限词效应满足 \(E_{[]} = I\)、\(E_{e::w}=\Phi_e^*(E_w)\)。
2. trace duality 给 \(r_\rho(w)=\operatorname{Tr}(\rho E_w)\)。
3. 按词长归纳，\(W_n\) 是长度至多 n 的词效应的实张成。
4. Hermitian 空间实维数为 \(d^2\)，包含 I 的严格增维最多 \(d^2-1\) 次；一次不增维即给 pullback 不变性。
5. 因而 \(W_*=\operatorname{span}_{\mathbb R}\{E_w:w\text{ 有限}\}\)，从而
\[
r_\rho=r_\sigma
\quad\Longleftrightarrow\quad
\operatorname{Tr}((\rho-\sigma)B_j)=0\quad\forall j
\]
对任意 W* 基成立。

这些是连接当前两层的明确证明义务。当前五个 Lean 模块中未定义 Heisenberg effect 闭包、W_n、W*、有限 basis、Gaussian elimination 或上述 iff；所以不能把 existsUnique_responseDecoder 的机器通过改写成“W* 算法已被 Lean 证明”。

### 4.3 Pullback 矩阵与坐标更新

运行时选 \(B_0=I\)，定义 \(x_j=\operatorname{Tr}(\rho B_j)\)，并实际计算唯一系数

\[
\Phi_e^*(B_j)=\sum_i A_e[j,i]B_i.
\]

因此应满足
\[
y=A_ex,\qquad y_0=p_\rho(e),\qquad
x'_j=y_j/y_0\quad(y_0>0).
\]

代码按此方向排列矩阵，独立测试还逐个 basis effect 重构 pullback，检查复数共轭与行/列方向，并将坐标继续律与闭式概率、直接矩阵记录律比较。

这里的响应维数包含恒定 trace 坐标。它不是“另一个更小 Hilbert 空间的维数”，也不是在任意受限协议语言或实际可达状态子集上的自动最小维数。代码已经显式排除这些外推。

### 4.4 因果树与更小协议类

Python 的 ProtocolNode 是有限确定性 outcome-adaptive 控制树，要求每个节点列齐全部 outcomes，包括不可达分支；两个解释器计算完整 action/outcome 叶记录律。

全词响应相同意味着同一确定性有限因果树上每一条叶记录的概率相同，这是可作树归纳的数学推论。但当前 Lean 文件只直接形式化全词 response 和固定控制序列的总质量，没有定义 ProtocolNode 或提供其总质量/响应商保持定理。随机控制策略也没有独立的运行时 policy 类型或 Lean 树解释器。

当前 W* 只覆盖固定时齐库任意有限组合的协议类。如果时刻、自动机、资源或剩余时域限制了可行动作，应保留那些协议状态，重新证明分层或增广后的表示；不能把现有全字母表闭包称为任意更小协议库的最小表示。

## 5. Option 零证据：正确的总/部分更新边界

以下 Lean 命题具有实质内容：

- zero_probability_iff_zero_branch：PSD 分支上 \(p=0\iff\Phi_e(\rho)=0\)；
- nextResponse_eq_none_iff：返回 none 当且仅当事件概率为零；
- nextResponse_eq_of_response_eq：全词响应等价的状态具有相同 Option 结果；
- nextResponse_inputFiberCompatible 与 existsUnique_reachableResponseUpdate：使用已证明的量子纤维相容，调用 Core 的 reachable 下降。
- nextReachableResponse_map_val 与 existsUnique_closedReachableUpdate：成功分支携带实际 posterior 的可达性见证，忘记见证与原 response 接口一致，并下降到输入/成功输出属于同一 reachable 类型的接口。

负概率不会被混入 none 分支的解释，因为合法 density/instrument 的非负性已先证明。正概率 posterior 使用一次归一化；零概率分支没有被任意指定一个物理 density。

Python 的密度路径使用未归一化 branch 组合，最后取 trace；坐标路径使用归一化后验并独立累计记录质量。因此没有 double normalization。坐标分支 p=0 时还检查全部未归一化响应均为零，再返回 None。

当前 Lean 同时保留裸 response 输出的接口和加强后的闭合接口。前者为

\[
U:\operatorname{range}(r)\to(A\times O)\to
\operatorname{Option}(\operatorname{Response}(A,O)),
\]

新加入的 nextReachableResponse 将正概率 posterior 作为实际 range witness，existsUnique_closedReachableUpdate 则给出

\[
U_{\mathrm{closed}}:\operatorname{range}(r)\to(A\times O)\to
\operatorname{Option}(\operatorname{range}(r)).
\]

因此成功输出已属于下一步能够直接使用的相同抽象状态类型。nextReachableResponse_map_val 证明忘记可达性见证后恢复原 nextResponse；两个接口的条件化语义相同。此前指出的 range 输出包装问题已在本次最终快照中修正，不再列为未完成项。它仍然是 all-word 函数响应上的抽象闭合接口，并非 W* 有限基程序的细化证明。

运行时 EncodedState 只通过 encode/update 工厂生成；context_fingerprint 检查避免在不同响应基或协议上下文中复用坐标。fingerprint 不是任意外部向量属于物理响应像的证明，也不是物理 gauge 等价的 canonical hash。不同 Kraus 分解即使实现同一通道，也可以得到不同指纹。

## 6. 任意有限 ancilla：已经跨过单系统正性的边界

ancillaKrausMap_posSemidef 对任意有限 ν 和任意联合 PSD 矩阵 X 证明

\[
\sum_k (K_k\otimes I_\nu)X(K_k^\dagger\otimes I_\nu)\succeq0.
\]

X 没有被限制成 product state。ancillaKrausMap_entry 又逐项识别该联合映射与对辅助指标 block 施加原 krausMap 的结果。两者结合，确实覆盖 Kraus 形式的任意有限 identity amplification 正性，避免把单系统 positivity 假冒成 complete positivity。

仍需区分以下范围：

- 当前声明使用具体矩阵函数，没有打包完整的抽象复线性 CP/CPTP 类型或 Choi 等价定理；
- 源码未单独构造 ancilla Instrument 并证明其全部 trace-preserving completeness 运输；相应代数后果可进一步补齐；
- 任意有限辅助系统的数学命题不等于 Python 运行时可以处理任意维数；
- 没有涉及无限维辅助系统、trace-class 扩张、无界生成元或连续变量 CCR；
- Python 的 Bell partial transpose 负例与纠缠 damping 正例是有区分力的测试，但其通过本身不是“任意 ancilla”的证明。

因此可将 Lean 候选命题描述为“任意有限辅助系统下的 Kraus 放大正性及其身份识别”，不要把它缩成单系统正性，也不要扩成已经建立整个无限维量子操作库。

## 7. Scalar transport 与有限协议证书

### 7.1 Scalar transport 的严格对应

Lean 与 Python 使用同一标量递推：

\[
b_0=b_{\mathrm{init}},\qquad
b_{t+1}=L_tb_t+\epsilon_t.
\]

Lean 的 scalar_transport_certificate 明确要求初值、误差和系数非负，初始 \(e_0\le b_0\)，以及所有相关步骤的
\[
e_{t+1}\le L_te_t+\epsilon_t.
\]
然后得到 \(0\le e_t\le b_t\) 和 \(b_t\ge0\)。

证明实际调用 Core weighted_chain_bound，但使用的是有向标量差 actual−budget，不是假称它是一个量子距离。forcing term 已纳入预算递推，Core 局部 residual 使用零上界；这没有重复计算 \(\epsilon_t\)。

Python transport_budget 只计算条件式上界。verify_transport_trace 还实际检查有限轨迹的初值和每个局部前提，不会因轨迹碰巧落在宽松全局包络内而放过局部前提失败。

Lean 用全自然数序列、Python 用有限 Fraction 列表；有限输入可在数学上作适当零延拓后应用定理，但列表/数域的细化映射尚未形式化。当前没有 trace-distance/diamond contraction 证明，没有通过一份有限协议证书自动建立所有状态上的 Lipschitz 前提。

### 7.2 有限覆盖、TV 与后选择

certificates.py 的有限比较指纹绑定两侧库、完整准备矩阵、协议名称与完整树结构。TV 在双方支持集并集上补零，先验证概率合法性。覆盖范围始终是已给定的准备对和有限因果树。

后选择要求双方事件质量严格正，精确计算条件 TV，并提供保守上界
\[
\min\!\left(1,
\frac{2\,\mathrm{TV}(P,Q)}{\min(P(E),Q(E))}
\right).
\]
这不是事件无关的收缩证书。上述 TV、条件 TV、有限覆盖和指纹功能没有对应的当前 Lean 证明，属于运行时精确计算与独立测试层。

此前发现的 1100 层合法单 outcome 因果树在指纹递归展开时触发 RecursionError，已改为确定性的 BFS 平坦节点表。当前源码不会递归序列化子树，并在独立重跑的正式测试中通过该 1100 层案例。该修正没有改变记录概率的数学定义。

## 8. 本轮验证证据与剩余验收门

本审查者完整阅读当前五个 Lean 模块、五个 Python 文件和 32 项测试源码，并独立执行已有测试：

- tests_run = 32；
- failures = 0；
- errors = 0；
- 当前环境用时约 0.396 秒；
- 包括闭式 H/S/Z 概率、复相位、全部 principal minors 的负例、Bell partial transpose、纠缠 damping、记忆相关负例、W* pullback 重构、坐标/矩阵记录律、零分支、跨上下文、有限覆盖、局部 transport 失败、rare-event postselection 和 1100 层协议序列化。

这些测试具有独立的闭式物理例及负例；其中直接矩阵/坐标一致性检查仍共享底层精确矩阵算术，不能冒充完全独立的程序语义证明。有限测试数量也不是一般定理数量。

本审查没有运行本地 Lean 编译，也没有把 scripts/AxiomAudit.lean 的源码当成其运行输出。机器验收必须由 root 对以下事项提供精确提交的 CI 回执：

1. 五个模块及统一 UEOTQM 入口实际导入、构建通过；
2. 使用指定 Lean 4.33.1 和锁定的 Mathlib/Core 依赖；
3. 公理审计的实际输出已检查，不能只凭源码未写 sorry 就宣称所有依赖无未闭合证明；
4. 回执对应本报告列出的源码哈希，或明确列出后续修改并重新核验。

在审查过程中，Operational.lean 新增了四个 closed-reachable 相关 theorem；公理脚本最初未同步列入它们。最终快照已补齐：五模块静态枚举的 56 个 theorem 均有对应审计目标，另包含 normalize、posterior 和 nextReachableResponse 三个承载证明的构造，共 59 个目标。此处确认的是脚本覆盖完整性，不代替实际运行后的公理结果。

后续最直接的形式化工作是把第 3 节的数域/权重/索引适配、第 4 节的 W* 张成与坐标 iff、finite-tree 解释器，与已给出的 range-valued Option 更新打通。程序层再单独选择可审计反射、证明携带的矩阵/闭包证书，或真正的程序细化路线。当前没有必要把这些尚未完成的工作包装成已交付结果。

## 9. 源码 SHA-256 快照

下列路径相对于仓库根目录。哈希为本次审查直接读取文件字节所得；报告正文自身不纳入此表。若任何文件在本快照后改动，相关构建与审查对应关系须重新确认。

| 源文件 | SHA-256 | 行数 |
|---|---|---:|
| `formalization/ueot-qm/UEOTQM/Basic.lean` | `db38c8dc2b873d5c784460146badcca889a37f2daf23c73bfaadce67eaf0d16e` | 82 |
| `formalization/ueot-qm/UEOTQM/Instrument.lean` | `4d848a9dbe7f5335e327ce659214cf3672e94dfaac3a4dd783473ee008ddd230` | 139 |
| `formalization/ueot-qm/UEOTQM/Operational.lean` | `0bae3c96b1facca3f51fe9189a6e05efeb1b532c29cb5854d860f76878162012` | 237 |
| `formalization/ueot-qm/UEOTQM/Selector.lean` | `0aa261fcd171e8985889067bb348abe6d84e486be1b918a3cdd6d3e951fdcbca` | 134 |
| `formalization/ueot-qm/UEOTQM/Transport.lean` | `e117c7904b6f8c755d5a35c25d2398fdbf727e4d90987096093e2b6423287f84` | 90 |
| `physics/qm/kernel/ueot_qm/__init__.py` | `89bebfc7b1a3954795d3dd743251d3fb06891b848dda731868d6525820c0c1bf` | 47 |
| `physics/qm/kernel/ueot_qm/algebra.py` | `1a5ce84eb0ce42d16c3e7460dc8af88b0923d47393d681ffd821251ed9397653` | 343 |
| `physics/qm/kernel/ueot_qm/certificates.py` | `b78421e91a72fa875fa9bcb0a6939752812f1399f97e1e0665cd2d7effbacc3f` | 219 |
| `physics/qm/kernel/ueot_qm/instrument.py` | `52cdbccd01bcb7dd231f33fa48dabb3ca717fea7fdcca47982f7e8eb04692757` | 319 |
| `physics/qm/kernel/ueot_qm/predictive.py` | `5eacaae2ba7c8b2d18b86734feed8cbd73744665fbfc4059582c0d70ee10844b` | 265 |
| `formalization/ueot-qm/UEOTQM.lean` | `8a3089b1e77dc8bc4f9214bba0b5956877e7b236c45429e5de237edf8a4b87b7` | 6 |
| `formalization/ueot-qm/scripts/AxiomAudit.lean` | `300bcc0eb0f590f60274af9b475f83ee54f38aec79411e81f21b2b161335d216` | 63 |
| `formalization/ueot-qm/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` | 1 |
| `formalization/ueot-qm/lakefile.lean` | `ad870bfd6d91841f30d37e90a2738a69b35696f43709dbf788189874b1c6b805` | 11 |
| `formalization/ueot-qm/lake-manifest.json` | `c4c658c455aaca9504eee020c16cb2fcec375b1c5d9a014adcf8f3f40897d4ff` | 127 |
| `physics/qm/kernel/tests/test_kernel.py` | `479e4457e19094a78ddd759a1e9016b5ee9ad05af7741bd62b1780fc0d722108` | 397 |

依赖配置记录：lean-toolchain 为 leanprover/lean4:v4.33.1；lakefile.lean 通过 ../ueot-core 消费 Core；lake-manifest.json 的 Mathlib 固定 revision 为 0df444a360eaa60ab8c11dca51a86af692955474。这些是本地配置事实，不等于本审查已验证远端 CI 使用了它们。

## 10. 最终范围结论

本次可以验收为：**具体量子数学证明源码、可执行精确操作内核、带范围的有限证书和独立测试已经形成相互可对照的工作切片。**

尚不能验收为：Python 经过 Lean 验证；W* 高斯消元闭包算法已经形式化；所有适应策略和无穷过程均有机器证明；有限测试给出任意输入、任意协议或 diamond 距离保证；通用 UEOT 已推出复 Hilbert、Born、ħ、完整规范模型或自然界三代。

