# B：原审计任务完成性与三组核心数学贡献的精确比较

日期：2026-11-13。作者：本轮原生审查子智能体 B。阶段：独立首审完成；交叉审查另行记录。

## 0. 结论先行

**原 B 审计所要求的必要数学整改已经完成。当前没有证据要求重开已完成的 Core 数学合同、再跑同一批 Lean 或增加生产定理。** P-CTL-01 的折扣条件勘误已入 main；D3 已有真实的固定版本定向编译和类型／公理查询，并由 PR #462 正式采用。旧报告中“尚未新跑 Lean”是前一阶段的历史事实，不是当前仍未完成的责任。[E1-S；复用原 E1-R]

本轮为 D4 增补了三组可检查的数学对应，而不是只增加参考文献：

1. **预测充分性：全文级比较。** 在明确的平稳有限字母过程及可测条件核的交叠类，UEOT 的逐协议因子化与因果状态的预测充分性／最小表示原则对应。原理已有 Shalizi–Crutchfield 的先行结果；UEOT 的依赖目标空间、显式可测核和共同零集接口具有形式化组织价值。
2. **精确控制商：全文级比较。** 在共享有限动作、状态奖励的交叠类，UEOT 的满射商及奖励／转移闭合字段，与 Givan–Dean–Greig 的随机双模拟商相互转换；Bellman 交换、最优值保持和最优策略提升是已有数学。
3. **再生增长：全文级的一般矩阵结构比较，加具体源内桥的独立核对。** 本文严格给出实际再生源的两类型行族、达到的正权重证书、完整允许联合历史策略的期望上界及最优底数，并将矩阵层准确代入 Nesterov–Protasov 的非负 product-family Theorem 4。该一般谱增长结构已有先行；本文也明确 JSR 数值等式不自动给最优底数处的全时常数界。**Pliska／Rothblum–Whittle 仍只取得原刊摘要，其完整定理包含关系未完成验证。** 不把后者摘要或自己的有限模型推导冒称其全文复核。

准确完成数量是 **3 组具有可取得一手全文支撑的精确数学层比较**：预测表示、精确控制商、product-family 谱增长；每组都保留与 UEOT 全接口的差异。不是“UEOT 三套完整理论已与三篇论文逐字等价”，也不是“Pliska／Rothblum–Whittle 两篇全文已经读完”。文献访问限度不产生 Core 数学矛盾，不阻止既定范围的 A 冻结。特定机制组合、参数分类和证明工程的全球优先权仍为 **NOT ESTABLISHED**。[E1-L / E1-S；优先权 U]

## 1. 本次独立刷新与证据层级

### 1.1 当前现场

B 本次独立通过 GitHub 连接器读取 main、两项 PR、提交差额及开放 PR 列表，未仅引用主审转述。

| 项目 | 本次结果 |
|---|---|
| 正式仓库 | https://github.com/MurphyHoops/UEOT |
| 当前 main | `ab4862db08bae9333f422f7bdbba490f8c1ce0df` |
| 当前树 | `c921e8ada008474c0cbf402ba5cca45b9cf41427` |
| PR #461 | 已合并，2026-11-13 08:54:41 UTC；合并提交 `6dd6a3bc13e26f41eddc10ee4d2f39fa1c8ab3d4` |
| PR #462 | 已合并，2026-11-13 10:01:38 UTC；合并提交为当前 main |
| 开放 PR | API 返回空列表 |
| D3 执行源到当前 main | 6dd6a3b → ab4862d，新增两个提交；102 个路径变化，**生产 formalization 路径变化为 0** |
| 差额性质 | 101 个 D3 证据路径和 `core/status/CURRENT.md` 的一行后继证据登记；不能把后继文档提交倒写为实际编译提交 |

原始响应与结构化差额保存在 `agents/B/evidence/REMOTE_HEAD_AND_PR461_462.json`、`COMPARE_EXECUTED_SOURCE_TO_CURRENT_MAIN.json` 和 `OPEN_PRS.json`。本次所读 Lean、来源矩阵和 D3 文件以当前精确 SHA 读取，并逐个校验 Git blob；清单见 `FETCHED_SOURCE_MANIFEST.json`。相同字节同时置于共享 `source/` 的原仓库相对路径，便于主审独立复核。[E1-S]

### 1.2 本文的等级含义

- **E1-S：** 当前精确源码、远端实际记录、可检查的自然语言数学推导；不是本轮新 Lean 执行。
- **E1-L：** 实际读取的一手文献。分别标“全文相关部分”和“仅原刊摘要”，二者不互换。
- **原 E1-R 复用：** 上轮真实执行的固定版本命令、原始输出和来源绑定；当前未变化的源继续使用这些已完成证据。本轮不重新执行。
- **E2：** 已验收研究记录和未在本轮重新计算的既有边界例证。
- **U：** 本次尚未确立的全文包含关系或全球原创性优先权。

本次没有操作 Mac、修改生产 Lean、升级 Lean／Mathlib、重新求值 native 数值端点或修改远端。下文的独立推导是审查说明，不是新增生产定理。

## 2. 原 B 数学事项的处置核对

### 2.1 两个必须区分的完成状态

**P-CTL-01：已准确修正。** 当前 `mathematics/THEOREM_SOURCE_MATRIX.md:82` 写 `0<β<1`；`FiniteDiscountedControl.lean:28–38` 的 `Model.discount_pos` 和 `discount_lt_one` 仍是严格正折扣。原正文及定理本来采用此条件，旧矩阵误写不说明此前证明了 β=0。没有必要为消除文档误字新增 β=0 定理。[S-CTL；S-MATRIX]

**D3：已在定向范围内真实完成。** 当前 `d3-reproduction-2026-11-13/VALIDATION.json` 登记 `PASS_TARGETED_D3_ACCEPTED`；实际内容与该包 README、B 原读回报告一致：

- 执行源是 6dd6a3b，Lean 4.33.1、编译器提交 `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`，Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`。
- 15 个选定源实际重编译退出 0；最终修正 probe 的实际 Lean 命令退出 0；44 条类型和公理查询、12 项定义／结构查询已发生。
- 44 个端点中 37 个来自新编译模块、7 个查询复用缓存；42 项仅有标准逻辑公理子集，2 项保留精确披露的 native 依赖。两项 native 计算没有重新执行。
- v1 的依赖定位失败、v2 的 `pp.width` 显示选项失败、continuation 的宇宙后缀解析失败都保留原失败状态。成功的是具体源编译和最终 Lean 查询；不是三个 wrapper 被改写为成功。
- 30 个新模块产物、63 个旧缓存产物及 1055 个源／配置的最终实际读回记录均保持一致。B/C 在云端复核的是 Mac 实测二进制哈希记录及取回日志，不能声称云端直接重新哈希了全部 Mac 二进制。
- 原 pretty print 存在 `⋯`；44 条查询成功不等于 44 个类型无省略全文展开。原审查已用同源精确声明补读关键省略，不能把长度限制误当假设消失。
- 不声称全库无缓存重建、全部依赖重新检查或自然语言哲学主张均获证明。[S-D3；S-D3B；S-D3V]

这些限制是完成结论的一部分，不是待消除的“失败”。当前 main 未改生产证明，重复运行同一批没有已识别的新风险可解决。[E1-S；原 E1-R 复用]

### 2.2 旧发现是否还有未处置项

本表以已入库贡献记录 §6、原总报告和 D3 后继审查为责任集合，不重新执行未变化模块。

| 原问题或责任 | 当前处置 | 本轮判断 |
|---|---|---|
| B-M01：折扣矩阵 | 字符条件已更正，实际数学未改 | 完成；P5 |
| C01 空 Ω、C02 退化静态模型 | 保留单调／有限删除条件；基础语言不保证非平凡发展 | 已有边界；不添加普遍非空或非退化公理 |
| C03 预测不等于控制／身份、C04 全码擦除 | 任务、动作、费用、记录与不可恢复条件均明确 | 已有条件理论；本文补先行比较，不重开证明 |
| C05 个体续存与增长目标、C06 有限期限与指数增长、C08 三种选择陈述 | 评价量和概率量分型保留 | P5；没有把期望率升级为所有目标或几乎必然胜出 |
| C07 亚临界请求拒绝、旧 Valid 将优势／超临界写入假设 | 新 `ProbabilityValid` 及全策略率／内部程序 iff 已覆盖失败区 | P5；本文 §6 说明实际行来源 |
| C09 共享资源下局部组合 | 联合许可、总预算与共同源是调用方义务 | P3；不补无条件组合定理 |
| C10 共同二维、C11 GOA 非空与收敛 | 共同瓶颈、有限性和混合等原条件保留 | P5；不改成普遍秩二或唯一收敛 |
| C12 泛型装配不等于同一身体 | P-CORE 为 K2 接口／K3 外层包装；具体同源源另给见证 | 已收窄；无需宇宙总定理 |
| 身份初态、内部程序归属 | `ValidIdentity`；`ProgramPopulation θ` 初态、可达保持、正分支仍显式 | 完成；不能删前提来增强宣传 |
| 四生成器与 106 P-ID | 11 generated、89 retained adapter、6 retained boundary 的原登记含义保留 | 计数不作为全部语义由四公理导出的证明；P5 |
| 两个 native 端点 | 精确披露，未声称纯内核归约 | 现行责任完成；更换信任仅在实际消费者需要时为 P2 |
| 独立新 Lean 未执行 | 已由 D3 真实定向复现及 PR #462 后继采用补足 | 完成；不能继续按旧阶段记为 OPEN |
| 无专门消费者的书面推论、增加有限实例 | 原 API 范围已分清书面结论与专门 Lean 端点 | P4；不为数量继续证明 |
| 零概率端点、更多程序、损伤族；未知参数学习、自发身体生成、一般连续模型 | 不在本次冻结的严格参数／源合同承诺内 | P2/P3；不是未修复的 Core 矛盾 |
| 原创性归属 | 原 §5 已有成熟理论与范围定位；全文命题映射仍可加深 | 本文完成三组精确数学层的全文对应及源内桥限定；全球优先权 U |

**没有一项旧 B 数学发现需要靠增加未要求的 Lean 定理才能清账。** D4 的有限责任是精确归属和公开未知，不能被解释为必须证明 UEOT 首创；也不能把两篇无法取得的全文写成已读。[S-CONTRIB；E2]

## 3. 文献阅读范围与比较规则

| 一手来源 | 本次实际取得与读取 | 能支持什么 |
|---|---|---|
| Shalizi & Crutchfield 2001，[R1] | 原作者 PDF 全文已取得；重点读作者版 pp.6–10、13–16、22–24，§III、§IV、§V Theorems 1–3、Lemma 7／Remark 4、Appendices E/F | 可比较预测目标、因果状态、充分性、a.e. 最小性及熵最小性的条件；不等于逐一审计全篇 ε-machine 理论 |
| Givan, Dean & Greig 2003，[R2] | 原作者 PDF 全文已取得；重点读作者版 pp.4–6、12–14、44–46，§2.1.2／2.1.3、§3.3、Theorems 5／7 及其附录证明 | 可比较共享动作的随机双模拟、商模型、最优值与策略提升 |
| Pliska 1976，[R3] | 原刊摘要与书目信息；出版社 PDF 路径回到摘要，JSTOR 未取得正文 | 可确认研究对象、期望奖励与非负矩阵 MDP 方向；不能确认全文的精确策略类／全部技术假设 |
| Rothblum & Whittle 1982，[R4] | 原刊摘要与书目信息；出版社 PDF／epdf、JSTOR 和公开作者稿检索均未取得正文 | 可确认有限 product-form 非负矩阵类和几何／代数增长目标；不能声称完成全文定理包含检验 |
| Nesterov & Protasov 2011／2012 作者稿、2013 期刊文，[R5] | 主审提供合法作者全文后，B 独立读 §2、§3 的 (3.2)／(3.3)、Theorems 1／2，§4 Theorem 4 及所引正势定义；重点作者稿 pp.2–10 | 第三组的可核全文一般矩阵结构；并区分最优正势下确界与实际达到的全时界 |

三份作者 PDF 的本地读取副本及文本在 `agents/B/literature/`；其校验信息见附录。它们是审查读取材料，不需要作为 UEOT 的重新发布内容。本文所有数学嵌入和反例均自行陈述，清楚区别于原文中的定理。

## 4. 比较一：P-PRED-01 与因果状态的预测充分性

### 4.1 先行命题与 UEOT 实际声明

Shalizi–Crutchfield 对离散时间、离散值平稳过程，把具有相同条件未来分布的历史归入同一因果状态。Theorem 1／Corollary 1 给出预测充分性；Lemma 7 及 Remark 4 使任何同样充分的表示几乎处处细化因果状态；Theorems 2／3 讨论统计复杂度最小和相应唯一性。作者对可测性、零测历史和有限熵设有明示限定，不能忽略。[R1，作者版 pp.6–10、13–16、22–24]

UEOT 当前 `PredictionDependent.lean:28–58` 则给：

\[
K_i:H\to\mathcal M(Y_i),\qquad L_i:S\to\mathcal M(Y_i),\qquad
K_i(h)=L_i(s(h))\quad\mu\text{-a.e.，逐 }i.
\]

当 \(I\) 可数、上述 \(K_i,L_i\) 是可测核时，

\[
C(h):=(K_i(h))_{i\in I}=d(s(h))\quad\mu\text{-a.e.},
\qquad d(z):=(L_i(z))_{i\in I}
\]

且 \(d\) 可测；随后给出 `AEFactors` 和 `AESigmaLE`。坐标核使 \(C\) 自身逐协议充分（同文件 60–73）。这是给定响应核后的因子化结果，并不从历史样本估计核。[S-PRED；S-AE]

类型细节不能抹去：`canonical_ae_minimal` 自身不要求核为概率核，也不显式要求 \(s\) 可测；它只需要已给的逐协议等式和可测 \(L_i\)。把 \(s\) 解释为真实随机统计量时，本次嵌入另给 \(s\) 可测、核为概率核。不能把这种额外解释前提偷偷说成该 Lean 签名已自动提供。[S-PRED:18–58；S-AE:25–29、39–41、74–81]

### 4.2 一个严格的交叠类对应

**命题 P：** 设 \(A\) 是有限字母表，\(X=(X_t)_{t\in\mathbb Z}\) 是平稳过程；给定历史空间 \(H=A^{\mathbb Z_{<0}}\) 上的历史分布 \(\mu\) 和一个可测条件未来概率核。令

\[
I=\mathbb N_{>0},\qquad Y_L=A^L,\qquad
K_L(h)=\mathcal L(X_0,\ldots,X_{L-1}\mid H=h).
\]

采用同一版本的条件核，则 \(C(h)=(K_L(h))_L\) 的纤维，恰是“全未来条件分布相同”的因果状态类；改变条件核版本只影响一个共同零集之外的解释。

**理由。** 全未来分布相同显然使每个有限前缀分布相同。反向由所有有限前缀的柱集生成未来的乘积 σ 代数，概率测度在这个生成族上的一致性决定全未来分布。这里的未来核来自同一个过程，已经满足前缀相容；不是任意核族都自动拥有这一性质。

现在令 \(R=s(H)\) 是可测表示，\(L_L(r)\) 是给定 \(R=r\) 的长度 \(L\) 未来分布。因 \(A^L\) 有限，

\[
H(X_{0:L-1}\mid R)-H(X_{0:L-1}\mid H)
 =\mathbb E\,D_{\mathrm{KL}}\!\left(K_L(H)\,\middle\|\,L_L(R)\right).
\]

两侧非负且有限；等号为零，当且仅当 \(K_L(H)=L_L(R)\) 几乎处处。因此，在这个交叠类，原文的“每个有限长度都同样有预测力”与 UEOT 输入的逐 \(L\) 因子化等价。对可数 \(L\) 取共同满测集，定义 \(d(r)=(L_L(r))_L\)，即得到 UEOT 的 `canonical_ae_minimal` 结论。

如果再把因果状态和比较表示限制为有限或适当可数、有限熵情形，\(C=d(R)\) 进一步给 \(H(C)\le H(R)\)，对应原文的统计复杂度最小性。**这个熵结论需要相应附加条件；不能从 UEOT 的一般可测因子序直接宣称任意连续状态的 Shannon 熵最小。**[本节为独立推导，E1-S；先行陈述对应 R1]

| 角色 | 先行理论的交叠实例 | 当前 UEOT 类型 |
|---|---|---|
| 历史 | 过去的无限符号序列 | `H` |
| 预测任务 | 每个长度 \(L\) 的未来块 | 可数 `I` |
| 输出空间 | \(A^L\) | 依赖空间 `Y L` |
| 因果状态表示 | 条件未来分布相同的历史类 | \(C(h)=(K_L(h))_L\) 的纤维 |
| 同样充分的竞争表示 | 所有长度预测不损失 | 已给 \(L_L\) 的逐 \(L\) a.e. 因子化 |
| 最小性 | 竞争表示 a.e. 细化因果状态 | 可测解码 \(C=d\circ s\) a.e. |
| 统计复杂度最小 | 有限熵的状态熵比较 | 因子序之外另用信息论；不是该 Lean 端点本身的完整结论 |

### 4.3 严格差异与贡献定位

- UEOT 允许任意可测响应核和依赖目标；它们不必是某个平稳过程的相容未来边缘核。因此一般 P-PRED 不是整套 computational mechanics 的同义改名，也不能直接据此恢复 ε-machine 的更新／转移结构。
- 原文的“因果状态”是预测分类。因果状态相同不意味着微观机制相同、现实个体同一或可控制性相同。UEOT 也没有由最小预测表示证明这些事。
- \(I\) 的可数性承担共同零集责任；不能将逐协议 a.e. 等式未经条件地推广为任意不可数族上的共同 a.e. 等式。
- 该证明的重要内容是把可测因子序及共同零集责任明确写入机器接口；“最小充分预测状态”这个基本思想并非 UEOT 首创。[S-PRED；R1]

**裁定：** 先行核心原则明确；UEOT 此部分属于既有思想的形式化与任务接口推广／组织。依赖输出空间和可测核版本的具体工程可以有贡献，但现有比较不支持“首次发现最小预测状态”或“全新普遍表示定理”。无需新增 Lean 来争取这种更强宣传。

## 5. 比较二：P-QUO-01 与随机双模拟商

### 5.1 两边各自的前提

Givan–Dean–Greig 采用有限状态集 \(X\)、共享有限动作集 \(A\)、随机转移 \(P(x,a,y)\)、状态奖励 \(R(x)\) 和 \(0<\beta<1\)。其主要表述使用状态奖励，原文也注明更一般奖励可扩展。随机双模拟要求同块状态的奖励相同，且对同一个动作、每一个块的转移概率相同。Theorem 5 保持最优值；Theorem 7 将商模型的最优策略提升到原模型；附录实际以块求和和动作值等式证明。[R2，作者版 pp.4–6、12–14、44–46]

UEOT `ExactControlQuotient` 的输入是：[S-QUO:26–52]

\[
f:X\twoheadrightarrow Y,\quad A_{\rm micro}(x)=\bar A(f(x)),
\]
\[
\beta_X=\beta_Y,\quad r_X(x,a)=r_Y(f(x),a),\quad
\sum_{x':f(x')=y}P_X(x,a,x')=P_Y(f(x),a,y).
\]

同一纤维的动作类型在 Lean 中按定义相同，不是已经证明任意两个不同动作类型都能运输。奖励可依赖动作并可为有界负数；这是比本文所选先行交叠设定更宽的接口，不应把原文写成与这个完整类型逐字相同。[S-CTL；S-QUO]

### 5.2 交叠类中的双向定义对应

**命题 Q：** 限制为共享 \(A\)、状态奖励的有限模型时，先行随机双模拟等价关系 \(E\) 与 UEOT 的精确满射商相互对应，差一个商状态的重命名。

从 \(E\) 出发，令 \(Y=X/E\)、\(f(x)=[x]\)、\(\bar A(y)=A\)。以任意块中代表定义

\[
R_Y([x])=R_X(x),\qquad
P_Y([x],a,[z])=\sum_{z'\in[z]}P_X(x,a,z').
\]

双模拟条件恰保证这两个定义与代表无关，并给 UEOT 的 `reward_closed`、`transition_closed`。概率行归一由有限分块求和得到；满射和共同折扣也满足。

反向从该交叠类的 UEOT 精确商出发，定义 \(xEx'\iff f(x)=f(x')\)。奖励闭合立即给相同奖励；转移闭合给相同块转移概率。满射使 \(X/E\) 与 \(Y\) 双射。因此 \(E\) 是原文意义的随机双模拟；这里不是仅凭名称相似下判断。[本段独立推导，E1-S]

### 5.3 值与策略结论如何一一对应

对任意 \(v:Y\to\mathbb R\)，块求和给

\[
\sum_{x'}P_X(x,a,x')v(f(x'))
 =\sum_yP_Y(f(x),a,y)v(y).
\]

结合奖励及折扣闭合，逐动作 Q 值相同；再对同一动作集取最大，得到

\[
T_X(v\circ f)=(T_Yv)\circ f.
\]

两个 Bellman 算子都是严格折扣压缩。把宏观固定点拉回并用微观固定点唯一性，

\[
V_X^\ast=V_Y^\ast\circ f.
\]

宏观最优动作在微观仍达到同一个最优 Q 值，故宏观最优 stationary selector 的提升最优。这正对应源码 `expect_pullback`、`bellman_pullback`、`optimalValue_pullback` 和 `liftSelector_optimal_actionwise`，也与先行 Theorems 5／7 的块求和证明吻合。[S-QUO:64–165；R2]

UEOT 另显式把比较目标扩大到声明的所有 `CausalPolicy`，包括随机历史策略（同文件 179–221）。不能把原文以 \(\pi:X\to A\) 表述的策略定义说成已经逐字包含这个 Lean 类型；但这种扩展的基本数学同样是标准 Bellman 上界：

\[
V^\ast(X_t)\ge r(X_t,A_t)+\beta\,
\mathbb E[V^\ast(X_{t+1})\mid\text{当前历史、所选动作}].
\]

对允许动作混合、取期望并望远镜求和，尾项受有界性和 \(\beta^n\to0\) 控制；greedy selector 达等号。它不会因为策略含历史和随机性就成为一个新的普遍控制原理。[本段独立推导；S-QUO；S-CTL]

### 5.4 不被这个对应自动包含的部分

1. 观察预测相同本身不保证商合法。例如两个自环状态的外部观测永远相同，但动作 \(a,b\) 在两状态分别取得奖励 \((1,0)\) 与 \((0,1)\)。预测可以合并，单一宏观 stationary 动作却不能在两状态都最优；奖励闭合正好不成立。这个边界说明控制接口有实质义务，不说明 UEOT 首先发现该义务。
2. 动作可行性、资源费用和机制实现必须在所选模型中一致；一般的名字重命名或观察等价没有提供这些字段。
3. P-QUO-02 的近似值误差和策略损失不等于这里比较的精确双模拟 Theorem 7。未在本轮另作全面近似 MDP 优先权检索；不能因精确论文没有该形式便宣称近似界首创。[S-QUO；S-APPROX]

**裁定：** P-QUO-01 的精确值／策略保持在该交叠类与成熟双模拟商对应。UEOT 的价值主要在与允许动作、观察、资源及共同误差消费者的明确接口衔接；它不是一种新发明的控制商原理。原 P-CTL／P-QUO 核心证明无需重开。

## 6. 比较三：真实再生源、全允许策略增长与受控多型分枝

### 6.1 先行范围与尚未取得的内容

Pliska 的原刊摘要已经把受控多型分枝的期望奖励问题连接到非负、可非次随机的矩阵决策模型。Rothblum–Whittle 的原刊摘要明说有限独立选行非负矩阵族、正终端向量，并在几何增长后比较代数增长；其主要结果是可由一个固定矩阵反复使用达到相应最优增长。[R3；R4，均仅摘要]

这些足以排除“受控分枝／固定增长最优是 UEOT 首次发现”的无证宣传。它们不足以单独证明前文已覆盖 UEOT 的联合随机历史策略、真实费用、程序继承和身份账本。下文先给本次对 UEOT 特定类的**独立数学推导**；§6.7 再将矩阵层代入另已取得全文的 Nesterov–Protasov Theorem 4。Pliska／Rothblum–Whittle 的完整全文定理包含状态仍为 U。

### 6.2 从当前源码提取实际两类型行族

记健康 \(H=\mathrm{false}\)，损坏 \(D=\mathrm{true}\)，参数

\[
s=p.\mathrm{survival},\quad
\delta=p.\mathrm{careOnly},\quad
b=p.\mathrm{commonBirth},\quad
\gamma=p.\mathrm{bloomOnly},\quad
q=p.\mathrm{damage}.
\]

当前 `ProbabilityValid` 是

\[
0<\delta<s<1,\quad b>0,\quad\gamma>0,\quad b+\gamma<1,\quad0<q<1.
\]

它没有预设 \(\gamma>\delta\) 或增长率大于 1。旧 `Valid` 恰再加 \(\delta<\gamma\) 与 \(s+b>1\)，源码已有等价定理。[S-GC:20–28、61–69]

令

\[
k_c=s+b,\quad k_b=s-\delta+b+\gamma,\quad
u=(1-q,q),\quad e_D=(0,1).
\]

实际均值行如下，每一行的两个分量是下一次 census 的健康／损坏输出个数期望：

| 当前类型 | care | bloom | stop |
|---|---:|---:|---:|
| H | \(k_cu\) | \(k_bu\) | \((0,0)\) |
| D | \(k_cu\) | \(e_D\) | \((0,0)\) |

**损坏 bloom 是拒绝后保留原个体的单位行，不能误替换为 \(k_bu\) 或零行。** 源码的损坏 bloom 所需 cap 是 7，而交易上限是 6，实际拒绝不产新生并退款；`realizedRow` 明确编码该行。`realizedMean_eq` 从实际 `step` 的 retained/newborn 计数证明上述均值，不以“均值已经正确”作为假设。合法概率解释另由 `ProbabilityValid` 保证。[S-SOURCE:186–209、303–328、448–517；S-GC:20–47]

按每个类型独立选一动作，共有 9 个带动作标签的选行组合，某些参数下矩阵可重复。行非负，但行和可大于 1，因此它们是分枝均值矩阵，不是普通随机转移矩阵。这个有限行族**严格满足 R4 摘要明示的 product-form 模型描述**；此归属来自本表和定义，不依赖取得其全文。

### 6.3 正权重证书给出精确最优基

定义

\[
k_\ast=\max(k_c,k_b),\quad
\mu=(1-q)k_\ast+qk_c,\quad
\rho_\ast=\max(1,\mu).
\]

这里的 \(\mu\) 是增长组合量，不是 §4 的历史分布。对每个类型和动作的行 \(m_{i,a}\)，我们构造严格正列向量 \(r\)，使

\[
m_{i,a}\,r\le \rho_\ast r_i,
\]

并找到每类一个动作同时达等号。**不能将它改写为“每个个体的未加权一步期望产出都不超过 \(\rho_\ast\)”；健康行和 \(k_\ast\) 可以大于 \(\rho_\ast\)。**

**情形一：\(\mu\ge1\)。** 取 \(r=(k_\ast,k_c)>0\)。因为 \(u r=\mu\)，健康最优行 \(k_\ast u\) 给 \(k_\ast\mu=\rho_\ast r_H\)，损坏 care 给 \(k_c\mu=\rho_\ast r_D\)；损坏 bloom 给 \(r_D\le\mu r_D\)，其余行也不超过上界。达到者矩阵

\[
M_\ast=
\begin{pmatrix}
k_\ast(1-q)&k_\ast q\\
k_c(1-q)&k_cq
\end{pmatrix}
\]

为秩一，\(M_\ast r=\mu r\)。

**情形二：\(\mu<1\)。** 设 \(d=1-(1-q)k_\ast>0\)，取

\[
r=\left(\frac{qk_\ast}{d},\,1\right)>0.
\]

则 \(ur=q/d\)；健康最大行给 \(k_\ast q/d=r_H\)。损坏 care 给 \(qk_c/d<1=r_D\)，恰因 \((1-q)k_\ast+qk_c<1\)；损坏 bloom 拒绝行给等号。达到者矩阵

\[
M_\ast=
\begin{pmatrix}
k_\ast(1-q)&k_\ast q\\
0&1
\end{pmatrix}
\]

有 \(M_\ast r=r\)。该等号来自现有拒绝语义，不是新增一个允许动作。

这些就是当前 `optimalValue` 和 `optimalAction` 的两支构造；`actual_row_bound`／`selected_row_eq` 与实际一步后代证书已证明这些性质。[S-GC:128–164、230–316] 本段仅把源码已实现的数学写成可独立检查的短推导。

### 6.4 为什么完整联合历史策略也受界

当前 `Policy.kernel` 的输入是人口长度、公共收据历史、当前观察词；输出是整个请求词的概率。它允许跨当前成员的动作相关和历史依赖，不允许读取审计身份、隐藏 tag 或未来噪声。噪声权重由声明的独立成员噪声生成。`State.good` 仅保证人口身体在 canonical 源类。[S-CP:244–281]

对人口 \(N_t\) 定义加权计数

\[
W_t=\sum_{v\in N_t}r_{\mathrm{kind}(v)}.
\]

固定任一当前人口和整个请求词，实际后代的期望可按成员相加；`realizedMean_eq` 把每个成员贡献变成实际行 \(m_{i,a}r\)，逐行证书给总和 \(\le\rho_\ast W_t\)。再按 `Policy.kernel` 的非负、总和为 1 的联合概率混合，仍有

\[
\mathbb E[W_{t+1}\mid\text{当前完整源状态／已有历史}]
   \le \rho_\ast W_t.
\]

这一步不要求请求彼此独立。经迭代有限期望的塔性质，

\[
\mathbb E_K W_n\le \rho_\ast^n W_0
\quad\text{对每个允许 }K.
\]

公共观察可读出 kind，所以达到每类等号的 stationary 选择属于同一个允许策略类；对它有 \(\mathbb E W_n=\rho_\ast^nW_0\)。令 \(r_{\min},r_{\max}>0\)，于是

\[
\mathbb E_K |N_n|
 \le \frac{W_0}{r_{\min}}\rho_\ast^n,
\]
\[
\frac{W_0}{r_{\max}}\rho_\ast^n
 \le\mathbb E_{K_\ast}|N_n|
 \le\frac{W_0}{r_{\min}}\rho_\ast^n.
\]

非空初始人口使 \(W_0>0\)。若另有一个对所有允许策略和所有 \(n\) 的共同上界 \(C\lambda^n\)，且 \(0<\lambda<\rho_\ast\)，达到策略的下界导致 \((\rho_\ast/\lambda)^n\) 无界而矛盾。因此 \(\rho_\ast\) 是最小的正统一指数上界底数。[S-GP:196–244；S-GA:41–64]

**归属判断：** 归一化混合、线性期望、塔性质及正权重比较都是标准数学；不能将它们宣传为 UEOT 发明。此模型需要完成的具体责任是：实际执行的行、拒绝项、观察可用动作、canonical 保持和程序／人口接口，确实满足所用标准论证。[E1-S]

### 6.5 与两篇先行工作的精确对应和严格差异

| 维度 | 本次可严格建立的对应 | 不能据此声称 |
|---|---|---|
| 对象 | 以每次 census 为一代，投影到 H/D 个数；保留者可在计数投影中作为下一代同类输出，新生另计；实际噪声给每个个体的后代分布 | 原账本身份等于分枝理论中的“新个体”；原论文已证明 UEOT 的亲本／身体同一 |
| Pliska 模型层 | 对类型依赖、逐个体选择的离散代策略，投影是一个受控两型分枝实例，均值矩阵非负且可超随机 | 原文全部策略类等于 UEOT 的公共历史联合 `Policy`；其期望累计奖励目标等于 UEOT 的最小增长底数 |
| Pliska 目标层 | 固定有限期限的人口期望可用“类型＋剩余期数”扩充为有限时域终端奖励模型：终期每人奖励 1，其余 0 | 该辅助有限期限嵌入已在 UEOT 新增形式化；或 Pliska 原文某个未经阅读的编号定理已经完成无限期增长分类 |
| Rothblum–Whittle 模型层 | 两类型各三行的有限 product-form 非负矩阵族、正终端向量 \(\mathbf1\)，与原刊摘要明确描述一致；固定逐型选择的期望计数为矩阵乘积 | 摘要已证明其全部技术条件覆盖 UEOT 的高层联合历史策略 |
| 完整历史策略 | 本文 §6.4 从实际逐行界独立证明所有允许联合历史策略的期望上界；无需把其全路径分布等同某个固定矩阵链 | 历史策略的完整概率律、账本或信息结构都已由矩阵投影保留 |
| 增长指标 | 当前类有正公共权重，并有 stationary 达等号；因此具上下常数倍的纯指数界和最小统一底数 | 一般非负矩阵族都不存在多项式因子；R4 明确还研究代数增长，本模型不代表其全部问题 |
| 机制语义 | UEOT 从 code、repair、budget、request/refusal、retained/newborn 推导计数行并接到策略界 | 原论文也有这些同源语义；或只因未见该语义便证明 UEOT 全球首创 |

固定逐型动作序列 \(a_t(i)\) 时，均值人口行向量满足 \(m_{t+1}=m_tM_t\)，终期人口期望为 \(m_0M_0\cdots M_{n-1}\mathbf1\)。高层策略可能为同型不同成员发不同请求并相关随机化，故不能不经论证把它们全部写成某一确定 \(M_t\) 的路径律。上节的条件期望证明正是避免这种偷换的桥。

也可以仅在无条件**一阶均值**层面，对每类将各动作的预期使用人数归一化，得到各行在原行集凸包中的 \(B_t\)，使 \(m_{t+1}=m_tB_t\)；类型平均人数为零的行任取。这仍只是均值投影，不是策略信息和个体路径的双向同构。[本节独立推导，E1-S；文献边界 R3/R4]

### 6.6 两个内部程序、拒绝边界与何为增量

源码给

\[
\lambda_0=k_c,\qquad
\lambda_1=(1-q)k_b+qk_c,\qquad
\rho_\ast=\max(1,\lambda_0,\lambda_1).
\]

在 `ProbabilityValid` 和非空 canonical 初态下：

\[
\text{程序 false 达到 }\rho_\ast
\iff \gamma\le\delta\ \land\ 1\le k_c,
\]

\[
\text{程序 true 达到 }\rho_\ast
\iff \delta\le\gamma\ \land\ 1\le\lambda_1.
\]

这些是两个预给程序的期望增长分类，不是程序自发产生或所有内部程序最优。将外部 `programPolicy θ` 解释为身体内部程序还须 `ProgramPopulation θ` 初态、`reachable_program` 保持和 `programPolicy_positive_branch_is_internal` 的正分支条件；一般 `State` 仅有 `good` 不足。[S-GA:73–105；S-CP:455–544；S-GP:293–355]

一个具体可检查的参数点是

\[
(s,\delta,b,\gamma,q)
=\left(\frac25,\frac1{10},\frac15,\frac3{20},\frac12\right).
\]

它满足 `ProbabilityValid`，有 \(k_c=3/5\)、\(k_b=13/20\)、\(\lambda_1=\mu=5/8\)。两内置程序均次临界，完整动作类却有 \(\rho_\ast=1\)：健康时 bloom，损坏时继续请求 bloom 并被拒绝，给

\[
M_\ast=
\begin{pmatrix}13/40&13/40\\0&1\end{pmatrix},
\qquad r=(13/27,1).
\]

直接相乘有 \(M_\ast r=r\)。这不是“拒绝也促进繁殖”：损坏者只被保留，增长指标为期望 census 人口。它显示为何完整允许动作表及拒绝语义会影响最优基，也显示不能把“内部修复程序最优”作为无条件结论。本例仅是当前已证明参数分类的算术实例，本轮没有增加 Lean 消费者。

**裁定：** 一般分枝控制、非负矩阵增长和正权重证明法属于成熟数学。UEOT 当前可保留的数学贡献是本项目中实际执行语义到均值行的桥、指定参数族的精确分类、全允许策略接口及内部程序达到条件的形式化贯通。它可能是一项有价值的构造／分类／形式化贡献；全球先行包含或首创仍未确立。无需为维持“原创”名称引入新公理或额外证明。

### 6.7 全文补充：Nesterov–Protasov 的 product-family 定理

主审找到同一数学问题的合法作者全文后，B 独立读取了其 §2 的正向量界、§3 的 (3.2)／(3.3)、Theorems 1／2 及 §4 的非负扩展 Theorem 4。作者稿为 2011 年、2012 年 7 月修订；期刊正式发表于 2013 年。下面因此补足第三组的**全文级数学层对应**，而不改写 R3／R4 仍只取得摘要的事实。[R5]

其上侧结论可以准确写成

\[
\inf_{r>0}\{\lambda: Mr\le\lambda r\ \text{对全部 }M\in\mathcal M\}
=\widehat\rho(\mathcal M)
=\max_{M\in\mathcal M}\rho(M)
\]

对该文 (3.3) 的非负 product family 成立。这里左侧是下确界，不自动保证一个严格正 \(r\) 在最优值上达到。Theorem 2 的严格正版本不能直接处理本模型的零行和拒绝行；适用的是 §4 的 Theorem 4。[R5，(2.9)、(2.14)、(3.3)／(3.4)、Theorem 4]

**逐项代入。** 取 \(E=E_1=\mathbb R^2\)、\(K=K_1=\mathbb R^2_+\)、\(B=I\)，让 \(F\) 的健康行在 \(\{k_cu,k_bu,0\}\) 内取值、损坏行在 \(\{k_cu,e_D,0\}\) 内取值。这两套有限集非空且紧，所有元素非负，独立选行构成 §6.2 的全部矩阵族。因而它确为 (3.3) 的实例；不是泛泛类比。

**行列约定。** 本文按作者稿 (3.2) 的 \(F^\mathsf T=(F_1,\ldots,F_N)\)、\(A=BF\) 及 Theorem 1 的实际行替换证明确定方向：\(F_j\) 是 \(F\) 的第 \(j\) 行所对应的协向量，\(B=I\) 时可直接代入 UEOT 行族。附近叙述与 Example 1 使用 independent-column 的用语，不能据此在共同正右势的等式中无说明地将 \(M\) 换成 \(M^\mathsf T\)。若人口用列向量 \(z\)，演化是 \(z'=M^\mathsf Tz\)，势仍为 \(r^\mathsf Tz\)，不等式仍来自 \(Mr\le\lambda r\)。JSR／最大谱半径的数值可经转置保持：长度 \(n\) 的全部产品与其反序转置逐一对应，转置不改变谱半径；这不等于任意共同右势表达式原封不动转置。[R5，作者版 p.8；本段独立类型对照]

§6.3 的显式 \(r>0\) 证明上式左端 \(\le\rho_\ast\)，同时所选 \(M_\ast\) 满足 \(M_\ast r=\rho_\ast r\)，故 \(\max_M\rho(M)\ge\rho_\ast\)。相反全部行的 \(Mr\le\rho_\ast r\) 给各矩阵谱半径及所有产品的增长上界；因此

\[
\widehat\rho(\mathcal M)=\max_M\rho(M)=\rho_\ast
=\max(1,k_c,(1-q)k_b+qk_c).
\]

这显示本例的矩阵增长最优结构属于已经存在的 product-family 理论，显式公式是特定参数类的计算结果。[本段独立推导；R5 的已有一般结构]

**不能遗漏的严格差异：JSR 等式不自动给最优底数上的全时常数界。** 取单矩阵族

\[
\mathcal J=\left\{
J=\begin{pmatrix}1&1\\0&1\end{pmatrix}
\right\}.
\]

它是非负 product family，且 \(\widehat\rho(\mathcal J)=\rho(J)=1\)，但

\[
J^n=\begin{pmatrix}1&n\\0&1\end{pmatrix},
\qquad (1,0)J^n(1,1)^\mathsf T=n+1.
\]

因此不存在一个有限 \(C\) 使该终期人口量对所有 \(n\) 都 \(\le C\,1^n\)。也没有严格正 \(r=(r_1,r_2)\) 满足 \(Jr\le r\)，因为第一分量会要求 \(r_1+r_2\le r_1\)。但每个 \(\lambda>1\) 可用足够小的 \(r_2/r_1\) 得到 \(Jr\le\lambda r\)，所以最优正势值 1 只是下确界。这是一般矩阵类的反例，不是当前 UEOT 严格参数源的反例。

UEOT 在本例确实给出最优值上**达到的严格正公共 \(r\)**，并通过实际行、完整允许策略的归一化混合、人口期望递推及非空初态，把矩阵层接到 UniformExpectedUpper 的最小元素和 HasExpectedGrowth 的双边常数界。这个具体证书和语义桥不由“JSR 等于最大谱半径”这一句单独提供；而证书使用的正向量方法在 R5 的 Lemma 1 与 §2 已明示，是成熟方法。

| 项目 | R5 全文可核结论 | UEOT 本例需要另行履行 |
|---|---|---|
| 一般矩阵条件 | 紧 product family、非负共同锥；Theorem 4 允许非严格正元素 | 由真实三动作／两类型表落实这一个 family |
| 评价 | 最大谱半径、JSR、共同正势下确界的数值相等 | 精确 \(\rho_\ast\) 公式；最优处严格正势确实存在并给出 |
| 策略 | 矩阵切换产品 | 公共历史、联合随机请求、实际源状态的期望解释 |
| 全时界 | 给定达到的正势可推出；数值等式本身不保证达到 | 当前显式 \(r\)、非空初态及实际人口桥给最小共同 \(C\rho_\ast^n\) 上界 |
| 机制／身份 | 该定理不带身体、费用、程序和亲本语义 | realizedMean_eq、内部程序不变式及身份记录另有源内证明 |

**最终第三组裁定：** 有全文支持的成熟一般结构现在已准确定位；特定最优公式、达到的正势和实际源接口的组合仍可作为 UEOT 的具体数学／形式化贡献，但不能宣传为新发现的一般谱增长最优化原理。R3／R4 全文覆盖、该特定组合的全球首创依然未确立，无需据此开新 Lean 工作。

## 7. 可对外使用的五条贡献陈述

这里列五条不同工作内容，不把它们计作五组已完成的先行论文全文比较。

| 可陈述的工作 | 先行定位 | 本次支持强度 |
|---|---|---|
| 将最小预测表示写成依赖协议输出、可测核和共同 a.e. 因子序 | 预测充分／最小原则已有 SC 明确先行 | 已实现接口和形式化；原理首创否 |
| 将有限折扣精确商与全声明因果策略比较统一到公共 Lean 接口 | 共享动作交叠类与 GDG 双模拟商对应；历史策略 Bellman 上界属经典机制 | 结构实现与消费者连接；不是新控制商原理 |
| 从实际代码读出、付费修复、请求拒绝及保留／新生计数导出增长行 | 两篇早期分枝摘要只确认矩阵／人口优化层，未读到该机制语义 | 当前源码中桥确已完成；全球原创性 U |
| 对两类型严格正参数域给最优统一指数基及两个程序的充要达到区域 | 一般增长优化已有强先行；本域用显式正权重可独立验证 | 特定分类明确；新定理全球优先权 U |
| 同一生成源中连接程序继承、实际人口及全允许策略的期望结论，并保留身份前提 | 矩阵投影本身不会携带该解释 | 同源实例／形式化接口贡献；不是任意现实对象的共同本体定理 |

这些表述允许结果被现有数学充分解释，同时保留具体建模、形式化和反例边界的学术价值。不是每一项有价值工作都必须是一个新的数学原理。

## 8. D4 的完成边界与停止决定

D4 旧阶段已经完成了来源归因和风险限定；本轮新增的是逐对象、逐前提、逐评价量的数学对应。其完成状态应记录为：

- **已完成：** 三组有一手全文支持的数学层对应：因果状态的明确交叠类、共享动作精确双模拟商、非负 product-family 的谱增长结构；另从实际源码核对两型增长行、达到的正权重和高层策略桥，给出 JSR 与精确全时界的严格差异。三组均区分成熟原理、本项目实现和不成立的互推。
- **没有声称完成：** Pliska／Rothblum–Whittle 全文定理完全包含关系、全球优先权、自然经验有效性、外部人类同行认可。
- **对 Core 的影响：** 没有发现现行冻结范围内的新 P0/P1 数学缺口；D4 阅读限度不要求新增 Core 证明。P-CTL 勘误与 D3 不应再次开为未完成任务。
- **后续启动条件：** 投稿评审提出一个具体先行定理匹配问题、取得相应全文后发现实质冲突，或有真正消费者需要不同参数／策略／资源合同；据此做有限比较或扩展。不能为了把“NOT ESTABLISHED”强行改为“首创”而开展无边界研究。

**B 的建议仍为：维持当前声明范围内的 A 冻结，停止已完成 Core 数学的数量扩张。** 可以继续学术定位和外部批评；其目标是让贡献更准确，而不是预定必须发现新数学。

## 9. 一手文献与可复核源码

### 9.1 文献

**[R1]** C. R. Shalizi and J. P. Crutchfield, “Computational Mechanics: Pattern and Prediction, Structure and Simplicity,” *Journal of Statistical Physics* 104 (2001), 817–879。作者全文：[cmppss.pdf](https://csc.ucdavis.edu/~cmg/papers/cmppss.pdf)。本次用作者版页码；Theorem 1／Corollary 1 pp.13–14，Lemma 7 p.14，Theorems 2／3 pp.15–16，条件测度与可测性 pp.22–24。不是期刊分页。

**[R2]** R. Givan, T. Dean and M. Greig, “Equivalence Notions and Model Minimization in Markov Decision Processes,” *Artificial Intelligence* 147 (2003), 163–223，DOI [10.1016/S0004-3702(02)00376-4](https://doi.org/10.1016/S0004-3702(02)00376-4)。作者全文：[GivanetalAIJ-03.pdf](https://cs.brown.edu/people/tdean/publications/archive/GivanetalAIJ-03.pdf)。模型 pp.4–6；随机双模拟、Theorems 5／7 pp.12–14；相应证明 pp.44–46（作者版）。

**[R3]** S. R. Pliska, “Optimization of Multitype Branching Processes,” *Management Science* 23(2) (1976), 117–124，DOI [10.1287/mnsc.23.2.117](https://pubsonline.informs.org/doi/abs/10.1287/mnsc.23.2.117)。仅原刊摘要和书目；本次未得到全文。

**[R4]** U. G. Rothblum and P. Whittle, “Growth Optimality for Branching Markov Decision Chains,” *Mathematics of Operations Research* 7(4) (1982), 582–601，DOI [10.1287/moor.7.4.582](https://pubsonline.informs.org/doi/10.1287/moor.7.4.582)。仅原刊摘要和书目；本次未得到全文。

**[R5]** Y. Nesterov and V. Y. Protasov, “Optimizing the Spectral Radius,” *SIAM Journal on Matrix Analysis and Applications* 34(3) (2013), 999–1013，DOI [10.1137/110850967](https://epubs.siam.org/doi/10.1137/110850967)。实际读取 [2011／2012 修订作者稿](https://optimization-online.org/wp-content/uploads/2011/12/3272.pdf)，pp.2–10 的相关定义与证明；特别 (2.9)、(3.2)／(3.3)、Theorems 2／4。作者稿题页标 October 2011、Revision July 2012，不把作者稿年代和正式刊年混为一谈。

本地原作者 PDF：
- R1：451112 字节，SHA256 `77a76d8c5140ab8449d440fe91a523fcf85b10c68124da6bde3de764b3942a6b`。
- R2：450913 字节，SHA256 `a771b95788a0d542c1a101fdaf0380bd759d02176f121af6af3b587ffea479ed`。

- R5：123300 字节，SHA256 3df19264ec639d0a6473f820b06f5c79e83c3ee5a368f6511e2d3ced34ea55aa。

### 9.2 当前精确源码引用

下列链接全部固定到本次核实的 main `ab4862db08bae9333f422f7bdbba490f8c1ce0df`；行号为该字节版本。源文件 blob 逐项记录在本地 manifest，不用漂移的 main 内容替换既有证据。

[S-MATRIX]: https://github.com/MurphyHoops/UEOT/blob/ab4862db08bae9333f422f7bdbba490f8c1ce0df/mathematics/THEOREM_SOURCE_MATRIX.md#L82
[S-CTL]: https://github.com/MurphyHoops/UEOT/blob/ab4862db08bae9333f422f7bdbba490f8c1ce0df/formalization/ueot-core/UEOT/V3/FiniteDiscountedControl.lean
[S-PRED]: https://github.com/MurphyHoops/UEOT/blob/ab4862db08bae9333f422f7bdbba490f8c1ce0df/formalization/ueot-core/UEOT/V3/PredictionDependent.lean
[S-AE]: https://github.com/MurphyHoops/UEOT/blob/ab4862db08bae9333f422f7bdbba490f8c1ce0df/formalization/ueot-core/UEOT/V3/PredictionAE.lean
[S-QUO]: https://github.com/MurphyHoops/UEOT/blob/ab4862db08bae9333f422f7bdbba490f8c1ce0df/formalization/ueot-core/UEOT/V3/FiniteDiscountedExactQuotient.lean
[S-APPROX]: https://github.com/MurphyHoops/UEOT/blob/ab4862db08bae9333f422f7bdbba490f8c1ce0df/formalization/ueot-core/UEOT/V3/FiniteDiscountedApproxQuotientBounds.lean
[S-SOURCE]: https://github.com/MurphyHoops/UEOT/blob/ab4862db08bae9333f422f7bdbba490f8c1ce0df/formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeSource.lean
[S-GC]: https://github.com/MurphyHoops/UEOT/blob/ab4862db08bae9333f422f7bdbba490f8c1ce0df/formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeGrowthClassification.lean
[S-CP]: https://github.com/MurphyHoops/UEOT/blob/ab4862db08bae9333f422f7bdbba490f8c1ce0df/formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeControlPopulation.lean
[S-GP]: https://github.com/MurphyHoops/UEOT/blob/ab4862db08bae9333f422f7bdbba490f8c1ce0df/formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeGrowthPopulation.lean
[S-GA]: https://github.com/MurphyHoops/UEOT/blob/ab4862db08bae9333f422f7bdbba490f8c1ce0df/formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeGrowthAttainment.lean
[S-CONTRIB]: https://github.com/MurphyHoops/UEOT/blob/ab4862db08bae9333f422f7bdbba490f8c1ce0df/research/audits/core-closure-2026-11-13/MATHEMATICAL_EVIDENCE_AND_CONTRIBUTION.md
[S-D3]: https://github.com/MurphyHoops/UEOT/blob/ab4862db08bae9333f422f7bdbba490f8c1ce0df/research/audits/core-closure-2026-11-13/d3-reproduction-2026-11-13/README.md
[S-D3B]: https://github.com/MurphyHoops/UEOT/blob/ab4862db08bae9333f422f7bdbba490f8c1ce0df/research/audits/core-closure-2026-11-13/d3-reproduction-2026-11-13/reviews/B_D3_MATHEMATICAL_REVIEW.md
[S-D3V]: https://github.com/MurphyHoops/UEOT/blob/ab4862db08bae9333f422f7bdbba490f8c1ce0df/research/audits/core-closure-2026-11-13/d3-reproduction-2026-11-13/VALIDATION.json

便于点击的主要入口：[预测][S-PRED]、[精确控制商][S-QUO]、[实际再生源][S-SOURCE]、[增长分类][S-GC]、[增长人口桥][S-GP]、[最小统一底数与程序 iff][S-GA]、[D3 正式后继验收][S-D3]。

