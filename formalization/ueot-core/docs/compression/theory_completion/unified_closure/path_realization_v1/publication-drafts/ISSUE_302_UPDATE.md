<!-- 仅供追加到 #302 的本批研究段落；本地草稿，未发送，不替换既有正文。 -->

## 2026-10-22 研究接续：实际记忆过程、条件路径与载体搜索

本批在已验收 [#363](https://github.com/MurphyHoops/UEOT/pull/363)、[#365](https://github.com/MurphyHoops/UEOT/pull/365) 的基础上，把“已经存在一个控制器/条件对象/最小下标”进一步接到其实际来源。operations [#366](https://github.com/MurphyHoops/UEOT/pull/366) 的 resulting main `d503586107974c56e0773b4ea106b41a7d144b43` 是本批不可变基线。新增七模块的具体数学报告与五份原始来源绑定见[完整数学报告][report]。

### 1. 同一控制器现在有自己的真实无限状态律

在有限状态、行动与记忆及相应可测性下，固定原初态 $p_0$、观察 $q$、完整数值源序列 $P_n$ 和同一个有限记忆控制器。其行动与更新按实际记录发生：

$$
A_n\sim\alpha(M_n),\qquad X_{n+1}\sim P_n(X_n,A_n),\qquad
M_{n+1}=u(M_n,A_n,q(X_{n+1})).
$$

本批构造实际增广初态与行序列 $J_n$，证明原微观完整历史律的增广等于该过程的因果律，再构造同一行序列的无限轨迹测度。每个完整有限前缀和每个状态坐标事件均被识别回原实验。状态律是同一个增广无限律的逐坐标投影；数值核可以非自治，观察类型保持任意。

这补上“这个控制器实际实现这个过程”的责任。它没有把擦除记忆后的状态过程自动变成 Markov，也没有宣称任意历史策略都可由有限记忆精确实现。支持固定与数值齐次仍是不同条件。

### 2. 零未认证占据如何推出物理安全

对于同一策略的真实占据 $U_n$，保留三项条件：原初态支持在 $K$；每个认证行动的实际后继支持保持 $K$；所有时刻 $U_n=0$。先对原微观支持作归纳，再通过已证明的坐标身份和可数个概率一事件的交，得到

$$
\Pr_{\mathrm{same\ controller}}(\forall n\ge0,\ X_n\in K)=1.
$$

已有支持固定点控制器直接消费这个接口，并证明自己的实际无限安全。新的公开三源合取在同一非空真安全集上证明：`false / false` 源满足三条件且全时安全质量为一；`false / true` 源保留自身零占据和初始安全，却明确违反认证转移闭合，时刻 1 与全时安全质量均为零；`true / false` 源保留自身零占据和认证转移闭合，却明确违反初始安全，时刻 0 与全时安全质量均为零。两个否定前提从真实支持点推出，下一步修复不会删除时刻 0 的原失败。

全部五个原质量计算继续保留为私有证明成分，并由公开合取逐项给出。这里证明两条物理前提在原充分条件定理中不可普遍删除，没有把它们改称所有安全过程的充要条件。

这一结果不改变旧有限时域策略与新控制器之间的身份责任，也不压缩参考过程在来源零概率历史上的完整检查预算。认证的物理语义仍由源模型与独立条件承担。

### 3. 有限窗完整路径与 Doob 的准确区别

在同一个齐次数值源、原初态、固定当前观察反馈及其 killed 矩阵 $Q$ 上，记 $g_r=Q^r\mathbf1$，$s_T=\eta_0Q^T\mathbf1$，$\eta_0$ 保留原安全初始质量。对原完整实验实际过滤，本批证明

$$
\Pr(X_0=i\mid S_T)=\frac{\eta_0(i)g_T(i)}{s_T},\qquad
C_T(\gamma)=\frac{\eta_0(\gamma_0)\prod_{k<T}Q(\gamma_k,\gamma_{k+1})}{s_T}.
$$

正质量父前缀事件给出正行分母，并推出真实下一行比 $Q(i,j)g_{r-1}(j)/g_r(i)$。完整条件 PMF 来自原实验；当前正行接口尚未另外构造所有零质量状态上的 total fallback 及独立生成该全路径的条件核。

对同一 $Q$ 的正右特征数据 $Qh=\rho h$，以原初态的自然 $h$ 倾斜和真正 Doob PMF 行生成路径，得到

$$
D_T(\gamma)=C_T(\gamma)\,
\frac{s_T h(\gamma_T)}{\rho^T\langle\eta_0,h\rangle}.
$$

在正 killed 权重路径上，两原子相等恰当且仅当末端权重为 $\rho^T\langle\eta_0,h\rangle/s_T$。相等要求只落在实际正质量路径上，不要求不可达状态满足多余条件。

三状态实际源的 killed 矩阵为

$$
Q=\begin{pmatrix}3/8&3/8\\1/8&1/8\end{pmatrix},\qquad
\eta_0=(1/2,1/2),\quad \rho=1/2,\quad h=(3/2,1/2).
$$

它具有真实左 QSD。时域 1 的原存活条件路径与自然 Doob 路径有相同初始边际 $(3/4,1/4)$，安全二时刻原子分别为 $(6,6,2,2)/16$ 与 $(9,3,3,1)/16$，其余五个墓地原子两侧都为零。全九原子计算给出 **TV $=1/4$**。因此，终端 QSD 稳定、有限窗完整路径和固定 Doob 路径不能据名称互换；谱极限与 Q-process 仍需另证。

### 4. C3 增加实际程序与准确查询责任

对已注册嵌套族的 $N$ 个候选，实际 Boolean oracle 扫描在首个正项停止并返回调用索引 trace。程序无需输入旧 `firstGoodIndex` 或未知真载体；在明确的 oracle/Good 匹配前提下，定理证明实际输出等于该旧数学选择。

成功下标为 $i$ 时恰调用 $i+1$ 次，失败时恰调用 $N$ 次，且查询均在表内、无重复索引。线性第一成功证明不要求 oracle 单调；nested 关系用于注册族内的包含极小性。重复集合值、内部 oracle 成本、噪声采样、全载体枚举与物理删除 frame 仍需分别处理。

这推进 C3-01/02 的一个受限算法责任；非自治记忆来源桥则为 C4 的实际过程输入提供明确来源。C1 的规范预测商递归、C4 的跟踪/变化载体、C7 的真实实验等原责任继续保留，不因局部包完成而整体关闭。

### 5. 已完成验证与全局状态

七个最终模块已实际聚焦 Lean PASS，独立静态数学/API 审查 CLEAR。最终有限窗来源链在 compile-09 顺序执行中通过；物理安全三源合取在 compile-10 实际通过并获独立语义审查。

当前完整源码指纹为 `de7c7e287bd1b351ed3f790de58bfd71edf18df4013f7e5aaf2af55a6b3f6379`。其实际完整 `lake build UEOT` 已 **PASS，14.23 秒，691 模块**；native 导出与固定 verifier 均实际 **PASS**（58.451 / 58.297 秒），摘要报告本批 **7 模块、73 个公开声明、249 个编译器审计定理常量、114 条注册直接证明边**，两个原日志哈希一致。原收据状态为 `PASS_PENDING_INDEPENDENT_REVIEW_AND_REGISTRATION`；完整执行原档独审、最终注册、canonical 与发布尚待对应证据。

原 `c344bf66…` 的 full build01 PASS 与 native01 中断 FAIL 各自保留。见证 API 的三源合取新增两条否定前提结论，五个原质量证明字节保留；公开比较域明确由 77 改为 73，新域按原 stored-type 全量比较规则执行，全部私有生成常量继续进入编译器审计。原 native01 未完成，不能表述为旧 77 项已完成全量验收。其他原始失败和旧缓存限制也不改写。

本批为 **uncounted** 来源实现，冻结 **106 P-ID = 11 generated / 89 adapters / 6 boundaries** 与 **4 counted generators** 均保持。**全局强数学闭合仍为 `NOT_ESTABLISHED`；#302 继续承担后续研究。** 统计错误预算、真实采样校准、物理领域适配和经验支持没有被形式路径结论替代。

后续可直接推进：全状态有限窗条件核的生成身份；有明确谱与支持条件的长窗/Doob 比较；记忆实际核到已有分布/占据跟踪接口的同源消费；有真实结构证据与含噪 oracle 的 C3 实验。每项都继续保留自己的量词、来源和失败条件。

### ROOT_TO_FILL：本批生产与发布证据

**当前构建及 native 两次执行已有 PASS；以下尚未完成的独审、注册与发布只按各自实际收据补入。**

| 项目 | 待填内容 |
|---|---|
| 本批 PR、最终 candidate / tree、验收或合并状态 | `ROOT_TO_FILL_PR_AND_STATE` |
| 两轮 native 完整原档、公理/ownership/raw-type/固定边与 JSON 等同性的独立核对 | `PENDING — ROOT_TO_FILL_NATIVE_REVIEW` |
| 最终注册公开声明、累计证明边与 overlay census | `PENDING — ROOT_TO_FILL_ACCEPTED_REGISTRATION_CENSUS` |
| 完整 clone、消费者、canonical 与必要回归 | `PENDING — ROOT_TO_FILL_INTEGRATION_GATES` |
| 原始执行证据及独立执行审查 | `ROOT_TO_FILL_EXECUTION_ARCHIVE_AND_REVIEW` |
| resulting main 与双端实际树身份 | `PENDING — ROOT_TO_FILL_RESULTING_MAIN` |

[report]: ROOT_TO_FILL_REPORT_URL
