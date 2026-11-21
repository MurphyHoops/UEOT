# 同一作用量的有限模联合演化、恢复代价与物理态

**物理统一仍未完成。** 本轮已经把同一齐次 lapse 作用量的完整有限模式
几何—物质算子接到酉演化和正常物理解空间，并实际检验旧历史的恢复条件。
当前主要物理结论是：正型候选无法恢复旧纯几何动量预算；负型候选在保留
旧 raw 源及受控几何三阶矩时同样失败。放开几何远尾后，已构造保留旧 raw 源、
精确匹配初片两个几何均值的正常态，但其巨大几何方差使它不能签收为旧历史。

这里的几何自由度是已声明的齐次 a/κ；“完整有限模”指同一代表中所有项及
两个物质场的 k≤K 模均保留，不表示全部空间引力约束已求解。

冻结基线：**2eb6ef97be385cdcf764d63f9ec43adf8ac67b1c**。
h_i 是前驱 QUIET_WINDOW 一次选择 c=exp(-20000) 的实际历史；
不是更早 c=1e-55 的初值。A、U0、incoming薄层源和σ保持同一冻结输入。
时间和能量均为模型单位。

## 研究闭环入口

| 问题 | 已得到的可验收结果 | 入口 |
|---|---|---|
| 同一实际系数是否完整 | 全部 AE、真空常数、非零 U0 及其导数已保留 | [系数](COEFFICIENT_WINDOW.md)、[共同型](COUPLED_FORMS.md) |
| 完整联合有限模演化 | 每固定有限K、g不为零的紧时钟窗、固定η≥−1/4的Friedrichs选择，完整弱酉演化成立；占据数截断M已移除，空间K未移除 | [两种符号](ALL_SIGN_EVOLUTION.md)、[lens](LENS_EVOLUTION.md)、[ordering](ORDERING_DOMAIN.md) |
| 原snapshot与物理切片 | 明确自伴实现、正内积、正常密度和加权gluing；不把运动学零核当物理态空间 | [snapshot](SNAPSHOT_DOMAIN.md)、[切片](PHYSICAL_SLICE.md) |
| 真正的几何动量 | Πg=Pu+D−2κQ；正型窗有协变强域运输及不依赖裸源边缘的恢复排除 | [几何动量](GEOMETRIC_MOMENTUM.md) |
| 负型候选的旧源恢复 | actual raw H³<exp(160)；受控T3拒收；放开远尾后给出rank≤2正常初态匹配κ/Πg均值，计算远尾和方差代价 | [负分支闭环](NEGATIVE_RECOVERY.md) |
| 原Pu与准备对照 | 源二矩、任意正常指针的固定门前沿、改变源的两均值对照；均与Πg验收分开 | [源预算](SOURCE_BUDGETS.md)、[Pu门](MEAN_RECOVERY.md)、[准备前沿](PREPARATION_FRONTIER.md)、[shift对照](SHIFTED_STATE.md) |
| g=0时钟边界 | 完整双向散射映射、所有正常态的有界κ概率逃逸；并构造关系算子的自伴匹配域族 | [边界](G_ZERO_BOUNDARY.md)、[匹配域](BOUNDARY_MATCHING.md) |
| 原φ源在边界的极限 | raw源边缘正常极限、源能量加权极限、有限K全部raw应力均值和同片协方差极限 | [源矩与应力](RAW_SOURCE_BOUNDARY.md) |
| 原零模作为另一时钟 | 原约束的自伴实现、正常正频解、显式rigging及原C的限定Abel群平均 | [物质时钟](MATTER_CLOCK.md) |
| 保原零模对称性的正常态 | 两方向Dirac角因子、正频KG映射、旧径向源律的精确谱测度验收门 | [双零模物理态](SYMMETRIC_CLOCK.md) |
| 单向时钟源的真实成本 | 能量律/齐次 prescribed influence 保持，完整裸态改变；单次读数、Gaussian门和局域非选择准备均有明确限制 | [角态准备](ANGULAR_CLOCK_INPUT.md) |
| 空间K极限 | 静态同AE源/反项Hessian领先项抵消；孤立frame失败不等于合并演化失败 | [截止门](CUTOFF_GATE.md) |

## 当前恢复边界

正、负分支的上述结论均相对于明确量子化和域，不是全部量子引力的no-go。
负分支远尾态只匹配初片均值；它不是原平均Einstein历史或可校准装置。
物质时钟的正常Dirac态也不自动是保留完整原bare source的正常联合准备。
[统一进展](UNIFICATION_PROGRESS.md)把这些连接和未完成责任逐层列明。

## 验证与追溯

当前设置 **20个科学检查入口 + 1个范围/源码绑定入口**。
解析域、波算子、正常态和制备证明由正文及独立源码审查承担；
入口数不等于新定理数或机器形式化证明。
运行回执见 [verification.json](verification.json)，
实际不可变源码审查见 [agent_reviews.json](agent_reviews.json)，
已观察CI见 [checkpoint_ci.json](checkpoint_ci.json)。
复用190项前驱结果、冻结698个前驱科学文件，旧科学模块和旧ODE未执行。

CP1曾遗漏非零U0；该完整输入结论已经撤回。
CP2补回U0及一二阶导数后经三名只读代理重新验收，历史记录保留。
本轮仍在继续，时长及后续检查点以[会话记录](SESSION.md)和[审计](AUDIT.md)为准。
