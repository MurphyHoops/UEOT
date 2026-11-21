# 同一作用量的联合量子演化、源历史约束与实际截止极限

**物理统一核心目标仍未实现。** 本轮得到所声明齐次几何/两场有限模式
量子化的完整弱酉演化与正常物理态，并算清了原历史恢复的代价和障碍。
同时，同一实际非静态背景上的共同截止二阶 CTP，以及齐次因果逆的
强极限，已从分别存在推进到共同序列的可核验连接。

一项关键修正是：在正 κ 的自由源 u-clock、正常态和有限共同型域内，
完整源第一导数不能精确等同于同 <κ> 的经典背景源演化。
这是明确条件下的恢复排除，不是所有量子引力、mean-RSET 或近似历史的排除。
后继必须计算实际联合态的加权源及反馈，或验证另一时钟/相互作用模型；
原精确恢复合同没有被改写成已通过。

冻结基线：**2eb6ef97be385cdcf764d63f9ec43adf8ac67b1c**。
A、非零 U0、incoming 薄层源及 σ 均来自同一冻结输入。
本轮实际 quiet 历史一次选择 c=exp(-20000)，不是更早的 c=1e-55。
时间、能量与增长率均为模型单位。

## 本轮研究入口

| 问题 | 本轮闭合内容 | 证明与结果 |
|---|---|---|
| 同一作用量的完整输入 | AE、真空常数、非零U0及导数均保留 | [系数](COEFFICIENT_WINDOW.md)、[共同型](COUPLED_FORMS.md) |
| 完整有限模式演化 | 每固定K、g≠0紧时钟窗及固定η≥−1/4的Friedrichs选择，完整弱酉演化成立；占据截断移除，空间K保留 | [演化](ALL_SIGN_EVOLUTION.md)、[lens](LENS_EVOLUTION.md)、[ordering](ORDERING_DOMAIN.md) |
| 算子域与正常物理切片 | 明确snapshot自伴实现、正内积、正常密度及加权gluing | [snapshot](SNAPSHOT_DOMAIN.md)、[切片](PHYSICAL_SLICE.md) |
| 原几何动量恢复 | Πg=Pu+D−2κQ；正分支预算排除；负分支受控三阶矩排除及大尾正常对照 | [几何动量](GEOMETRIC_MOMENTUM.md)、[恢复](NEGATIVE_RECOVERY.md) |
| 完整源历史恢复 | 原薄层源的显式有界第一jet witness；任意正常free source的结构排除；实际product候选的purity初二阶及局部迹距离代价 | [恢复 N7–N10](NEGATIVE_RECOVERY.md) |
| 原Pu与准备对照 | 源二矩、固定准备门的指针前沿、改变态的两均值对照；不冒充Πg验收 | [源预算](SOURCE_BUDGETS.md)、[Pu](MEAN_RECOVERY.md)、[准备](PREPARATION_FRONTIER.md)、[shift](SHIFTED_STATE.md) |
| g=0关系时钟边界 | 完整双向散射、正常态κ概率逃逸、自伴匹配域族；边界位置随裸cutoff漂移 | [边界](G_ZERO_BOUNDARY.md)、[匹配](BOUNDARY_MATCHING.md) |
| 原φ源的边界记录 | 正常源边缘、加权能量、有限K raw应力均值及同片协方差极限 | [源与应力](RAW_SOURCE_BOUNDARY.md) |
| 原零模作物质钟 | 原C自伴实现、正频正常解、rigging及原C的限定Abel平均 | [物质钟](MATTER_CLOCK.md) |
| 正常Dirac态与旧源谱律 | 双零模角态到正频KG的unitary；R_T纯ac全实谱；旧总径向律仍须实际Rbar谱密度门 | [谱与物理态](SYMMETRIC_CLOCK.md) |
| 制备与钟读数 | 能量律/限定齐次influence保持；裸态改变、单次RMS、Gaussian门及因果局域准备成本 | [角态](ANGULAR_CLOCK_INPUT.md) |
| 同一实际共同截止CTP | response/noise、AE接触、GNS-L2及固定lapse u–u弱Hessian尾，含H4→H−2弱界 | [实际UV桥](ACTUAL_UV_BRIDGE.md)、[静态前驱](CUTOFF_GATE.md) |
| 有限K逆到全场逆 | K≥10^9共同static/action界和实际强逆极限；pressure保off-shell项，最后K1仅存在 | [共同截止逆](ACTUAL_CUTOFF_INVERSE.md) |

“完整有限模式”只指同一齐次 a/κ 模型中所有项和两物质场 k≤K 模均保留，
并不表示全部空间引力模式、四维张量约束或装置已解。
[统一进展](UNIFICATION_PROGRESS.md)给出结果的物理解释和下一验收对象。

## 当前验收边界

- 原平均Einstein背景的存在复用；正常量子联合解的存在不等于完整原历史恢复。
- 大尾初态匹配两项几何均值和一个导数，但已由有界源记录拒收为完整原源历史；
  其方差下界只属于该明确双包构造，一般负分支的必要条件是所声明三阶矩门。
- 物质钟采用全实κ与另一明确ordering/domain；其正常态不自动保原bare源或与u-clock等价。
- 实际retarded齐次逆的强截止极限已闭合；强adjoint极限、实际源GNS读数的共同极限、
  完整lapse/tensor/initial混合块及联合量子几何—源—装置的全场极限仍分别验收。

## 验证、纠错和追溯

当前 **22个科学检查入口 + 1个范围/源码绑定入口，共23项**。
解析域、散射、正常性和制备论证由正文及不可变源码审查承担；
入口数不等于新定理数、机器形式化证明或外部同行评议。

[verification.json](verification.json)记录实际执行；
[agent_reviews.json](agent_reviews.json)记录代理实际读取文件及根端Git身份核对；
[checkpoint_ci.json](checkpoint_ci.json)只录已经观察到的准确提交CI。
复用190项前驱结果、冻结698个前驱科学文件，旧科学模块和旧ODE未执行。

CP1遗漏非零U0的完整输入子结论已撤回；CP2补回U0及导数并重新审查，
该漏审和修复记录保留。后续措辞、frame因子和absolute-moment证明补全也逐项留痕。
本轮时间和最终检查点以[SESSION.md](SESSION.md)和[AUDIT.md](AUDIT.md)为准。
