# 完整联合传播：快时间正极限与原固定时间核的拒收

本目录接续 `joint_feedback`，基线为
`bcfde447685b0d976a94ef1e754b72fd8307cb8a`。
物理统一仍为 **OPEN**；这里研究原齐次量子约束的完整传播与准备，
不修改 Core，不包含 GI，不把齐次结果扩写成全部时空模式或实物装置。

## 本轮核心结论

保留原作用量、AE 系数、全部有限 K 源项、既定边界实现及固定 bulk
识别后，实际完整传播子在 epsilon_K=log K/K 的时间尺度上强收敛到
F_s=exp[is/(2kappa)]。这来自带高模激发修正的完整 Duhamel 证明。

把该估计在原时钟区间内统一重置后，得到更强结论：对固定原时间
Bochner-L1 向量测试，原约束映射 T_K 趋于零。因此该比较下的
state-independent rigging 和任意正常准备的固定测试两时核都退化为零。
这拒收原非零归一化 N3 门；有限 K 的物理 Hilbert 空间仍存在。
该结论还覆盖 eta_K>=-1/4、每 K 在时钟上恒定的全部既定 Friedrichs
排序序列。新的反项、其它边界实现和移动测试空间不在该排除范围内。

缩放时间上的正常两时核、有限完整 CP 记录和有界读数可以构造；
它们不是原固定时间门的通过。原 C5 与实际 C9 还分别显示平方矩逃逸、
一阶矩逃逸和真正由测量证明的导数信息不收敛。

复盘后继续构造了高斯准备与真实有限 K 的有界探针 Dyson 演化。
高斯约化读数可按明确速率隐藏，但完整记忆保留区别；固定有限秩
探针接入该逃逸准备族后作用也消失，投影成功概率受 O(1/sigma) 约束。
对原实际 C9 则可构造非零快时间两结果读数，所需峰值强度为
K/log K 量级；它还不是局域自主引力装置。

进一步把记忆能量写进同一保留 lapse 的作用量，完成真实有限 K
联合演化和条件影响泛函。总时钟生成元方差成为三个非负项之和，
证明高斯准备的完整二阶矩下界不能靠平均值重调或删除交叉项消掉。
明确的经典 w 指针有正常概率极限；这不恢复正常联合核，也没有
把旧共同平均几何自动搬到含新记忆的模型上。

实际谐振记忆演化中的有界几何读数也已校准：在同一
sigma_K=(log K)^1/10 准备下，MSE 为 O((log K)^-1/5)，
RMS 为 O((log K)^-1/10)。证明直接使用共同净化向量误差，
保留全部记录与 C9 重调误差。未截断 kappa 只证明概率收敛，
并未取得其无界二阶矩或实验单位校准。

共形／固有时 lapse 的区别也已直接检验：固定光滑 f(u)>0 的
记忆耦合保留实际传播、校准和原时间核拒收结论；完整总方差下界
相应乘 f(u_i)^2。变分给出同一记忆器的齐次密度／压力与精确
交叉协方差：f=1 类辐射，f=a 类无压物质。这些是齐次作用量投影，
没有被扩大成局域四维应力构造或新总源的共同平均解。

完整中文进展与责任边界见 [UNIFICATION_PROGRESS.md](UNIFICATION_PROGRESS.md)。

## 可验收入口

| 文件 | 新闭环 | 保留的边界 |
| --- | --- | --- |
| [ADIABATIC_CONNECTION.md](ADIABATIC_CONNECTION.md) | 完整连接、二/四粒子逆能隙与统一界 | 不投影实际演化 |
| [INITIAL_LAYER.md](INITIAL_LAYER.md) | 完整缩放传播、稠密扩张、双向传播 | 原固定正时间不同 |
| [INTERIOR_COLLAPSE.md](INTERIOR_COLLAPSE.md) | 实际原时钟固定测试核为零；正常历史排除 | 非紧致单一读数仍另审 |
| [ORDERING_SWEEP.md](ORDERING_SWEEP.md) | 全部允许截止排序序列的同类拒收 | 固定边界实现与测度 |
| [LOCAL_CONSTRAINT.md](LOCAL_CONSTRAINT.md) | 原约束精确局部复形与三种完成 | 非全局自伴约束证明 |
| [RESCALED_KERNEL.md](RESCALED_KERNEL.md) | 正常缩放两时核及完整抽象仪器 | 非真实局域装置 |
| [BOUNDED_WITNESS.md](BOUNDED_WITNESS.md) | 固定有界相干读数，含几何侧存在结果 | 不宣称已校准探针 |
| [RARE_PREPARATION.md](RARE_PREPARATION.md) | 实际 C9 距离、失败记录、后选择及 GNS 运输 | 不控制无界矩 |
| [SNAPSHOT_SPECTRUM.md](SNAPSHOT_SPECTRUM.md) | 强预解式、真实谱律与逃逸矩 | 能量矩不由强极限继承 |
| [RARE_FISHER.md](RARE_FISHER.md) | 实际混合 C9 的完整测量 Fisher 下界 | 不从方差推 QFI |
| [DEPHASING_CONTROL.md](DEPHASING_CONTROL.md) | 平滑改准备、实际对角选择、资源及完整记忆 | 丢失正常极限，非闭环修复 |
| [SCALAR_COUNTERTERM.md](SCALAR_COUNTERTERM.md) | leading 分类、具体候选与 lapse/action 代价 | 未采用新反项，四维来源开放 |
| [GAUSSIAN_CONTROL.md](GAUSSIAN_CONTROL.md) | 高斯正常准备、实际误差、精确信息／资源与完整记忆 | 极限态不正常，实际原生成元 QFI 不由此控制 |
| [PROBE_RESPONSE.md](PROBE_RESPONSE.md) | 原时钟紧算符耦合消失；实际快时间仪器及高斯组合 | 全局受控算例，装置总应力未闭合 |
| [MEMORY_ACTION.md](MEMORY_ACTION.md) | 同一 lapse 记忆作用量、实际联合传播、完整总方差下界与指针仪器 | 原固定时间核仍零；主动门与四维装置未构造 |
| [MEMORY_INFLUENCE.md](MEMORY_INFLUENCE.md) | 同一准备的精确条件影响泛函、初始混合块、响应及接触项 | 未积分或解出量子几何 |

每个科学入口有独立的新 Python 检查与源绑定 JSON。
检查验证代数、有限矩阵或外向数值界；无限维结论由文档中的解析证明
和只读源审查承担，不称机器形式化证明或外部同行评议。

## 执行与接续

只在原 Local Mac 工作树执行本目录新检查；旧科学模块及旧模式/几何
ODE 不执行。231 个前驱检查入口复用，859 个前驱科学文件逐字节冻结。
当前会话的真实计时、审查记录及验收门见
[SESSION.md](SESSION.md)、[AUDIT.md](AUDIT.md)、
[NEXT_GATE.md](NEXT_GATE.md) 和 [verification.json](verification.json)。
第一次提交前的核验回执会明确记录工作树状态，不伪称已针对未来提交执行。
