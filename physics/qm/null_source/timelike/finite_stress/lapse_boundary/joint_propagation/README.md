# 完整联合传播：快时间正极限与原固定时间核的拒收

本目录接续 \`joint_feedback\`，基线为
\`bcfde447685b0d976a94ef1e754b72fd8307cb8a\`。
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
