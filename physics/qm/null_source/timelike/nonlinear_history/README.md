# 同一 incoming 态的精确非线性共同历史

本轮承接冻结的 a01fd663：保留两条真实增长根，关闭完整重整化应力的非线性映射、精确 mean-SCE 历史和同幅度误差门。继而证明当前 incoming 条件没有唯一选定快幅度，并排除仅随机化这两个增长幅度来承接非退化源能量的方案。新的纯度反例还明确了完整 CP 记录合同与任意非线性协变选择的区别。

## 已关闭的五项

1. **精确全阶核。** 用 W=F+F− 的精确三阶方程拆出两个低 Born 阶与绝对可和高尾；前两阶的对数权重恰好匹配四阶几何导数。完整原 AE k 减项、有限局部项、实际零模、热壳全部保留。
2. **同半径非线性映射。** 在权重 (1+lambda)^4 log(e+lambda) 的双变量 Wiener 空间 E4 内，完整密度和压力全纯。||u||E4≤0.1 时 ||S(u)||A<4；无需旧 WKB 的七阶导数，也没有缩小求解空间的系数半径。
3. **完整线性逆接合。** 在所有总次数至少二的慢／快组合频率上，||T||A→E4<2e20。新全量 RSET 的 DS(0) 精确等于冻结 P(Theta)，不是只在两个根上相等。
4. **精确共同历史及误差。** 总几何球 rho=1e−25、线性种子和校正球各 rho/2，收缩率≤0.128。构造保留两幅度的真实解析解。Ward 和固定静态过去给完整齐次平均 Einstein 方程；相同 incoming 态随几何共同运输，正窗上全部平均残差及法向导数恒为零。同幅度残差到解距离界 <2.3e20。
5. **闭合后的选解裁决。** 固定非零慢幅度，快幅度仍给不同精确解；这些解共享慢过去的前 468087 个整数增长阶。当前已给条件不唯一选解。仅随机化增长幅度仍不能消去改变零模源能量带来的静态过去常数约束。

## 阅读顺序

- [全阶协方差核、原 AE 减项与同半径证明](KERNELS.md)
- [显式逆、收缩、同态正窗和误差定理](EXISTENCE.md)
- [精确非唯一性、反思及下一物理关口](SELECTION.md)
- [独立审查、证据等级和冻结合同](REVIEW.md)

| 认证量 | 保守界 |
|---|---:|
| 同半径全纯几何球 | ||u||E4≤0.1 |
| 完整空间方程球上界 | <4 |
| 校正域 E4 线性逆 | <2×10^20 |
| D²S 在半球的界 | 6400 |
| 精确求解总球 rho | 10^−25 |
| 收缩率 | ≤0.128 |
| 固定双圆盘 (Rz,Rw) | (10^−28,10^−51) |
| 同幅度残差—距离增益 | <2.3×10^20 |
| 具体正窗 | T=1/sigma_F，终点在两个半径的一半处 |

这些幅度是十分保守的充分条件，不是物理最大幅度；不覆盖旧 z≤10^−4 种子窗。proper duration 使用模型单位，不换称实验秒。

## 精确构造的范围

保持双场 closed-S3 FLRW、G=2T、minimal massless、AE mu=1、零额外有限曲率项、固定原 M2/U0 及 unfiltered incoming 制备。原 Q/P、eta_ref、完整 S0 谱与 thermal occupations 不变。不同几何的有限片 Cauchy 协方差按同一 incoming 数据运输，通常不同；本轮没有冻结旧 seed 的有限片密度算符再改几何。

收缩唯一性限定在同一两幅度和认证解析球内。物理态与全阶 Hadamard 在严格内部双圆盘的实际轨道上验收，未把闭边界的四阶对数正则性冒称全部时间光滑性。

这是当前明确物质模型的精确非线性平均历史存在结果，尚未给出完整涨落引力法则、联合算符约束、真实控制器／探针／时钟，或经验确认。Core 物理选择与整体统一目标仍开放。

## 可复核证据

五项新检查：[kernels.py](kernels.py)、[norm_bounds.py](norm_bounds.py)、[inverse_bound.py](inverse_bound.py)、[history.py](history.py)、[selection.py](selection.py)。全部结果对应同名 JSON；[汇总回执](verification.json)。

[运行入口](run_verification.py)复用 **80 项前驱结果**，以完整 source/hash/CI 链冻结 **293 个继承科学文件**。没有运行旧科学 checker 或模式／几何 ODE。root 独占已授权 Mac 工作区写入执行，恰好三位原生研究子智能体只读 GitHub／文献并做数学审查。

[前驱精确 HEAD 科学 CI](https://github.com/MurphyHoops/UEOT/actions/runs/44693131877)与[出版 CI](https://github.com/MurphyHoops/UEOT/actions/runs/44693131858)均 SUCCESS。本轮提交、精确 HEAD CI、artifact 和最终三方审查记录在 [PR #468](https://github.com/MurphyHoops/UEOT/pull/468)；PR 保持 OPEN DRAFT，不合并。
