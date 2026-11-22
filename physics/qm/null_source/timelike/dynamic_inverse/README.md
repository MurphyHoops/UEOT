# 完整响应谱、合法态匹配与保留双增长模的逆

本轮接续 [前轮同态正窗](../dynamic_seed/README.md)，实际推进“受控近似能否通向精确共同历史”的下一门。
结果是：**完整开右半平面谱恰有两条简单正实增长根；保留它们的因果线性逆和双变量无共振系数逆现已建立。**
同时排除冻结片上态后单独修补 jerk 的 UV 错误路径。

固定同一个 unfiltered 实际态、原 M2、U0、两场、canonical Q/P、全热壳和 AE 方案。
不逐时换根，不删除快模，不把求得的线性逆宣称为已完成的非线性精确历史。

## 1. 本轮关闭的具体结果

| 新结果 | 认证值／范围 | 证明入口 |
|---|---|---|
| 完整复谱 | P 在开右半平面恰两条简单正实根，没有非实右半平面根 | [SPECTRUM](SPECTRUM.md) |
| 快根固有时增长率 | 11.45521916747093 < sigma_F/A < 11.45521917819977，模型单位 | [fast_root.json](fast_root.json) |
| 快慢频率比 | 468087.11913820513 < sigma_F/s_* < 468087.34103423485 | [fast_root.json](fast_root.json) |
| 快根约束／态 | 完整线性 Hamiltonian 缺陷为 0；原 incoming 态同步运输；非 gauge | [STATE_MATCHING](STATE_MATCHING.md) |
| 保留两根的严格因果逆 | 光滑零过去响应；背景 proper 窗 1/24 模型单位 | [INVERSE](INVERSE.md) |
| 短窗 sup 增益 | norm(w) < 4.20e-14 norm(f)，norm(w') < 1.30e-7 norm(f) | [causal_inverse.json](causal_inverse.json) |
| 全部二阶及以上纯／混合频率 | abs(P(n s_*+m sigma_F)) > 11.99，n,m>=0,n+m>=2 | [harmonics.json](harmonics.json) |
| 双变量逆的四阶导数界 | M4 < 1.73e18；完整算子域为 graph 域 | [INVERSE](INVERSE.md) |
| 双变量实际态 | 有限势能范数下精确 Jost 阶乘收敛，保留两幅度及原 Q/P、eta_ref | [STATE_MATCHING](STATE_MATCHING.md) |
| 冻结 canonical covariance 的 UV 条件 | 当前模类中 Hadamard iff 全部 V=a''/a jets 匹配 | [STATE_MATCHING](STATE_MATCHING.md) |

这是分析证明加符号／区间证书，未声称新增机器形式化或外部人类同行评审。

## 2. 为什么这轮推进改变了下一任务

上一轮已经给 eta∈[0,1] 的近似残差和法向导数。
新快模说明：只固定静态过去、incoming 态、慢幅度和二阶系数，不能直接得到没有核的逆。
它并没有证明非线性无解或非唯一。

闭合后的主路线改成保留两个一次幅度的 u(z,w)=z+w+O(total degree²)，
而且本轮已证明全部组合频率无共振，给这个空间上的真实收敛线性系数逆。
下一门是完整 AE/Jost 非线性映射与余项估计；通过后才能构造有误差控制的精确共同历史族。

有限初片因果逆是另一项已经闭合的工具。
它不能直接从无限过去卷积旧慢残差，也不能突然截断残差而冻结旧初片全部数据。
这两个域的区别和剩余责任都在 [反思及下一验收](REVIEW.md) 中明确登记。

## 3. 六项新检查与继承链

| 检查 | 内容 |
|---|---|
| [spectrum.py](spectrum.py) | pole residues、差商、完整谱证明所需恒等式与符号界 |
| [fast_root.py](fast_root.py) | 正尾界、相关 log(x) 精确消元、快根／留数 |
| [state_matching.py](state_matching.py) | AE 对数系数、八阶 Riccati、实际 Jost covariance、约束 |
| [causal_inverse.py](causal_inverse.py) | 正实部结构、Bromwich 积分与短窗定量增益 |
| [harmonics.py](harmonics.py) | 无限纯／混合频率、统一分母、四阶系数逆 |
| [review.py](review.py) | 独立差商、前六阶递推与域／物理主张复核 |

[统一复现](run_verification.py) · [本地回执](verification.json) · [基线 CI](baseline_ci.json)。

复用74项已通过结果，冻结272个继承科学文件，旧 checker 重跑0次；
模式和几何 ODE 积分0次。主执行者在同一 Mac 工作树执行，三位 native 研究代理只读审查。
精确提交的 CI、artifact 与复核见 [研究 PR #468](https://github.com/MurphyHoops/UEOT/pull/468)，保持 OPEN DRAFT。

## 4. 总体目标仍按物理责任验收

非线性共同历史、物理选解、完整涨落法则、联合约束和局域可校准引力仪器仍开放。
相同 full joint twirl 配共同协变选择／仪器的 old/new 全记录等价继续有效。
不同 fast 幅度是不同几何输入，不能偷换成原制备降噪的可辨认后果。
Core 只读，GI 排除；统一物理目标尚未完成。
