# UEOT-QM 物理学阅读入口

当前候选书稿含第0–71章、六个附录和210项结果。第71章研究共享同一 Ramsey 曲线的相关浴，给出带符号干预、有限预测与类空场响应的适用条件。本次留出与校准均使用合成数据。

- [中文第71章](book/UEOT_PHYSICS.md#ch-71) · [English Chapter 71](book/UEOT_PHYSICS.en.md#ch-71) · [完整书稿与3.12版印本](book/README.md)
- [科学说明与复核程序](correlated_bath/README.md) · [状态](status/CURRENT.json) · [主张账本](status/CLAIM_LEDGER_v31.15.json) · [研究路线](ROADMAP.md)

## 第71章之后的有限源研究

[同一有限源的应力、装置与有限数据研究](null_source/timelike/continuation/README.md)接续本地跨域研究：完成辅助静态最小场的绝对应力尾界、原场有限秩响应、相容装置壳及有限数据噪声上界的不可估计结果，保留动态反馈与器件校准开放。该研究候选有独立[复算入口](null_source/timelike/continuation/run_verification.py)与[主审裁决](null_source/timelike/continuation/REVIEW.md)，尚未并入上述正式章节或编号主张。

### 前轮：动态参考应力与初始几何一致性

[当前动态研究与统一裁决](null_source/timelike/evolution/README.md)已在同一归档参考态上完成有验证误差的模式传播、动态局部补项和无限模尾。固定原尺度、AE μ=1 且无额外有限曲率项时，初片全量子密度严格大于 **1.5101633543**；原初始几何要求的总密度为 **0.5**。因此原背景与该参考态的直接组合不满足半经典 Hamiltonian 约束，下一步须先处理总源和几何的一致性。

本轮还给出两种消去有限曲率系数的完整窗关系：原总二阶源已标定时使用两个新增密度读数；源标定未知时才升级为三项独立收缩和第四项留出。精确动态压力、窗口参考积分、自洽反馈和真实几何仪器仍开放。[实际复算入口](null_source/timelike/evolution/run_verification.py) · [总回执](null_source/timelike/evolution/verification.json)。新结果保持研究候选身份，没有升级正式章节、经验状态或 Core 物理选择。

### 前轮：初片相容与整段平均方程缺陷

[新的统一研究报告](null_source/timelike/compatibility/README.md)已给出合法的完整参考态缩放、明确保留的原混合源，以及满足初片平均约束的正源构造。在充分尺度 λ=8192，逐模估计与独立总能量估计都认证整个 η∈[0,3/16] 上无限场平均方程的相对缺陷：密度小于 **0.0291%**，压力小于 **0.810%**。另提供明确的有理源参数及其有限初片残差。

同一研究证明了相同初片空间几何和外曲率不足以直接移植旧完整量子核，并给出有限秩 Hadamard 修复。保留原混合分布时，指定非负紧支撑密度涂抹的相对应力方差仍大于 **0.7495**。下一责任是态与几何的共同演化及稳定性、噪声到几何的响应、外区量子态和真实仪器；小平均方程缺陷没有被改称为精确半经典解。

[物理合同](null_source/timelike/compatibility/CONTRACT.md) · [四项新检查与旧证据复用](null_source/timelike/compatibility/run_verification.py) · [执行回执](null_source/timelike/compatibility/verification.json)。原14项通过证据按精确提交和59个旧文件身份复用，本轮新增零次模式积分。正式书稿、Core、Lean及经验状态保持原身份。

### 当前：新制备、完整量子噪声与线性几何响应

[新的统一研究报告](null_source/timelike/response/README.md)已构造偏置的 \(\pm f_\lambda\) 完整制备，保留新旧一阶均值、完整二点函数和平均 RSET，同时将经典幅度平方混合方差从 \(3/4\) 降到 \(0\)。每个新符号分支也继承原平均源证书。完整剩余噪声已分解，指定局部测试的全模式线性项给出数值上界；预先固定的有限测试族可在充分大的相关重调尺度达到任意弱噪声目标，\(\lambda=8192\) 上完整二次量子噪声的数值上界仍开放。

同一研究精确求解保持约束的 Einstein—标量受迫线性系统。全段尺度一阶响应对精确相关源小于 **0.02215%**，有理源采用相关初片修复时小于 **0.02219%**；独立比较方法另行验证。新孔径 Weyl 仪器在声明的校准和准备合同下，256 次独立新启动可将两种候选各自的误判界压至 \(10^{-5}\) 以下。完整概率是固定背景理论结果，不是硬件数据，也不能认证任意未知幅度尾。

[共同合同](null_source/timelike/response/CONTRACT.md) · [四项新检查及18项旧证据复用](null_source/timelike/response/run_verification.py) · [执行回执](null_source/timelike/response/verification.json)。本轮冻结76个旧科学文件，新增零次模式 ODE。下一共同接口是完整连通应力二点分布：对称部分给完整噪声，推迟交换子及局域项进入量子几何响应。非线性半经典解、稳定性、外区态、总装置应力和 Core 独立物理选择仍开放。

## 历史入口 · v31.12

当时的科学增量为 **v31.12 / Kernel 1.12**，出版版本为 **《UEOT物理学》3.9**。实际集成阶段和数学、物理选择、计算、经验四条状态轴均由 [CURRENT](status/CURRENT.json) 给出。

第66章的完整有限条件链、第67章的操作／微观／鲁棒桥保持有效。第68章从指定分段蓝脉冲推出增长的有限载体，接通完整矩形仪器、可见控制、物理过滤和可控省略；同时保留同时作用的无限尾反例与旗计数不可识别性。该条件模型的充分误差界为0.0498877753592667…，真实器件仍缺独立标定和完整数据。

### 当时的入口

- [科学结果](UEOT_QM_KERNEL_v31.12.md)与[执行合同](UEOT_QM_EXECUTION_v31.12.md)。
- [连续中文主文](https://github.com/MurphyHoops/UEOT/blob/cb17211653fde30aa50e0e9848798a6a5b3b3f12/physics/qm/book/UEOT_PHYSICS.md)、[英文主文](https://github.com/MurphyHoops/UEOT/blob/cb17211653fde30aa50e0e9848798a6a5b3b3f12/physics/qm/book/UEOT_PHYSICS.en.md)、[中文PDF](https://github.com/MurphyHoops/UEOT/blob/cb17211653fde30aa50e0e9848798a6a5b3b3f12/physics/qm/book/UEOT_PHYSICS.pdf)与[英文PDF](https://github.com/MurphyHoops/UEOT/blob/cb17211653fde30aa50e0e9848798a6a5b3b3f12/physics/qm/book/UEOT_PHYSICS.en.pdf)：第0–68章、六附录、188项稳定结果。
- [新实现](growing_cutoff/README.md)、[四组实际运行回执](kernel/evidence/v31.12/runtime/execution_receipt.json)及[旧证明身份复用](kernel/evidence/v31.12/proof-reuse.json)。本轮没有新Lean源码，不将书面无限维结论改为机器证明。
- [现行主张台账](status/CLAIM_LEDGER_v31.12.json)、[六项精确证据边界](audits/GROWING_CUTOFF_v31.12/chapter68_formal_bindings.json)与[完整长期任务图](ROADMAP.md)。
- 继承入口：[第66章原解释器](conditioning/README.md)、[第67章实现](operational_micro_robust/README.md)、[既有Lean证明](../../formalization/ueot-qm/README.md)、[旧精确内核API](kernel/README.md)。

Core只读，GI不在范围。原182项结果对象、105条主张及历史回执保留原身份；新增六项单列。复杂量子结构、有效控制、真实物理过滤和蓝面积约束仍是独立输入。没有真实数据就不声称经验闭环，也不将有限示例等同完整量子、场论、粒子或引力理论。
