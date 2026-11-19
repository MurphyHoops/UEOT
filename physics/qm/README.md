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

### 前轮：新制备、完整量子噪声与线性几何响应

[新的统一研究报告](null_source/timelike/response/README.md)已构造偏置的 \(\pm f_\lambda\) 完整制备，保留新旧一阶均值、完整二点函数和平均 RSET，同时将经典幅度平方混合方差从 \(3/4\) 降到 \(0\)。每个新符号分支也继承原平均源证书。完整剩余噪声已分解，指定局部测试的全模式线性项给出数值上界；预先固定的有限测试族可在充分大的相关重调尺度达到任意弱噪声目标，\(\lambda=8192\) 上完整二次量子噪声的数值上界仍开放。

同一研究精确求解保持约束的 Einstein—标量受迫线性系统。全段尺度一阶响应对精确相关源小于 **0.02215%**，有理源采用相关初片修复时小于 **0.02219%**；独立比较方法另行验证。新孔径 Weyl 仪器在声明的校准和准备合同下，256 次独立新启动可将两种候选各自的误判界压至 \(10^{-5}\) 以下。完整概率是固定背景理论结果，不是硬件数据，也不能认证任意未知幅度尾。

[共同合同](null_source/timelike/response/CONTRACT.md) · [四项新检查及18项旧证据复用](null_source/timelike/response/run_verification.py) · [执行回执](null_source/timelike/response/verification.json)。本轮冻结76个旧科学文件，新增零次模式 ODE。下一共同接口是完整连通应力二点分布：对称部分给完整噪声，推迟交换子及局域项进入量子几何响应。非线性半经典解、稳定性、外区态、总装置应力和 Core 独立物理选择仍开放。

### 前轮：完整二次应力噪声与同尺度可测响应

[新的统一研究报告](null_source/timelike/stress_kernel/README.md)已关闭原局部四维测试的完整二次噪声数值缺口：包含零模、全部简并度与高模尾，\(C_0/D^2<5.189752\times10^{15}\)。在重新调源的 **\(\lambda=32768\)** 上，主审独立认证完整相对方差 **<0.450316%**，相对标准差 **<6.710559%**；同尺度旧/新完整方差比 **>167.5436**。8192 上的保守上界不能通过原噪声门，但不证明实际噪声失败。

本轮证明新旧完整平均 RSET 泛函在共同合法几何类上相同，推迟交换子相同而完整噪声核相差正半定秩一项。同一局部 lapse 扰动的未来 Weyl 概率在零扰动处的斜率 **<0.06710438**。几何线分类了合法伴随测试，保留初值相关、局域通量与绝对标尺责任，并区分共形标签的相对体积盲区和共同固有钟读出。

同一尺度上的密度/压力平均缺陷分别 **<0.001812764% / 0.05060600%**，独立一阶相对尺度响应 **<0.001409585%**。声明校准及固定背景合同下，**128 次独立新启动**使每个候选的误判界低于 \(10^{-5}\)。物理长度与固有时间增为旧尺度的四倍，未认证完整装置成本优势。

[共同合同](null_source/timelike/stress_kernel/CONTRACT.md) · [四项新检查及22项旧结果复用](null_source/timelike/stress_kernel/run_verification.py) · [执行回执](null_source/timelike/stress_kernel/verification.json)。92 个旧科学文件保持原字节，新增模式 ODE 为零。完整 RSET 响应范数、有限修正几何、非线性 SCE、真实装置与外区量子态仍开放。

### 当前：有限度规扰动、局部 TT 与固有钟基准

[本轮统一报告](null_source/timelike/metric_response/README.md)已把原局部 lapse 的零点斜率推进到整个 \(|\epsilon|\le1\) 的有限概率界。在同一 \(\lambda=32768\)、原过去态与固定未来坐标 Weyl 涂抹上，旧/新 plus 概率变化分别 **<\(7.780355\times10^{-5}\) / \(5.756185\times10^{-5}\)**；含询问前失败的全部启动概率仍为旧 \([0.46364405,0.48670672]\)、新 \([0.00059723,0.01827913]\)。以 plus 至少11次判旧，**固定64次完整启动**给每候选误判 **<\(9.481784\times10^{-6}\) / \(7.050492\times10^{-6}\)**。需要独立新制备，或每次条件于完整过去仍满足合同；不能只用单次边缘概率或删除失败记录。

局部几何线实际构造紧支撑 TT 测试，使用完整空间张量波方程和规范不变伴随读出；全模式二次应力常数 **\(C_T<9.188034\times10^8\)**，32768时指定原始读出 RMS **<\(2.823004\times10^{-5}\)**，未把它称为已校准应变灵敏度。该通道在未扰动齐性背景上对旧/新齐性幅度律完全相同，原密度降噪不能直接移植。

固有钟线给出额外纯经典分支几何的精确非线性解和带钟/体积误差的有限门分离，也证明未知标尺及内部标量钟的盲性。它的初片绝对尺度按分支改变，不能替代原同背景量子实验。三条几何作用域逐项列明；完整量子 RSET 响应、非线性 SCE 与真实硬件仍开放。

[共同合同](null_source/timelike/metric_response/CONTRACT.md) · [四项新检查及26项旧结果复用](null_source/timelike/metric_response/run_verification.py) · [执行回执](null_source/timelike/metric_response/verification.json)。108 个旧科学文件保持原字节，新增模式 ODE 为0。前轮密度噪声及平均方程缺陷保留原背景，没有被搬到整个有限度规路径。

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
