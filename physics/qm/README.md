# UEOT-QM：有限量子内核与物理总著

当前科学增量为 **v31.12 / Kernel 1.12**，出版版本为 **《UEOT物理学》3.9**。实际集成阶段和数学、物理选择、计算、经验四条状态轴均由 [CURRENT](status/CURRENT.json) 给出。

第66章的完整有限条件链、第67章的操作／微观／鲁棒桥保持有效。第68章从指定分段蓝脉冲推出增长的有限载体，接通完整矩形仪器、可见控制、物理过滤和可控省略；同时保留同时作用的无限尾反例与旗计数不可识别性。该条件模型的充分误差界为0.0498877753592667…，真实器件仍缺独立标定和完整数据。

## 当前入口

- [科学结果](UEOT_QM_KERNEL_v31.12.md)与[执行合同](UEOT_QM_EXECUTION_v31.12.md)。
- [连续中文主文](book/UEOT_PHYSICS.md)、[英文主文](book/UEOT_PHYSICS.en.md)、[中文PDF](book/UEOT_PHYSICS.pdf)与[英文PDF](book/UEOT_PHYSICS.en.pdf)：第0–68章、六附录、188项稳定结果。
- [新实现](growing_cutoff/README.md)、[四组实际运行回执](kernel/evidence/v31.12/runtime/execution_receipt.json)及[旧证明身份复用](kernel/evidence/v31.12/proof-reuse.json)。本轮没有新Lean源码，不将书面无限维结论改为机器证明。
- [现行主张台账](status/CLAIM_LEDGER_v31.12.json)、[六项精确证据边界](audits/GROWING_CUTOFF_v31.12/chapter68_formal_bindings.json)与[完整长期任务图](ROADMAP.md)。
- 继承入口：[第66章原解释器](conditioning/README.md)、[第67章实现](operational_micro_robust/README.md)、[既有Lean证明](../../formalization/ueot-qm/README.md)、[旧精确内核API](kernel/README.md)。

Core只读，GI不在范围。原182项结果对象、105条主张及历史回执保留原身份；新增六项单列。复杂量子结构、有效控制、真实物理过滤和蓝面积约束仍是独立输入。没有真实数据就不声称经验闭环，也不将有限示例等同完整量子、场论、粒子或引力理论。
