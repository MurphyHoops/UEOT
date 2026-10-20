# UEOT-QM

当前研发：**v31.5 / Kernel 1.5 — LOCAL_VERIFIED_CI_PENDING，2026-10-20 UTC**。最新集成身份以 [CURRENT.json](status/CURRENT.json) 为准。

规范理论总入口是 [《UEOT物理学》正式 3.1](book/UEOT_PHYSICS.md)：第 0–53 章、附录 A–F，54 章、101 个编号结果；[完整 PDF](book/UEOT_PHYSICS.pdf) 共 171 页。第 49–50 章给出有限内核和稳定性，第 51–53 章加入概率混合预算、Cesàro 平稳态与条件存活。完整推导、来源、细节、思想和未完成的科学义务在同一著作持续维护。

本版新增三项严格结果：实际通道混合的全态 TV 上界及有理预算；实际有限 CPTP 通道的平均残差、紧性和平稳态存在；次随机核的量子仪器实现、实际成功记录的 Core QSD/Perron 与 Doob 桥接。其完整范围见 [v31.5 主报告](UEOT_QM_KERNEL_v31.5.md) 和 [数学审查](audits/FINITE_DYNAMICS_REVIEW_v31.5.md)。

实际本地验收为 **18 通用模块、334 显式定理、392 项命名公理审计、100 个运行方法、4 个演示 PASS**。六个既有精确实例重新验收，42 项审计另列；四个篡改真值证明被拒绝且同数据假值证明通过。新增具体见证有 29 定理／10 定义／39 项独立审计。[统一回执](kernel/evidence/v31.5/lean-verification.json)、[64 项源清单](kernel/evidence/v31.5/source-manifest.json)

## 阅读与工作入口

- [正式总著](book/UEOT_PHYSICS.md)、[完整阅读版](book/UEOT_PHYSICS.pdf)、[逐章档案](book/CHAPTER_DOSSIER.json)：连续理论、推导、来源与证据责任。
- [本版数学和实现报告](UEOT_QM_KERNEL_v31.5.md)、[执行任务](UEOT_QM_EXECUTION_v31.5.md)：为什么选择这三项工作，实际闭合什么，如何使用资源。
- [Lean 包](../../formalization/ueot-qm/README.md)、[运行内核](kernel/README.md)：定义、接口、复验命令、具体正负见证。
- [路线图](ROADMAP.md)、[当前台账](status/CLAIM_LEDGER_v31.5.json)：根本科学问题、下一轮任务、接受条件和未完成义务。

## 已形成的有限内核

给定明确的复密度态／Kraus／Born 量子扇区及允许操作库，有限坐标相等当且仅当全部有限记录响应相等。局部闭包证书构造真实仪器与全词 presentation；分支计算 Ax、读取单位坐标概率，并在正概率时返回 Ax/p，仍留在物理可实现坐标像中。完整有限自适应树的叶律可由同一坐标计算。

实际效应定义全效应响应伪距离。完整通道收缩该量；实际全态通道缺陷经量子一步推导，接入 Core M-TC 的累计误差界。正事件后验另有放大界，零概率没有后验。现在同一通道成员库的有理权重变化给出明确的可靠预算

\[
\delta(\Phi_p,\Phi_q)\le \tfrac12\sum_b|p_b-q_b|.
\]

长期部分证明

\[
\Phi(\bar\rho_N)-\bar\rho_N=(\rho_N-\rho_0)/N,\quad
d_{\rm eff}(\Phi(\bar\rho_N),\bar\rho_N)\le1/N
\]

并在实际有限矩阵拓扑中构造不变子极限及平稳密度态。条件生存部分把真实成功记录解释为 diag(pQⁿ)，给定合法 qQ=rq 后得到 rⁿ 生存律；给定右特征数据后，Doob 不变律为 qh。全部前提、实际 Core 调用与反例见 [主报告](UEOT_QM_KERNEL_v31.5.md)。

## 执行与复验

从仓库根执行：

~~~bash
python physics/qm/kernel/demo.py
python physics/qm/kernel/demo_v312.py
python physics/qm/kernel/demo_v313.py --output-dir /tmp/qm-exports
python physics/qm/kernel/demo_v315.py
python physics/qm/kernel/verify_kernel.py --output /tmp/qm-runtime-v315.json
~~~

完成 Lean 包的统一构建后，再分别运行精确实例门与新增具体见证门：

~~~bash
python physics/qm/kernel/verify_lean_exports.py --output-dir /tmp/qm-lean-exports
python formalization/ueot-qm/scripts/verify_finite_witnesses.py --output-dir /tmp/qm-finite-witnesses
~~~

工具链固定 Lean 4.33.1；全部实际公理报告只允许 propext、Classical.choice、Quot.sound。生成源文件与真正编译验收分别记录；JSON、Python、搜索／消元／PSD／树程序的全输入细化仍独立开放。

## 核心科学边界

已形成的是量子扇区中的有限形式化内核。通用 Core 尚未无条件选择复量子结构；三代结论仍取决于指定的完整谱与有效弱窗口、表示及一致性条件。混合上界不等于任意通道缺陷的精确求值或 diamond norm。平稳存在不意味着唯一或逐时 mixing；QSD、Doob 不变律和无限条件过程也必须分开证明。本版没有新增实验数据。

下一轮优先推进独立的量子选择前提／反模型审查和保留记录与记忆的联合通道模型；并行扩展非交换存活、可失败的 QDRR 数据合同及现实 G3 义务。[工作包与资源次序](ROADMAP.md)

## 历史与证据身份

| 版本 | 累计通用定理／审计／运行方法 | 独立身份 |
|---|---|---|
| v31.1 | 56／59／32 | [原回执](kernel/evidence/lean-verification.json) |
| v31.2 | 128／137／72 | [证明](kernel/evidence/v31.2/lean-verification.json)、[集成](kernel/evidence/v31.2/integration-verification.json) |
| v31.3 | 196／213／87 | [证明](kernel/evidence/v31.3/lean-verification.json)、[集成](kernel/evidence/v31.3/integration-verification.json) |
| v31.4 | 256／287／87 | [证明](kernel/evidence/v31.4/lean-verification.json)、[集成](kernel/evidence/v31.4/integration-verification.json) |
| v31.5 | 334／392／100 | [证明](kernel/evidence/v31.5/lean-verification.json)、[当前状态](status/CURRENT.json)；具体见证审计分别统计 |

旧证据只认证各自源码。v23–v30.11 的继承链、操作／重构／CV／开放系统／场论／异常谱研究保留于正式总著和 [v31.0 总体规划](UEOT_QM_UPGRADE_PLAN_v31.0.md)。五份原件身份保持 [原审查](audits/SOURCE_AND_REPRESENTATION_REVIEW_v31.2.md)，冻结 Core 的 106 项与四生成器计数不变。
