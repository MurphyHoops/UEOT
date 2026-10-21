# UEOT-QM：有限量子内核与物理总著

当前 **v31.8 / Kernel 1.8 — MAIN_VERIFIED**。[CURRENT](status/CURRENT.json)分别记录原本地验收、已通过的实际源码PR/main CI与本次独立元数据身份。

目标是基于UEOT建立完备、可解释、可检验的量子物理理论。理论思想、全部推导、前提、反例与开放责任持续维护于[《UEOT物理学》正式3.4：63章（0–62）、6附录、147个稳定编号结果、229页实际PDF](book/UEOT_PHYSICS.md)，以及[完整PDF](book/UEOT_PHYSICS.pdf)。

| 本轮关键点 | 实际成果与边界 |
|---|---|
| 全效应与复局部层析 | 全部合法效应分离密度，全部产品效应识别任意复联合态；固定受限仪器库仍有独立识别责任 |
| 完整纯性与纯化比较 | 完整凸极点 iff 归一向量；真实同载体辅助酉，异载体先等距嵌入共同直和 |
| 逐动作记录预算 | 共同固定深度因果控制器、真实历史与旧协议回接、实际动作缺陷之和控制完整记录TV |

35 个公共模块、747 条显式 theorem、985 个唯一命名公理审计；本轮新增 101 条 theorem、130 个审计目标。十组具体见证另计 193 条 theorem、71 个定义、5 个缩写，共 269 个审计。 六精确证书42审计、四真假配对控制、100运行方法、四演示均实际通过。全部89受验源与实际执行绑定；允许基础仅为propext、Classical.choice、Quot.sound。[证明回执](kernel/evidence/v31.8/lean-verification.json)与[源清单](kernel/evidence/v31.8/source-manifest.json)记录实际身份。

实际8799-job统一本地执行仍绑定原89源SHA256 `a34337cd75cd70b0f2e1125899c4dcd09aa7b132642adaad2c17ef8a69f12f6e`。实际远端受验发布输入的89源SHA256为 `054f2e01c50f25d2519a2200eeda5ccd9849c27cfc67141eeaaf552dd4d995d1`；仅一处文档注释把英文词 admit 改为 have，数学代码不变，未重跑本地编译。两份原始源码清单及追加的发布身份桥分别保留；最终发布原字节已通过实际PR运行 39420751354 与独立main运行 39424068985。 [发布身份桥](kernel/evidence/v31.8/publication-source-reconciliation.json)给出两者的逐项对应。

## 阅读与推进入口

- [本轮完整报告](UEOT_QM_KERNEL_v31.8.md)、[当前主张台账](status/CLAIM_LEDGER_v31.8.json)、[当前执行状态](status/ACTIVE_RESEARCH_v31.8.json)。
- [总著目录和逐章证据](book/README.md)、[Lean包](../../formalization/ueot-qm/README.md)、[运行内核](kernel/README.md)。
- [路线图](ROADMAP.md)、[本轮已完成本地科学与书门的合同](UEOT_QM_EXECUTION_v31.8.md)。

v31.7 的源码PR #347、两实际CI与元数据PR #348保持独立历史身份；v31.8科学源码发布、真实PR/main CI和逐项字节回读现已完成。冻结Core的106项、四生成器以及其他研究保持独立。复理论的Core唯一选择、一般谱与无限过程、真实实验、质量与连续理论仍开放；三代仍是带完整谱、表示、阈值与有效窗口前提的条件结论。

## 实际远端验收与元数据身份

[PR #350](https://github.com/MurphyHoops/UEOT/pull/350)及[实际整合回执](kernel/evidence/v31.8/integration-verification.json)记录本版唯一科学源码发布、两次独立CI和逐项Git blob核对。

| 实际身份 | 值 |
|---|---|
| 源码提交 / tree | `d9a1858c86ca82e08ae862389b51c1ea76690c24` / `6717f47ff1a062f04cb0ba54e01ebaeddac5770a` |
| PR CI | [39420751354](https://github.com/MurphyHoops/UEOT/actions/runs/39420751354)，PASS；实际 8799 build jobs |
| 受验主线提交 / tree | `97c7b29c1aec470be58ca34b552e9d56ad06c197` / `2669b1fa73d37b442398d9c0fa7b2ffd3972cd9d` |
| 独立 main push CI | [39424068985](https://github.com/MurphyHoops/UEOT/actions/runs/39424068985)，PASS；实际 8799 build jobs |

最终89项发布输入、56项实际递归Core源码、三份规范正文和全部338项冻结发布载荷均与实际源码及受验主线逐项一致。原8799 jobs仍只绑定原a343…本地输入，实际CI绑定054f…发布输入；单词注释桥及原验收回执保留原字节。CI解码日志逐项核对39条源码hash、985个公共审计名、100个运行测试名，并核对证书/正反控的执行摘要及十组见证269项审计总数。见证193/71/5的种类分拆来自已绑定本地源码和回执；未下载artifact ZIP，不声称检查其内部逐名或演示JSON。

当前证据与导航元数据在后续独立提交中记录这些真实身份；该元数据提交自身不冒充上述任何CI受验提交。原12份本地元数据可按整合回执内的科学源码提交及Git blob精确恢复，旧本地待远端措辞按该历史检查点理解。此次未新增科学执行、实验、前提外结论或下一版本合同。
