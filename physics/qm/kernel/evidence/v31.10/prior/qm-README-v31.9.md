# UEOT-QM：有限量子内核与物理总著

当前 **v31.9 / Kernel 1.9 — LOCAL_VERIFIED_REMOTE_PENDING**；实际统一科学与正式书本地门已齐，v31.9 远端验收待完成。 [CURRENT](status/CURRENT.json)明确区分当前源身份、历史执行复用与仍待完成的远端身份。

目标是基于 UEOT 建立完备、可解释、可检验的量子物理理论。理论思想、全部推导、前提、反例与开放责任持续维护于[《UEOT物理学》正式 3.5：66 章（0–65）、6 个附录、161 个稳定编号结果、248 页实际 PDF](book/UEOT_PHYSICS.md)及[完整 PDF](book/UEOT_PHYSICS.pdf)。已有有限量子内核不等于完整自然理论已证明。

| 本轮责任 | 实际成果与边界 |
|---|---|
| 精确全效应距离 | 真实矩阵绝对值的半迹公式、合法最优效应、等先验判别和非循环 PSD 支持证书；零迹前提明确 |
| 最小纯化与等距 | 全密度纯化 iff 实际秩界、Fin rank 达到下界；同边际纯态在明确辅助维数方向下直接等距 |
| 变长停止预算 | 真实吸收补齐、非法历史零块、原叶联合态回接；只向真实 J 参考未停止质量计费 |

41 个公共模块、854 条显式 theorem、1123 个唯一命名公理审计；本轮新增 107 条 theorem、138 个审计目标。十三组具体见证合计 298 条 theorem、110 个定义、8 个缩写，共 416 个审计。 本轮统一门实际编译全部公共模块并执行公共公理审计，实际执行三份新增见证（147 个命名审计）。十份旧见证的 269 项审计、六精确证书的 42 项审计、四个篡改真证明拒绝与四个同数据假值证明、100 个运行方法和四个演示，按未变的科学输入、依赖闭包与既往真实执行回执复用；这些旧门本轮未重新运行。 允许基础仅为 `propext`、`Classical.choice`、`Quot.sound`；实际 Lean 构建有普通 linter 警告。

98 项受验源与当前发布候选保持同一 SHA256 `bf026d2a1f7d8c8bd1f9f6c1ad9015aa20bdae6bd36b9d432c7ce6f0581effc0`。实际统一构建 8805 jobs、退出 0。[证明回执](kernel/evidence/v31.9/lean-verification.json)、[源清单](kernel/evidence/v31.9/source-manifest.json)与[旧门身份复用](kernel/evidence/v31.9/legacy-reuse.json)给出实际范围。

## 阅读与推进入口

- [本轮完整报告](UEOT_QM_KERNEL_v31.9.md)、[当前主张台账](status/CLAIM_LEDGER_v31.9.json)、[当前执行状态](status/ACTIVE_RESEARCH_v31.9.json)。
- [总著目录和逐章证据](book/README.md)、[Lean 包](../../formalization/ueot-qm/README.md)、[运行内核](kernel/README.md)。
- [路线图](ROADMAP.md)、[本轮合同与实际完成范围](UEOT_QM_EXECUTION_v31.9.md)、[书的实际本地门](book/evidence/v3.5/local-release-gates.json)。

原 70 项主张逐值保留，新增 14 项分别对应第 63–65 章。冻结 Core 的 106 项和四生成器以及其他研究保持独立。复理论的 Core 唯一选择、一般谱与无限过程、真实实验、质量与连续理论仍开放；三代仍依赖完整谱、表示、阈值与有效窗口前提。

## v31.8 历史远端身份

已闭环 v31.8 的科学源码提交为 `d9a1858c86ca82e08ae862389b51c1ea76690c24`，实际受验 main 为 `97c7b29c1aec470be58ca34b552e9d56ad06c197`；[PR #350](https://github.com/MurphyHoops/UEOT/pull/350)、[PR CI 39420751354](https://github.com/MurphyHoops/UEOT/actions/runs/39420751354)及[main CI 39424068985](https://github.com/MurphyHoops/UEOT/actions/runs/39424068985)各有实际 PASS。后续元数据已随本轮基线 `6b3ba80ec418ff04c4b6e2cd5c321b654540e9d1` 保留。

这些历史身份及原本地/发布注释对应关系见[原整合回执](kernel/evidence/v31.8/integration-verification.json)，不作为本轮 v31.9 的 CI 运行。当前旧门复用另有逐项源码、依赖和既往实际执行闭包；本轮新证明和新见证须有各自实际执行。远端 artifact ZIP 内部内容不由这些本地元数据推断。

