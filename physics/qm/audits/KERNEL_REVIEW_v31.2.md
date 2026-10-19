# UEOT-QM Kernel 1.2：领域集成审查

日期：2026-10-19。变更类别：B（QM 领域结构）。

本轮由用户“继续推进整个 UEOT-QM 的构建”和既有远端 QM 同步要求授权。审查按 `constitution/UEOT_CHANGE_CONTROL.md` 的领域 memo／交叉审查及领域状态 acceptance marker 办理。本地数学与运行验收已通过，状态为 `LOCAL_VERIFIED_CI_PENDING`；远端 CI 与正常主线集成仍单独待验收。

## 1. 集成对象

承接 main `23d36e4d4b805ef138c9179c5b33c1a89a924dbe`，复用 `qm/upgrade-core-v3-v31` 临时分支，PR [#333](https://github.com/MurphyHoops/UEOT/pull/333)。范围为 `physics/qm/**`、`formalization/ueot-qm/**` 与专用 QM 工作流。

本轮补齐真实词效应空间、有限局部表示、闭合坐标后验和完整有限自适应协议的数学接口；同时实现独立表示证书与从实际谱行到 G3 的算术桥。有限谱选择和有限量子响应都通过明确输入合同接入既有 Core。

并行 Core PR #332 已在本轮实施期间合入 main `4b29172c7efef9de95e8070abfd3ded9006bd462`。主执行者核对与本轮基线的四路径差异：Core 压缩工作流、研究登记和两个审计脚本；Core 数学源码及本轮固定依赖没有变化。最终主线集成仍需验收。

## 2. 交叉审查分工与结论

| 实现 | 实现角色 | 独立源级审查 | 结论 |
|---|---|---|---|
| `Observables`、`FiniteCoordinates` | `finite_response` | `kernel_certificates` 与主执行者 | 生成／闭包双向包含、迹对偶顺序、Ax/p 与 range 语义 CLEAR |
| `Adaptive` | 主执行者；`finite_response` 补组合接口 | `finite_response` 审核树归纳和依赖叶；主执行者复核组合 | 完整分支、叶唯一与归一化目标 CLEAR |
| 表示证书 checker | `kernel_certificates` | `spectrum_bridge` 与主执行者 | 实际词、系数方向、库与基身份、独立算术检查 CLEAR |
| 有限谱 Lean/Python | `spectrum_bridge` | `kernel_certificates` 与主执行者 | 行和、非零因子、额外和、完整弱系数及阈值边界 CLEAR |
| 原件／接口总报告 | 主执行者与专题角色 | 不同专题角色交叉核对 | 原始猜想与现行数学、程序与经验层不混同 |

这是协作代理的源级与工程语义审查，不是外部科学同行评审。checker 独立于闭包生成器的计算路径，也不意味着精确矩阵底座已获独立程序证明。

## 3. 本地已执行证据

统一 `verify_kernel.py` 实际运行 72 个方法全部通过：原有 32、表示证书 18、谱桥 22。旧演示与 `demo_v312.py` 均已运行。后者实际输出 Z/HZ/HSZ 的 2/3/4 维证书、Gram 行列式 1、1/2、1/4，以及 4、9、16 个局部等式检查。

自适应示例从 I/2 开始：先 Z，结果 0 后执行 H 再 Z，结果 1 后执行 Z。完整记录权重为 1/4、1/4、0、1/2；密度矩阵与坐标计算完全相同，总概率为 1。

谱正反例覆盖三代＋Higgs、混合两代、六代复制、补偿一代、零异常单位、额外屏蔽及部分阈值失活。六项 331 局域异常另由明确全左手行独立求和；缺少一般带荷 Ec 产生确定非零残余。详见两个专题审查。

固定 Lean 发行版最初在受限执行环境中下载失败；随后通过正常批准的本地执行，保留原代理配置，取得官方 Lean 4.33.1。归档 SHA256 与官方发行元数据一致，全部九项已安装 Git 依赖 revision 与锁文件一致。首次实际编译暴露三处模块中的参数绑定、实例解析和加法交换收尾问题；修复均未改变数学合同，最终整包构建和公理审计实际通过。

## 4. 机器验证状态

**本地 PASS；远端 CI 与主线集成 PENDING。**

官方 Lean 4.33.1 的 `lake build UEOTQM` 返回 0，输出 `Build completed successfully (8729 jobs).`。9 个模块包含 128 个显式 theorem；真实 137 个命名声明审计全部通过，依赖并集仅为 `propext`、`Classical.choice`、`Quot.sound`。源码 proof-escape gate 通过。计数限于显式定理与列出的构造，不宣称扫描全部编译器生成常量；8729 是含依赖的构建任务数。

已验证源码提交为 `323db6d1c2e50a432bdcf6a6872212426cc826ce`，树为 `5e79f7e920dbe59a5988d816a8fb8648723f6ca0`。本地先在首轮提交副本上修正三个 Lean 文件并完成构建，再将同样字节发布；30 个实现／审计／工作流／锁定源文件均与远端树和实际构建副本一致。该执行顺序与所有源码 SHA256 记入 [证明回执](../kernel/evidence/v31.2/lean-verification.json)。

独立收口复核重新读取实际构建、公理及运行回执，确认数学合同 CLEAR：有限 presentation 未预置全词充分性；完整树保留零分支与共同有限结果索引；Ax/p 输出仍在物理坐标像内；谱选择保留额外 cubic 净和、全部 ordinary 活跃及完整 b2 > 0。未发现实质缺陷。

截至本次观察，源码提交的 [工作流 39284136188](https://github.com/MurphyHoops/UEOT/actions/runs/39284136188) 仍 queued。GitHub [官方事故](https://www.githubstatus.com/incidents/8tzbpcnl75jp) 报告 Actions、Pages 和 Webhooks 性能下降；此处只登记实际观察，不把排队状态当作成功。

## 5. 本地验收已晋升的范围

- 真实 Kraus 定义的词效应与最小实闭包；有限生成存在性。
- 有限局部 presentation 的全词充分且必要性、坐标更新和物理像闭合。
- 完整有限数学适应树的记录概率与有限坐标计算接口。
- 有范围的精确表示证书 producer／checker 及实际运行结果。
- 实际 finite spectrum 到条件 G3 的代数桥与明确反例。
- 本轮五份原件的来源核对，以及其中根 PDF 的精确仓库身份。

验收不晋升：Python/JSON/PSD/search/solver/tree 程序细化；专门 d² 维数与 Wn 搜索终止；物理窗口声明的真实性；无限维或完整 QFT；所有历史档案；新实验确认；冻结 Core 的计数。

## 6. 状态与保留义务

领域 acceptance marker 位于 [CURRENT.json](../status/CURRENT.json)，逐条主张位于 [v31.2 台账](../status/CLAIM_LEDGER_v31.2.json)。机器回执已存放于 `kernel/evidence/v31.2/`；旧 Kernel 1 的源码和回执保持原身份。

本地构建、公理、运行示例、源字节核对与源级审查均已完成。合入前继续要求真实远端 CI 和领域状态一致；合入后检查实际 main 的工作流及源码身份。采用正常 PR 合并，不绕过仓库保护或强制覆盖并行工作。

