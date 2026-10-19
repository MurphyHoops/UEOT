# UEOT-QM

当前研发：**v31.2 / Kernel 1.2 — LOCAL_VERIFIED_CI_PENDING，2026-10-19**。  
本轮已使用官方 Lean **4.33.1** 在本地实际执行 `lake build UEOTQM`，退出码为 **0**：九个模块的 **128 个显式 theorem 声明全部编译通过，137 项实际公理审计 PASS**，依赖仅为 `propext`、`Classical.choice`、`Quot.sound`。**72 个运行测试方法及两个演示均已通过**。  
这些结果绑定源码提交 [`323db6d1c2e5`](https://github.com/MurphyHoops/UEOT/commit/323db6d1c2e50a432bdcf6a6872212426cc826ce)，见 [v31.2 本地证明回执](kernel/evidence/v31.2/lean-verification.json)。GitHub Actions 仍在排队，PR #333 与主线集成尚未验收；最近已完成主线验收的版本仍是 **v31.1 / Kernel 1**。  
主线：从已有 UEOT-QM 和 Core v3 成果，构造具有合法记录、有限表示、闭合更新和明确证据范围的量子操作内核。

## 从这里开始

- [v31.2 内核主报告](UEOT_QM_KERNEL_v31.2.md)：全词效应空间、有限坐标、完整自适应树、独立表示证书与实际谱桥。
- [运行内核](kernel/README.md)：标准库 Python 入口、API、精确示例和独立测试。
- [Lean 证明包](../../formalization/ueot-qm/README.md)：量子定义、数学接口、Core 定理复用及构建命令。
- [原件与表示语义审查](audits/SOURCE_AND_REPRESENTATION_REVIEW_v31.2.md)、[谱桥审查](audits/SPECTRUM_BRIDGE_v31.2.md)。
- [v31.2 集成 PR #333](https://github.com/MurphyHoops/UEOT/pull/333)：本轮代码与远端 CI 入口；当前本地验证已通过，远端 CI 和 resulting-main 仍待验收。
- [工作路线](ROADMAP.md)、[当前状态](status/CURRENT.json)。

## 本轮已实现的增量

Kernel 1 的完整 Kraus 操作已给出合法概率、全词响应商及可实现响应空间内的递归更新。v31.2 进一步建立以下数学合同，新增数学层已通过本地实际 Lean 编译和公理检查：

- **全词效应与有限坐标**：由真实 Heisenberg 拉回构造词效应；实际词生成、单位效应与局部闭包共同保证有限坐标保持全部有限词响应。
- **坐标上的闭合更新**：分支计算 `y = A x`，从单位坐标读概率，正概率后验计算 `y / p`；输出仍属于同一物理可实现坐标像。
- **完整有限自适应树**：记录允许依已观察结果选择下一动作，所有结果枝都保留；叶概率的总和及坐标解释接到同一个记录模型。
- **独立表示证书**：导出实际词见证、基、全部分支矩阵及库身份。checker 从 Kraus 数据直接复算局部等式，以 Gram 行列式检验独立性，无需重跑表示搜索。
- **有限谱桥**：从 family 和额外物质条目求和，再导出既有三代 selector 的异常式与必要弱预算。物理表示、完整谱、补偿贡献和有效窗口继续显式输入。

本轮运行验收包括 32 项既有测试、18 项表示证书测试和 22 项谱桥测试。新表示证书保持固定时齐库范围，有限协议比较仍只认证所列准备与协议。三代主结论仍是指定谱及窗口合同下的 `(Nc,Nf,k)=(3,3,1)`；没有新增 atomicity 前提。

```bash
python physics/qm/kernel/demo.py
python physics/qm/kernel/demo_v312.py
python physics/qm/kernel/verify_kernel.py --output /tmp/ueot-qm-runtime-v312.json
```

Python 支持 Hilbert 维数 1–4、精确有理复数及加权 Kraus 项；表示证书基数不超过 `d²`，见证词长不超过 `d²−1`。这个词长限制约束证据大小，证书所覆盖的允许有限记录没有统一时域上限。

Lean 处理一般有限复矩阵与共同有限结果/Kraus 指标。新数学 presentation 与 Python/JSON、加权项、不同结果集合之间的适配仍未形式化；搜索终止、消元程序正确性与外部坐标的物理可实现性也各有后续任务。程序测试通过不等于 Python 已由 Lean 验证。

## 已验收基线与证据身份

[v31.1 / Kernel 1](UEOT_QM_KERNEL_v31.1.md) 已完成五模块、56 个 theorem 声明及 59 个审计目标的验收，其 [Lean 回执](kernel/evidence/lean-verification.json)、[运行回执](kernel/evidence/runtime-verification.json)、[主张台账](status/CLAIM_LEDGER_v31.1.json) 和 [验收审查](audits/KERNEL_REVIEW_20261019.md) 保留原版本身份。

v31.2 的新回执按 `kernel/evidence/v31.2/` 单独登记。[本地证明回执](kernel/evidence/v31.2/lean-verification.json) 保存本轮源码身份、实际构建和公理检查结果。当前状态为 `LOCAL_VERIFIED_CI_PENDING`；本地构建、公理检查、程序回归、远端 CI／主线集成和物理适用性分别报告，不沿用旧回执给新源码背书。

## 保留的研究与历史证据

[v31.0 升级方案](UEOT_QM_UPGRADE_PLAN_v31.0.md) 保留完整继承链、六个量子桥及更大扇区规划。

此前审计继续保留：

- [对象—协议桥](audits/CORE_OBJECT_PROTOCOL_BRIDGE_20261019.md)
- [Core/Lean 证据](audits/CORE_LEAN_TO_QM_AUDIT_20261019.md)
- [G3 条件精化与宽谱对照](audits/G3_SELECTOR_REFINEMENT_20261019.md)
- [来源清单](status/SOURCE_MANIFEST_20261019.json)、[v31.0 主张台账](status/CLAIM_LEDGER_v31.json)

旧的两个精确审计程序仍可从仓库根执行：

```bash
python physics/qm/benchmarks/qm_bridge_benchmarks.py
python physics/qm/benchmarks/qm_frontier_exact_audit.py
```

本轮已核对上传 PDF 与当前仓库根目录 `UEOT_v3_top.pdf` 的同字节身份。其他历史原件迁移、两份 v28.1 身份裁决和历史 validator 重跑仍按先前来源清单办理。新的内核回执不会自动升级旧版本的证据状态。

