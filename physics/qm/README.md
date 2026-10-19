# UEOT-QM

当前研发：**v31.3 / Kernel 1.3 — LOCAL_VERIFIED_CI_PENDING，2026-10-19 UTC**。

本轮把精确数值证书接入 Lean：**数值表 → 内核检查 → 真实复数量子仪器 → 全词响应坐标 → 闭合后验与完整有限自适应树**。官方 Lean 4.33.1 已完成统一构建：**13 个通用模块、196 个显式定理，213 项实际命名公理审计 PASS**。六个导出实例各自编译成功；四种数据篡改同时满足原通过证明失败、同数据 `check = false` 内核证明成功。运行回归为 **87 个方法 PASS**。

本地源码与日志见 [v31.3 证明回执](kernel/evidence/v31.3/lean-verification.json)、[实例验收](kernel/evidence/v31.3/lean-exports/verification.json)。本轮远端状态单列于 [CURRENT.json](status/CURRENT.json)，未用本地结果冒充远端 CI。

前版 v31.2 已正常合入 [PR #333](https://github.com/MurphyHoops/UEOT/pull/333)，主线 `c7aa925f338877d7338326f5cee8a165253f69dd` 的 [工作流 39294335590](https://github.com/MurphyHoops/UEOT/actions/runs/39294335590) 已通过 Lean 与 runtime。其 [集成回执](kernel/evidence/v31.2/integration-verification.json) 补充原始本地证据。

## 从这里开始

- [v31.3 内核主报告](UEOT_QM_KERNEL_v31.3.md)：五项有限条件、数域／加权／索引桥、全词结论、六实例与严格负控。
- [运行内核](kernel/README.md)：Python API、完整样例和可重复生成／验收命令。
- [Lean 证明包](../../formalization/ueot-qm/README.md)：13 模块、公共接口及实际 Core 定理复用。
- [精确证书审查](audits/EXACT_CERTIFICATE_REVIEW_v31.3.md)、[加权／可变指标审查](audits/WEIGHTED_RAGGED_REVIEW_v31.3.md)、[领域验收说明](audits/KERNEL_REVIEW_v31.3.md)。
- [工作路线](ROADMAP.md)、[当前状态](status/CURRENT.json)、[主张台账](status/CLAIM_LEDGER_v31.3.json)。

## 当前可交付的内核

固定操作库后，有限坐标相等当且仅当全部有限记录响应相等。分支在坐标上计算 `y = A x`，以单位坐标读概率，正概率后验为 `y / p`；结果仍在物理可实现坐标像中，零概率返回 `none`。完整有限自适应树的叶律也由这些坐标给出。

新 `ExactCertificate.check` 独立检查非负权重、完整 Kraus 和、空词、每个词的实际基效应、每个分支的全部局部闭包等式。这些局部条件构造数学 presentation；全词充分性与更新相容性是证明输出。`Exact` 解释真实 Gaussian-rational 复矩阵，`Weighted` 处理非负有理权重，`Ragged` 证明沿有限嵌入补零保持操作语义。

六份 [完整固定证书](kernel/certificates/v31.3/exports.json) 覆盖 Z、H+Z、H+S+Z、不同结果与项数、1 维复数样例和 4 维射影样例。Lean 验收绑定每份实际源码；导出器的 manifest 保留生成时的 `NOT_COMPILED` 状态，之后的成功由独立编译回执表达。

```bash
python physics/qm/kernel/demo.py
python physics/qm/kernel/demo_v312.py
python physics/qm/kernel/demo_v313.py --output-dir /tmp/qm-exports
python physics/qm/kernel/verify_kernel.py --output /tmp/qm-runtime-v313.json
```

在完成 `formalization/ueot-qm` 的统一 Lean 构建后，运行 `python physics/qm/kernel/verify_lean_exports.py --output-dir /tmp/qm-lean-exports`，即可从仓库根目录重新生成、绑定并实际核验证书及假值见证。CI 使用同一入口。

## 范围与下一步

Python 表示证书支持 Hilbert 维数 1–4、基数不超过 `d²`、见证词长不超过 `d²−1`。新 exporter 还限制整数为 4096 bit、补零后标量存储数为 65536、源文件为 8 MiB；这些是证据生成边界，不是全词定理的未来时域界，也不保证统一编译时间。

本轮完成通用检查器的可靠性和具体实例的内核验证；Python/JSON/闭包搜索/消元/树解释程序的全输入正确性仍未形式化。Lean 允许冗余 presentation，Python 的 Gram 独立性检验没有被改称为最小 Hilbert 实现定理。输入仍是明确的复数密度态／Kraus／Born 量子扇区。

已有三代结论保持指定谱与弱窗口条件下的 `(Nc,Nf,k)=(3,3,1)`。实际表示、完整母谱、全局异常、有效窗口、真空与质量继续有独立物理义务。下一主任务是具体量子距离的一步误差与后选择概率门，再接已有 M-TC；并行推进 QMB-05/06 长期／存活和可失败的 QDRR 数据入口。

## 版本与证据身份

| 版本 | 已实现范围 | 对应证据 |
|---|---|---|
| v31.1 / Kernel 1 | 五模块、56 显式定理、59 审计、32 运行测试 | [原证明回执](kernel/evidence/lean-verification.json)；已完成主线验收 |
| v31.2 / Kernel 1.2 | 九模块、128 显式定理、137 审计、72 测试；有限坐标／完整树／谱桥 | [原本地回执](kernel/evidence/v31.2/lean-verification.json)、[主线集成补充](kernel/evidence/v31.2/integration-verification.json) |
| v31.3 / Kernel 1.3 | 13 通用模块、196 显式定理、213 审计、87 测试；六个内核检查实例与四个假值见证 | [新版本回执](kernel/evidence/v31.3/lean-verification.json)、[台账](status/CLAIM_LEDGER_v31.3.json)；远端状态由 CURRENT 单列 |

旧证据只认证原版本源码字节。Core v3 冻结定义、106 项覆盖和四个计数生成器保持不变。

## 保留的研究与历史证据

[v31.0 升级方案](UEOT_QM_UPGRADE_PLAN_v31.0.md) 保留完整继承链、六个量子桥与更大扇区规划。继续保留 [对象—协议桥](audits/CORE_OBJECT_PROTOCOL_BRIDGE_20261019.md)、[Core/Lean 证据审查](audits/CORE_LEAN_TO_QM_AUDIT_20261019.md)、[G3 条件精化](audits/G3_SELECTOR_REFINEMENT_20261019.md)、[五份原件身份及语义核对](audits/SOURCE_AND_REPRESENTATION_REVIEW_v31.2.md)。

旧基准仍可运行 `python physics/qm/benchmarks/qm_bridge_benchmarks.py` 和 `python physics/qm/benchmarks/qm_frontier_exact_audit.py`。其他历史原件迁移、两份 v28.1 身份裁决与历史 validator 重跑继续按来源清单办理，新内核不会自动提升其证据等级。
