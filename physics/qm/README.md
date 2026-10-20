# UEOT-QM

当前研发：**v31.4 / Kernel 1.4 — LOCAL_VERIFIED_CI_PENDING，2026-10-19 UTC**。

理论总入口为 [《UEOT物理学》正式 3.0](book/UEOT_PHYSICS.md)，连续正文为第 0–50 章、附录 A–F；[PDF](book/UEOT_PHYSICS.pdf) 与正文同目录。第 49 章接通精确证书、有限响应坐标和内核执行，第 50 章展开实际量子稳定性。总著保留操作语义、重构输入、物理适用条件和未完成义务；具体机器证明以 Lean 源码、命名审计及绑定源码的回执为准。

本轮新增 **效应 → Born 概率界 → 全效应响应伪距离 → 完整通道收缩与实际缺陷 → Core M-TC 组合 → 正事件后验界**。统一 `lake build UEOTQM` 已实际通过：**15 个通用模块、256 个显式定理、287 项唯一命名公理审计 PASS**；允许的基础仅为 `propext`、`Classical.choice`、`Quot.sound`。**87 个运行方法和 3 个演示 PASS**。六个导出实例重新编译，产生 42 项独立审计；四种篡改的原通过证明被拒绝，同数据的四份 `check = false` 内核证明通过。详见 [本轮证明回执](kernel/evidence/v31.4/lean-verification.json)、[运行回执](kernel/evidence/v31.4/runtime-verification.json) 和 [实例验收](kernel/evidence/v31.4/lean-exports/verification.json)。

这些是本轮实际本地验收。v31.4 的远端 CI 与主线集成尚未验收，状态由 [CURRENT.json](status/CURRENT.json) 单列。上一已完成主线版本 v31.3 的 PR #335 及主线工作流 39300120071 具有独立 [集成回执](kernel/evidence/v31.3/integration-verification.json)，不替代新源码的验收。

## 从这里开始

- [正式总著](book/UEOT_PHYSICS.md) 与 [PDF](book/UEOT_PHYSICS.pdf)：完整理论正文、条件与论证，而非仅有版本报告。
- [v31.4 内核主报告](UEOT_QM_KERNEL_v31.4.md)：实际效应、全效应上确界、完整通道误差、严格正后验及证据边界。
- [Lean 证明包](../../formalization/ueot-qm/README.md)：15 模块、公共接口、实际 Core 定理复用及复核命令。
- [运行内核](kernel/README.md)：精确数值证书、Python API、样例与可重复生成／验收。
- [效应与稳定性审查](audits/EFFECT_STABILITY_REVIEW_v31.4.md)：60 个新增定理、14 个公开定义的完整名单、假设和已执行聚焦验证。
- [精确证书审查](audits/EXACT_CERTIFICATE_REVIEW_v31.3.md)、[加权／可变指标审查](audits/WEIGHTED_RAGGED_REVIEW_v31.3.md)：继续适用的数域与有限证书合同。
- [工作路线](ROADMAP.md)、[当前状态](status/CURRENT.json)、[v31.4 主张台账](status/CLAIM_LEDGER_v31.4.json)。

## 当前可复用的内核

固定操作库后，有限坐标相等当且仅当全部有限记录响应相等。分支在坐标上计算 `y = A x`，以单位坐标读概率，正概率后验为 `y / p`；结果仍在物理可实现坐标像中，零概率返回 `none`。完整有限自适应树的叶律由这些坐标给出。`ExactCertificate.check` 检查非负权重、完整 Kraus 和、空词、每个基矩阵的实际词效应、每个分支的全部局部闭包等式，从五项有限条件构造真实仪器及全词 presentation。[ExactCertificate](../../formalization/ueot-qm/UEOTQM/ExactCertificate.lean)

`Exact` 解释真实 Gaussian-rational 复矩阵，`Weighted` 通过精确平方根把非负权重实现为普通 Kraus 矩阵，`Ragged` 证明有限嵌入补零保持操作。六份 [固定证书](kernel/certificates/v31.3/exports.json) 覆盖 Z、H+Z、H+S+Z、不同结果与项数、1 维复数样例和 4 维射影样例；本轮已经重新生成、绑定源码并实际核验。生成时的 manifest 继续保留 `NOT_COMPILED`，后续成功由独立编译回执表达。

新增 `Effect` 直接要求实际矩阵满足 $E\succeq0$ 与 $I-E\succeq0$，并证明 $P_E(\rho)=\operatorname{Re}\operatorname{tr}(E\rho)\in[0,1]$。完整 Kraus 拉回保持效应，每个有限记录的实际词效应也属于此集合。由全部效应定义

$$
d_{\mathrm{eff}}(\rho,\sigma)=\sup_{0\preceq E\preceq I}|P_E(\rho)-P_E(\sigma)|.
$$

已经证明非负、对称、三角不等式、上界 1、零值当且仅当全部效应概率相等，以及每个共同后续记录的响应控制。此处正式登记为伪距离；本轮尚未在 Lean 中证明密度态分离或与迹范数、diamond norm 的识别。[Effects](../../formalization/ueot-qm/UEOTQM/Effects.lean)、[Stability](../../formalization/ueot-qm/UEOTQM/Stability.lean)

对同一有限载体上的完整通道，实际证明收缩。通道缺陷 $\delta(\Phi,\Psi)$ 是全态输出伪距离的上确界，进而得到真实轨迹界

$$
d_{\mathrm{eff}}(\rho_n,\sigma_n)
\le d_{\mathrm{eff}}(\rho_0,\sigma_0)+\sum_{j<n}\delta(\Phi_j,\Psi_j).
$$

该量子一步递推由 Kraus 定义推导，再实际调用既有 Core M-TC。两条序列可采用不同结果／Kraus 类型，每条序列内部类型固定，矩阵可随时间改变。后续记录响应比较使用同一个操作库。对同一仪器、同一结果且两态事件概率都严格正，后验差另有 $2d_{\mathrm{eff}}/p_\rho$ 上界；若 $d_{\mathrm{eff}}<p_\rho$，则证明第二态事件仍为正。完整结论与假设见 [稳定性审查](audits/EFFECT_STABILITY_REVIEW_v31.4.md)。

## 运行与复核

从仓库根目录执行：

```bash
python physics/qm/kernel/demo.py
python physics/qm/kernel/demo_v312.py
python physics/qm/kernel/demo_v313.py --output-dir /tmp/qm-exports
python physics/qm/kernel/verify_kernel.py --output /tmp/qm-runtime-v314.json
```

完成 `formalization/ueot-qm` 的统一构建后，运行 `python physics/qm/kernel/verify_lean_exports.py --output-dir /tmp/qm-lean-exports`，重新生成并核验证书及假值见证。新 `channelDefect` 是数学上确界定义；这些命令没有被宣称为计算它的程序。具体命令与证据格式见 [运行内核说明](kernel/README.md)。

## 本轮范围与后续建设

**QMU-04 完成的是有限共同载体完整 Kraus 通道与正事件后验的数学切片。** 丢弃结果后的通道误差不自动控制两个不同仪器的标签或自适应历史；需先显式加入经典记录与量子记忆。ancilla 稳定误差、密度态分离、范数识别和可执行的通道缺陷数值上界仍需独立证明。条件化可以放大误差，零概率后验继续未定义。[范围审查](audits/EFFECT_STABILITY_REVIEW_v31.4.md)

Python 表示证书支持 Hilbert 维数 1–4、基数不超过 `d²`、见证词长不超过 `d²−1`。exporter 另限制整数为 4096 bit、补零标量存储数为 65536、源文件为 8 MiB；这些界限约束证据生成，并不限制全词定理的未来记录长度，也不保证统一编译时间。通用 Lean checker 与逐实例证明已经完成；Python/JSON/闭包搜索/消元/PSD/树程序的全输入细化继续开放。冗余 presentation 的充分性不等于最小物理 Hilbert 实现。[证书说明](UEOT_QM_KERNEL_v31.3.md)

三代结论保持为指定谱与弱窗口条件下的 `(Nc,Nf,k)=(3,3,1)`。实际表示、完整母谱、全局异常、有效窗口、真空与质量继续具有独立物理义务。标准复密度态／Kraus／Born 量子扇区仍为明确输入，本轮没有新增经验验证。后续优先推进可认证的通道缺陷上界及记录扩展，并行开展 QMB-05/06 长期／存活和可失败的 QDRR 数据入口，详见 [路线图](ROADMAP.md)。

## 版本与证据身份

| 版本 | 对应范围与实际本地验收 | 集成身份 |
|---|---|---|
| v31.1 / Kernel 1 | 五模块、56 显式定理、59 审计、32 运行测试 | [原证明回执](kernel/evidence/lean-verification.json)；已完成主线验收 |
| v31.2 / Kernel 1.2 | 九模块、128 显式定理、137 审计、72 测试；有限坐标／完整树／谱桥 | [原本地回执](kernel/evidence/v31.2/lean-verification.json)、[主线集成补充](kernel/evidence/v31.2/integration-verification.json) |
| v31.3 / Kernel 1.3 | 13 模块、196 显式定理、213 审计、87 测试；六实例／四假值见证另列 | [证明回执](kernel/evidence/v31.3/lean-verification.json)、[主线集成](kernel/evidence/v31.3/integration-verification.json) |
| v31.4 / Kernel 1.4 | 15 模块、256 显式定理、287 审计、87 测试、3 演示；六实例／四假值见证重新核验 | [证明回执](kernel/evidence/v31.4/lean-verification.json)、[台账](status/CLAIM_LEDGER_v31.4.json)；LOCAL_VERIFIED_CI_PENDING |

新增 60 个定理与 14 个公开定义共列入 74 个命名审计目标，其中定义含 9 个携带证明的构造和 5 个数据定义。287 是通用命名审计数，六实例的 42 项和四个假值见证的 4 项单列。旧证据只认证原版本源码字节；新 [55 项源清单](kernel/evidence/v31.4/source-manifest.json) 绑定当前候选。Core 冻结定义、106 项覆盖和四个计数生成器保持不变。

## 保留的研究与历史证据

[v31.0 升级方案](UEOT_QM_UPGRADE_PLAN_v31.0.md) 保留完整继承链、六个量子桥与更大扇区规划。继续保留 [对象—协议桥](audits/CORE_OBJECT_PROTOCOL_BRIDGE_20261019.md)、[Core/Lean 证据审查](audits/CORE_LEAN_TO_QM_AUDIT_20261019.md)、[G3 条件精化](audits/G3_SELECTOR_REFINEMENT_20261019.md)、[五份原件身份及语义核对](audits/SOURCE_AND_REPRESENTATION_REVIEW_v31.2.md)。正式总著把论证组织为连续正文，历史版本和原始证据各自保留身份。

旧基准仍可运行 `python physics/qm/benchmarks/qm_bridge_benchmarks.py` 和 `python physics/qm/benchmarks/qm_frontier_exact_audit.py`。其他历史原件迁移、两份 v28.1 身份裁决与历史 validator 的证据等级继续按来源清单核准。
