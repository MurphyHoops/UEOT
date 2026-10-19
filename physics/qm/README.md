# UEOT-QM

当前成果：**v31.1 / Kernel 1，2026-10-19**。  
主线：从已有 UEOT-QM 和 Core v3 成果，建立可执行、可机器核查的有限维操作内核。

## 从这里开始

- [内核理论与本轮结论](UEOT_QM_KERNEL_v31.1.md)：量子合法性、对象表示、递归闭合、误差证书与三代选择。
- [运行内核](kernel/README.md)：标准库 Python 入口、API、精确示例和独立测试。
- [Lean 证明包](../../formalization/ueot-qm/README.md)：真实量子定义、Core 定理复用及构建命令。
- [机器回执](kernel/evidence/lean-verification.json)、[测试回执](kernel/evidence/runtime-verification.json)、[主张台账](status/CLAIM_LEDGER_v31.1.json)、[验收审查](audits/KERNEL_REVIEW_20261019.md)。
- [工作路线](ROADMAP.md)、[当前状态](status/CURRENT.json)。

## 本轮形成的闭环

完整 Kraus 操作产生合法概率与记录；全部有限记录响应给出协议相对的等价类；同响应态具有相同后验响应，更新在可实现响应空间内闭合。运行时精确求出 W*、响应基和分支矩阵，使用坐标继续预测。有限协议比较及误差链都保留明确覆盖和前提。

三代选择器保留指定异常方程与弱预算，推出 `(Nc,Nf,k)=(3,3,1)`，没有 atomicity 前提。具体物理谱、补偿贡献与有效窗口的适用性继续独立证明，详见 [物理接入合同](audits/G3_PHYSICAL_ADAPTER_CONTRACT_20261019.md)。

```bash
python physics/qm/kernel/demo.py
python physics/qm/kernel/verify_kernel.py
```

Python 支持 Hilbert 维数 1–4、精确有理复数及加权 Kraus 项。Lean 处理一般有限复矩阵与共同有限结果/Kraus 指标。W* 算法与 Python 实现的形式化细化，以及二者的加权/索引适配，是下一优先任务；现有测试通过不等于 Python 已被 Lean 验证。

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

历史原件字节迁移、两份 v28.1 身份裁决和历史 validator 重跑仍按先前来源清单办理。新的内核回执不会自动升级旧版本的证据状态。

