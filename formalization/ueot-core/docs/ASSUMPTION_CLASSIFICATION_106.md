# UEOT Core v3.0 — 106 项命题假设分级与内核公理审计台账

本文件在不改动已冻结 `COMPRESSION_LEDGER.yaml`（保持原字节与哈希不变）的前提下，为全部 106 项 Core v3.0 源命题提供细粒度**假设类型分级（`assumption_class`）**，并记录全库 1,051 个 Lean 模块的逐常量内核公理审计结果。

## 1. 全库内核公理纯度（2026-11-22 独立全量构建核验）

- 构建命令：`lake build UEOT`（9,757 jobs，exit 0）
- 逐常量审计脚本：`lake env lean scripts/ExhaustiveAxiomAudit.lean`
- 模块总数：**1,051**（其中定义常量的模块 **1,030** 个）
- 已编译常量总数：**19,987**（其中定理常量 **13,004** 个，定义常量 **6,281** 个）
- 自定义 `axiom` / `opaque` / `unsafe`：**0**
- `sorryAx` 依赖：**0**
- `native_decide`（`Lean.ofReduceBool` / `Lean.trustCompiler`）依赖：**0**（原 `RegisterMechanismDecisionConsumer` 的两处有限求值已升级为精确整数缩放下的纯内核 `decide` 证明）
- 唯一传递逻辑公理：`{propext, Classical.choice, Quot.sound}`

## 2. 106 项冻结源命题的假设分级汇总

| 假设分级 (`assumption_class`) | 数量 | 含义说明 |
|---|---:|---|
| `generated_from_four_core_generators` | 11 | 由四个已登记生成器（商下降、有限定量传输、正特征结构、占据极限不变性）直接重推导 |
| `standard_math_interface` | 5 | 因固定版本 Mathlib 尚未内置完整连续随机分析/偏微分谱栈而保留的过程级标准数学接口（如 `ItoRun`、`DynkinExpectationCertificate`、`TerminalGirsanovData`；后继模块已为受控有界 Brownian 源给出具体实例化） |
| `protocol_calibration_contract` | 12 | 统计采样、有限字母表集中不等式、设计矩阵非退化与共同好事件（Common Good Event）预算合同 |
| `domain_modeling_adapter` | 72 | 具体结构模型前提（Markov 可合并、折扣控制、可行核、恢复裕量、组合窗口、Price/Perron 谱系桥等） |
| `explicit_no_go_or_gauge_boundary` | 6 | 显式不可辨识性、规范自由度冗余或数据处理损失边界（防止过度强读） |
| **合计** | **106** | 与 `11 generated + 89 retained_adapter + 6 retained_boundary` 严格对齐 |

## 3. 标准数学接口项及其后继具体源实现

| P-ID | Core v3 接口形式 | 后继具体源实例化模块 |
|---|---|---|
| `P-CTL-03` | 连续时间扩散 HJB 验证，接收过程级 `ItoRun` 期望恒等式 | `BrownianControlledItoRunSource`、`BrownianControlledHJBSource` |
| `P-REC-02` | 连续时间随机恢复上界，接收 `DynkinExpectationCertificate` | `BrownianBoundedC2DynkinSource` |
| `P-KL-05` | 路径空间 KL 能量恒等式与状态投影不等式，接收 `TerminalGirsanovData` | `BrownianBoundedGirsanovSource`、`BrownianBoundedTerminalKLSource` |
| `P-QSD-04` | 可逆 killed 算子正交谱展开与准平稳收敛窗 | `GeneralPerron` / 紧谱源证书（第 39 章） |
| `P-PER-04` | 连续状态切锥可行性接口（Aubin–Nagumo 条件证书） | 离散/有限状态双向完备对应见 `ViabilitySource.p_per_03` 及第 37、40 章 |

完整逐项 JSON 数据见同目录 [ASSUMPTION_CLASSIFICATION_106.json](./ASSUMPTION_CLASSIFICATION_106.json)。
