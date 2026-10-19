# UEOT-QM / Physics Roadmap

状态：**v31.1 / 第一操作内核**  
日期：2026-10-19  
领域：physics/qm  
Core 基线：`54378ff962b2a6038d9405edb83a33a3099833cb`

## 当前目标

已有 v23–v30.11 研究经 v31.0 审计后，形成首个有限维操作内核：量子合法性、全词响应对象、可实现响应空间的递归更新、精确有限表示与有范围的证书。

当前完整论证见 [v31.1 内核报告](UEOT_QM_KERNEL_v31.1.md)，原始阶段规划见 [v31.0](UEOT_QM_UPGRADE_PLAN_v31.0.md)，实际状态见 [CURRENT.json](status/CURRENT.json)。

## 本轮交付与任务边界

| 工作包 | 本轮推进 | 下一项验收 |
|---|---|---|
| QMU-00 来源与方案 | 维护单一 QM 入口、继承旧审计 | 历史原件字节迁移及两份 v28.1 身份裁决 |
| QMU-01 G3 | 无 atomicity 的整数 selector 与逐前提/复制对照进入 Lean | 实际有限谱逐项求和→selector；保留谱与窗口前提 |
| QMU-02 有限量子包 | 建立独立包、PSD/Kraus/概率/后验及有限 ancilla 证明 | weighted Kraus、不同结果指标与数域 adapter |
| QMU-03 协议递归 | 全词响应商及 `range → Option range` 更新；运行时 W* 与适应树 | W* 张成和坐标 iff 的 Lean 证明、程序细化 |
| QMU-04 缺陷组合 | 真实 M-TC 复用、有限协议 TV 与有限误差轨迹证书 | 指定物理距离的局部收缩/缺陷界及条件化 theorem |
| QMU-05 QDRR | 保留 v23 解析合同，尚未新增实验结果 | 固定协议、噪声基线、注入验证、统计门 |
| QMU-06 长期/存活 | 仍为后续任务 | CPTP Cesàro 不变性、对角 CP→substochastic→M-PE |
| QMU-07 CV | 保留能量与有限资源合同 | 尾概率、有限秩、Weyl 有界测试 |
| QMU-08 QFT/RG | 保留正规化模型与表示运输分型 | 单一模型，两侧独立有界记录响应及误差 |
| QMU-09 HGP | 保留完成谱、两代宽模板、heavy-current 前沿 | 完整全局异常、真空/质量、阈值与可观测关系 |

代码与证明的实际通过状态统一由 [Lean 回执](kernel/evidence/lean-verification.json)、[运行回执](kernel/evidence/runtime-verification.json) 和 [主张台账](status/CLAIM_LEDGER_v31.1.json) 给出。上表的某个切片完成，不代表该工作包的全部物理阶段完成。

## 六个量子桥的准确覆盖

| 桥 | 当前机器/运行切片 | 尚未覆盖 |
|---|---|---|
| QMB-01 | Kraus 完整性→分支概率、正概率后验、固定控制词归一化；适应树运行实例 | Lean finite-tree 解释器与一般树归纳 |
| QMB-02 | 全词响应纤维与唯一商 decoder，真实调用 M-QD | 有限效应坐标与该函数响应的机器等价；协议层析条件 |
| QMB-03 | 从前缀记录律推导递归相容；闭合 reachable Option 更新 | W* 有限张成、数域/索引 adapter 和程序细化 |
| QMB-04 | 非负标量递推调用 M-TC；实际有限协议与轨迹比较 | 每个具体量子距离的 uniform 局部界 |
| QMB-05 | planned | 有限 CPTP Cesàro 残差→平稳极限点；唯一混合另证 |
| QMB-06 | planned | 对角存活 CP→非负 substochastic 矩阵→M-PE |

## 下一轮执行次序

1. **证明有限表示正确。** 定义 Heisenberg 词效应与 W_n，证明 W* 张成、trace duality、有限坐标 iff 和 pullback 更新；将闭合 reachable 接口落到有限坐标。
2. **补实现 adapter。** Gaussian-rational→Complex、非负 weighted→ordinary Kraus、每动作不同结果集→统一有限指标零填充；选择证明携带证书或程序细化路线。
3. **证明一种真实误差合同。** 固定协议闭包、准备/观测对应和操作 seminorm，再证明局部界并调用现有 transport。
4. **并行关闭 G3 的有限谱桥。** 用完整谱逐项计算导出前提，再调用已建立的 selector。谱输入不得内置三代或最终异常方程。
5. **选择一个实验或扩大扇区的出口。** QDRR 与长期有限维桥优先；其余按资源和模型依赖推进。

## 继承的研究链

| 既有版本 | 保留内容 | 当前处理 |
|---|---|---|
| v23.0 | FFIPS、instrument conditioning、公共代数、SRN/CPSD、QDRR | 操作核落地；SRN/QDRR 接入另验收 |
| v24.4 | 外部原则量子重构、Weyl–CCR、有限资源 CV | 量子扇区输入与重构前提分开登记 |
| v25.2 | Wigner、Galilei、spin、置换/Fock | 对称与 spin–statistics 接口继续独立 |
| v26.3 | GKSL/Davies、记忆、KMS、有限多体 | 联合状态反例已纳入内核测试 |
| v27.1 | 自由场、局域代数、微因果性 | 后续使用有界操作响应桥 |
| 两份 v28.1 | 相互作用、scheme、counterterm、matching | 先完成版本身份核查与 RG 分型 |
| v29.2 | QED 一环、Ward、散射基准 | 保持已有范围锁定 |
| v30.11 | GOIT、指定谱异常算术、331 类见证 | 原子性已从选择前提删除，物理接入继续 |

早期 `β₁=3 → Index(D)=3 → generations` 推论继续退役。family gauge factor 与 331 的 extended weak factor 保持分型；同质轻子模板、异常补偿和有效窗口具有实质选择作用。

## 集成原则

按 [Core–Physics Contract](../interfaces/CORE_PHYSICS_CONTRACT.md) 保留 C/B/S/P/E/O/X 输入。领域结构修改提供交叉审查与状态 acceptance marker。实际 Lean 源码进入专门包，运行时与领域证据进入 QM；冻结 Core 计数保持不变。

历史迁移、公共 validation 登记和 QFT/RG 专门实现继续遵循原目录合同。完整机器回执、编译源码与有限程序结果分别存档，不能互相替代。

