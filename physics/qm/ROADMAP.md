# UEOT-QM / Physics Roadmap

Status: active research plan, v31.0  
Date: 2026-10-19  
Layer: physics/qm  
Evidence baseline: `MurphyHoops/UEOT@195ebb06fb8afcc592c69671dabfd2250e9d1989`

## 1. 目标与当前决策

在已有 UEOT-QM 研究链上，精确连接 Frozen Core v3 的对象、协议、表示运输与证书；明确区分已证明的 Core 数学、量子扇区输入、桥接命题、有效近似和可观测后果。

本路线更新 2026-09-09 版本的迁移与研究安排。详细论证见 [v31.0 完整方案](UEOT_QM_UPGRADE_PLAN_v31.0.md)，执行状态见 [CURRENT.json](status/CURRENT.json)。

当前优先推进：

1. 有限量子 instrument、受限协议下的对象表示和可组合误差；
2. v30.11 三代条件定理的假设精简、完整谱和独立对照；
3. v23 SRN/QDRR 的方法验证与实验预注册；
4. 完成历史原件迁移后，按具体模型推进 CV、QFT/RG 与 HGP 物理实现。

## 2. 继承已有阶段

这些是已有研究版本的内容及声明范围；本表不授予新的 Lean 或实验完成状态。

| 阶段 | 当前读取的版本 | 保留内容 | 后续动作 |
|---|---|---|---|
| 有限维操作核心 | v23.0 | FFIPS、instrument conditioning、相干父级、公共代数、SRN/CPSD、QDRR | 与 Core v3 精确去重并建立 QMB-01–04 |
| 量子选择 P2 | v24.4 内的 P2 章节 | 精确 causal OPT 背景与外部两原则重构、相对独立性 | 对照 Nakahira 原文和完整背景，不将其重命名为 UEOT 原创 |
| 无限维 P1 | v24.4 | Weyl–CCR、Stone、自伴定义域、有限资源 CV | 证明能量尾、有限秩和有界可观测误差 |
| 对称/自旋/同粒子 P3 | v25.2 | Wigner、Galilei、spin、置换/Fock | 保留独立 sector 输入和 spin–statistics 边界 |
| 开放/多体/统计 P4 | v26.3 | GKSL/Davies、过程记忆、KMS、响应、有限多体 | 记忆诊断、可观测闭包与误差比较 |
| 相对论自由场 P5 | v27.1 | 自由场、局域代数、微因果性、无限模表示 | 用有界操作响应给出对象桥 |
| 相互作用/RG/EFT P6 | 两份 v28.1 | φ⁴ 一环、scheme、counterterm、matching | 原件身份裁决；Object-RG/过程粗粒化/Wilsonian RG 分型 |
| QED P7 | v29.2 | Abelian QED 一环、Ward、散射与标准基准 | 维持 FINAL scope lock；实际错误才重开 |
| 三代 P8-R(G3) | v30.11 | GOIT、指定谱异常算术、331 类见证 | 删除 selector 的 atomicity 前提；补 E^c；审计宽谱反例 |

早期 `β₁=3 → Index(D)=3 → generations` 推论保持退役。完整来源和冲突见 [SOURCE_MANIFEST](status/SOURCE_MANIFEST_20261019.json)。

## 3. 本轮完成与下一轮执行

| 工作包 | 2026-10-19 状态 | 下一交付 / 验收 |
|---|---|---|
| QMU-00 来源与方案整合 | 本次交付；历史原件字节迁移待办 | 维护单一 QM 入口，裁决 v28.1 冲突 |
| QMU-01 G3 条件精化 | 纸面证明与新精确审计完成；Lean pending | 独立算术 theorem；谱到异常/预算的 adapter |
| QMU-02 有限量子包 | planned，首个主执行任务 | QMB-01/02 真实声明、实际构建和公理审计 |
| QMU-03 协议递归闭包 | planned，已有精确正负例 | W* 一般有限词证明、reachable 更新、记忆反例 |
| QMU-04 缺陷组合 | planned | 合法距离与非负放大系数、后选择/漂移失证、有限置信证书 |
| QMU-05 QDRR 方法出口 | planned，继承 v23 解析界 | 模拟注入/噪声基线/预注册；真实数据另验收 |
| QMU-06 长期/存活 | planned | QMB-05 Cesàro 不变；QMB-06 对角 CP→QSD/Doob |
| QMU-07 CV 资源桥 | planned | 尾概率、有限秩和有界 Weyl 测试，不要求有限维精确 CCR |
| QMU-08 QFT/RG 小桥 | planned | 一个正规化模型，两侧独立计算响应及误差 |
| QMU-09 HGP 完整模型类 | planned | 完整谱、全局异常、真空/质量、阈值、独立可观测关联 |

第一轮约两至四周只验收端到端有限维切片与独立 selector 算术，不承诺全部阶段同期完成。

## 4. 六个 QM 机器证明目标

- **QMB-01**：Kraus 完整性 → 合法分支概率、正概率后验与历史记录律。
- **QMB-02**：效应响应纤维 → 唯一商下降；只有层析完备才得态唯一。
- **QMB-03**：未来拉回闭包 → 正概率条件化相容 → reachable 递归状态。
- **QMB-04**：物理/协议距离的具体收缩与局部缺陷 → M-TC 链证书。
- **QMB-05**：有限维 CPTP Cesàro 残差 → 极限点平稳，唯一混合另证。
- **QMB-06**：保持对角交换代数的 CP 存活映射 → 非负 substochastic 矩阵 → M-PE。

这些编号是任务 ID，不是已经编译的 Lean declaration。准确已有接口见 [Lean 审计](audits/CORE_LEAN_TO_QM_AUDIT_20261019.md)。

## 5. 三代前沿的新重点

指定模板的异常整除条件与弱窗口上界已足以排除多包复制，因此停止把“为什么宇宙 primitive”作为 selector 必需前提。

新的重点是：

- 将 family gauge factor 与 331 的 extended weak factor 分型；
- 解释或独立检验同质 lepton 表示模板，保留两代宽谱反例；
- 从完整协变导数求 heavy neutral-current 耦合，研究 universality 对模板的条件约束；
- 从特殊 quark family 求 rank-one 非普适耦合关联，再加入 mixing、loop 与多 mediator 误差；
- 对每个候选报告全局异常、阈值窗口和动力学门，不用 Nf=3 作为程序筛选输入。

## 6. 验收与迁移

每条主要结果按 [Core–Physics Contract](../interfaces/CORE_PHYSICS_CONTRACT.md) 登记 C/B/S/P/E/O/X 输入，分别记录数学、机器、回归与现实数据状态。

历史原件迁移需要准确文件身份与哈希；本次可读正文审计不替代这个门。QFT 的专门实现后续进入 `physics/qft/`，RG/EFT 进入 `physics/rg-eft/`，正式公共 validation 登记遵循其目录合同；本次的新检查作为 QM 方案的本地领域审计证据保存在 `physics/qm/benchmarks/`。

proof-bearing 变更必须有真实 focused build、导入可达与公理回执；当前方案和精确检查不改变 Core 106 P-ID 或四 counted generators。

