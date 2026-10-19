# UEOT-QM / Physics Roadmap

状态：**v31.2 / Kernel 1.2 — LOCAL_VERIFIED_CI_PENDING**  
日期：2026-10-19  
领域：physics/qm  
本轮研究基线：`23d36e4d4b805ef138c9179c5b33c1a89a924dbe`  
最近已验收版本：v31.1 / Kernel 1；Core v3 冻结定义与计数保持不变。

## 当前目标

已有 v23–v30.11 研究经 v31.0 审计后，在 v31.1 形成有限维操作内核：合法量子记录、全词响应对象、可实现响应空间的递归更新、精确有限表示与有范围的证书。

v31.2 将实际 Heisenberg 词效应、有限坐标 presentation、完整有限自适应树与谱行和接入现有内核，并提供可导出、可独立复查的表示证书。**官方 Lean 4.33.1 的本地 `lake build UEOTQM` 已以退出码 0 完成，九模块、128 个显式 theorem 声明全部编译通过；137 项实际公理审计 PASS，仅依赖 `propext`、`Classical.choice`、`Quot.sound`。72 个运行测试方法和两个演示也已通过。**

本地验证绑定源码提交 [`323db6d1c2e5`](https://github.com/MurphyHoops/UEOT/commit/323db6d1c2e50a432bdcf6a6872212426cc826ce)，详见 [v31.2 本地证明回执](kernel/evidence/v31.2/lean-verification.json)。GitHub Actions 仍在排队，[PR #333](https://github.com/MurphyHoops/UEOT/pull/333) 的远端 CI 与主线集成尚未验收。最近已完成主线验收的版本仍是 v31.1。本轮完整论证见 [v31.2 内核报告](UEOT_QM_KERNEL_v31.2.md)，原始阶段规划见 [v31.0](UEOT_QM_UPGRADE_PLAN_v31.0.md)，实际状态见 [CURRENT.json](status/CURRENT.json)。

## 本轮交付与任务边界

| 工作包 | 已实现的切片与证据层 | 下一项验收 |
|---|---|---|
| QMU-00 来源与方案 | 上传五份原件有字节与章节记录；PDF 与基线根目录文件身份一致；维护单一 QM 入口 | 其他历史原件迁移、两份 v28.1 身份裁决与原有 validator 复现 |
| QMU-01 G3 | 既有无 atomicity selector 已完成主线验收；本轮实际谱行和→异常式/弱预算的 Lean 桥已通过本地编译及公理审计；谱与反例程序已通过 | 完成新桥的远端 CI／主线集成；继续证明实际表示系数、完整母谱、额外补偿和弱窗口匹配 |
| QMU-02 有限量子包 | 既有 PSD/Kraus/概率/后验及有限 ancilla 已完成主线验收；本轮真实 Heisenberg 对偶与词效应已通过本地编译及公理审计 | 完成远端 CI／主线集成后，推进 Gaussian-rational、weighted Kraus、不同结果和项数的 adapter/refinement |
| QMU-03 协议递归 | 既有全词响应商与 reachable 更新已完成主线验收；本轮 W* 最小闭包、有限坐标 iff、Ax/p 闭合更新和完整树已通过本地编译及公理审计；独立表示 checker 已实测 | 先完成远端 CI／主线集成，再把具体 JSON 证书解释成 Lean 实例；保留算法终止/消元的独立缺口 |
| QMU-04 缺陷组合 | 既有真实 M-TC 复用、有限协议 TV 与逐步轨迹证书保持；本轮没有新增统一量子距离结论 | 固定一种物理距离的局部收缩/缺陷界及正概率条件化 theorem |
| QMU-05 QDRR | 保留 v23 解析合同，尚未新增实验结果 | 固定协议、噪声基线、注入验证、统计门 |
| QMU-06 长期/存活 | 仍为后续任务 | CPTP Cesàro 不变性、对角 CP→substochastic→M-PE |
| QMU-07 CV | 保留能量与有限资源合同；明确有限矩阵不能承载精确全空间 CCR | 尾概率、有限秩、Weyl 有界测试及无界算子定义域桥 |
| QMU-08 QFT/RG | 保留正规化模型与表示运输分型 | 单一模型，两侧独立有界记录响应及误差 |
| QMU-09 HGP | 保留完整谱、两代宽模板、heavy-current 前沿；本轮六类 331 局域异常的显式 Weyl 行和进入精确程序 | 全局异常、规范群全局形式、真空/质量、阈值与可观测关系；不把六零当作三代充分条件 |

v31.1 的 [Lean 回执](kernel/evidence/lean-verification.json)、[运行回执](kernel/evidence/runtime-verification.json) 和 [台账](status/CLAIM_LEDGER_v31.1.json) 保留旧源码身份。v31.2 的新回执写入 `kernel/evidence/v31.2/`，按实际源码哈希、运行和公理输出登记。上表一项切片完成，不代表该工作包的全部物理阶段完成。

## 六个量子桥的准确覆盖

| 桥 | 主线已验收基线及本地已验证的 v31.2 增量 | 尚未覆盖 |
|---|---|---|
| QMB-01 | 已验收 Kraus→概率/后验/固定控制词归一化；本轮 `Adaptive.Protocol`、叶记录唯一、非负及总概率一已通过本地编译与公理审计 | 新源远端 CI／主线集成；Python 不同结果集合、树序列化与 Lean 数学解释器之间的适配 |
| QMB-02 | 已验收响应纤维与唯一商 decoder，实际调用 M-QD；本轮词效应实张成与有限坐标↔全词响应已通过本地编译与公理审计 | 新源远端 CI／主线集成；具体协议的层析能力和更小物理 Hilbert 实现条件 |
| QMB-03 | 已验收前缀比值→递归相容及 closed reachable update；本轮有限坐标 Ax/p 与完整树叶律接口已通过本地编译与公理审计 | 新源远端 CI／主线集成；JSON/数域/weighted/索引适配、外部坐标可实现性以及程序细化 |
| QMB-04 | 非负标量递推实际调用 M-TC；有限协议与逐步轨迹比较均有既有程序证据 | 指定量子距离的统一局部界；后选择事件概率门 |
| QMB-05 | planned | 有限 CPTP Cesàro 残差→平稳极限点；唯一混合另证 |
| QMB-06 | planned | 对角存活 CP→非负 substochastic 矩阵→M-PE |

上述“有限坐标↔全词响应”建立在实际生成词、单位效应与全部局部拉回等式上。只枚举有限词深、仅比较有限协议概率或只记录 hash 都不能代替这些条件。Lean presentation 允许冗余；运行 checker 增加实基独立性检查。两者都不直接给出更小 Hilbert 模型、信息位成本或 Π/Φ 驱动识别。

## 当前验收与下一轮执行次序

1. **完成 v31.2 的远端 CI 与主线集成。** 本地统一入口构建、137 项实际公理审计、72 个运行测试方法和两个演示已经通过。先将本地回执、源码提交和领域审查对齐，待 Actions 执行后验收对应提交的远端结果；PR 合并后再验证 resulting-main。当前保持 `LOCAL_VERIFIED_CI_PENDING`，不能把本地通过登记为远端 CI 或主线通过。
2. **让具体表示证书成为 Lean 实例。** 先完成 Gaussian-rational→Complex、非负 weighted→ordinary Kraus、每动作不同结果/项数→共同有限指标。再证明短 checker 的解释可靠性，把导出局部等式接入 `FiniteObservablePresentation`。完整 W_n 搜索终止与消元证明另列，只在实际依赖时展开。
3. **证明一种真实误差合同。** 固定准备/观测对应、协议闭包和操作 seminorm 或 trace distance，证明局部界后调用既有 M-TC。正概率后选择保留事件质量下界；不由有限样本 TV 声称全协议距离已受控。
4. **推进 QMB-05 与 QMB-06。** 有限 CPTP 的 Cesàro 残差和平稳极限点先行；对角存活 CP 接到 substochastic 矩阵和既有 Core 存活桥。长期存在、唯一性、混合率、路径存活各自验收。
5. **完成一个可失败的数据入口。** QDRR 先冻结准备、仪器、允许协议、噪声与零假设，保存原始记录和注入控制。闭包证书是已知精确模型的结果，现实含噪模型识别仍需统计和部署覆盖。
6. **继续 G3/HGP 的物理模型义务。** 从明确表示和完整母谱解释系数，提供弱 EFT 的阈值匹配、全局异常、标量势与质量。程序窗口布尔值只声明条件；实际窗口存在需要另证。
7. **按接口扩大到 CV 与 QFT/RG。** 先有界 Weyl 测试、能量/尾部界，再处理无界算子；QFT/RG 使用一个指定正规化模型、明确的协议/读出运输及独立误差。

本轮使 QMU-01/03 的首个谱/表示数学切片完成本地实际编译与公理审计，远端 CI／主线验收仍待完成。不重复开设同题研究包，不把 C1–C7 的有限切片标记为全部科学端口关闭。主线验收之后，优先减少具体证书到 Lean 实例的可检查缺口。

## 继承的研究链

| 既有版本 | 保留内容 | 当前处理 |
|---|---|---|
| v23.0 | FFIPS、instrument conditioning、公共代数、SRN/CPSD、QDRR | 操作内核及有限表示持续落地；SRN/QDRR 接入另验收 |
| v24.4 | 外部原则量子重构、Weyl–CCR、有限资源 CV | 量子扇区输入与重构前提分开登记 |
| v25.2 | Wigner、Galilei、spin、置换/Fock | 对称与 spin–statistics 接口继续独立 |
| v26.3 | GKSL/Davies、记忆、KMS、有限多体 | 联合状态反例已纳入内核测试 |
| v27.1 | 自由场、局域代数、微因果性 | 后续使用有界操作响应桥 |
| 两份 v28.1 | 相互作用、scheme、counterterm、matching | 先完成版本身份核查与 RG 分型 |
| v29.2 | QED 一环、Ward、散射基准 | 保持已有范围锁定 |
| v30.11 | GOIT、指定谱异常算术、331 类见证 | 原子性已从 selector 前提删除；本轮有限谱行和桥已通过本地 Lean 验证，六局域异常程序已补强，物理接入继续 |
| v31.1 | 首个可执行操作内核、56 theorem/59 审计、32 程序测试 | 已验收基线；原回执和版本文档保留 |
| v31.2 | 有限表示/树/谱新合同、独立证书、72 程序测试 | LOCAL_VERIFIED_CI_PENDING：128 theorem 本地实编译通过，137 项实际公理审计 PASS，72 运行方法及两个演示 PASS；远端 CI／主线集成待验收 |

早期 `β₁=3 → Index(D)=3 → generations` 推论继续退役。family gauge factor 与 331 的 extended weak factor 保持分型；同质轻子模板、异常补偿和有效窗口具有实质选择作用。

## 集成原则

按 [Core–Physics Contract](../interfaces/CORE_PHYSICS_CONTRACT.md) 保留 C/B/S/P/E/O/X 输入。领域结构修改提供交叉审查与状态 acceptance marker。实际 Lean 源码进入专门包，运行时与领域证据进入 QM；冻结 Core 计数保持不变。

历史迁移、公共 validation 登记和 QFT/RG 专门实现继续遵循原目录合同。源身份、语义审查、实际编译、公理输出、运行证据和物理适用性分别存档；阶段合同关闭不增加冻结 Core 计数，也不自动支持现实对象、自维持、目的或普适双驱动的更强主张。

