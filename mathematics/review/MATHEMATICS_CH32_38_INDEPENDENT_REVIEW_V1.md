# 数学著作第 32–38 章独立内容核验收据

日期：2026-10-20。

结论：**CLEAR_WITH_EXPLICIT_API_SCOPE**。完整阅读第 32–38 章及附录 F，并逐项对照下述关键 Lean 声明、实际定义、源索引和原始检查记录，未发现阻塞性的数学假命题、同源偷换、量词倒置或错误数值。本收据独立于书稿作者的自审；它是书稿内容核验，未重新运行 Lean，也不代替正式模块构建或发布审查。审阅者参与过联合风险部分的研发。

## 1. 冻结对象与排版增量

| 对象 | 字节数 | SHA-256 |
|---|---:|---|
| 作者原稿 UEOT_MATHEMATICS.md | 298372 | `c9596e541cd4aba2ad43c0eb8738ac377f14625621a8720f993e8b795b71306d` |
| 最终核验的工作树书稿 | 298383 | `7981369dc93272afec006aa2d18486de3ffc28fe9b06e9f6f9e855c29cf9126b` |
| UEOT_MATHEMATICS_SOURCES.md | 29560 | `dd6d8693f8a1ca744257c8d26ee61ee9e5371ab4fb993fce4258ca1d97edf9cf` |
| PRINT_DELTA_V2.json | 477 | `a2704538aef34e1d43e0853d1e2753672d405f675b9928e6881f9e490be462e1` |

工作树书稿位于 `/workspace/scratch/548ae22ee5c9/ueot-books/mathematics/UEOT_MATHEMATICS.md`。作者原稿、打印差分记录位于本收据相邻的 `../mathematics/`。

实际完整 diff 只有第 37.3 节 Viable 的 aligned 公式：在后继条件的蕴涵前加入换行和缩进。递推项、量词、条件和其它源字节保持一致；没有重复审读未改变的原 106 条。

## 2. 核心数学核对

| 章节 | 核验结果与不可删除的前提 |
|---|---|
| 32 | H0 八型与实际目录一致。M-QD 保留满射及纤维相容；集合降落与可测降落区分。M-TC 保留非负传输常数和逐步误差。M-OI 需要真实极限、连续测试与分离性。M-PE 消费正特征数据，不产生其一般存在性。账本实值为 11 generated、89 adapter、6 boundary；四机制的最小性仅相对于登记推导系统。 |
| 33 | 正比例不改变零关系但改变缺陷数值；零关系不保证三角性。双边校准需要正下常数和非负上常数；准三角常数及跨阶段常数的方向正确。标度链的系数与局部缺陷同步变换。双驱动定理刻画同一数值目标；锚定 Φ 可识别 Π，锚定 Π 识别 Φ 还需 λ≠0；排序等价更弱。 |
| 34 | FBT 使用独立形成误差、binding 传输和 Lipschitz 条件。P9 的两常值流记录没有尺度/动力学相容方程。P12 消费同一物理源、可信底座、程序来源及实施证明、故障包络、资源、身份、谱系和尺度桥；结论是渐近平均损坏、期望累计资源等条件组合，不是有限死亡或逐路径永续。PARTIAL / EXPLICIT BOUNDARY 与现实支持 UNVERIFIED 均有原状态文件依据。 |
| 35 | 商、源核、生存、修复均保持同一来源。所有时刻概率一安全需要初始律支撑在固定点内，不能推出非空性。Bellman 最优只比较同一安全动作限制内的全部因果策略。可信有效修复程序接回原核，并未被赋予未经证明的最优性。8/5 的手算反例与 Bellman 方程一致，正文未冒称独立 Lean 见证。 |
| 36 | 后验来自实际历史纤维；同一粗历史中的动作因子相同。占据 ν 来自真实前缀与策略扩张。认证收费为 ε+(1−ε)ν(Cᶜ)，以 κ 代换需要 ε≤1；风险另需共同事件包络。零质量历史不需认证；训练设计均值不能替换实际 ν。 |
| 37 | traceSupport 不依赖未知策略概率；在同一实际正历史上等于后验支持。正后继 iff 保留旧历史正质量、动作正质量和非空 Succ。递推先选择一个共同动作，再要求全部非空观察后继可行；必要性与充分性使用同一实际律。完整 fallback 保留 T=0 边界；终值 True 只约束 n<T 的行认证。可执行检验需要确切源支持关系，不从样本未出现推断支持为零。严格记忆例、零历史边界及已认证死路均与实际源码一致。 |
| 38 | 联合律按实际训练记录再采所选未来核构造。Good-only 拟合、覆盖和预算检查只付一次注册校准坏质量。薄桥内部用同候选 viablePolicy 推出 ν(Cᶜ)=0；具体注册例则直接证明零占据，正文未混称两种策略实例。两个真实选择质量 7/8、1/8，条件风险 1/8、1/4，故实际联合风险 9/64；16 exp(−8)≤1/16、β=1/2 给保守证书 17/32。全一记录有真实正概率且预算为 1，确实排除全记录小预算前提。零未认证占据仍允许正物理失败风险。 |

主要对照源：工作树 `formalization/ueot-core/` 下的 QuotientDescent、TransportCertificate、OccupationLimitInvariance、PositiveEigenstructure、MinCore 三文件、DualDriveGaugeCompleteness、C4FBT、C6PurposeMechanism、AutopoiesisClosure、ObjectScaleCalculus、ProgramPurposeInformationBoundary、CoreSourceAllTimesAssembly、SafeOptimalControlFromViability、RepairProgramSafeControlBridge、DeploymentCoverage、TrainingDeploymentJoint；以及 `../../viability/production-candidates/` 的 PosteriorSupportCoverage、FiniteSupportViability、FiniteSupportViabilityCheck、ControlCoverageWitness、RegisteredDeploymentRisk、RegisteredDeploymentRiskWitness、ViableRegisteredJoint。

## 3. 交接必须保留的形式 API 范围

以下是数学叙述与当前现成 Lean 入口的粒度区别，不是发现反例：

1. 第 36 章的现行路径 TV/风险入口要求 `Fintype Y`；第 37 章支持桥及支持 Viable 本身不要求 Y 有限。不能将后一条的广度直接赋予前一条。有限支撑情形的文字论证不等于已有任意可测观察空间的完整形式入口。
2. 第 38.3 节允许书面按行写 N_j 的集中界；当前注册联合入口的样本类型是同一个 `Fin N`，具体例取 N=256。逐行不等样本量是相同有限并合推理的数学推广，不是本轮另有的 Lean 联合端点。
3. `hfit`、`hcap`、`hinit`、`hchecked` 的相关条件确实在 Good 上使用；当前两个联合端点的 `henvelope` 仍量化所有候选。书面逐 Good 风险推理只需选定好分支的包络，但不能据此声称现成 Lean 签名已把全候选包络端口删除。

附录 F 已说明章内 M 编号可以组合多个形式结果与书面推理，并非每项都对应一个完全同型的单独 Lean 声明。上述范围应随新窗口交接保留；如需进一步放宽形式 API，应另行证明。

## 4. 原始检查记录核验

只读核对 `../../checks/` 的原始 source、log、status，下面五个实际成功子项的源 SHA、日志 SHA 均与各自原 status 一致；全部打印依赖只含 propext、Classical.choice、Quot.sound 的子集，无 sorryAx。

| 原检查 | 成功子项 | 实际打印数 |
|---|---|---:|
| check-03 | SupportViabilityPolicyCheck_v1.lean，退出 0 | 12 |
| check-04 | RegisteredGoodJointCheck_v2.lean，退出 0 | 9 |
| check-06 | SupportViabilityFiniteCheck_v2.lean，退出 0 | 17 |
| check-06 | ViableRegisteredJointCheck_v1.lean，退出 0 | 22 |
| check-08 | RegisteredSelectionWitnessCheck_v3.lean，退出 0 | 12 |

有限关系检查原日志实际含 `(true, false, true)`。check-04 整批仍为 COMPLETED_WITH_FAILURES，另一有限检验第一稿的错误和 sorryAx 记录保留；没有将其追溯改成成功。check-03/06 的原警告也未删除。这里的打印数包含被拼接的复用声明，不能相加当作新增数学结果数量。

本收据没有修改书稿、Lean、原检查材料、冻结账本或 Git 状态；不声称正式发布、远端 CI 或现实实验已经完成。
