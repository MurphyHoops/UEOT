# 《UEOT物理学》3.0 第 49–50 章：内核接口对照复核

日期：2026-10-19 UTC。对限定审查对象的结论：**CLEAR**。

本次只读复核对象为 `/tmp/qm314_book_stage/kernel_chapters.md` 的第 49–50 章，并定点确认两项修正已进入 [canonical 正文](../book/UEOT_PHYSICS.md)。审查者负责 Effects/Stability 数学模块；这份书稿由另一作者编写。因此本文件记录书稿与实际数学接口的对照及范围检查，不将模块作者检查改称为独立作者外的数学复核。新模块的另一协作者独立语义意见与实际编译结果记录在 [效应与稳定性审查](EFFECT_STABILITY_REVIEW_v31.4.md)。

此次核对的阶段书稿 SHA256 为 `514d84d24bc1580aae64d00f8abaca772766fd6a1cea1a6212e96f506d56d33e`。该身份只覆盖两章输入文件，不覆盖总著其他章节、最终 PDF 版式或后续编辑。

## 1. 书稿与实际接口

| 书稿部分 | 对应实际接口 | 对照结果 |
|---|---|---|
| 49.2 响应与后验 | `response_posterior`、`posterior_response_eq`、`nextResponse_eq_none_iff`、`existsUnique_closedReachableUpdate` | 正概率归一化、零支路无后验、响应像内闭合均对应现有证明 |
| 49.3 全词有限表示 | `FiniteObservablePresentation`、实际词生成、局部拉回、坐标 iff 及 Ax/p | 行系数方向正确；冗余生成元允许；未把 d² 专用维数或 Python 搜索终止计入 Lean 已证 |
| 49.4 完整有限树 | `Adaptive` 的路径、归一化和坐标叶律 | 保留每个结果；共同协议；未越界到无限停时或程序通用细化 |
| 49.5 加权与指标 | `WeightedInstrument.toInstrument`、`RaggedInstrument` 及显式有限嵌入 | 平方根在真实数域中精确使用；补零保持语义；索引映射仍为显式输入 |
| 49.6 有限 checker | `Exact.MatrixData.toMatrix`、`ExactCertificate.check_sound`、`presentation` | 五条件局部、无目标结论字段；数值实例与 Python 全输入正确性明确区分 |
| 50.1–2 效应 | `pairing_nonneg`、`Effect.probability_nonneg`、`probability_le_one`、`pullbackEffects`、`recordTest` | 使用完整 PSD 分解和真实配对；不假设非交换乘积本身 PSD；保效应实际使用 completeness |
| 50.3 伪距离 | `effectDistance`、`effectDistance_eq_zero_iff`、`response_sub_le_effectDistance` | 非空、有界、全效应量词明确；零值只声称全部效应概率相等；范数识别与密度态分离未晋升为 Lean 已证 |
| 50.4–5 通道与 M-TC | `channelState_effectDistance_le`、`channelState_perturbation_bound`、`channelTrajectory_transport_certificate` 及两个求和界 | 缺陷是真实上确界；一步递推由 Kraus 定义推导；共同载体及共同后续库边界正确 |
| 50.6 后验 | `posterior_effectDistance_le`、下界版本及 `probability_pos_of_effectDistance_lt` | 两个正概率见证、η 下界、可能放大和零概率未定义均保留 |

书中引用的公共结果名称已经与本轮实际 [287 项公理集合](../kernel/evidence/v31.4/proof-axioms.json) 对照。结构名、源文件名和普通数据解释函数按其源码存在性核查，不将它们当作额外定理计数。

## 2. 本次指出并已确认修复的两项问题

**轨迹指标范围。** 原句容易理解为已证明每一步都可改变结果与 Kraus 的指标类型。实际接口是 `I : ℕ → Instrument ι O κ` 与 `J : ℕ → Instrument ι O' κ'`：两序列之间类型可以不同，每条序列内部类型固定，矩阵可随时间改变。第 50.5 节现已明确这一点，并将逐步可变索引的适用留给显式统一有限嵌入。

**稀有事件的第二个正支撑。** 由终态误差至多 0.005 与第一态事件概率至少 0.001，不能推出第二态事件概率严格正。第 50.6 节现已明确第二后验可能未定义；只有另行确认两态事件都正时才可代入条件化界。概率至少 0.2 的前一例能够通过误差小于事件概率得到正支撑，其 0.05 后验界仍正确。

上述修正已在阶段输入及 canonical 第 49–50 章定点读回。本次没有修改书稿。

## 3. 当前证据与科学范围

本轮整包实际本地结果为 15 模块、256 个显式定理、287 项唯一命名公理审计 PASS；87 个运行方法、3 个演示、6 份数值实例的 42 项审计及 4 个同数据假值见证另行通过。结论引用 [统一证明回执](../kernel/evidence/v31.4/lean-verification.json) 和 [实例回执](../kernel/evidence/v31.4/lean-exports/verification.json)，本次文档复核没有重新运行 Lean 或测试。

整个版本当前阶段为 **LOCAL_VERIFIED_CI_PENDING**。本文件的 CLEAR 只对应上述两章的数学接口与范围，不替代远端 CI、主线集成、总著其余章节审查或 PDF 导出验收。

必须继续保留：输入量子扇区及 Born 规则的物理角色；条件三代结论及谱／窗口／全局义务；通用程序细化开放；共同有限载体和每序列固定指标；通道丢弃结果后不能直接控制历史律；实际缺陷上确界与可执行数值上界算法的区别；ancilla／diamond、无界与连续极限的独立证明义务。

第 50 章对 QMU-04 的登记为“有限共同载体完整 Kraus 通道及正事件后验切片完成”，与本次实际源定义和证明相符。
