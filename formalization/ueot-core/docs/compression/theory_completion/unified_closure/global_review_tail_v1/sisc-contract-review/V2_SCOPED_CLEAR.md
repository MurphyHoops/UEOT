# SISC 逐探针实验合同 V2：独立窄审

**结论：STATIC_MATHEMATICAL_AND_API_CLEAR_NOT_IMPLEMENTED。** 本次仅复核新增 `SISC_PROBE_CONTRACT_V2.md` 对 V1 §2 的替代合同。三项初审发现已准确补齐；统计来源、间隔条件和实验身份范围一致。新增适配仍是数学合同，没有新增 Lean 实现、编译结果或生产发布。

审查对象为 19,005 字节的 V2，SHA256 `a250910c89276c5b68ddac9748ff015bd2601937bafe9826316390e380ca83cc`。原 `NEXT_TASKS_AND_PASSAGES.md` 与本审查目录中 V1 快照仍逐字相同；原 `INITIAL_FINDINGS.json` 保留。附随 JSON 绑定九份实际 API 源文件及其在两个工作树中的字节身份。

## 1. 三项原发现的解决

| 原发现 | V2 中的准确修订 | 独立结论 |
|---|---|---|
| 自由均值风险尚未绑定旧 N3 核风险与区间 | §3.1 固定同一 P 的 kernel/source/action/read，取 `g j y = P.read y j`；显式保留逐坐标 `hMean`，参考表定义为 `P.prediction`。§3.2 由这些输入推出风险身份，§3.3 构造 estimate=Lhat、statisticalRadius=r、driftRadius=0 的新 interval。 | 能接现有校准与间隔端点；没有把最终风险身份偷放成无来源假设。`hMean` 仍是明确的模型匹配义务。 |
| 空 J 的均值界与现有 N3 非空字段混淆 | §2.2 保留 J 空时 G=univ、预算0；§3.1 从 `P.observed_nonempty` 取得 `Nonempty J`。 | 纯集中与 N3 适配的量词边界准确。 |
| “所有竞争者”未指明当前 N6 的全类型量词 | §4.1 写出 `∀ d:C, d ≠ c → ∃ j, 2u < |R_c(j)-R_d(j)|`；§4.2 将只限 registered/authenticated 的更弱条件列为另待证明的局部引理。 | 与实际 `LocalResponseGap` 定义完全相符，不用较弱前提冒充现成 API。 |

## 2. 共同 Good 与功效推导

第2节在同一个真实概率空间上固定 N_j>0、u≥0、ν_j、读数及采样协议。每行的可测性、IID 与实际边缘均明示。对每行调用现成 `BoundedLossTwoSided.measure_empiricalRisk_bad_le`，再对探针作有限并合，可得

\[
\mu^{\mathrm{real}}(G^c)\le\min\left(1,\sum_j2e^{-2N_ju^2}\right).
\]

不需要跨行独立。实际 `productRowLaw` 提供一个更强、可明确实例化的实验来源；其坐标定理可以复用。V2 正确区分这一标量预算与含 `|Finset X|` 因子的 TV 预算，也没有将已有共同 N 的包装定理说成已经接受 N_j。

反三角不等式在同一个 G 上同时控制所有候选的 L1 风险，因此不产生候选数的额外并合罚项。接 N3 时，内侧条件为 `risk(c)+2r ≤ tolerance`，其它注册且 causal 候选的外侧条件为 `tolerance+2r < risk(d)`；严格性与现有 `registered_unique_identified_of_calibrated_margin` 一致。候选 c 只进入正确性定理，不进入估计协议或解析程序。

接 N6 时，V2 构造新的逐组审计值，先由 Good 与 hModel 推出实际 `FormedByResponse`，再消费现有确定性 `audited_source_candidates_eq_singleton_of_gap`。现有共同 N、每单位全探针记录的统计包装尚未因此获得逐组 API。固定 child 的实际实验也没有被推广为所有 child 共享同一真实记录。

## 3. 来源与未实施范围

普通单处理数据只需每单位记录实际处理下的读数。它本身不推出不同处理均值等于 N3 所指定的单一 source/action 核坐标。V2 §3.1 的受限例子——重复同一实际动作、各组只读取一个坐标——提供一个非空且语义明确的可适配来源；其它实验必须另证自己的 hMean。§5.1 的 δ₀ 数据与 δ₁ 核行反例正确说明集中不能修复错误的目标模型。

认证转移、实际干预匹配和到 genealogy 的 soundness 均保留为独立义务；拟合或唯一标签不产生物理来源、SameObject 或 OffspringOf。固定 N_j 不包含随机停止；未来部署核、策略和事件也不由本合同自动获得同源身份。

后续可实施的最小工作仍是：逐行标量共同 Good 包装、N3 区间适配、N6 审计适配及一个真实乘积实验实例。V2 尚无这些新 Lean 声明；本审查也不报告它们已编译。

## 4. 复核范围与保留记录

复用初审对原八份源文件的语义审读，并对修订涉及的声明和新引用的 `C2IntervalDecision.lean` 作窄核对。九份源文件的字节与 V2 表中身份及另一个工作树副本一致。V2 表中的 `模块.端点` 是源文件定位标签；SISC 端点实际处于 `UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC`，`IntervalCertificate` 则处于其上级 ScientificClosure 命名空间。实现时应使用实际 Lean 命名空间。

没有运行 Lean、Lake、native、测试或 Git，没有修改作者文件、生产、书稿、旧独立收据或已冻结全局报告。原发现没有被覆盖为 PASS；本文件与附随 JSON 只记录 V2 的后续修订结论。
