# 实际两状态过程中的记忆分离

状态：`FOCUSED_LEAN_COMPILE_PASS`。最终源码已通过本批 `compile-04` 的实际 Lean 编译，退出码为 0，诊断日志为空；源码与执行记录见 [compile-04 原始收据](../actual-execution/compile-04/STATUS.json)。本说明记录该见证的数学范围，不替代整组生产导入、完整构建、native 导出和独立生产验收。

生产候选文件：`UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteMemorySeparation.lean`。
命名空间：`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMemorySeparation`。

## 同一个实际来源

状态与行动均为 `Bool`，观察为 `Unit`，初态为 `PMF.pure false`。
每一步的来源转移为

\[
P_n(x,a)=\delta_{\neg x},\qquad q(x)=\star,\qquad C_n(x,a)\iff a=x.
\]

所有占据均使用已有的 `coverageDeploymentRowLaw initial observe source π n`；策略变化时，源初态、观察、转移和认证谓词保持这组定义。这里没有另外传入一份“实际占据”证书。

## 完整有限记忆控制器

`flipController : FiniteMemoryController Bool Unit Bool` 使用根模块中的通用控制器类型：初始记忆为 `false`，行动为当前记忆的纯 PMF，记忆更新为 Boolean 取反。输出和更新本身没有时间参数；从完整记录递归计算记忆只是该有限控制器的语义，不给控制器额外的无界时钟。这个控制器在所有记录上都有定义，不调用任意完整历史 fallback。

对任意完整观察—行动记录，来源支持递推都满足

\[
S_n(h)=\{\operatorname{memory}(n,h)\}.
\]

这是 `trace_support_eq_memory_singleton` 的归纳结论：初始支持为单点；每步的真实纯转移把该点取反，观察恒定。这里的来源支持身份在所有记录上成立；一般后验支持唯一性仍只在正概率记录上消费。

策略的正概率行动只能等于当前记忆，因此它认证当前支持上的每个状态。通过既有 `zero_uncovered_iff_support_certified` 得到 `flip_controller_zero_uncovered`：对所有时间，**该控制器自己产生的实际部署行律**的未认证事件质量为零。这是任意时间的 Lean 归纳结论，不是截止到若干步的数值模拟。

## 固定当前观察随机反馈的精确障碍

任取一个固定行动 PMF \(\rho\)。`stationaryPolicy ρ` 在每个时间、每个完整记录使用同一个 \(\rho\)。实际源过程在时刻 0 位于 `false`，时刻 1 位于 `true`，不依赖行动，故

\[
U_0=(\rho(\mathrm{true})).\operatorname{toReal},\qquad
U_1=(\rho(\mathrm{false})).\operatorname{toReal},\qquad
U_0+U_1=1.
\]

`stationary_uncovered_zero` 与 `stationary_uncovered_one` 从实际行律的期望展开证明两式：实际微观前缀支持分解给出第 0、1 时刻的状态分别为 `false`、`true`；零质量历史不贡献期望，其余历史共享同一个未认证行动质量。前缀 PMF 与行动 PMF 的归一化完成两式及其和为一的证明。

现行生产 `SourcePolicyPathBridgeCheck.observationMarkovPolicy σ` 在单点观察类型上恰等于 `stationaryPolicy (σ ())`。因此 `stationary_feedback_cannot_certify_two_rows` 对**所有**当前观察随机反馈证明：第 0、1 步不可能同时零未认证占据。这里没有偷偷允许反馈依赖时间或历史；随机化本身已被这个全称量词覆盖。

## 原问题与边界

原 Core 的完全观察状态反馈可直接选行动 \(a=x\)。本例保留同一真实状态过程，但把观察协议限制为常量，说明在这一协议下需要利用记录中可递推的记忆。结果加强的是观察受限的实际控制能力，不否定完全观察版本的可行性定理。

本例没有把认证谓词解释成物理安全，没有推出给定收益的最优性，没有压缩任何参考过程的检查预算，也没有修改参考过程零源概率记录上的完整策略值。两个记忆值足以实现这里的正例；当前形式化负例明确针对固定当前观察随机反馈类，不另宣称一般控制器的最小内存复杂度定理。

本文件对应一个数学 PMF 实验与其形式证明，不构成现实采集数据或经验验证。
