# 固定逐行样本量至实际选中联合风险：独立审查

审查者：`/root/independent_audit`。日期：2026-10-20。

**结论：CLEAR_SOURCE_REVIEW_FOR_RESEARCH_PROTOTYPE。** 新终端从实际逐行采样校准推出真实源行误差，再调用既有路径风险与联合实验定理；量词、Good 事件、策略和实验身份一致。没有将待证的校准概率、真实行误差或联合风险作为调用者假设。此结论适用于下列精确源码，最终候选 Git head 另作窄范围绑定。

## 1. 源码与执行证据身份

本次直接读取 `/workspace/scratch/9a8d58b21e30/tmp/interface-validation/` 中的两个文件，并核对实际生产源码中的被调用合同。

| 对象 | SHA256 |
|---|---|
| `VariableRegisteredSamples.lean` | `915b4f906c43429b25c010e7ffc44f766abf4066d9a32dcd91bb69fa7ce02e5f` |
| `VariableRegisteredJoint.lean` | `69f82675fff64434bc939cf719b0edf2602c6770d33fa3b1594eb3932364c271` |
| 聚焦检查的组合源码，15,886 字节 | `f124fedb8058d75d330dbf6675c8e7e5d5af7d242b00aec2b6ff7d70879c4f29` |

已在内存中精确重建组合字节：一行 `import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredDeploymentRisk`（含换行），紧接完整 Samples 文件，再加一个换行，紧接完整 Joint tail。重建 SHA 与主智能体报告相同。Joint 与数学智能体原草稿 `4f36808e8766c0b80cfb2f7cde30d6e3c663b0a2c921326bd323d22b0208cbc2` 仅首段状态说明不同；声明及证明不变。

**执行结果的来源是主智能体实际读取后的报告，本审查者未读取原始 Mac 日志或重新执行编译：**

- Combined：exit 0，6.422 秒；日志 SHA256 `7aff9b4ea0d36a3fd562e048876ab96915c62466af7fe48840f468dab54e86eb`。
- Samples 单独检查：exit 0，6.911 秒；完整日志 SHA256 `17261fee36a60a1be42fd1d16ba9f6325ad25d4091a1e7e8de6db1540ac29019`。该后续身份补充不改写旧 `FINAL_SOURCE_BINDING.json` 中历史 `null`。
- Combined 的四项输出：Samples 的 `registered_row_calibration`、`product_experiment_calibration`，Joint 的 `registered_calibration_good_bad_le`、`registered_selected_joint_failure_of_cap_on_good`；主智能体报告每项公理闭包均只有 `propext`、`Classical.choice`、`Quot.sound`。

## 2. 精确量词与实际实验

固定有限 `Ω、X、Y、A`，相应可测结构及可测单点；`C` 仅需可测空间。`training` 是同一个概率测度。固定真实源 `P`、注册条件 `certified`、时域 `T`、注册行类型 `J := CoverageRegisteredRow certified T`，以及

\[
N:J\to\mathbb N,\quad \forall j,\ N_j>0,\qquad
\rho:\mathbb N\to\mathbb R,\quad \forall n<T,\ \rho_n\ge0.
\]

样本类型真实变为 `sample : ∀ j, Fin (N j) → Ω → X`。这些固定输入均不以训练记录 `ω` 为参数。每个坐标在同一 `training` 下可测；`hindep` 逐行要求行内独立，`hlaw` 逐坐标要求其真实边缘等于准确的 `P` 行。这里的行编码是 `(n,a,x)`，实际 `P` 访问顺序为 `P n x a`，未交换动作与状态。通用样本定理不要求行间独立，已审真实乘积实验则提供这些采样前提的一个具体实现。

新定义的规范事件与预算为

\[
G=\{\omega:\forall j\in J,\ \operatorname{TV}(P_j,\widehat P_j(\omega))\le\rho_{n_j}\},\qquad
\alpha=\sum_{j\in J}|\operatorname{Finset}X|\,2e^{-2N_j\rho_{n_j}^{2}}.
\]

`registered_calibration_good_bad_le` 将已审逐行定理特化到这些准确的源行，得到一个校准事件 `good ⊆ G`，再由 `Gᶜ ⊆ goodᶜ` 推出 `training.real Gᶜ ≤ α`。有限 `Ω` 与可测单点保证规范 `G` 可测。**`α` 的概率意义由证明给出，未作为调用者合同要求。**

所有 `hfit、hcap、henvelope、hchecked` 均为 `∀ ω, G ω → ...`，不是另一个 Good，也不是仅几乎处处。固定失败事件 `E` 对全部候选相同；`F c` 是候选事件族。`β∈[0,1]` 是统一常数。允许 `select ω` 随数据变化；其可测性由有限训练空间推出，不需要候选类型有限。

## 3. 真实行误差、策略与概率组合

在 `intro ω hω` 后，证明对任意 `n<T、x、a、certified n x a` 构造准确注册行 `j`。`hω j` 给出真实 `P n x a` 至该行、该 `N_j` 所生成经验 PMF 的 TV 界；`hfit ω hω ...` 给出同一经验 PMF 经 `q (select ω)` 后至同一 `Q (select ω)` 的拟合界。`empirical_coarse_row_tv` 将二者组合为

\[
\operatorname{TV}\bigl((P_{nxa})_{\#q_{c(\omega)}},Q_{c(\omega),n,q_{c(\omega)}x,a}\bigr)
\le\varepsilon_{\omega n}:=\min(1,\rho_n+\eta_{\omega n}).
\]

这正是局部 `have hcert` 的证明；它不是终端参数，也没有将真分布替换为经验分布来定义实际部署。

随后三处严格使用同一个 `initial (select ω)`、`q (select ω)`、真实 `P` 和 `policy (select ω)`：

1. `coverage_same_policy_microscopic_failure_risk` 给出该真实策略的路径失败界；参考过程保持相同策略，只将转移替换为候选 `Q`。
2. 实际占据预算引理用同一策略的 `hcap` 代入 `κ`；系数非负由 `ε≤1` 给出，没有借用另一策略的占据证书。
3. 联合分布精确为 `selectedTrainingDeployment training.toPMF select (fun c => causalLaw (initial c) (riskMicroControlKernel (q c) P (policy c)) T)`。

`henvelope ω hω` 仅在这个 Good 分支传入路径定理，映射保留动作分量且使用同一 `q`；`hchecked` 使用同一 `F、Q、policy`。因而 Good 上该实际部署的 `E` 风险至多 `β`。

最后只调用一次既有 `selectedTrainingDeployment_failure_le`，以 `Measure.toPMF_toMeasure` 回到原训练测度，并使用刚证明的 `μ(Gᶜ)≤α`。得到

\[
\mathbb P_{\text{实际选中联合实验}}(E)
\le\min\{1,\alpha+(1-\alpha)\beta\}.
\]

这是先抽取训练记录、再按其选中候选部署的联合实验；没有误用训练与选中部署独立的乘积。坏事件仅计一次。无需附加 `α≤1`：既有混合证明对坏质量的单调性由 `1-β≥0` 保证，外层单位截断仍有效。

## 4. 保留的范围与最终结论

- 逐行正整数 `N_j` 已进入这份受检原型的实际联合风险接口；数据依赖的样本量、停止规则或事后注册不在合同内。原型使用时间半径 `ρ_n`，没有假称任意逐行半径都已自动进入现有时间预算。
- 空 `J` 合法且 `α=0`；它不推出零未认证占据或零失败风险，所选策略仍必须满足相应占据与风险检查。`T=0` 也不使任意初始失败事件的风险自动为零。
- 这里只给定完整候选策略族，并不证明满足检查的选择器或策略一定存在，也不将其识别成 `Classical.choose` 的生存策略。Good 包络若改成另一个事件上的包络，必须重新控制共同事件的坏概率。
- 有限观察类型、有限训练空间与有限时域边界保留；本次未增加数值自适应见证，旧统一样本量见证没有被重新描述为不等样本量见证。

**发布定位：已受检的 research prototype，存于全新文档子树，生产 import graph 与现行 API 范围仍按实际代码说明。** 本审查仅进行了云端源码读取、精确字节比较和数学合同审查；没有 Mac、远端、Git 写操作、构建或重复集中界审查。旧审查及历史失败状态均未修改。未发现阻塞性数学问题；最终仅需把这些精确源码及主执行证据绑定到实际候选 head。
