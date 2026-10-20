# Good-selected envelope：研究原型源审查

审查者：`/root/independent_audit`。日期：2026-10-20。

**结论：CLEAR_SOURCE_REVIEW_FOR_RESEARCH_PROTOTYPE。** 两个终端的量词、选中策略和真实联合实验身份一致；事件补全严格复用既有证明，未增加未经说明的概率预算或假设。本收据不代替主智能体的聚焦编译收据，也不宣称生产 Lean API 已改变。

审查文件：`tmp/interface-validation/GoodSelectedEnvelope.lean`。
SHA256：`e348a1afd6966dc26c8f239331dad89b0e1373d7cf2e58a01a57f9b9e2736bda`。
与已审草稿 `3cc22b6a4def21b6639d4e455b884ca530475d7eafc5d8ccb98ad2fe67b51470` 比较，入口 import 与首段说明之后的全部代码逐字相同；只有首段状态说明变化。复用此前数学审查，不重新进行全库检查。

## 1. 两个终端的准确合同

记 `G ω := RegisteredCalibrationGood hN P certified T sample rho ω`，`cω := select ω`。

### 有实际占据上界的终端

`registered_selected_joint_failure_of_cap_and_envelope_on_good`

- `hfit`、`hcap`、`henvelope`、`hchecked` 均为 **∀ω，G ω → 相应结论**，不是对全部候选要求这些条件，也没有偷偷弱化为仅几乎处处成立。
- `hcap` 对每个 `n<T` 约束由同一 `initial cω`、`q cω`、微观源 `P`、`policy cω` 构造的实际未认证行占据。
- `henvelope` 为同一固定微观事件 `E` 在 `q cω` 的历史映射下包含于 `F cω` 的逆像；动作分量保持原动作。
- `hchecked` 使用同一候选、同一策略、同一 `F cω`，误差预算为逐步 `min 1 (rho n + eta ω n)` 与相应 `kappa ω n`。
- 结论中的联合分布准确为 `selectedTrainingDeployment training.toPMF select (fun c => causalLaw (initial c) (riskMicroControlKernel (q c) P (policy c)) T)`；没有替换成独立训练/部署乘积或另一策略。

### 内部推出零占据的终端

`viable_registered_selected_joint_failure_with_envelope_on_good`

- `hinit` 对每个 Good 记录、每个非空初始观察支持纤维要求同一 `q cω`、`P`、`certified` 下的有限时域可行性。
- 参考检查和实际联合部署都使用准确的 `viableFamilyPolicy initial q P certified T fallback c`。
- 它直接调用已证明的 viable 终端；零未认证占据由该终端为这同一策略内部推出，没有外部 `hcap` 或另一策略的证书。
- `fallback` 仍是显式完整因果策略输入；没有新增空行动类型上的策略存在性声明。

两个终端都保持有限 `Ω、X、Y、A`；`C` 仅需可测空间，无 `Fintype C`。注册采样仍为预定统一 `Fin N`，`N>0`；每行样本可测、行内独立，边缘分布等于同一 `training` 下相应真实 `P` 行。没有要求行间独立，也没有实现逐行样本量或任意观察类型的推广。

## 2. 补全为何合法

`completeSelectedEnvelope` 对存在 Good 记录选中的候选保留 `F c`，对其余候选使用 `Set.univ`。两个通用引理分别证明：Good 上选中事件不变；补全后的全候选包络成立。

因此可以原样调用已有注册风险与 viable 终端，并在 Good 上将预算中的补全事件化简回原 `F`。补全不改 `G`、`P`、采样实验、`Q`、策略、初始分布或实际失败事件。即使同一候选同时被 Good 和 Bad 记录选中，也仍保留其原 `F`，不存在选中身份冲突。无需额外假设 Good 非空。

最终界仍是 `min 1 (α + (1−α)β)`，其中 `α=registeredConfidenceBudget certified T N rho`、`β∈[0,1]`。Bad 记录原本即按条件风险至多 1 处理；补全没有引入第二个坏事件，因此没有额外概率收费，也没有漏收原坏事件。

## 3. 聚焦编译绑定与保留范围

主智能体报告该精确 SHA256 的文件已在真实 Mac 固定工具链缓存上聚焦编译通过：exit 0、3.673 秒，空日志 SHA256 为 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`。该编译版本与本次实际读取的受审源码身份相同；编译执行收据由主智能体单独保存。本审查者未重新运行编译，也不把编译通过解释为生产集成。

这是一项证明复用的接口原型；事件补全是 `noncomputable` 的数学构造，不是新增可执行校验器。若另用包络事件 H，仍须控制共同 `G∩H` 的坏概率；若要 a.e. 条件或部署测度下的几乎处处包络，仍需另行零测/支持桥接。零未认证占据不等于零物理失败风险，有限时域可行不等于无限存活。

**归档定位明确：受检 research prototype，位于生产 import graph 之外。** 当前生产接口的 all-candidate `henvelope` 范围说明仍应保留，直至未来实际集成。本次未调用 Mac、远端、Lean 或重复测试，未修改生产或 Git。
