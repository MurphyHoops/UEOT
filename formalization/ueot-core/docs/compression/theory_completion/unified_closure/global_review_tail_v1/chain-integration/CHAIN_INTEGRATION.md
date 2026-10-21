# 从完整历史可行策略到同源有限记忆链：源码接口与整组集成

状态：**源级数学与 API 路线核对；本报告所列新引理尚未实现或编译。** 本次仅写此目录，不改冻结 Stage1–7、tail 包、生产、书稿或 Git。现有 tail 已有独立执行 CLEAR，身份见 `../independent/TAIL_EXECUTION_CLEAR.json`；其作者包中的原 PENDING 不改写。

## 1. 决定最小任务范围的事实

生产 `SupportViabilityClosure.viablePolicy`（`FiniteSupportViability.lean`）的定义是：当 `n < T` 且当前 `traceSupport` 可行时，取 `viableWith_step_of_lt` 的 `Classical.choose` 并返回纯行动；否则调用输入的完整历史 `πbase n h`。因此：

1. **在可行的时域内，确实能够证明同一个原策略只依赖 `(n, traceSupport)`。** 这应从实际定义和证明无关性推出，不能另选一个可行行动后声称二者相同。
2. `viablePolicy_supported_histories_viable` 已保证：给定 `hinit`，原策略在每个 `n ≤ T` 的实际正概率观察历史上可行。于是时域内可得到同一策略的有限支持记忆表示。
3. 非可行历史及 `n ≥ T` 上的任意 fallback 不保证按支持、当前观察或任何固定有限记忆因子化。有限时域的来源身份不能扩成原无限后缀的身份。
4. `ViableVariableRegisteredJointCheck.viable_registered_selected_joint_failure_on_good` 只在同一个 `RegisteredCalibrationGood` 上要求 `hinit`。因此上述支持记忆身份也首先是 **每个 Good 训练记录上的实际部署前缀身份**。
5. Good 上的实际来源支持不等于参考 `Q` 路径的支持。参考过程可到达来源零质量历史，甚至离开 `q(X)`；在那里原策略仍可能用完整历史 fallback。不能用来源侧的支持压缩改写原 `hchecked` 中的参考路径或策略。

**推荐的最小包**：证明 Good 上、`n ≤ T` 的实际来源支持记忆推前身份，复用原生产风险端点与原参考预算；Bad 侧仍是原实际实验，由现有混合界计一次。只有目标明确要求“辅助有限机器的整个训练／部署联合分布等于原联合分布”时，才追加覆盖全部 fallback 的有界完整记录机器。

## 2. 已有端点：直接复用，不能重新列为空缺

下表中路径均相对 `/workspace/scratch/9a8d58b21e30/ueot-integration/formalization/ueot-core/`；`UC/` 表示 `UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/`。其中 UC 端点省略公共 namespace `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure`；其他表列 namespace 省略 `UEOT.V3`。实际读取文件和哈希见 `SOURCE_INPUTS.json`。

| 当前状态 | 精确端点 / 文件 | 已经解决的责任与界限 |
|---|---|---|
| 生产 THEOREM | `SupportViabilityClosure.traceSupport_eq_fiberTerminalPosterior_support`，`UC/FiniteSupportViability.lean` | 正概率完整观察历史的递归支持等于实际终态后验支持。不能删除历史正质量条件，也不是只看当前观察纤维。 |
| 生产 THEOREM | 同文件 `viablePolicy_supported_histories_viable`、`viablePolicy_support_step`、`viablePolicy_zero_uncovered` | 同一 `viablePolicy` 的可达可行性与 `n<T` 的实际零未认证占据；不要求整体 `Y` 有限。 |
| 生产 THEOREM | 同文件 `initial_viability_iff_exists_zero_uncovered_policy` | 固定 T、显式完整 fallback 下的精确存在等价式。没有宣称所有 T 的各自策略已是同一个无限策略。 |
| 生产定义与 THEOREM | `ViableRegisteredJointCheck.viableFamilyPolicy`；`ViableVariableRegisteredJointCheck.viable_registered_selected_joint_failure_on_good` | `viableFamilyPolicy c` 就是该候选原 `viablePolicy`。逐行固定 `N j`、选择依赖训练、Good-only 的初始可行／拟合／包络／预算在同一个实验内组合。 |
| 生产 THEOREM | `PolicyPrefixCongruenceCheck.actual_causalLaw_congr_before`、`deployment_rowLaw_congr_through`，`UC/ReachablePolicyExtension.lean` | 全历史策略在前 n 步相等则前缀相等；占据含当前行动，所以需一致到 n。现有假设量词是所有历史，不能直接套用只有来源支持上的相等。 |
| 生产 THEOREM | `PathObservationEscapeCheck` 内的 `observationHistoryMap_comp`、`escapePolicy_actual_history`、`escape_micro_control_kernel`、`escape_deployment_row_law`，`UC/PathObservationEscape.lean` | 原完整策略在真实有限观察像上的编码不改变实际核／完整占据。`ArbitraryObservationRiskCheck.coverage_arbitrary_observation_path_error`（`UC/ArbitraryObservationRisk.lean`）的证明内部已用 `I := Set.range q` 构造有限像。有限像编码不是记忆消除。 |
| 生产 THEOREM | `risk_causalLaw_map`，`UC/FiniteHorizonRisk.lean` | 真实条件投影核的完整前缀就是原前缀的推前。它不把所得历史条件核变成平稳支持反馈。 |
| 生产 THEOREM | `RepresentationCovariance.causalLaw_transport_equiv` | 双射表示变换的路径协变。添加冗余记忆一般是图嵌入，非整个目标类型上的双射，不能直接把该定理当作有限记忆证明。 |
| 生产 THEOREM | `ReflexiveStateAugmentation.historyKernel`／`isMarkovKernel_historyKernel`；`ReflexiveStatePathLaw.historyPathLaw_prefix`／`reflexivePathLaw`；`ReflexiveStatePathUniqueness.p_ref_01_pathlaw_unique` | 完整历史因果随机策略已有真实齐次历史核、无限路径律及前缀唯一性。载体 `FiniteHistory.Carrier = Σ n, HistoryFiber ... n` 含无限时间标签，通常无限；这不是当前有限 killed 矩阵 API 的有限状态输入。 |
| 生产 THEOREM | `ViabilityTrajectory.exists_stationary_policy_all_times_of_fixed`；`exists_source_micro_all_times_viable_path_law`（`UC/CoreInfinitePathClosure.lean`）；`single_source_terminal_object_viability_all_times`（`UC/CoreSourceAllTimesAssembly.lean`） | 已有真实来源、固定点和原初态条件下的全时域安全及同源装配。新任务是当前观察历史策略的身份适配，不能把这些已有结论误列为项目空缺。 |
| 私有 PASS + CLEAR | `SourcePolicyPathBridgeCheck.actual_next_state_eq_stationary_row`／`actual_state_path_eq_stationary_path` | 对同一个 `M,q,sigma,p0` 证明实际行动—状态记录擦除行动后等于平稳状态路径。输入 sigma 必须是时间齐次当前观察反馈。 |
| 私有 PASS + CLEAR | K1、一般 K2、同源 QSD、首次退出、G1–G3、SafePrefix、SurvivalTail | 已有同源 killed 有限质量、正存活条件终态、QSD 特化、真实首次退出、完整无限前缀、安全事件和尾极限。它们尚未进入生产 import；不能把这八个已有证明当成八个待重证的数学命题。 |

`FiniteBayesBelief.Belief` 存储实值概率权重。即使 X 有限，所有概率信念组成的类型通常无限。本次有限记忆是**支持集合和有限时钟**，不是声称完整 Bayes 概率信念只有有限个。

## 3. 当前 Good-only 目标的准确扩张

先固定一个候选，记原策略为

\[
\pi_T=\operatorname{viablePolicy}(p_0,q,P,\mathrm{cert},T,\pi_{base}).
\]

这里 `P : ℕ → X → A → PMF X` 可以随时间变化。使用生产风险层的有限 X、A；Y 不要求有限。概率事件层保留 X、A 的可测空间和单点可测条件，有限记忆与扩张观察可取离散可测结构。已有完整 fallback 与 p0 足以导出所需 Nonempty A，推导见第 6 节。以

\[
\mathsf{Mem}_T=\operatorname{Fin}(T+1)\times\operatorname{Finset}(X),
\qquad Z_T=X\times\mathsf{Mem}_T
\]

为有限记忆与扩张微观状态。`Finset X` 与原 `Set X` 支持之间需用真实有限集强制转换等式连接；不能另建未经识别的关系表。

初始嵌入为

\[
\iota_0(x)=\bigl(x,0,\operatorname{initialSupport}(p_0,q,q(x))\bigr),
\qquad \widehat p_0=p_0.\operatorname{map}(\iota_0).
\]

原 p0 未过滤、未重新归一化。扩张观察只读记忆 `qhat(x,m)=m`，不泄露隐藏微观状态 x。该记忆由已有观察／行动记录确定。

在记忆 `(n,S)` 上定义 `sigmahat`：若 `n<T` 且 `Viable q P cert n (T-n) S`，取与 `viablePolicy` 完全相同的 `viableWith_step_of_lt` 选择；否则使用一个固定总行动 PMF。该固定补全只服务于不可达状态和截断后的新延拓，**不宣称逐点等于原完整 fallback**。

扩张控制行在 `n<T` 时由原行直接推前：

\[
\widehat P((x,n,S),a)
=\operatorname{map}_{x'\mapsto(x',n+1,\operatorname{successorSupport}(q,P,n,S,a,q(x')))}
     P(n,x,a).
\]

时钟到 T 后可明确冻结整个扩张状态。这样 `P̂ : Z_T → A → PMF Z_T` 是齐次的；原非自治时间只在有限时钟内读取。`sigmahat : Mem_T → PMF A` 也是真正的当前扩张观察反馈。

私有链消费 `FiniteDiscountedControl.Model`。现有 `Objecthood.finiteNormalizedRepairModel P̂ ∅ (1/2)` 可以作为概率行适配载体：空吸收目标使其行仍为 P̂，折扣／奖励字段不参与这里的路径或风险论证。必须证明其 `transitionPMF = P̂`，可用 `absorbedRepairPMF_of_not_mem` 和 `Model.transitionPMF_apply_toReal`；不能把等式列为新调用假设。无需为此重造并列概率证书或赋予这些辅助奖励任何目的解释。

## 4. 真正需要的新引理及最少公开输出

下面的名称都是**建议名称，尚非现有 Lean API**。可以在两三个有内聚性的模块内完成；证明辅助项不必全部公开。

### N1. 原选择按支持因子化

建议 `viablePolicy_eq_supportMemorySelector`。

输入：原 `p0,q,P,cert,T,πbase`，`n<T`，完整观察历史 h，及
`hV : Viable q P cert n (T-n) (traceSupport p0 q P n h)`。

输出：

\[
\pi_T(n,h)=\widehat\sigma\bigl(n,\operatorname{traceSupport}(p_0,q,P,n,h)\bigr).
\]

证明展开同一个 `viablePolicy` 与新 selector，先识别 Set/Finset 支持，再用同一存在命题的证明无关性对齐 `Classical.choose`。仅仅证明两个行动都经过认证不够。将该引理与已证的 `viablePolicy_supported_histories_viable` 组合，才获得每个正概率来源历史上的行动分布相等。

### N2. 可达行一致性与图更新

需要的通用辅助输入可以是有限初始／记录类型、同一 p0 和两族历史行 K,L，以及

\[
\forall n<T,\ \forall h\in\operatorname{support}(\operatorname{causalLaw}(p_0,K,n)),
\quad K_n(h)=L_n(h).
\]

输出是全部 `n≤T` 的前缀 PMF 相等。这个一步假设在具体应用中由 N1 推出，不能把目标完整路径等式作为输入。现有 `causalLaw_congr_before` 的全历史假设更强，不能直接替代此量词。可用 `pmfExtend_apply` 分支持／零质量情形，或 Mathlib `bindOnSupport_eq_bind` 完成归纳；不需要新测度构造。

对图扩张还需证明真实一步：原当前行动与 `P n x a` 的 `pmfExtend`，映射到 `(a,扩张后继)` 后，等于 `sigmahat` 与实际 P̂ 的 `pmfExtend`。支持更新是原 `traceSupport` 的 successor 递归，时钟更新来自 `n<T`；目标行身份必须由这些定义推出。上述通用支持一致性可作为该图归纳的内部工具，无须另立一个只有包装作用的公共定理。

### N3. 完整行动—状态前缀的同源图身份

建议 `viable_supportMemory_prefix_law`。

输入：原数据，以及现有 `hinit`——所有非空初始观察支持都 T 步可行；`n≤T`。

构造 `Phi_n`，把原完整微观行动记录的每个状态位置 x_k 扩成
`(x_k,k,traceSupport ... (projectHistory q k h_k))`，保留原每一步行动。它需要以此前缀递归定义，不能只映射终态。

记原实际前缀为 `mu_n := causalLaw p0 (riskMicroControlKernel q P π_T) n`；扩张前缀为 `muhat_n`，由同一 P̂ 的有限模型、`qhat` 和 `observationMarkovPolicy sigmahat` 构造。准确输出为

\[
\boxed{\widehat\mu_n=\mu_n.\operatorname{map}(\Phi_n)},\qquad n\le T.
\]

同时证明纯函数回读

\[
\operatorname{riskHistoryMap}(\operatorname{fst},(a,z)\mapsto(a,\operatorname{fst}z),n)
\circ\Phi_n=\operatorname{id}.
\]

于是可推出反方向的完整前缀推前 `muhat_n.map readout = mu_n`。这保留动作相关事件、原初始法则和全部过去坐标，比单时刻边缘相等更强。证明仅在原支持上使用 N1；不存在“假定所有不可能历史也有同一个 fallback”的步骤。

### N4. 安全事件与 killed 量的具体实例化

取一个单独指定的物理安全集 B⊆X，令 `Bhat := Prod.fst ⁻¹' B`。N3 的回读及 `riskEverFailure` 真实递归给出每个 `n≤T` 的安全事件逆像身份。随后直接实例化已有 K1、G1–G3、SafePrefix：

\[
\mu_n.\operatorname{toMeasure}.\operatorname{real}
  \{h:\neg\operatorname{riskEverFailure}(x\notin B,n,h)\}
=\widehat\eta_0\widehat Q^{\,n}\mathbf1,
\qquad n\le T.
\]

其中右侧 killed 矩阵、初始行和无限轨迹都由上面的实际 P̂／sigmahat／p0hat 构造，不能独立输入另一个 Q 或初态后声称来源相同。

已通过的 SurvivalTail 可以作用于这个扩张过程；但 T 后冻结的极限只是该**明确截断延拓**的无限安全质量，等于原实验截至 T 的安全质量。它不是原任意 fallback 后缀的无限存活概率。若本次调用仅需要原 T 步风险，根本无需再证明该截断尾的包装定理。

### N5. Good 域实例化，保留原联合实验

对每个 `ω` 满足原 `RegisteredCalibrationGood`，在 N3/N4 中代入
`c=select ω`、`p0=initial c`、`q=q c`、`πbase=fallback c`，并使用生产 hinit。

输出是这些 Good 记录上的实际部署前缀／事件质量身份。若候选的有限记忆类型依赖 c，先逐候选证明，再回读到共同的原 `CausalHistory X (A×X) T`；不必无故要求整个 C 有限。

生产 `hfit`、`henvelope`、`hchecked` 中的原 Q 与原 `viableFamilyPolicy` 保持原样。源支持上策略一致性不推出参考路径策略一致性。如果另由扩张模型导出一个新的 Good 上实际风险上界，可直接交给既有 `selectedTrainingDeployment_failure_le`；其 Bad 部分仍为原实际部署实验，坏事件只计一次。

这里不输出 `auxiliaryJoint = originalJoint`。若调用者需要这个更强等式，必须补下一节的全部记录实现；不能从 Good-only hinit 得到它。

## 5. 更强目标的两条准确边界

### 5.1 要整个有限联合分布相同：有界完整记录

对固定候选取实际有限像 `I := Set.range q`，`qI x := ⟨q x,⟨x,rfl⟩⟩`，`i := Subtype.val`。`Fintype I` 由有限 X 得到；不对整体 Y 加 Fintype。定义

\[
\mathsf{HistMem}_T=\sum_{n:\operatorname{Fin}(T+1)}
   \operatorname{CausalHistory}(I,A\times I,n).
\]

这是有限类型。其当前反馈直接调用原完整策略
`π n (observationHistoryMap i n g)`；因此非可行分支、源零质量历史上的 fallback 都被保留。扩张初态和行以同样方式添加实际观察与行动，时钟到 T 后才选择明确的延拓。

需证明的主输出仍是 N3 的图身份，但对**任意原完整策略 π、无 hinit**成立，只限 `n≤T`。现有 `escapePolicy_actual_history`、`observationHistoryMap_comp` 提供编码复用；实际 source 图更新仍需证明。

这足以在全部训练记录上回读到原共同历史空间，进而由 PMF bind/map 证明选样联合分布身份；可保持 Ω、select、P、初态族与原策略族完全相同。它不要求不同候选的辅助载体相同，也不授权修改原注册样本或置信预算。

若还要把任意**动作相关** E 通过私有“擦除动作”的状态前缀接口表示，需另证：在真实扩张路径上，历史记忆中的行动序列确实等于被擦除的原行动记录。对任意不一致扩张路径可给总解码，但等式只在已证图像／真实路径上使用。对物理安全集 B 的事件，N4 已足够，无需这项额外解码。

### 5.2 要原无限过程相同：实际有限控制器或无限历史载体

最窄的全时有限控制器输入是有限 Mem、初始化 `init : Y→Mem`、确定更新 `upd : Mem→A→Y→Mem`、当前反馈 `act : Mem→PMF A`，以及齐次原行 `P : X→A→PMF X`。从这些数据递归定义完整策略 `π_FC`；扩张初态仍是 `p0.map (fun x => (x,init(q x)))`，扩张行是

\[
\widehat P((x,m),a)
=\operatorname{map}_{x'\mapsto(x',\operatorname{upd}(m,a,q(x')))}P(x,a).
\]

新的主引理应对**每个 n**证明与 N3 相同的完整图身份，从而把 G1–G3、K1、SafePrefix、SurvivalTail 用于同一原无限控制器。若另有一个既定完整策略 π，要证明 π 的实际可达行动分布等于该递归控制器；不能把完整无限路径等式作为表示定义的输入。

有限相位源可把相位并入状态，用已证明的相位递推逐步识别原 `P n`。一般随时间变化的 P 和一般无限历史 fallback 不保证存在这样的有限表示。保留所有时间／历史的生产 `historyKernel` 是合法的无限载体替代；它已有路径构造，但不满足当前有限 killed 矩阵链的 Fintype 前提。

B 正研究的最大支持固定点可构造一个新的无限支持控制器；它的选择一般不等于当前每个 `viablePolicy_T` 的 Classical.choose。正确的风险组合接口是生产通用 `VariableRegisteredJointCheck.registered_selected_joint_failure_of_cap_on_good`，并证明该新控制器自己的 hcap=0。不能为了使用固定 `viableFamilyPolicy` 的特化端点而假定两种策略相同。

## 6. 必须覆盖的退化与反例

- **T=0**：N3 只涉及原 p0 的图嵌入与回读。没有行动认证义务；不能借此保证原 fallback 的未来。截断扩张若立即冻结，其无限安全质量只是 p0(B)。
- **空支持／不可能历史**：控制器仍须总定义；任意值不会改变已证明的实际图路径，但不能把这些位置的取值称作真实后验。原 posterior 支持身份仍需正概率历史。
- **非可行 fallback 不能按支持压缩**：取 X、Y 为单点，A={0,1}，P 自环，T≥2，所有行都不认证。让 fallback 的第一步随机取两行动，第二步重复前一行动。两个正概率历史的 `(n,traceSupport)` 相同，行动分布不同。该例不满足 hinit，正好阻断未经 Good 限定的支持压缩。
- **无限 fallback 不保证有限实现**：单点状态／观察时，原 fallback 可以按非最终周期的时刻序列输出确定行动。任何有限齐次机器若输出一个概率一确定的无限序列，其可达支持集合序列最终周期；因此不能普遍实现这种 fallback。有限时钟只处理预先固定的 T。
- **原动力学非自治**：同样可以让原 P n 强制产生非最终周期的二状态序列。把所有 n 放进状态是无限扩张；有限相位是额外结构，不是从有限 X 自动推出。
- **空安全集 B、初始失败、零存活**：N4 与已有 K1/SafePrefix 一样保留时刻 0，p0hat 不做条件化。一般 K2 仍只在当前安全质量严格正时归一化。
- **行动类型**：不能为空 A 构造总 PMF。当前已有 p0、q 和完整 fallback 时，可以先取 p0 的支持点 x，再用 `fallback 0 (q x)` 的非空支持导出 Nonempty A；这不是无条件创造行动。
- **认证与物理安全**：零未认证占据不等于零物理失败。若另求物理全安全，必须补原初态支持在 B 内，以及已认证的实际行保持 B 的支持条件；不能只把 B 叫作 certified 就省掉该桥。
- **参考路径**：即使 hinit 成立，来源零质量历史仍可能有正参考质量。未经额外证明，保持原参考策略及预算；不要套用来源支持上的同策略身份。

## 7. 下一批整组生产集成的最小执行计划

1. **作为一个依赖整体整理八个已有私有来源模块**：动作擦除 → K1 → 一般 K2／QSD／首次退出，以及 G1–G3 → SafePrefix → SurvivalTail。选择必要公共端点，保留数学需要的辅助证明；现有 PASS/CLEAR 继续作为原证据，不通过改名改写其历史身份。
2. **先实现 N1–N4 的 Good-only 有限支持记忆适配**：一个定义层提供真实扩张模型和记忆反馈，一个证明层给完整前缀图身份及原安全事件质量。若 N2 只是归纳内部步骤，则保持私有，避免为了计数另造公开包装。
3. **以 N5 形成实际消费端点**：仍使用原 registered experiment、原 Good、原 viableFamilyPolicy、原参考 Q 和预算。原 Bad 质量只计一次。尚未需要整个辅助 joint 等式时，不开发第 5.1 节的更强有界完整记录实现。
4. **无限控制器任务接 B 的真实构造**：只在同一实际无限控制器及原动力学有有限实现后，使用第 5.2 节的全时图身份和已有尾链。新 W* 控制器与当前有限时域选择不同，单独陈述；不能让“有限前缀已接通”替代这项责任。
5. **整组发布时统一做生产门槛**：在真实基线决定生产路径／namespace／入口，绑定完整源码与依赖；必要聚焦构建先完成，再按治理要求一次进行该整组的 full build、native 公理／类型复用、消费者和 canonical resulting-main 验收。由于真正增加了来源适配，不能只凭旧私有 olean 预称生产 PASS；也不必为每个包装反复跑全库导出。

不为单个小适配制造独立发布；不改变冻结 106 项的 11 generated / 89 adapters / 6 boundaries。模块计数只有实际生产集成后才更新。

## 8. 对根总稿指定段落的只读核对

已对根最终 `GLOBAL_MATHEMATICAL_REVIEW.md` 的指定段落做窄核对，读取身份见 `SOURCE_INPUTS.json`，未编辑根稿。§4 的新结果、8.895 秒实际执行、公理范围、同源尾事件及不声称正极限均与源码一致；实数初始行已明确为 `η₀(v)=(p₀ v).toReal`。

§5.4 已注明有限 `q(X)` 编码，Good 上实际来源前缀与整个 auxiliary joint 身份分开；原 Bad 实验保留一次收费。来源支持身份不可改写参考 Q／hchecked／fallback，且支持齐次与数值齐次已明确分开。

§7A/B 的整组集成与来源目标无新的源级错误。§7C 已明确 `s_T>0`、一步剩余时域 `r≥1` 和 `g_r(u)>0`，初态为 `η₀(u)g_T(u)/s_T`，保留原初始失败；反例也准确区分两个安全态加一个墓地的三状态源与二维 killed Q。本次窄确认没有发现新增阻塞，不替代 B 的固定点或有限窗独审。
