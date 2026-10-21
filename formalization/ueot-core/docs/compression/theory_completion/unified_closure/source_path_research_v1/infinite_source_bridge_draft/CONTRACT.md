# 同一实际有限状态历史到既有无限轨迹：最小来源桥合同

日期：2026-10-21。作者工作区仅为 `tmp/finite-encoding-20261021/infinite-source-bridge-v1/`。

**状态：数学合同与完整私有 Lean 草稿；NOT_COMPILED，未独立审查，未集成。** 本目录没有运行 Lean、`lake build`、native export，也不改变既有源码、证据、书稿或 Git。草稿没有 `sorry`、新增公理或作为输入的目标来源等式；这不等于 elaboration 已通过。主智能体应统一安排一次聚焦编译窗口。

## 1. 此处已有事实与唯一新增目标

项目已经具有真实无限轨迹 `DynamicsKernel.homTrajMeasure`、完整前缀的初值与后继递推、初态混合、存活尾极限，以及同源的全时域受控安全定理。私有 `SourcePolicyPathBridge` 已实际证明：当前观察决定、时间齐次的随机策略所产生的实际行动—状态历史，在擦除行动后，等于同一模型及由该策略构造的 `policyPathKernel` 状态历史。私有 K1 又已实际证明该历史上从时刻 0 起的安全事件质量为真实限制矩阵的 `eta0 Q^n 1`。

**当前新增目标仅为：把这份完整递归状态历史，与同一初态、同一转移行产生的既有无限轨迹的完整有限前缀相等。** 只证明单时刻边缘、只验证前缀一致性，或并列放置一个 Markov 证书均不能替代这个目标。

`NEXT_MATHEMATICAL_TASKS.md` 的首选端点要求可测等价。Mathlib 实际存在 `MeasurableEquiv.IicProdIoc` 和 `MeasurableEquiv.piSingleton`，因此本草稿直接复用其逆映射及可测性，没有降级为只有终态的映射，也没有重建 Ionescu–Tulcea。

## 2. 一般有限 PMF 行定理：精确量词

给定任意有限类型 `X`，其可测结构使单点可测，任意实际初态 `p0 : PMF X`，以及固定行族 `J : X → PMF X`。定义

\[
R_J(x)=J(x).toMeasure,\qquad
\nu_\infty=\operatorname{homTrajMeasure}(p_0.toMeasure,R_J).
\]

Lean 中 `R_J := pmfRowKernel J`，以 `Kernel.ofFunOfCountable` 直接构造，并从每个实际 PMF 行证明其 Markov 性。没有另给一个核，再要求它与 J 相等。

令 `H_n := CausalHistory X X n`，`last_n := CoreOperationalAssembly.currentState n`，

\[
\lambda_n=\operatorname{causalLaw}
  \bigl(p_0,(n,h)\mapsto J(last_n(h)),n\bigr).
\]

构造可测等价

\[
e_n:H_n\simeq^m (\mathrm{Iic}(n)\to X).
\]

其时刻 0 分支是既有 `piUnique.symm`；后继分支先用 `e_n × piSingleton n`，再用区间拼接可测等价 `IicProdIoc (n ≤ n+1)`。因此恰有

\[
e_{n+1}(h,x)=\operatorname{appendHistory}_n(e_n(h),x),
\qquad e_n(h)(n)=last_n(h).
\]

所有旧坐标均由该等价保留，`Iic n` 包含 **0 到 n 共 n+1 个时刻**。

### G1：完整前缀身份

对每个 `n : ℕ`：

\[
\boxed{(e_n)_*\lambda_n.toMeasure
  =(\operatorname{frestrictLe}_n)_*\nu_\infty.}
\]

草稿端点：`state_history_eq_homogeneous_prefix`。Lean 左侧采用等价的 `(lambda_n.map e_n).toMeasure`，通过实际 `PMF.toMeasure_map` 与上式连接。

定理没有安全域、正概率历史、正存活、QSD、右特征函数、观察有限性、lumpability 或有限时域可行性前提。`p0` 直接作为输入，故不另索取 `Nonempty X`；若 X 为空则不能给出 p0，命题并不凭空构造一个概率分布。有限性用于现成有限历史实例及自动可测性；本批不宣称可数或一般状态空间 API 已完成。

## 3. 代入实际行动—状态来源

与已过来源桥完全同量词：`X Y A : Type u`，`Fintype X`、`Fintype A`、`Nonempty A`；任意模型 `M : Model X (fun _ => A)`、观察函数 `q : X → Y`、`sigma : Y → PMF A`、实际 `p0 : PMF X`。Y 无有限性或可测结构要求。

`observationMarkovPolicy sigma` 在每个完整可见历史上取末观察 y 后返回 `sigma y`，既不依赖时间，也不依赖更早历史。其实际微观来源为

\[
\nu_n=\operatorname{causalLaw}
 \left(p_0,\operatorname{riskMicroControlKernel}
 (q, M.transitionPMF,\operatorname{observationMarkovPolicy}\,\sigma),n\right).
\]

定义既有 `pi := liftedStationaryPolicy q sigma`，并令
`J := policyTransitionPMF M pi`、`a_n := eraseActionHistory n`。

### G2：实际随机闭环的完整前缀身份

\[
\boxed{(e_n\circ a_n)_*\nu_n.toMeasure
 = (\operatorname{frestrictLe}_n)_*
   \operatorname{homTrajMeasure}(p_0.toMeasure,R_J).}
\]

草稿端点：`actual_state_prefix_eq_homogeneous_prefix`。其正式 Lean 语句把左侧写成 `(nu_n.map (e_n ∘ a_n)).toMeasure`，因此仅要求 X 的单点可测，不需要对原行动记录载体预设可测结构。证明先应用已过 `actual_state_path_eq_stationary_path`，再实例化 G1；没有新的来源相等前提。

### G3：原始记录事件与无限圆柱事件的质量

为在原始 `nu_n.toMeasure` 上求事件质量，再给 A 可测结构且单点可测。对任意 `B : Set (Iic n → X)`：

\[
\boxed{\nu_n.toMeasure\big((e_n\circ a_n)^{-1}(B)\big)
 =\nu_\infty\big(\operatorname{frestrictLe}_n^{-1}(B)\big).}
\]

草稿端点：`actual_state_prefix_event_mass`。有限前缀空间上的任意 B 都可测；两边质量通过 G2 与实际 map 语义得到。这是任意**状态前缀事件**的桥，不只当前安全事件。任意行动相关事件若不能如此因子化，不在 G3 范围内。

一般完整因果策略仍属于现有风险接口的范围，但不会因本批 G1 泛化了 J 而自动成为齐次状态 Markov 策略。特别是，不可把 `viableFamilyPolicy` 与这里的 sigma 直接识别；需要实际平稳当前观察反馈身份，或另用完整历史/时间扩充状态的既有理论。

## 4. 构造性证明路线与可复用 API

| 当前步骤 | 实际源码与端点 | 作用 |
|---|---|---|
| 递归有限 PMF | `UEOT/V3/PathError.lean`：`CausalHistory`、`pmfExtend`、`causalLaw` 及有限/可测实例 | 保留实际初态和每个新增状态。 |
| 历史表示 | Mathlib `Probability/Kernel/IonescuTulcea/Maps.lean`：`MeasurableEquiv.piSingleton`、`MeasurableEquiv.IicProdIoc`；`MeasureTheory/MeasurableSpace/Embedding.lean`：`piUnique`、`prodCongr` | 构造真正可逆且可测的全部前缀编码。 |
| PMF → compProd | Mathlib `ProbabilityMassFunction/Monad.lean`：`toMeasure_bind_apply`；`Constructions.lean`：`toMeasure_map_apply`；`Integral/Lebesgue/Countable.lean`：`lintegral_countable'` | 按实际有限行积分计算，不把递推来源身份作为输入。 |
| 旧历史映射 | `DynamicsKernel.lean` 中 `homHistory_compProd_naturality` 的已过 measure-map/lintegral-map 计算模式 | 草稿仅抽取本题需要的左坐标映射计算，不引入 lumpability 前提。 |
| 无限初值及后继 | `DynamicsKernel.lean`：`homTrajMeasure_prefix_zero`、`homTrajMeasure_prefix_succ`、`appendHistory`、`homHistoryKernel` | G1 按 n 归纳，直接对齐既有完整前缀递推。 |
| 实际策略来源 | 已过私有 `SourcePolicyPathBridge.lean`：`actual_state_path_eq_stationary_path`；生产 `CoreOperationalAssembly.lean`：`policyTransitionPMF`、`policyPathKernel` | G2 复用已证明的同模型、同初态、同策略动作擦除身份。 |
| 无限概率律唯一性 | `DynamicsKernel.pathMeasure_eq_of_prefix_eq` | 若未来比较两个无限概率律，完整前缀身份可直接作为其输入；当前不造第二个无限过程。 |

归纳的实质是：

1. 真实 PMF 的 `pmfExtend` 测度等于旧历史测度与由实际 PMF 行构造的 kernel 的 `compProd`。
2. 在旧历史上推前 e_n 后，`e_n(h)(n)=currentState n h` 使下一状态读到同一个 J 行。
3. `e_(n+1)` 正是先保留新状态再 append；G1 的归纳假设与既有 `homTrajMeasure_prefix_succ` 因而适用。

没有把“同一核”“同一前缀分布”或“事件质量相等”放进前提来完成这三步。

## 5. 后续存活接入：准确结论与本批实现边界

本批草稿只实现 G1–G3 的候选证明体；**下述安全事件对齐、K1 组合、尾极限组合尚未在此目录形式化或执行验证**，不能写作已过端点。

对任意安全集 K，选择 `B_n(K)={z | ∀i:Iic n, z i∈K}`。在实际递归记录上证明

\[
(e_n\circ a_n)^{-1}B_n(K)
 =\{h:\neg riskEverFailure(\cdot\notin K,n,h)\}.
\]

该式是可复用的有限递归事件对齐证明义务，不是可作为输入省略的假设。G3 和已过 K1 随即给出

\[
\nu_\infty\{\omega:\forall t\le n,\omega_t\in K\}
 =s_n=\eta_0 Q^n\mathbf1,
\]

其中 Q 是同一 `policyMatrix M pi` 在 K 的子矩阵，`eta0(i)=p0(i)` 不归一化，时刻 0 已纳入事件。K1 使用实数质量；G3 使用 ENNReal 质量，最终组合必须显式使用概率有限性与 `toReal`，不能默默混淆两种类型。

接着可以直接复用下列生产定理，而无需重证整个无限理论：

- `UEOT.V3.Compression.Objecthood.survivalProb_eq_homTrajMeasure_apply`（`AbsorbedRepairHittingSemantics.lean`）：命中目标应传 `Kᶜ`，不是 K。
- `UEOT.V3.Compression.Objecthood.homTrajMeasure_apply_eq_lintegral_initial`（同一文件）：同一 R 的真实初态混合。
- `UEOT.V3.Compression.Objecthood.neverHitSet_eq_iInter_survivalSet`（同一文件）与事件反单调性，以及 `UEOT.V3.Compression.Objecthood.survivalProb_tendsto_neverHitProb`（`FiniteStationaryHittingExpectation.lean`）：有限尾到永不命中的既有连续性。

因此将来的组合结论是

\[
\Pr_{\nu_\infty}(\forall t:X_t\in K)
 =\lim_n s_n
 =\sum_{x\in K}p_0(x)h(x),\quad
h(x)=\Pr_{\delta_x,R_J}(\forall t:X_t\in K).
\]

`h=lim Q^n1`、最大不动点、`D={h=1}` 的完整转移支撑闭合、有限状态正安全可达性等是另一份已审数学合同的后续形式化；本批不越界宣称实现。既有 `ViabilityTrajectory.exists_stationary_policy_all_times_of_fixed`、`CoreInfinitePathClosure.exists_source_micro_all_times_viable_path_law` 与 `CoreSourceAllTimesAssembly.single_source_terminal_object_viability_all_times` 已证明真实同源概率一全时域安全，绝不是本批待填的“项目缺失结论”。

## 6. 必须保留的边界与小反例

1. **单时刻相等不足。** 在 `{0,1}` 上，先采一次公平位并永远保持，与每步独立公平位具有相同的全部一维边缘，但 `Pr(X0=X1)` 分别为 1 与 1/2。故完整前缀身份不可用所有单坐标边缘身份替代。
2. **历史策略不自动齐次状态化。** 取原状态 `{0,1}`，动作令下一状态等于该动作，初态公平。时刻 0 统一选动作 0，故 X1 总为 0；时刻 1 选动作 X0。两个正概率历史具有同一个当前状态 X1=0，却具有不同的下一状态律。故没有统一的当前状态行代表该完整历史策略。
3. **动作擦除有精确范围。** 在只有一个原状态、两个动作且两者均自环的模型中，总选动作 0 与总选动作 1 的状态路径完全相同，动作事件概率却分别为 1 与 0。G3 的状态事件因子化条件不能省略。
4. **初始失败不丢弃。** 若 `p0(Kᶜ)>0`，则 `s0=p0(K)`。把初态换成条件于 K 的分布会把时刻 0 存活改成 1，是另一概率实验。当前 G1–G3 始终使用原 p0。
5. **空 K 与 n=0。** 前缀有时刻 0；K 为空时每个有限安全事件和无限安全事件都为空，存活质量为 0。K1 的空子类型矩阵/有限和边界保持。本桥从来不要求 K 非空或当前正存活。
6. **全部有限存活正，不推出无限存活正。** 一个安全状态以 1/2 自环、以 1/2 退出到吸收坏态，给出 `s_n=2^{-n}>0`，无限存活为 0。此边界不是无限来源桥失败，而是正确的尾极限现象。
7. **不推得观察过程 Markov。** 微观状态行 J 的齐次性与观察值 q(X) 的 Markov 性不同；G2 不需要也不证明观察 lumpability。
8. **同一策略。** 本桥不能把另一存在性定理挑出的 `viableFamilyPolicy`、另一个 QSD 证书或不同初态接到当前随机实验；来源必须通过既有构造或实际证明的身份相连。

## 7. 后续最小执行窗口

候选文件：`SameSourceInfinitePrefix.lean`。直接 imports：已过私有 `SourcePolicyPathBridge`、生产 `UEOT.V3.DynamicsKernel`、已钉住 Mathlib 的 `MeasureTheory.Integral.Lebesgue.Countable`。不需载入 K2、QSD 或首次退出私有模块；它们不是 G1–G3 的证明依赖。

未来一次私有聚焦编译只检查此文件及三个 `#print axioms`。可复用来源桥实际 PASS 的 `.olean` 与生产缓存；必须核对其源码、二进制及环境身份，使用 root 统一分配的单线程绝对 Lake/Lean 协议。当前未开进程，不申请全库构建或 native。预期真实 elaboration 风险集中于递归可测等价的类型归约、`PMF.toMeasure_map`/`Measure.map_map` 的显式参数，以及 compProd 的核实例；任何修复只针对证明体或必要显式参数，不能加入来源等式前提。
