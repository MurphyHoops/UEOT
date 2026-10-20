# 下一批数学接口研究：有限观察载体与逐行样本量

状态：这是先于实现写出的科学论证。当前发布闭环已经完成；本目录 README 和实际构建收据记录其后的研究原型编译状态。原型尚未进入生产 import 图，本文不是生产 API 已完成的收据。

审读对象：Core `3869d166a6bd7f6eda9ea7a9aa6878fb7a3b7a7b`；路径以 `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/` 为基准。

## 1. 结论与建议次序

1. **逐行样本量可首先落地。** 将注册样本族改为 `sample : ∀ j, Fin (N j) → Ω → X`，`N : J → ℕ` 在数据前固定，`hN : ∀ j, 0 < N j`。逐行套用现有校准定理、取有限交事件即可。新统计结论不需发明集中不等式，也不需行间独立。真实实验坐标是 `Σ j, Fin (N j)`，不能给短行补虚构样本再当真实样本。
2. **有限观察载体可分成两个严格不同的范围。** 若同一个有限集合承载实际过程和参考过程，可以通过有限子类型及路径推前相等定理，复用现有所有有限观察风险结论。若只知道实际观察像有限，任意参考 `Q` 可能把质量送到该集合外，不能直接限制、丢掉或重归一化 `Q`。这种情况不使 TV 风险不等式本身失效；它需要保留越界质量的有限 escape 构造或一个真正的任意字母表 TV 扩展证明。
3. **近期不要同时把 `N_j`、`rho_j`、随机停时、任意观察类型全塞进同一个接口。** 保留当前 `rho : ℕ → ℝ`，只改 `N_j`，即可继续使用既有每时刻标量路径预算。行半径进一步推广是有价值的独立增强，须保留行占据权重或证明上界桥。

## 2. 逐行样本量的准确命题

令 `J` 和 `X` 为有限类型；`μ` 是同一个概率实验；每个预注册行有真实 PMF `p_j`。数据前固定整数 `N_j>0` 和半径 `ρ_j≥0`。样本

\[
Z_{j,k}:\Omega\to X,\qquad k\in\operatorname{Fin}(N_j)
\]

满足可测、每行内联合独立，并满足真实边缘律

\[
\mu\circ Z_{j,k}^{-1}=p_j.
\]

不要求两个不同行的样本彼此独立。经验 PMF 为同一批实际样本的经验分布

\[
\widehat p_j(\omega)=N_j^{-1}\sum_{k<N_j}\delta_{Z_{j,k}(\omega)}.
\]

存在同一个可测事件 `G`，使

\[
\mu(G^c)\le\alpha_N,
\qquad
\alpha_N=\sum_{j\in J}2^{|X|}\,2e^{-2N_j\rho_j^2},
\]

且

\[
\forall\omega\in G\;\forall j\in J,
\quad \operatorname{TV}(p_j,\widehat p_j(\omega))\le\rho_j.
\]

这里仍使用原有固定完整事件测试库，`Fintype.card (Finset X)=2^{|X|}`；未声称更优的有限字母表集中常数。

### 2.1 证明路线与真实复用

对每个 `j`，把 `DeploymentCoverage.coverage_registered_row_calibration` 的注册类型取为 `Unit`，样本量取 `N j`，真实行为常值 `row j`，得到可测好事件 `G_j` 与其坏概率界。取 `G=⋂j G_j`，使用 `measureReal_iUnion_fintype_le`。这是对已审单行统计结果的直接实例化；不需要重写 `BoundedLossTwoSided`、P-STAT 或冻结命题。

也可以将 `StatisticalRiskCalibration.measure_finite_row_calibration_bad_le` 的外层 `j` 求和保留，逐 `j` 调用 `BoundedLossTwoSided.measure_exists_candidate_bad_le (hN j)`。这一写法更短于重做 Hoeffding，但 singleton 适配能更直接复用已发布完整 TV 校准端点。

### 2.2 构造的真实采样实验

令

\[
I_N=\coprod_{j\in J}\operatorname{Fin}(N_j),
\qquad \Omega_N=X^{I_N},
\qquad \mu_N=\bigotimes_{(j,k)\in I_N}p_j,
\qquad Z_{j,k}(\omega)=\omega(j,k).
\]

Lean 使用 `Measure.pi (fun jk : Σ j, Fin (N j) => (row jk.1).toMeasure)`。概率性来自坐标 PMF 的概率性；边缘律来自 `measurePreserving_eval`；所有坐标独立来自既有 `HilbertMeanProductBlockIndependence.coordinate_iIndep`，再用 `iIndepFun.precomp` 沿 `k ↦ ⟨j,k⟩` 限制到该行。这是生成实验本身的证明，不是把独立性和采样律列成一个无法兑现的外部假设。

`VariableRegisteredSamples.lean` 实现这条路线；在完成当前发布后，已对独立研究原型作聚焦编译并检查终端公理闭包。实际状态与源码身份见本目录构建收据；尚未将该原型登记为生产 API。

### 2.3 注册部署接口的最小扩展

仍取

```lean
J := CoverageRegisteredRow certified T
N : J → ℕ
hN : ∀ j, 0 < N j
sample : ∀ j, Fin (N j) → Ω → X
rho : ℕ → ℝ
```

真实行保持 `P j.1.1 j.1.2.2 j.1.2.1`。好事件改为

```lean
∀ j : J,
  tvDist (P j.1.1 j.1.2.2 j.1.2.1).toMeasure
    (empiricalResponsePMF (hN j) (sample j) ω).toMeasure
      ≤ rho j.1.1
```

预算是

```lean
∑ j : J, (Fintype.card (Finset X) : ℝ) *
  (2 * Real.exp (-2 * (N j : ℝ) * (rho j.1.1)^2))
```

在 `coverage_empirical_registered_microscopic_failure_risk` 的局部证明中，每个注册 `j=⟨(⟨n,hn⟩,a,x),hc⟩` 使用自己的 `empiricalResponsePMF (hN j)`。真正使用的数学桥 `empirical_coarse_row_tv` 不含样本量，因此其推导完全保留。得到的每时刻误差仍是 `ε_n=min 1 (rho n + eta ω n)`，实际占据预算、选择后联合分布和坏事件只计一次的证明全部可以复用。

于是同一个 Good 上的拟合、实际占据上界和检查预算为 `β∈[0,1]` 时，

\[
J(E)\le\min\{1,\alpha_N+(1-\alpha_N)\beta\}.
\]

无需按所选候选再次 union，也不需要重新花一个“样本量事件”预算，因为所有 `N_j` 已经预注册。

### 2.4 最小非平凡见证

可以复用现有 `RegisteredDeploymentRiskWitness` 的两个真实 Bernoulli 行、控制定义、事件和第一行首个样本选择规则，仅令

\[
N_{\mathrm{false}}=256,
\quad N_{\mathrm{true}}=512,
\quad \rho=1/8.
\]

新的真实坐标积包含 768 个样本，不是 512 个加上重复填充。好事件坏预算成为

\[
\alpha_N=8e^{-8}+8e^{-16},
\]

比把两行都按最小样本量处理得到的 `16e^{-8}` 更小。首个 false 行样本的真实边缘律仍是失败概率 `1/8`，因此同一选择规则的实际部署风险仍由

\[
(7/8)(1/8)+(1/8)(1/4)=9/64
\]

给出。实际风险等式必须重新绑定到新的积样本空间和选择映射，不能把旧 witness 的类型当成新证明。

全一记录有正概率 `(1/8)^256(1/4)^512`；它的所选经验失败率为 1，仍能见证全记录检查界不成立，而 Good-only 检查有实质内容。现有零占据证明只依赖初始状态和选中动作确实为注册行，不依赖两行样本量相同，适合直接复用。

### 2.5 必须保留的边界

- `N_j` 不能直接改成 `N_j(ω)`。固定样本量定理不提供任意停时有效性。若确要数据驱动样本量，可先注册有限允许长度并对 `(j,n)` 分配显式预算，或另证时间一致界。
- `N_j=0` 无法由当前 `empiricalResponsePMF` 构造经验概率分布。应把该行排除在训练认证集外，保留真实未认证占据代价；不能补一个任意 PMF 再声称已校准。
- `J=∅` 合法：好事件是全空间，预算为零，所有样本前提为空。这不产生任何已认证部署行；实际未认证占据仍由策略和源过程决定。
- 不同行可以共享相关数据，但每行内独立及真实边缘律不能省略。例如把同一个 Bernoulli 样本复制 `N` 次，各坐标边缘律虽正确，经验均值没有获得 `N` 次独立样本的集中率。
- 事后从大量未注册实验里挑一个极端记录，再把它当成事前固定一行，会改变采样法律。原有允许的 data-dependent selection 是对共同好事件已经同时覆盖的模型/策略选择，不是随意重定义产生该好事件的实验。

### 2.6 若进一步使用 `rho_j`

若要各行半径也不同，可以定义已认证行误差

\[
e_n(x,a)=\min\{1,\rho_{(n,a,x)}+\eta_n(x,a)\}.
\]

最精细的路径端点已由 `coverage_same_policy_path_error` 支持，它保留实际行占据权重：对认证行用 `e_n(x,a)`，对未认证行用 1。不能把 `rho_j` 毫无证明地塞进旧的单一 `rho n`。

要复用当前标量时间预算，可明确给定 `rhoTime : ℕ → ℝ` 和 `∀ j, rho j ≤ rhoTime j.time`。或取该时刻注册行的有限最大值，但空注册行必须有显式 fallback（例如 0）并证明其上界，而非额外假定每个时刻一定存在注册行。独立审查员已确认这一量词边界。

## 3. 有限观察像：精确的子类型方案

### 3.1 当前范围在哪里出现

`coverageDeploymentRowLaw` 及 `coverage_rowLaw_expectation` 本身不要求 `[Fintype Y]`；实际过程只在有限 `X` 与 `A` 上生成历史。`[Fintype Y]` 出现在：

- `coverage_same_policy_row_tv` 对 `pmfExtend` 的有限共同质量恒等式复用；
- `coverage_projected_causalLaw_error` 中参考历史和下一步观察字母表的有限性；
- 风险端点把任意 `F` 自动当作可测集合；
- `PathError` 的有限全空间共同质量公式与相应递推。

因此不能只删除最外层定理的类型类前提；需要一个保真的载体桥，或推广底层 TV 结果。

### 3.2 可直接证明的有限载体定理

令 `X,A` 有限，`Y` 任意且配备可测单点的可测结构。`q:X→Y` 是观察映射。取有限集合 `S⊆Y`，满足：

1. `q(X)⊆S`；
2. 对 `n<T`、`y∈S`、行动 `a`，参考行 `Q_n(y,a)` 的支持包含于 `S`。

第二项可以进一步只要求实际会被参考策略使用的可达行，但第一版使用上面的可检查闭合条件，证明及接口更短。若 `S=range q`，第一项自动成立，且其有限性来自 `X` 有限。

令 `Y_S={y//y∈S}`，包含映射 `i:Y_S→Y`，`q_S(x)=⟨q(x),…⟩`。由支持闭合构造真正的归一化 `Q_S`，要求并证明

\[
(Q_{S,n}(y,a)).\operatorname{map}(i)=Q_n(i(y),a),\qquad n<T.
\]

不是把该等式或结论偷偷加入模型公理；支持闭合先作为可检查前提，`Q_S` 用子类型提升/可测回缩构造，等式由 PMF 支持性质推出。零概率行的 totalization 和 `n≥T` 的 fallback 明确给出。

将政策限制到被嵌入的历史：

\[
\pi_{S,n}(h)=\pi_n(I_n(h)),
\]

其中 `I_n` 保留每个行动并逐观察应用 `i`。必须证明以下三个绑定等式：

1. 微观实际路径律相等：`source(q,P,π)=source(q_S,P,π_S)`；
2. 原参考路径律是有限参考路径律的真正推前：`reference_S.map I_T=reference`；
3. 对每个 `n≤T`，两种表示给出的实际部署行 PMF 完全相同。

第三项保证引用的是同一个策略和源产生的真实占据，避免从另一个策略拿 `hcap`。

有限嵌入保持 TV：对有限载体上的两个 PMF `p,r`，

\[
\operatorname{TV}(p\circ i^{-1},r\circ i^{-1})=\operatorname{TV}(p,r).
\]

可用两次 `tvDist_map_le`：`i` 可测，并有可测左逆 `r:Y→Y_S`。当 `S` 非空时，回缩在 `S` 外取固定 fallback；每个逆像是有限点集或其补集，因此可测。`S` 的非空性由实际初始 PMF 和 `q(X)⊆S` 推出，不必无端添加 `Nonempty Y`。

结合这些等式，直接调用现有 `coverage_same_policy_certified_path_error`、`coverage_same_policy_microscopic_failure_risk`；同样的 `ε_n` 和实际 `κ_n` 原值保留。

对于任意 ambient 事件 `F`，建议新原生风险 API 显式接受 `MeasurableSet F`，而不是继续借 `[Fintype Y]` 自动生成。有限载体的逆像总是可测，但原参考事件概率与推前等式的 Lean 证明仍须给出正确可测桥。

### 3.3 哪些常用参考行自动满足闭合

- `Q_n(y,a)=(P_n(r(y),a)).map q` 形式的代表元参考行；
- `Q_n(y,a)=\widehat p_{n,y,a}.map q` 形式的真实经验参考行；
- 任何已证明由有限 `Y_S` PMF 经 `Subtype.val` 推前的参考行。

这说明第一版有实际覆盖范围，并非为绕过难题凭空增加对现实无用的前提。但它仍是“支持闭合参考模型的任意 ambient 观察类型”API，不能宣传为任意 `Q` 的通用范围已经全部放宽。

### 3.4 必要的反例：不能丢弃参考越界质量

取 `X=Unit`，`A=Unit`，`Y=ℕ`，`q(*)=0`，实际过程始终为 0，参考行

\[
Q(0)=\tfrac12\delta_0+\tfrac12\delta_1.
\]

实际观察像 `{0}` 有限，但是该参考行不能作为 `{0}` 上的归一化 PMF 原样提升。正确一阶 TV 是 `1/2`。若先删掉 `1` 的质量、再把 `{0}` 上剩余质量重归一化为 `δ_0`，会错误得到 TV 为零。

反例否定的是“不保留越界质量的子类型简化”，不是否定任意 `Y` 上的真实 TV 界。

## 4. 不要求参考闭合的有限 escape 路线

### 4.1 基本构造

取 `S=range q` 和有限 `S_+=S⊔{escape}`。在所有观察仍在 `S` 的活历史上，原策略可由有限历史唯一恢复：仍用原 `π`。参考下一观察若在 `S` 内则保留其具体值，若在外则记为 `escape`；之后吸收于 `escape`。越界后的行动可固定为明确 fallback，因为最终历史已经与实际过程的全部历史支持不相交。

原参考过程在活历史上的点概率不变；所有曾越界路径合并进某些 escape 历史，质量总和保留。实际过程永不进入 escape。

### 4.2 为什么路径 TV 能精确保留

对支持于有限集合 `H_S` 的实际 PMF `p` 和任意参考 PMF `r`，在可测单点结构下有

\[
\operatorname{TV}(p,r)=1-\sum_{h\in H_S}\min(p(h),r(h)).
\]

参考在 `H_S` 外的全部质量与 `p` 没有共同质量，合并它不会改变右式。escape 构造保持每个活历史的参考点概率，故原路径 TV 与有限 escape 路径 TV 相等。下一步行 TV 同理：实际行支持于 `S`，把参考行所有外部质量合并为 escape 精确保留真实行 TV。

之后可调用现有有限路径加性界；经这两个 TV 等式把预算带回原始 `Y` 与原始参考路径律。不能只用普通推前收缩，它的方向只给有限压缩 TV ≤ 原 TV，不足以反推原路径风险；**足以带回原路径的双向 TV 桥**是必须新增的责任；它可以通过共同质量证明，也可以通过后续 [有限逃逸编码的事件证明](FINITE_OBSERVATION_ESCAPE.md) 完成。

### 4.3 尚须形式化的真实责任

- 有一侧有限支持时的精确有限编码 TV 等式。本文初始路线使用共同质量公式；后续 `FINITE_OBSERVATION_ESCAPE.md` 已给出不依赖该公式的事件与补事件证明，仍需落实到 Lean；
- escape 因果核的构造与所有活历史质量等式；
- 不依赖真实过程的微观不可见信息来选择 escape 核；活历史中 `π` 由原观察历史恢复；
- 行 TV 和全路径 TV 精确保留；
- 原 ambient 事件 `F` 的可测性与概率转移；
- 明确有限时域和 fallback；不声称无限时域存活。

这条路线很有希望完整删除风险端点 `[Fintype Y]` 而不限制参考 `Q`，但当前没有编译证据，应作为支持闭合接口后的独立研究目标。如果期间找到可直接复用的任意 PMF TV 混合/扩张定理，可以比较复杂度后选择更短证明，不能将“预计可行”写成 API 已实现。

## 5. 与统一主线的连接

有限观察载体强化了已有 `RecursiveSufficientState` 的重要区别：表示的 ambient 坐标空间不等于实际可达像。M-QD 的唯一性属于实际可达像上的因子化；扩展到整个 ambient 空间时，支持、可测性和未达历史的 totalization 是额外责任。风险层做同样的区分，能使这一结构贯穿表示—动力学—验证，而非另立一个无来源抽象。

逐行样本量则明确区分“统一结构”与“统一资源额度”：不同注册行可以花费不同数据预算，统一性来自同一个真实实验、同一个好事件与同一个实际部署策略的严格对接，不要求所有行使用同一数量的样本。

这两点能反哺哲学著作对“对象边界、可达性、表述与现实、有限验证责任”的独立论证。它们不把真实世界的样本同源性、可重复实验或经验适用性由 Lean 自动证明出来。

## 6. 可复用来源清单

| 文件 | 实际公开来源 | 新任务用途 |
| --- | --- | --- |
| `DeploymentCoverage.lean` | `coverage_registered_row_calibration` | singleton 行校准，变量 N_j |
| `StatisticalRiskCalibration.lean` | `measure_finite_row_calibration_bad_le` | 可替代的逐行 union 证明模板 |
| `UEOT/V3/BoundedLossTwoSided.lean` | `measure_exists_candidate_bad_le` | 固定 N 单行 Hoeffding 与有限测试 union |
| `StatisticalRiskWitness.lean` | `productRowLaw`, `productRowSample_law`, `productRowSample_independent` | 现有同源 product 实验路线 |
| `UEOT/V3/HilbertMeanProductBlockIndependence.lean` | `coordinate_iIndep` | Σ j, Fin(N_j) 的真实独立坐标 |
| `EmpiricalReferenceRisk.lean` | `empiricalResponsePMF`, `empirical_coarse_row_tv` | 真实经验分布；统计到风险接口不依赖 N |
| `DeploymentCoverage.lean` | `coverage_same_policy_path_error`, `coverage_expected_error_le` | 逐行 TV 占据加权，标量时间预算桥 |
| `RegisteredDeploymentRisk.lean` | `registered_selected_joint_failure_of_cap_on_good` | 共同好事件、选择、真实占据、一次坏预算 |
| `TrainingDeploymentJoint.lean` | `selectedTrainingDeployment_failure_le` | 保留 α+(1−α)β 的联合概率步骤 |
| `UEOT/V3/Compression/RecursiveSufficientState.lean` | `ReachableState`, `toReachable`, `toReachable_surjective` | 有限真实观察像的现成概念 |
| `FiniteHorizonPathAdapter.lean` | `causalLaw_congr_before` | 只在 n<T 控制参考行，明确时域外 totalization |
| `FinitePMFProjection.lean` | `risk_map_extend_right` | 新观察映射与因果扩张自然性 |
| `UEOT/V3/TotalVariation.lean` | `tvDist_map_le` | 有限包含/可测回缩两向 TV 相等 |
