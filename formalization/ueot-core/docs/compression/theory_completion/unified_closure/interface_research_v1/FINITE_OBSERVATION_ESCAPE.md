# 有限实际观察像、逃逸质量与原路径 TV

数学论证已完成；本节给出的任意观察类型风险扩展尚未成为生产 Lean API。本文以当前 Core 的 `TotalVariation`、`PathError` 与 `UnifiedClosure/DeploymentCoverage` 实际定义为准。

## 1. 要解决的准确问题

当前 `coverage_same_policy_path_error` 与 `coverage_same_policy_certified_path_error` 要求微观状态 X、行动 A 和观察 Y 都有限。实际源过程在有限 X、A 上生成历史，因此 q : X → Y 的完整像已经有限；Y 的其他点只可能出现在参考过程 Q 中。

这不能直接支持“把 Q 限制到 range q”：Q 可能向该像以外发送正质量。正确目标是允许任意可测单点的观察空间 Y，并保留原始 Q 的全部概率质量。先使用完整 S = range q；较小的可达观察集另外讨论。

以下论证给出：

1. 一侧源概率全部集中于有限载体时，保留每个载体点并把其余点合并为一个逃逸点，**精确保持源—参考 TV**。
2. 用这个有限字母表构造一个真正的吸收参考 PMF 过程。其每条完全位于 S 的完整历史质量等于原参考过程的相应质量。
3. 两个过程逃逸后的详细行为可以不同；共同有限路径编码仍精确保留与源路径的 TV。
4. 因而现有有限字母表的实际占据路径界可以传回原 Y，原来的 Q、源策略和实际占据预算均被保留。

## 2. 核心引理：一侧有限支撑下的精确 TV 编码

设 Y 是可测空间，所有单点可测；S ⊆ Y 有限。设 μ、ν 是 Y 上的概率测度，且 μ(Sᶜ) = 0。ν 无须集中于 S。

给有限集合 S 增加一个不同于其中任何点的符号 ⊥，记 Z = S ⊔ {⊥}，赋予离散可测结构。定义

\[
c(y)=\begin{cases}
y\text{ 的 S 子类型},&y\in S,\\
\bot,&y\notin S.
\end{cases}
\]

则 c 可测，且

\[
\boxed{\operatorname{TV}(\mu,\nu)
 =\operatorname{TV}(c_*\mu,c_*\nu).}
\tag{1}
\]

这里 TV 正是 Core 的可测事件上确界定义：

\[
\operatorname{TV}(\mu,\nu)
 =\sup_{A\text{ 可测}}|\mu(A)-\nu(A)|.
\]

### 2.1 可测性与逃逸质量

c 的每个 live 单点纤维是 Y 的单点；⊥ 的纤维为 Sᶜ。有限可测单点的并给出 S 可测，所以 c 可测。特别地，

\[
(c_*\nu)(\{s\})=\nu(\{s\})\quad(s\in S),\qquad
(c_*\nu)(\{\bot\})=\nu(S^c),\qquad
(c_*\mu)(\{\bot\})=0.
\tag{2}
\]

没有删除、重新归一化或条件化任何参考质量。

### 2.2 正向不等式

可测数据处理给出

\[
\operatorname{TV}(c_*\mu,c_*\nu)\leq\operatorname{TV}(\mu,\nu).
\]

这只是所需等式的一半，单独使用它不足以把有限编码的路径上界传回原路径。

### 2.3 反向不等式的完整事件证明

记 d = TV(c_*μ,c_*ν)。对任意可测 A ⊆ Y，令 B ⊆ Z 只包含 A∩S 对应的 live 点，不包含 ⊥。于是 c⁻¹(B) = A∩S，而且 μ(A) = μ(A∩S)。由 ν 的非负性，

\[
\begin{aligned}
\mu(A)-\nu(A)
&\leq\mu(A\cap S)-\nu(A\cap S)\\
&=(c_*\mu)(B)-(c_*\nu)(B)\\
&\leq |(c_*\mu)(B)-(c_*\nu)(B)|\leq d.
\end{aligned}
\tag{3}
\]

再对 Aᶜ 使用同一个结论。**因为 μ、ν 的总质量都为 1**，

\[
\nu(A)-\mu(A)
 =\mu(A^c)-\nu(A^c)\leq d.
\tag{4}
\]

因此所有可测 A 都满足 |μ(A)−ν(A)| ≤ d，取确界即得反向不等式，完成 (1)。这个证明不需要假设 ν 有限支撑，不需要完整空间的共同质量公式，也不需要事先构造最大耦合。

### 2.4 各假设的作用

- 一侧 μ 全部集中于 S，使 (3) 中 μ(A) = μ(A∩S)。两侧都可在 S 外有质量时，合并不同外部点一般会严格减少 TV。
- 参考总质量不能丢失；等式 (4) 使用两侧相同的概率总质量。此证明不能原样套给总质量不同的有限测度。
- 保留 S 上的每个独立观察点，并为外部设置与所有 live 点不同的 ⊥，确保 A∩S 是编码事件的精确逆像。
- 单点可测和 S 有限给出 c 可测及任意载体迹的可测性。不要求 Y 有限、可数或具有拓扑。

更抽象地，令 I 有限、i : I ↪ Y 为注入，编码到 Option I；对 i(I) 外统一返回 none。同一引理成立。这个按有限索引编号的版本用于下一节，让两个不同路径空间共用同一个有限目标类型。

## 3. 核心路径比较引理：相同 live 原子足够

设 I 有限，i : I ↪ H、j : I ↪ K 为两个可测单点空间中的注入。p 是 I 上的源 PMF，ν、ξ 分别是 H、K 上的参考 PMF。假设

\[
\forall\ell\in I,\qquad \nu(\{i(\ell)\})=\xi(\{j(\ell)\}).
\tag{5}
\]

则

\[
\boxed{\operatorname{TV}(i_*p,\nu)
 =\operatorname{TV}(j_*p,\xi).}
\tag{6}
\]

证明如下。分别把 H、K 编码到**同一个** Option I：i(ℓ)、j(ℓ) 都编码为 some ℓ，其他点编码为 none。由 (5)，两个编码参考 PMF 在所有 some ℓ 上相等；由于它们都归一化，剩下的 none 质量也相等：

\[
1-\sum_{\ell\in I}\nu(\{i(\ell)\})
 =1-\sum_{\ell\in I}\xi(\{j(\ell)\}).
\]

编码后的源 PMF 都是 some_*p。分别对 H、K 使用 (1)，中间编码 TV 完全相同，得到 (6)。

这不是假定两个完整参考过程互为推前。只要求证明所有 live 历史的原子质量相等，并保留总质量；两侧非 live 部分内部的分配可以不同。

## 4. 为当前受控风险 API 构造有限参考过程

固定有限 X、A，配备可测单点的可测结构；Y 任意并具有可测单点。输入保持现有接口的真实对象：

- 初始 PMF p₀ : PMF X；
- 观察 q : X → Y；
- 实际源行 P : ℕ → X → A → PMF X；
- 任意参考行 Q : ℕ → Y → A → PMF Y；
- 完整因果策略 πₙ : CausalHistory Y (A×Y) n → PMF A；
- 有限时域 T。

第一版取 **S = range q**，有限性来自 X 有限。更一般，也可用任何有限 S 满足 q(X) ⊆ S。令 Z、c 如上，q̄ = c∘q。

### 4.1 完整策略及逃逸后的定义

取 y★ ∈ Y，定义解码 d : Z → Y：live s 解码为 s，⊥ 解码为 y★。这里无需增添不明的非空假设：p₀ 的非空支持给出 x★，可取 y★ = q(x★)。

对每个完整 Z 历史逐观察应用 d，保留所有行动，得到 Dₙ。定义

\[
\bar\pi_n(\bar h)=\pi_n(D_n\bar h).
\tag{7}
\]

这给出所有历史上的完整策略，包括逃逸或不可能历史。它直接使用已有完整 π 返回的 PMF，不从空行动类型凭空构造行动分布。y★ 只参与逃逸历史的全定义，不改变 live 历史上的行动 PMF。

定义真正的有限参考行

\[
\bar Q_n(z,a)=\begin{cases}
c_*Q_n(s,a),&z=s\in S,\\
\delta_{\bot},&z=\bot.
\end{cases}
\tag{8}
\]

每行仍然是 PMF。参考过程进入 ⊥ 后吸收；进入 ⊥ 的概率正是原行离开 S 的概率。

### 4.2 实际源及实际占据保持相同

由于 q(X) ⊆ S，对每个微观历史 h 都有

\[
D_n\bigl(\operatorname{historyMap}(\bar q)(h)\bigr)
 =\operatorname{historyMap}(q)(h).
\tag{9}
\]

因此 (7) 在实际微观历史上返回与 π 完全相同的行动 PMF。两个 `riskMicroControlKernel` 逐历史相等，于是它们生成的微观 `causalLaw` 相等。进一步，

\[
\operatorname{coverageDeploymentRowLaw}(p_0,q,P,\pi,n)
 =\operatorname{coverageDeploymentRowLaw}(p_0,\bar q,P,\bar\pi,n).
\tag{10}
\]

这一步保留同一个实际 P、初始分布和策略行为，因而以后使用的未认证占据是原占据，不是有限参考过程的占据。

## 5. 完整 live 历史质量的真实递推

令

\[
L_n=\operatorname{CausalHistory}(S,A\times S,n).
\]

它包含初始观察、每一步行动和每一步后继观察；A、S、n 有限，所以 Lₙ 有限。令 Iₙ : Lₙ ↪ Hₙ 把 S 子类型嵌入原 Y 历史；令 Jₙ : Lₙ ↪ Kₙ 把 S 嵌入 Z 的 live 点。两者都保留行动且为注入。

记 νₙ 为原参考 `causalLaw (p₀.map q) (riskMacroControlKernel Q π) n`，ν̄ₙ 为有限参考对应路径律。证明

\[
\forall n\;\forall\ell\in L_n,\qquad
\bar\nu_n(J_n\ell)=\nu_n(I_n\ell).
\tag{11}
\]

这里等号比较 PMF 原子质量。

初始步由 q̄ = c∘q 和 c 在 S 上的单点纤维性质得到。归纳步对附加记录 (a,s′) 使用实际 `pmfExtend_apply`：

\[
\begin{aligned}
\bar\nu_{n+1}(J_{n+1}(\ell,(a,s')))
={}&\bar\nu_n(J_n\ell)\,
\bar\pi_n(J_n\ell)(a)\,
\bar Q_n(\operatorname{last}(J_n\ell),a)(s')\\
={}&\nu_n(I_n\ell)\,
\pi_n(I_n\ell)(a)\,
Q_n(\operatorname{last}(I_n\ell),a)(s')\\
={}&\nu_{n+1}(I_{n+1}(\ell,(a,s'))).
\end{aligned}
\]

第二个等号分别使用归纳假设、live 历史上 (7) 的策略相等，以及 (2) 的 live 行原子质量相等。**没有把 (11) 放进模型假设。**

令 p⁽ᴸ⁾ₙ 为实际微观路径经 q 的 S 子类型映射所得 PMF。原实际观察路径为 (Iₙ)_*p⁽ᴸ⁾ₙ；有限实际观察路径为 (Jₙ)_*p⁽ᴸ⁾ₙ。把 (11) 代入 (6)，即得

\[
\boxed{\operatorname{TV}(\mu_n,\nu_n)
 =\operatorname{TV}(\bar\mu_n,\bar\nu_n).}
\tag{12}
\]

原参考过程离开 S 后可以回到 S，但相应**完整历史**仍不是 live 历史。有限吸收过程与原过程在非 live 部分可以不同；(12) 的证明使用两边到 Option Lₙ 的完整历史编码。只比较末状态不够，也不能把 (11) 误述为 ν̄ₙ 是 νₙ 的逐坐标 c 推前。

## 6. 传回原观察空间的风险结论

对任意实际源行，`(P n x a).map q` 的全部质量位于 S；在 q̄(x) 处，(8) 正好采用对应原 Q 行的完整编码。因此 (1) 还给出逐行精确等式

\[
\operatorname{TV}((\bar q)_*P_n(x,a),\bar Q_n(\bar q(x),a))
 =\operatorname{TV}(q_*P_n(x,a),Q_n(q(x),a)).
\tag{13}
\]

记原实际状态—行动占据 PMF 为 wₙ。把有限 Z 输入现有 `coverage_same_policy_path_error`，再用 (10)、(12)、(13)，可推出同样的原路径界：

\[
\operatorname{TV}(\mu_T,\nu_T)
\leq\sum_{n<T}\sum_{(x,a)}w_n(x,a)\,
\operatorname{TV}(q_*P_n(x,a),Q_n(q(x),a)).
\tag{14}
\]

若在所有 n<T 的已认证行上有真实行 TV ≤ εₙ，则继续复用 `coverage_same_policy_certified_path_error` 得到

\[
\operatorname{TV}(\mu_T,\nu_T)
\leq B_T:=\sum_{n<T}\bigl[\varepsilon_n+
(1-\varepsilon_n)u_n\bigr],
\quad
u_n=w_n\{(x,a):\neg\operatorname{certified}(n,x,a)\}.
\tag{15}
\]

这保持当前加性占据端点的量词，不宣称由平均行误差得到统一乘积界。式 (15) 使用实际占据 u_n；若进一步用上界 κ_n 替代它，还须保留 ε_n ≤ 1，才能沿 1−ε_n 的非负系数代入占据上界。

最后，给出原 Y 历史中的可测事件 F，以及同一个微观 E 的包络
`E ⊆ historyMap(q)⁻¹ F`。原型应显式接受 `MeasurableSet F`，以替代旧有限 Y 自动给出的可测性。现有两个本来就不要求有限观察类型的末端引理，`risk_microscopic_event_le_envelope` 与 `risk_event_transfer`，给出

\[
\Pr_{\text{原实际源}}(E)
\leq\min\{1,\nu_T(F)+B_T\}.
\tag{16}
\]

因此有限编码只是证明工具；(16) 中的 ν_T(F) 仍是**原始 Q、原始 π 的参考事件概率**。无需把任意 F 强行编码成一个在所有逃逸历史上精确保持的有限事件。

## 7. 为什么第一版必须先使用完整 range q

S = range q 自动保证所有实际源行的下一观察都在 S，而且 q̄(x) 永远是 live 点。这样 (9)、(10)、(13) 都是全局逐点等式，可以直接消费现有对所有 certified 行量化的合同。

如果 S 只是某个初始分布和策略下的较小可达像，则可能存在 q(x)∉S 的全局 certified 行。此时 q̄(x)=⊥，而 Q̄ 在 ⊥ 上被定义为 δ⊥，它一般不等于 c_*Q(n,q(x),a)。原全局 `hcert` 不能直接传给新的全部 certified 行。

较小 S 的第二版可以采用下述路线，但还需独立的实际支持归纳：

1. 明确证明原源在每个 n≤T 的正概率完整历史都只观察到 S。
2. 有限模型只认证 `certified(n,x,a) ∧ q(x)∈S`。
3. 证明新旧源路径 PMF 相同，并利用实际占据在 q(x)∉S 上为零，证明新旧未认证占据完全相等。
4. 在真正用到的实际支持上证明后继观察仍落于 S；不能从当前观察纤维代替真实历史后验支持。

这条更小载体路线有可能缩小有限编码的规模，但不能用一句“都是不可达状态”跳过同策略的路径与占据证明。当前完整 range q 的方案已经足以从现有有限 X、A 风险层移除全局 `[Fintype Y]`，不需要同时完成这项进一步收缩。

## 8. 必要反例和不可替代的步骤

**删除后归一化错误。** 取 Y=ℕ，S={0}，μ=δ₀，ν=(δ₀+δ₁)/2。原 TV 为 1/2。保留逃逸质量的编码为 μ̄=δ₀、ν̄=(δ₀+δ⊥)/2，TV 仍为 1/2。删除 1 并重新归一化会错误得到 TV=0。

**一侧集中条件不可删除。** 取两个不同点 1、2 都在 S 外，μ=δ₁、ν=δ₂。原 TV 为 1，两个编码都为 δ⊥，编码 TV 为 0。

**外部不能碰撞 live 点。** 若把外部 1 直接映回 S 内 0，μ=δ₀、ν=δ₁ 的 TV 会从 1 变为 0。单独要求编码在 S 上单射还不够，外部必须用独立逃逸点。

**吸收过程不是逐坐标推前。** 取原参考确定性路径 0→1→0，S={0}。逐坐标编码为 0→⊥→0；吸收参考为 0→⊥→⊥。两者不同。但两条完整历史都非 live，所以在 Option L₂ 中都进入 none；(11)、(12) 没有要求它们逐坐标相等。

**末观察不足以编码路径。** 对实际路径 0→0→0 和参考路径 0→1→0，末观察律相等，而完整历史 TV 为 1。因此 Lₙ 必须保留全部观察及行动。

## 9. 具体 Lean 义务与可复用入口

本节的数学证明不把未编译草稿当作生产证据。最小实现宜分成以下实际义务；每项的目标都由前面证明推出。

| 义务 | 精确目标和可复用源 |
|---|---|
| 有符号事件转 TV | 证明 `(∀ A, MeasurableSet A → μ.real A - ν.real A ≤ b) → tvDist μ ν ≤ b`；用 `tvEventSet_nonempty`、`csSup_le` 与 `probReal_add_probReal_compl`。现有 `InformationKernelTV`、`BinaryTesting` 已实际使用同一种概率补集论证，可核对 API，不必引入其更重的密度/Hahn 证明。 |
| 载体迹 TV 反向 | 对可测 S、μ.real Sᶜ=0，使用 `measureReal_inter_add_sdiff` 和 `measureReal_mono` 证明 (3)，并证明每个 A∩S 为某个编码事件的精确逆像。配合 `TotalVariation.tvDist_map_le` 得到 (1)。 |
| 真实有限编码 | 以有限 I 及注入 i 定义 `Y → Option I`；证明 some 纤维恰是 `{i s}`、none 纤维恰是 `(Set.range i)ᶜ`，以及可测性、真实 `PMF.map` 单点质量。 |
| 编码参考法相等 | 在有限 Option I 上，由所有 some 质量相等和 `PMF.tsum_coe`／`coverage_sum_toReal` 的总质量 1 推出 none 也相等，再用 `PMF.ext`。由此实现 (6)。 |
| 历史映射结构 | 通过 `riskHistoryMap` 的定义归纳，证明复合、注入性和解码—live 嵌入相等；`risk_last_project` 已可复用。 |
| 原实际源与占据 | 展开 `riskMicroControlKernel` 和 `coverageDeploymentRowLaw`，以 (9) 证明同一实际核、`causalLaw` 与实际占据 PMF 的等式 (10)。 |
| 原参考 live 原子 | 以 `causalLaw` 和 `pmfExtend_apply` 证明 (11)。每步先证明 live 策略和 `Q̄` 的实际 PMF 原子相等；不能把完整路径相等作为输入。 |
| 原路径 TV 精确传回 | 用有限 `L_n`、两个历史注入和共同 `Option L_n` 实例化 (6)，得到 (12)。 |
| 原行与原预算 | 用有限源行的 (1) 得到 (13)；调用现有 `coverage_same_policy_path_error`／`coverage_same_policy_certified_path_error`，改写路径、行和占据的精确等式，得到 (14)、(15)。 |
| 原事件风险 | `MicroscopicFailureRisk.risk_microscopic_event_le_envelope` 与 `FiniteHorizonRisk.risk_event_transfer` 已无 `[Fintype Y]`；给出原 F 的可测性，直接得到 (16)。 |

前述公开声明位于 `formalization/ueot-core/UEOT/V3/TotalVariation.lean`、`PathError.lean` 以及 `Compression/TheoryCompletion/UnifiedClosure/` 下对应文件。第一版完成前，不应把生产 `RegisteredDeploymentRisk`、`VariableRegisteredJoint` 或支持生存层更宽的观察类型范围标为已经全部统一。

## 10. 结论范围

本次实质数学进展是 (1) 的反向事件证明及 (6)、(11)、(12) 的完整路径衔接。对于当前有限 X、A 的模型，完整 range q 的有限性已由输入保证；参考 Q 可任意向该像外泄漏，所有泄漏质量被保留。有限吸收参考的用途是调用已有有限字母表证明，而最终界仍关于原始参考与实际源。

剩余工作是把这些已给出的结构等式和 PMF 归纳落实到 Lean 并完成必要验证。本节不声称已有生产 API 去掉 `[Fintype Y]`，也不把有限时域路径界解释为无限时域存活或零实际失败风险。
