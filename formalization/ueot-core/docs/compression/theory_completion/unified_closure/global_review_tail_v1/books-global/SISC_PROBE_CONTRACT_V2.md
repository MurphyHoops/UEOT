# SISC 逐探针真实采样合同 V2：明确接回现有 N3/N4/N6

日期：2026-10-21。状态：**修订后的数学与 API 合同；新增适配尚未实现、未编译。**

本文件仅替代 `NEXT_TASKS_AND_PASSAGES.md` 的 **§2 数学草案**，不修改该冻结文件，不改变其中其它书稿建议，也不改两部著作、生产源码或旧审查收据。原文件 SHA256 为 `c669bec1b01c946eabe55c901158a5c00d8f33744649e4800481f20864f09b53`。V1 独立窄审指出的三项实际 API 绑定——核均值与区间字段、N3 非空观察、N6 完整竞争量词——在此显式补齐。当前 V2 的独立审查由审查者另写，不在本文预称 CLEAR。

## 1. 要增加的接口，以及保留的责任

目标是为“不同注册探针使用不同样本组、各组训练前固定 N_j”的真实实验提供适配，复用已经成熟的均值集中、N3 候选解析、N4 校准/功效和 N6 审计候选集合。

既有 `SISCInterventionSamplingPower` 使用 `sample : Fin N → Ω → Z` 与 `outcome : Probe → Z → ℝ`，每个独立单位须合法提供全部探针的联合记录。新适配不要求一个单位同时提供其它处理的反事实结果。但它**不会自动建立**不同实验律与同一源模型的联系：N3 的单一 `kernel/source/action/read` 均值匹配、N6 的真实干预均值与候选响应匹配，以及外部认证的物质/程序转移仍须有独立来源。

新合同分成三个端点族：

1. 固定逐探针样本的共同均值 Good 事件；允许探针集为空。
2. 将该 Good 明确接到现有 N3/N4 协议；要求非空探针，并保持同一实际核、来源、动作、读出与预测。
3. 将该 Good 接到现有 N6 的确定性审计端点；保留 `LocalResponseGap` 对整个亲本类型的竞争量词。

N3 的风险匹配与 N6 的亲本响应匹配是两个分别陈述的合同，不能因都使用一个均值向量就省略其中任何一个。

## 2. 真实实验与标量均值预算

### 2.1 固定数据与量词

先给有限探针集 J、有限样本值域 X，X 的可测结构及单点可测性。给定同一个概率空间 `(Ω, μ)`，训练前固定：

- `ν : J → PMF X`，每个探针自己的真实样本律；
- `N : J → ℕ` 及 `hN : ∀ j, 0 < N j`；
- `g : J → X → ℝ`，逐探针可测并满足 `0 ≤ g j x ≤ 1`；
- `sample : ∀ j, Fin (N j) → Ω → X`；
- `hmeas : ∀ j k, Measurable (sample j k)`；
- `hindep : ∀ j, iIndepFun (sample j) μ`；
- `hlaw : ∀ j k, μ.map (sample j k) = (ν j).toMeasure`；
- 一个固定容差 `u : ℝ`，`hu : 0 ≤ u`。

这里 N、u、ν 和读数协议都不依训练记录 ω 改变。跨行独立不是后述并合界的假设；行内独立与真实边缘必须在同一个 μ 上成立。若 J 为空，这组量词仍合法。

为了给出一个实际构造而非只有形式假设，可直接实例化现有 `VariableRegisteredSamples.productRowLaw ν N`，其样本空间为

\[
\Omega_{\rm prod}=(\Sigma j:J,\operatorname{Fin}(N_j))\to X.
\]

使用现有 `productRowSample` 和其可测性、真实边缘、行内独立定理，逐项导出上述采样条件。这一具体乘积实验实际上具有跨行独立；一般定理无需要求它。不同 j 的坐标属于不同实验单位，不是同一单位的潜在结果向量。

### 2.2 精确 Good 与预算来源

沿用已有 `BoundedLossSampling` 的定义：

\[
m_j:=\operatorname{trueRisk}((\nu_j).\operatorname{toMeasure},g_j),\qquad
\widehat m_j(\omega):=
\operatorname{empiricalRisk}(g_j,\operatorname{sample}_j,\omega).
\]

定义

\[
G:=\{\omega:\forall j:J,\ |\widehat m_j(\omega)-m_j|\le u\},
\qquad
\alpha_N:=\sum_{j:J}2\exp(-2(N_j:\mathbb R)u^2).
\]

目标证明 G 可测，并由逐行调用

`UEOT.V3.BoundedLossTwoSided.measure_empiricalRisk_bad_le`

得到

\[
\mu^{\rm real}\{\omega:u<|\widehat m_j(\omega)-m_j|\}
\le 2e^{-2N_ju^2}.
\]

随后只对 j 并合，再用 μ 为概率测度，推出

\[
\mu^{\rm real}(G^c)\le\min(1,\alpha_N).
\]

**这个 α_N 是标量均值预算。** 它不来自 `VariableRegisteredSamples.confidenceBudget` 或 `registered_row_calibration` 的完整 PMF–TV 估计；后两者包含 `|Finset X|` 因子。本接口复用该模块的真实乘积实验与坐标定理，统计部分则逐 j 复用标量均值集中后重新作有限并合。现有 `measure_exists_candidate_bad_le` 的共同 N 形状也不能直接改名为任意 N_j 的定理。

J 为空时，G 为全空间、α_N=0，纯均值结论成立。这一边界不能用于绕过下一节 N3 的非空字段。

## 3. N3/N4：把均值和估计区间接到同一个实际协议

### 3.1 输入的现有协议与独立均值匹配

给实际已有类型

```lean
P : RegisteredCausalCandidateProtocol X A C J
```

其中 `[Fintype X] [Fintype J]`，调用候选解析时有 `[DecidableEq C]`。N3 只需要 `P.registered : Finset C`；不要求把整个 C 人为限制为有限。该结构已有

```lean
P.observed_nonempty : Nonempty J
```

因此**消费 N3/N4 的这一分支要求 Nonempty J**，从 P 的字段取得；不能用空 J 构造该协议。

在第2节选择 `g j y := P.read y j`，并提供这些读数的可测性及 `[0,1]` 界。均值仍由实际行律 ν_j 给出。另要求独立模型匹配：

```lean
hMean : ∀ j : J,
  m j = ∑ y : X,
    P.kernel.mass P.source P.action y * P.read y j
```

候选参考响应不是自由选择的另一张表，而是**定义**

\[
R_c(j):=P.\operatorname{prediction}(c,j).
\]

这里不能把任意不同处理下的 ν_j 自动看作同一个 `P.source/P.action` 的核行。若实验改变了处理，必须真实证明所测均值仍等于本节声明的核坐标，或另建一个有明确实际语义的协议；没有这种适配就不能消费 N3。尤其不能为了凑齐类型，虚构一个未经说明、把同一单位所有反事实结果装进去的联合核。

一个可行的受限来源是：每组都独立重复同一实际动作实验，只在该组读出坐标 j；其真实微状态律已经与 P 的核行匹配。此时各组样本量可以不同，且每单位只需实际读出一个坐标。这个例子说明合同并非要求所有处理共享同一单位的联合记录；它不消去实际核匹配的证明责任。

### 3.2 目标风险身份由定义与 hMean 推出

定义

\[
L(c):=\sum_j|m_j-P.\operatorname{prediction}(c,j)|,
\quad
\widehat L_\omega(c):=\sum_j|\widehat m_j(\omega)-P.\operatorname{prediction}(c,j)|,
\quad r:=(|J|:\mathbb R)u.
\]

由逐项使用 hMean、展开现有 `registeredCandidateRisk`，**证明**

\[
L(c)=\operatorname{registeredCandidateRisk}(P,c).
\]

不是把该最终风险等式额外当作一个无来源假设。被保留的模型输入是逐坐标的实际均值匹配 hMean；它是本新实验尚未消去的科学来源义务。

### 3.3 新协议的 interval 必须完整构造

令 P_ω 复制 P 的全部核、来源、动作、读出、预测、注册表、因果谓词、阈值和非空字段，只替换 `interval`：

```lean
-- Contract sketch only; this adapter is not implemented/compiled.
{ P with
  interval := fun c => {
    estimate := Lhat ω c
    statisticalRadius := r
    driftRadius := 0
    statisticalRadius_nonneg := /* from card J ≥ 0 and hu */
    driftRadius_nonneg := le_refl 0
  }
}
```

此处占位只用于说明将来须构造的证明字段，不是可编译 Lean 文件或已有声明。于是按定义有：

- `(P_ω.interval c).estimate = Lhat ω c`；
- `(P_ω.interval c).statisticalRadius = r`；
- `(P_ω.interval c).driftRadius = 0`；
- `(P_ω.interval c).totalRadius = r`；
- `registeredCandidateRisk P_ω c = registeredCandidateRisk P c`；
- P_ω 的注册、因果谓词与阈值仍逐项等于 P 的对应字段。

复用 `finite_absolute_response_risk_lipschitz`，对每个 ω∈G 先得

\[
|\widehat L_\omega(c)-L(c)|
\le\sum_j|\widehat m_j(\omega)-m_j|\le r.
\]

利用刚推出的风险身份和 interval 字段，得到 **`P_ω.Calibrated`**。同一个 G 对所有候选同时有效，不再按候选个数叠加坏事件概率。这里原有 `empiricalCoordinateProtocol` 只接受共同 N 和同一组完整微状态样本；本新记录形状不同，需要上述新构造，不能声称已直接调用该旧构造完成适配。

### 3.4 精确复用 N4 间隔端点

固定正确性定理中要研究的候选 c，并假设

\[
c\in P.\operatorname{registered},\quad P.\operatorname{causal}(c),
\]

\[
\operatorname{registeredCandidateRisk}(P,c)+2r\le P.\operatorname{tolerance},
\]

\[
\forall d\in P.\operatorname{registered},\quad
P.\operatorname{causal}(d)\to d\ne c\to
P.\operatorname{tolerance}+2r<\operatorname{registeredCandidateRisk}(P,d).
\]

对 ω∈G，向现有

`registered_unique_identified_of_calibrated_margin P_ω c r`

逐项传入上述注册/因果/间隔条件、`totalRadius = r` 和新证明的 `P_ω.Calibrated`，得到

\[
\operatorname{resolveRegisteredCandidates}(P_\omega)=\operatorname{unique}(c).
\]

候选 c 不进入 P_ω 的构造或解析程序，只出现在正确性/功效命题。失败事件包含于 Gᶜ，因此目标功效界为

\[
\mu^{\rm real}\{\omega:\operatorname{resolveRegisteredCandidates}(P_\omega)
\ne\operatorname{unique}(c)\}\le\min(1,\alpha_N).
\]

三值解释继续沿用现有程序：只有“唯一 possible 且已 certified”才是 unique；空 possible 是注册模型不覆盖；其它情况 abstain。它不证明物理对象或未注册候选的无条件唯一性。

## 4. N6：逐探针样本接入来源审计

### 4.1 与 N3 分开的审计数据

给 `[Fintype C] [DecidableEq C]`、Child 类型，以及实际

```lean
audit : FiniteInterventionTransferAudit C Child J
```

固定 child 与正确性命题中的 c。使用第2节的实际行律、读数和估计均值；这里 g 不需要被默认为第3节 P.read，除非另外提供这项同一性。定义新审计值 audit_ω：保留 `registered`、`authenticatedTransfer`、`referenceResponse`；将 `observedResponse := fun _ j => mhat j ω`、`tolerance := u`。本次结论只用于所指定的 child，不从这一字段更新推出其它孩子共享同一实际实验。

要求以下独立输入：

```lean
hreg : c ∈ audit.registered
htransfer : audit.authenticatedTransfer c child
hModel : ∀ j : J, m j = audit.referenceResponse c j
hgap : LocalResponseGap audit.referenceResponse u c
```

其中最后一项的**完整定义**为

\[
\boxed{\forall d:C,\ d\ne c\ \Rightarrow\
\exists j:J,\ 2u<|\operatorname{referenceResponse}(c,j)
-\operatorname{referenceResponse}(d,j)|.}
\]

它量化整个 C，而非只量化 `registered` 中或已有 `authenticatedTransfer` 的竞争者。N3 的注册且因果竞争量词与 N6 的这一量词不同，不能相互替换。

### 4.2 精确复用确定性 N6 端点

由 ω∈G 与 hModel 得

\[
\forall j,\ |\widehat m_j(\omega)-\operatorname{referenceResponse}(c,j)|\le u,
\]

这正是新审计的 `FormedByResponse`。然后调用现有

`audited_source_candidates_eq_singleton_of_gap audit_ω child c`

并传入 hreg、htransfer、该拟合证明和完整 hgap，得

\[
\operatorname{auditedSourceCandidates}(audit_\omega,child)=\{c\}.
\]

失败事件同样包含于 Gᶜ，故其真实概率不超过 min(1,α_N)。这里复用的是现有**确定性**审计端点；旧的 `sampledInterventionAudit` 和 `measure_failure_to_identify_interventional_parent_le` 接口仍具有共同 N／每单位全探针记录形状，不能直接声称它们已支持新逐组实验。

如将来只要求

\[
\forall d\in audit.\operatorname{registered},\quad
audit.\operatorname{authenticatedTransfer}(d,child)\to d\ne c\to
\exists j,\ 2u<|audit.\operatorname{referenceResponse}(c,j)
-audit.\operatorname{referenceResponse}(d,j)|,
\]

需要**另证新的局部竞争者引理**。这个弱条件不会逻辑上给出当前 `LocalResponseGap`，本 V2 不把它列为已经可直接复用的 API。

纯 N6 审计结构没有 N3 的 `observed_nonempty` 字段。J 为空时，全竞争者 gap 只有在不存在其它 d≠c 时才可能成立；保留这个退化范围即可，不把它拿来构造缺少非空字段的 N3 协议。

## 5. 必要边界与最少实现路线

### 5.1 三个不能删掉的条件

**均值匹配不可省。** 取 X={0,1}、J为单点，P 的实际声明核恒转移到1，读数为状态值，候选预测为0。若另一组数据却来自 δ₀，则 m=0、样本均值恒0，而旧 `registeredCandidateRisk` 为1。小半径围绕0的区间并未校准旧目标。均值集中完全不能修复错误的源模型。这个书面例只说明 hMean 的必要性，不是新的已编译见证。

**非空与 gap 量词有实质差别。** 空 J 的纯均值和为0不满足 N3 的构造接口。另取一个与 c 响应完全相同、但未注册的 d；它可能不影响当前审计候选集合唯一，却仍使现有全类型 `LocalResponseGap` 不成立。要利用这种更弱情形，必须证明新引理，不能把它暗传入旧接口。

**来源和身份不由拟合制造。** hMean／hModel、实际干预忠实性、`authenticatedTransfer` 及转移到 P8 genealogy 的外部 soundness 都保留。若要推 OffspringOf，还要提供它要求的不同身份；唯一模型标签不是 SameObject。

### 5.2 最少待实现端点

1. 固定行数的标量 Good 可测性与 α_N 界，直接消费既有标量集中。
2. N3 的逐行估计协议构造、风险身份和 Good 上 `Calibrated`；再用既有间隔功效。
3. N6 的逐行审计构造、Good 上拟合和全类型 gap 下 singleton；再由事件包含给失败概率。
4. 用既有 productRowLaw／sample 定理构造真实有限实验，实例化前三项；选择一个源匹配可被明确证明的非空模型及一个不匹配反例。

不重新证明 Hoeffding，不扩大到随机停止 N_j，不把源模型匹配放到样本拟合之后决定，不把平均绝对损失 E|Y−R| 当成绝对均值差 |EY−R|。若后续接注册部署风险，还必须对实际未来条件核、策略及事件另做同源证明。

## 6. 实际源码映射

下表将“已存在可复用内容”和“新适配仍需完成之处”分开。全文没有新增 Lean 声明，源文件哈希只是绑定本合同实际读取的 API，不表示又做了一次生产编译或独立证明审计。

| 现有源文件/端点 | 此合同准确复用 | 不冒称已完成的部分 |
|---|---|---|
| `BoundedLossTwoSided.measure_empiricalRisk_bad_le` | 每行固定 N_j、实际边缘和行内 IID 的标量均值双侧界 | 不直接给逐行 N_j 的共同 Good；有限并合适配须写 |
| `VariableRegisteredSamples.productRowLaw`、`productRowSample`、三个坐标定理 | 实际乘积实验、可测坐标、边缘、行内独立 | 不使用 TV `confidenceBudget` 代替标量 α_N |
| `RegisteredCausalCandidateProtocol`、`registeredCandidateRisk`、`Calibrated`、`resolveRegisteredCandidates` | P 的实际核/来源/动作/读出/预测、非空观察字段和三值程序 | 不把自由均值风险当作旧核风险；不消去 hMean |
| `C2IntervalDecision.IntervalCertificate`、`totalRadius` | estimate=Lhat、statisticalRadius=r、driftRadius=0及非负证明 | 没有额外漂移或随机半径推广 |
| `SISCMeanResponseCalibration.finite_absolute_response_risk_lipschitz` | 向量均值误差控制全部候选 L1 风险 | 旧 empiricalCoordinateProtocol 的样本形状不自动变成逐组样本 |
| `SISCSeparationPower.registered_unique_identified_of_calibrated_margin` | 注册且 causal 竞争者、正确的内外2r间隔、完整区间校准 | 新 P_ω 字段与旧风险身份须先证明 |
| `SISCFormationIdentityBridge.LocalResponseGap`、`unique_formed_target_of_local_gap` | 对所有 d:C,d≠c 的响应分离量词 | 限 registered/authenticated 的弱条件需新引理 |
| `SISCInterventionTransferAudit.audited_source_candidates_eq_singleton_of_gap` | 真实注册、认证转移、拟合和全类型 gap 的确定性 singleton | 不由响应或集中产生认证转移 |
| `SISCInterventionSamplingPower` | 对照其现有联合记录假设，保留其成熟结果 | 不将旧共同 N、全探针记录功效定理改名为新接口 |

### 6.1 源文件身份

以下身份在 V2 冻结前由实际文件计算；路径均为本次使用的已出版工作树生产源码副本。

| 源文件 | 字节数 | SHA256 |
|---|---:|---|
| [BoundedLossTwoSided.lean](sandbox:/workspace/scratch/9a8d58b21e30/ueot-books-publication/formalization/ueot-core/UEOT/V3/BoundedLossTwoSided.lean) | 7947 | `38b0d02c99b2aeeb22074b55fef0b36a5d7e7b9131da3f0b53a651d43e05cc30` |
| [VariableRegisteredSamples.lean](sandbox:/workspace/scratch/9a8d58b21e30/ueot-books-publication/formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/VariableRegisteredSamples.lean) | 5916 | `98972b20af6a18004c428c0905d571922296be8d79695b7201d6518b8e111ee5` |
| [SISCRegisteredCausalCandidates.lean](sandbox:/workspace/scratch/9a8d58b21e30/ueot-books-publication/formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/ScientificClosure/SISCRegisteredCausalCandidates.lean) | 13814 | `60c4e4dd3bf20b066a94d6cfa00ff2b7fb98ca113da6aa788d167c16980aa0e0` |
| [C2IntervalDecision.lean](sandbox:/workspace/scratch/9a8d58b21e30/ueot-books-publication/formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/ScientificClosure/C2IntervalDecision.lean) | 4300 | `08c790579c21bc982c5d5d8c8c0fe67516775241f1de93e42f5d7480bc08944f` |
| [SISCMeanResponseCalibration.lean](sandbox:/workspace/scratch/9a8d58b21e30/ueot-books-publication/formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/ScientificClosure/SISCMeanResponseCalibration.lean) | 15432 | `5d1565737e0b792a48dbdcf62c1f7ddebe22a21c089d2ddbe81e616697b0c013` |
| [SISCSeparationPower.lean](sandbox:/workspace/scratch/9a8d58b21e30/ueot-books-publication/formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/ScientificClosure/SISCSeparationPower.lean) | 8873 | `d2c03d3cd1e28fbb557d7c150834e591df118009ded24a7d83155f73977c77d7` |
| [SISCFormationIdentityBridge.lean](sandbox:/workspace/scratch/9a8d58b21e30/ueot-books-publication/formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/ScientificClosure/SISCFormationIdentityBridge.lean) | 4982 | `11baaf55f146ff11e9ab176cb0e4d3400ca162ab39f3115c0bb07b463d35b329` |
| [SISCInterventionTransferAudit.lean](sandbox:/workspace/scratch/9a8d58b21e30/ueot-books-publication/formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/ScientificClosure/SISCInterventionTransferAudit.lean) | 7884 | `618d78fb36c181575ac7aaf299b3d685616e37aa0925bd188ed7c9dde74825cc` |
| [SISCInterventionSamplingPower.lean](sandbox:/workspace/scratch/9a8d58b21e30/ueot-books-publication/formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/ScientificClosure/SISCInterventionSamplingPower.lean) | 7105 | `efc218467f52fa25f97dfa7cde0bf04b2602c53b9cd7472c29adf32a3d8dd714` |
