# 独立理论与实现审查：有限条件量子链条

审查者：`/root/core_physics_bridge`。日期：2026-11-11。只读审查他人模块；本文未修改 `QuantumFiniteWindow.lean`、`QuantumFiniteWindowSpectral.lean` 或 `CHAPTER_66.md`。

## 审查结论

**未发现有限原仪器→谱支撑工厂→完整条件叶记录/量子联合态的数学阻塞。** 原来源、原成功率、奇异核消去和隐藏 Kraus 指标均有真实实现，未见将所求条件律作为输入字段的循环。书面实现、成本和误差推导在声明的有限复量子、固定原树和允许操作类内成立。

可进入最终集成核验，但发布时必须保持下列证明层次和量词边界。本文的“通过”是数学与源码审查；Lean 编译成功以主代理实际回执为准，本审查者没有独立执行 Mac 编译。

## 1. 审查快照与来源身份

初次完整审读时的文件 SHA-256（后续必要补充会改变文件身份，最终应重新取统一集成快照）：

| 文件 | 审读快照 SHA-256 |
|---|---|
| `QuantumFiniteWindow.lean` | `9f661d832f434c0744efb6f5ecfeb236f1947e998ac01eb216c31ec555c5aec0` |
| `QuantumFiniteWindowSpectral.lean` | `aa0f7841377455932e4c4cc2ad42a2804a1715e56c78093b20c01bb4e207b102` |
| `CHAPTER_66.md` | `a07e0ac1cef93771a6e7125678a2b787455f0b1dd50574fd8402a67a7eb78140` |

另审读了动作、后选择误差与成本候选的接口。`sourceWeights`、`sourceWeights_accepted_sum` 新适配已确认加入；成本模块已直接消费它们，并消费 `metric_complement_posSemidef` 构造原树初始完整滤波器。其最新版本仍需纳入主代理最终编译回执。

## 2. 原来源工厂是否真实

### 2.1 原始输入没有夹带结论

`QuantumFiniteWindowSpectral.SourceTree` 只有两类节点：

- `stop accept`：原接受/拒绝决定。
- `node source next`：实际完整源仪器与可见结果后的子树。

没有输入成功率 p、后向 H、变换后的仪器、条件记录等式或可实现性证书。`SourceTree.canonical` 先递归构造子树，再由 `backwardGram I G` 计算父节点的 PSD 矩阵，最后调用 `spectralFilter`。这是实际原仪器的后向构造，不是把独立给定目标改名成同源目标。

`canonical_valid` 通过 `spectralFilter_metric` 和 `StepCertificate.of_backward` 证明局部证书成立。`canonical_erases_to_source` 逐节点证明擦除新数学证书后完全返回原 `SourceTree`；源仪器、分支和接受标志都保留。

### 2.2 谱存在性不再留作悬空假设

`spectralFilter` 从有限 Hermitian 谱定理得到 U 与实特征值 λ_i，明确构造：

\[
S=U\operatorname{diag}(\sqrt{\lambda_i})U^\dagger,
\quad T=U\operatorname{diag}((\sqrt{\lambda_i})^{-1})U^\dagger,
\quad P=U\operatorname{diag}(1_{\sqrt{\lambda_i}\ne0})U^\dagger.
\]

实数零逆为零，正好给核上的零延拓。代码证明 TS=ST=P、P 自伴幂等、PS=S，及 S≥0、S†S=H。没有偷偷假设 H 正定，也没有用浮点阈值替代真实零谱。

这是非可计算的存在构造，不是数值特征分解程序的可靠性证书。主章 §66.3、§66.13 已正确区分两者。

### 2.3 奇异核消去由原数据导出

`SupportFilter.matrix_projection` 从代数支撑关系推出 SP=S。`support_of_backward` 对

\[
A_{o,k}=S_oK_{o,k}(I-P)
\]

证明 ΣA†A=0，然后 `gram_sum_zero_component` 使用每项 Gram 的非负迹和零迹判据，导出每个 A=0。故 `StepCertificate.of_backward` 的 `support` 字段是定理的结果，不再是要求使用者独立相信的物理约束。

这一点直接支撑主章 P-FCOND-02；未发现奇异逆的非法消去。

## 3. 完整仪器、可见记录和原成功率

### 3.1 实际完整仪器

`tiltedKraus` 的隐藏索引是 κ⊕ξ；可见结果仍为 O。主 Gram 和为 P，补全 Gram 和为 I−P，所以 `tiltedInstrument.complete` 真正证明了完整性。`tilted_branch_transport` 在每个原可见 o 上对所有复矩阵 X 证明：

\[
\widetilde I_o(SXS^\dagger)=S_oI_o(X)S_o^\dagger.
\]

这是算符等式，强于只验证迹或单一初态；隐藏 Kraus 求和发生在分支内。

### 3.2 叶类型是真实原可见记录

`FilterTree.Leaf` 在节点为依赖和 `(o : O) × next(o).Leaf`，没有 κ、ξ 或 Kraus 直和标签。`sourceWord_injective` 证明每个叶的完整可见动作/结果词可区分；`sourceLeafOperator_eq_recordOperator` 将新解释器直接连接至原有 `recordOperator`。

同一预先给定的树根据可见历史决定动作，故叶标签保留原记录及停止深度。若将来要把独立于仪器矩阵值的外部动作名称也作为原始输入数据，应显式携带名称或声明叶到该名称序列的解码；当前固定树合同不会因此丢失可见结果或路径身份。

### 3.3 p 来自原叶质量

`successMass P X` 定义为原 `acceptedLeafOperator` 的质量总和。`acceptedLeafOperator` 只在原 `accepts` 标志为真时保留原 `sourceLeafOperator`，拒绝块为零。`successMass_eq_filtered_mass` 随后证明它等于 `mass(rootFilter.apply X)`；它不是 p 的定义，更不是外加谱参数。

`sum_sourceLeafOperator_trace` 证明原完整实验的全部叶迹和等于输入迹。`successMass_le_one` 对密度输入证明 p≤1；`metric_complement_posSemidef` 由原完整性及子节点补效应正性证明 I−H≥0。故主章 P-FCOND-01 的成功概率及 effect 边界都有源码依据。

### 3.4 完整条件 CQ 联合态

`leaf_transport` 从局部分支运输进行有限树归纳；到接受叶为恒等，到拒绝叶为零。`conditional_leaf` 只在根处归一化一次，并使用**原 successMass**。`jointState` 的 PSD 与 trace-one 由实际变换仪器的叶解释器推出；`conditional_joint` 保留叶与终端量子系统的每个块，不只保留概率或系统边缘。

`zero_success_all_accepted_blocks_zero` 证明零事件的所有原接受块为零；`initialState` 需要严格正概率证明，未对 p=0 注入任意备用密度。

## 4. 需要明确的形式范围

这些是证据登记边界，不是当前书面定理的反例。

1. **固定全树 fallback J 与逐节点 J_h。** 当前 `tiltedLeafOperator J` 和 `fallback_independent J J'` 形式端点在每棵树内复用同一个 J。主章允许每节点单独选择 J_h，其书面证明正确：每个节点的补项都在对应可达支撑上消失，逐层归纳不使用 J 相同。但不要把当前命名 Lean 定理的类型扩大成已覆盖任意节点依赖 fallback 的函数量词。可明确“Lean 给固定 J 的通用实现；逐节点任意选择的补全无关由同一局部证明作书面归纳”。

2. **共同有限载体。** 形式树使用同一 ι、O、κ，且每个类型有限。零填充可以处理有限树中不等长 Kraus 列表；更换 Hilbert 维数、无限输出、量子控制或无界停止不在这些类型的直接量词内。主章目前限定有限固定复 Hilbert 空间和经典控制树，范围相容。

3. **支撑动作匹配到全树实际执行。** 动作模块已经证明真正的复线性 Choi 注入、实际 Kraus 随机化、全空间/支撑/观察纤维 iff。将每节点通过判据的实际混合替换进条件树，因目标到达态在相应支撑上，逐层归纳给同一完整 CQ 输出。这一组装证明数学上直接成立；若没有另一个“混合后的整个树”Lean 解释器及命名定理，不应宣称已有一个单一 Lean 端点同时量化原树、动作库、观察函数、策略以及整树输出等式。

4. **条件输出误差的接受器组装。** `QuantumPostselectionError.posterior_effectDistance_le_div_max` 已给任一实际同一接受仪器的锐界。将满载体原 CQ 输出与对原接受叶的投影仪器作为输入，就得到主章结果；不必删去拒绝坐标。若未另建专门 CQ 接受投影适配器，这一实例化属于书面组装，不影响通用后选择定理本身。

5. **无限重试概率空间。** 成本模块直接从原叶 `sourceWeights` 得有限重试树递推、闭式和极限；非负成本下把极限识别为无限独立重试的总期望，仍是书面概率论步骤。模块没有谎称已构造无限产品源或形式化其独立性。资源重置条件必须保留。

建议在最终台账将“已编译的一般端点”“书面组装”“精确有限实例”“浮点诊断”分栏，而不是用同一个 completed 标志掩盖上述差别。

## 5. 实现、初始化与资源主张审查

### 5.1 允许动作与观察权限

主章 P-FCOND-05 正确保留可见结果 Choi 块，并在整条观察纤维内使用共同权重。全空间指定补全、全支撑任务、固定初态/仅末端任务分开，未把某一任意补全的不可实现误报为一切补全的不可实现。

新增 `QuantumReachableActionRealizability` 已为指定可达输入的逐分支输出另给凸包 iff；这仍不等于只检查最终输出的全局必要条件。主章可以在第三行任务表标注已存在这个较弱的局部判据，而保持对 terminal-only 任务的边界。

### 5.2 未知态初始化分类

P-FCOND-07 的系统边缘分类正确：H非零PSD时，规范归一滤波能由同一确定 CPTP 通道在所有正概率输入上实现，当且仅当 H=cI 或 rank(H)=1。两个不同正特征值、以及 cP 的非满支撑 rank≥2 情形，主章的仿射反例覆盖完整。

参考联合态的否定必须按“局部 Φ⊗id_R”理解；证明已经使用局部确定操作保持参考边缘。rank1 replacement 不会自动复现输入依赖的成功标志或成功率。建议术语写“半正定矩阵”以避免“正矩阵”被误读为正定而与 rank1 例外冲突。

**已修正的审查问题：** 本审查者自己的证明附件此前 rank1 参考条件公式漏 λ；若 H=λ|u><u| 且 p=Tr(Hρ)，正确分子为 λ〈u|ρ_AR|u〉。已修正 `ACTION_INITIALIZATION_COST_PROOF.md`。主章只有不变性论证，没有这个漏因子公式，未受影响。

### 5.3 过滤尺度与成本

P-FCOND-08 的 p/c、c/p 及后验尺度无关正确，且仅对每次可以独立重准备输入成立。c=||H|| 的“最佳”限定在固定成功 Kraus 的缩放族内，也已限定得当。建议首次明确此处 ||·|| 为算子谱范数。

P-FCOND-09 的 μ/p 正确，即使本次成本与本次成功相关。成本中的复位若只在失败后支付，应在 C(R) 中用失败指示量计入，最后成功试次不另收无须执行的复位。固定最大时域不能替代真正早停成本。主章没有宣称所有驱动实现存在相同 1/p 下界，也没有从数值例推出硬件优势。

`sourceInitialFilter` 新桥从原树的 I−H≥0 构造实际 c=1 滤波器，其成功率等于同一原 `successMass`；成本的原源概率不再是一份手工独立输入。

## 6. 误差与数值主张审查

### 6.1 ε/max(p,q) 界

P-FCOND-10 的两个 effect 证明正确。对 p≥q：

\[
p(a-b)=(pa-qb)-(p-q)b,
\]

\[
p(b-a)=[p(1-a)-q(1-b)]-(p-q)(1-b).
\]

b∈[0,1] 同时给正负方向；交换两态得到最大分母。相同接受器、p,q>0、完整原输出误差前提都没有省略。给出的三结果经典例在 0≤δ≤p≤1 时确实达到 δ/p，因而证明这个常数不可普遍改小。

### 6.2 Kraus 范数充分界

P-FCOND-11 的插入减去、Schatten-1 理想不等式、隐藏项及可见块三角估计正确；两仪器完整才能最终截于1。该界依赖配对后的 Kraus 表示，是充分界而非表示不变的最优距离。主章已经说明非最优及不把机器残差当严格上界，适当。

保持任意有限参考时，局部恒等放大的算子范数不变，所以同一个估计成立；它不覆盖未建模的系统—设备额外耦合。书面与 Lean 的范围区分也已声明。

### 6.3 根与逆根的稳定性

对 H,H'≥ηI>0，两条常数分别 1/(2√η)、1/(2η^(3/2)) 正确。令 A=√H、B=√H'，A(A−B)+(A−B)B=H−H'，Sylvester 半群积分给第一式；逆差恒等式及 ||A^{-1}||,||B^{-1}||≤η^{-1/2} 给第二式。

奇异版本应写清“在**同一个经认证的支撑子空间**上应用”；不同支撑的变化须另计投影扰动，不能在各自不同的支撑上分别获得下界后直接套相同矩阵空间的估计。当前“固定且认证支撑”可作此理解，建议明确一字。H_ε=diag(1,ε) 的反例正确。

## 7. 独立精确重算两类见证

本审查者没有调用既有 `exact_witnesses.py` 来复用其结论，而是从主章列出的矩阵重新用 SymPy 进行精确有理/代数计算。

### 7.1 非标量例

重新计算得到：

\[
\sum K^\dagger K=I,\qquad
H_0=\frac1{4096}\begin{pmatrix}183&27\\27&51\end{pmatrix},
\]

\[
p=117/4096,\quad \mu=701/512,\quad \mu/p=5608/117.
\]

最大混态上的失败概率精确为23/32。H_0的最大特征值为 `(117+3√565)/4096`，p/c化简为 `39/(39+√565)`。因此主章 §66.15 的数量、缩放和单动作库分离结论相符。

该例还确实包含不交换的 CP 超算符。令 Q=|0><0|，独立计算：

\[
K_0(K_1QK_1^\dagger)K_0^\dagger
-K_1(K_0QK_0^\dagger)K_1^\dagger
=\begin{pmatrix}0&-1/128\\-1/128&-3/256\end{pmatrix}\ne0.
\]

### 7.2 Pauli 正证书

源每次成功总概率恒为1/2，连续三次接受概率1/8，初态不变，原早停均值7/4、重试总步数14；允许公平随机 Z/X 的三步成本在明确计价中为3+3r，均正确。

**必须保留的表述修正：** XZ=−ZX 只差全局相位，故 Ad_X、Ad_Z 通道实际上交换。这个正例证明真实二维仪器与完整可见记录的实现，可保持量子相干，但不能单独作为不交换 CP 超算符的顺序见证。主代理已收到并正在修正该措辞。非标量例可承担真正的非交换测试。

## 8. 最终验收建议

最终集成应在同一源码身份下编译：原窗、谱工厂、动作 iff、指定输入 iff、实际正/负见证、物理初始滤波、原源成本适配及锐误差端点，并审计指定端点公理。与依赖的 Core 保持清晰只读 lineage。

数学论域内可以称为有限条件过程的闭环：即使动作库判断为不可实现、或完整成本比较没有优势，仍是精确结论。不能从这个闭环升级为 Core 唯一选择复量子、一般量子 Perron 极限、无界停止、场论/相对论或硬件实验的闭环。当前主章最后一节总体保留了这些范围限制。
