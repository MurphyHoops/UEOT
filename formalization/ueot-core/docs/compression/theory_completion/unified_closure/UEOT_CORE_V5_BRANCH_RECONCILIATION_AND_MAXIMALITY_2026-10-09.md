# UEOT Core V5：分支取证整理、最粗组织表征与最大微观存续闭环（2026-10-09）

## 1. 任务边界

- 当前本地分支：compression/theory-completion-unified-local。冻结 main：6fa4c39d2a41f1563ba75c277b7112b61b2799db。
- 不改原始 Core 106/106、Compression 四 counted generators、Theory Completion P0–P12 历史合同和 P12 PARTIAL / EXPLICIT BOUNDARY。
- 本轮判定：FINITE_OPERATIONAL_CORE_BRIDGE=PROVED；UEOT_FULL_MATHEMATICAL_CLOSURE=NOT_ESTABLISHED；EXTERNAL_PHYSICAL_VALIDATION=UNVERIFIED。
- 不进行 GitHub push / PR，不删除或重置旧分支、工作树、untracked 文件，不重写已有分割、概率、控制或不动点算法。

## 2. 先审查现有定理，避免重复造轮子

精确阅读并实际引用：
1. FiniteStablePartition / Termination / CoarsestFixedPoint / QuotientLaw / Normalization / FiniteHorizon，已有有限算法、最粗性及保真。
2. PAlg01.p_alg_01，已有一体化冻结算法公开定理。
3. SISCModelKernelReconciliation.model_strongLumpability_iff_stable，已有同一核在 Setoid 与可达商的类型桥。
4. FiniteDiscountedExactQuotient.p_quo_01、ExactControlQuotient.optimalValue_apply，已有价值保持及全部因果随机策略最优。
5. UMC ViabilityKernelIntertwining，已有微宏可行性等价、有限不动点、最大受控不变安全域及微观有限正概率路径保持。
6. 已有 CrossTrack.EndogenousCandidateFormation / EndogenousConstitutivePersistence 以及 P12 AutopoiesisClosure，远强于简单布尔资源标签；不可重新发明或用 V5 替代。

先前本地提交 96eb4495 已把 1–5 项接到同一个源 M，新增三份编译通过的 assembly/certificate/witness 文件；4b4a4eca 已对 106 个 canonical P-ID 的实际 Lean 声明作 #check + #print axioms 全量审计，106/106 elaborated，0 个自定义公理依赖。两项任务不能冒充 106 条自然语言语义逐一等价审核。

## 3. 本轮真正新增的源侧最大性桥

模块：UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/OrganizationalViabilityMaximality.lean。

对每一个有限 X、有限非空共享行动 A、正规受控状态核 M、注册输出 O、有限奖励界和 0<β<1：

- 直接调用已有 terminalSetoid M；证明它仍是保留原始输出和全动作奖励的**最粗**稳定表示。
- 直接构造已有 organizationalTerminalControl，从 M 的同一 transition 与 reward 导出真 ExactControlQuotient Q，无手工外加宏核。
- 把原始输出的安全谓词 safe : O → Prop 经冻结 quotientOutput 搬运到商状态 good。
- 考虑**任意**微观子集 region : X → Prop，不要求 region 为商的纤维饱和。
- 若 region ⊆ safe ∘ M.output，且对每个在 region 内的微态都有某动作使全部外部微态转移质量为零，则证明：

  对所有 n 和 x，region x → microViable Q good n x。

  关键是 action 可以因原始微态而异，并且微观转移**定义上就是 M.transition**；不在 premises 中要求 region 已降到宏观。

- 由已有 V4 有限不动点，存在 n ≤ |ReachableState q|，可得 microViable Q good n x ↔ macroViable Q good n (Q.f x)。
- 对任意候选 source-controlled-invariant region，必被该最大微观可行核包含；对最大核内每个微态，存在**实际原始微核动作**零概率离开宏观最大核。
- 因而这是**最粗精确组织表征**与**最大受控安全域**通过相同微核接合的形式化结果，而不只是把两个互不相干的存在命题装进一个结构。

两个新公共 Lean 定理：
- source_invariant_enters_every_terminal_viability_horizon
- terminal_organizational_quotient_maximal_micro_viability

## 4. 同源可压缩与不可压缩的非空证据

复用前一阶段同一个 survivalMicroKernel：4 个微态、2 个真实行动、下一微态仍有 1/2 概率隐态随机性。
- 可见输出和安全位受保护而隐藏位未受保护时，coarsest partition 允许两个隐藏态合并。
- 将同一个隐藏位登记为必须保护的程序状态，原先两个隐藏态不得合并。
- 持续域非空，而且选错误动作确实可破坏生存条件。
- 这些结果不证明程序状态的历史因果来源，也不意味着完整 Ω-loop 自创生。

## 5. 其他本地分支的处理

机器索引：UMC_LOCAL_BRANCH_INVENTORY_2026-10-09.json。
人工说明：UMC_LOCAL_BRANCH_RECONCILIATION_2026-10-09.md。
可重复脚本：audit_local_branch_inventory.py。

取证结果：
- 本地 83 branches，61 已成为 main 的祖先；1 为本轮活动研究；21 有图上独有历史提交。
- 共 25 worktrees，其中 24 detached review 快照；所有 worktree 已跟踪文件均无待提交修改。但许多有 untracked 文件，不得直接清理。
- 图上独有 ≠ Lean 证明未并入。扫描当前 UEOT 首方声明名后，21 个历史分支中仅 1 个历史声明名在当前代码中不存在：
  backup/p7-p12-pre-stack-rewrite 中 objectScaleMap_does_not_determine_wilsonian_flow；
  current main 收窄为 wilsonianCouplingFlow_nontrivial_of_twoCouplings，避免断言未建立的物理解释兼容性，所以**不恢复旧的强命名/解释**。
- backup/endogenous-object-pre-main-rebase 已包含在 main 的后续强化版本中：当前证明了坏控制器不会自动修复、全时轨迹安全以及非空构成持续证书；旧备份不 cherry-pick。
- formal/pctl03、formal/pkl04、formal/pkl05、formal/pqsd04 和旧 Compression 支线的核心 Lean 声明已在现有全库可找到，但未据此宣称每个旧文件正文与当前等价；旧根导入/账本不覆盖新主线。
- local/post-reflection-scientific-audit 保留一份没有直接进入 main 的历史积分报告，其 ref 和 SHA 保存在清单，属于取证资料，不是新定理。
- 本轮没有确认任何应整体合并的旧分支，均原样保留供审计和复核；这避免破坏已完成治理与科研成果。

## 6. 复现验证

- 单模块 lake env lean OrganizationalViabilityMaximality.lean => PASS。
- 将新模块加入 TheoryCompletion.lean 入口，lake build UEOT => Build completed successfully (9330 jobs)。
- 新增两定理 #print axioms：仅 Lean 标准 propext、Classical.choice、Quot.sound，未引入自定义 axioms。
- 新源无 sorry/admit/axiom/opaque/native_decide。
- validate_unified_closure.py => UNIFIED_CLOSURE_GOVERNANCE_PASS，9 gates / 106 sources / 4 generators / 7 stages。
- test_validate_unified_closure.py => UNIFIED_CLOSURE_NEGATIVE_CONTROLS_PASS，12/12 不合法治理变异被拒绝。
- git diff --check => PASS。

## 7. 下一条真正的科学缺口

当前“组织”数据仍是注册的当前态 output。一个完整 UEOT 对象的内部自生产／资源来源／损坏后修复／目的内生生成属于更强的**历史因果与构成结构**。

优先重用 current main 已有 EndogenousConstitutivePersistence 与 P12 的假设与 no-go，而非再创一套自生概念；在同一状态历史和真实转移核上构造程序与资源生产事件，再证明存续和对象身份可与这些事件同源联结。要特别避免把把“controller 嵌入状态并保持不变”直接解释为“controller 损坏后会自修复”。若仍缺实际资源生产或真实目标来源，则明确列为未完成数学/科学门。

**最终判定：本轮取得新的有限层数学接合与工作流整合证据；整体 UEOT 理论闭环仍未完成，不允许标为 FULL。**
