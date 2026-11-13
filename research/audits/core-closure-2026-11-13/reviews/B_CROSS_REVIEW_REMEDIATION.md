# B 对 A 治理整改候选的数学语义交叉审查

日期：2026-11-13。审查者：原生子智能体 B；候选作者：原生子智能体 A。固定数学源：`cb17211653fde30aa50e0e9848798a6a5b3b3f12`。

## 1. 范围与独立性

本记录独立、只读审查 A 的四个 constitution 文件、RFC 和 architect resolution，核对其数学前提、量词、类型语义、来源链接及证明状态措辞。B 没有编辑 A 候选，发现由 A 修改后再回读。这里的独立性是不同原生代理先读证据再交叉质询；不是独立人类同行评审。

本记录不把 B 自己撰写的矩阵勘误或数学证据文档列为“独立审查通过”。B 自己文档新增的 `ProgramPopulation θ` 限定来自 C 的交叉意见，其作者修正情况另列于第 5 节。源类型采用 E1 源码读审，历史编译采用 E2；本轮未执行 Lean。

**结论：A 的六份候选在已回读的最终字节上，没有遗留的数学语义阻断项。** 发现的一条错误源链接已修正；同源内部程序解释所需的初态不变式和正分支条件已明确。现有条件定理无需修改，也没有产生新 Core 证明任务。

## 2. 关键问题的独立裁决

下表是 B 直接阅读候选及已审计数学源后作出的判定，不伪称 A 在会话中逐条回答过这些问题。

| 审查问题 | A 候选的位置与表达 | 数学判定 |
|---|---|---|
| 是否用空操作 Ω 直接否定全部自再生组织？ | Constitution §Foundational Commitments 2；Glossary “Operational Omega”；Resolution §2 区分组织反馈与极小失败族，允许空族并保留有限/单调条件 | 准确。`Failure=False` 可使操作族为空，却不逻辑决定另一个组织谓词；候选没有混用 |
| 是否把定性资源/信息二分变成普遍二维因子？ | Constitution §3、Glossary “Pi/Phi Representation”、RFC §2 明列响应族、锚、因子化与适用正则条件 | 准确。与 `CommonBottleneckRank.p_ddh_04` 的条件性结论相容；没有从秩三反例否定一切定性二分，也没有声称不可微编码普遍不可能 |
| 是否把 GOA 名称当作唯一吸引子、收敛或最优证明？ | Constitution §5；Glossary “GOD/GOA”；Resolution §4 明分不变律、吸引子、周期和条件生存律，允许不唯一、不达到或不适用 | 准确。保留有限 Cesàro、不变律、额外混合等不同合同；未添加无条件长期定理 |
| 六角色是否又被包装成普遍身份互推？ | Constitution “Model Admission, Object Roles, and Shared Sources”；Glossary 表格及 RFC §3 要求共同源/解释映射，否定普遍互推 | 准确。泛型 `p_core_01` 的独立 H/I/Y、X/M、Obj 类型不能自行提供同一身体，候选正面保留了该义务 |
| `actual`、亲本记录是否被解释为现实数值同一或任意初态唯一？ | Constitution 当前 L134–140；Glossary “Identity Records and ValidIdentity”；Method “Shared-Source and Identity Discipline”；Resolution §6 | 准确。`newborn_fresh_from_old_population` 的 `ValidIdentity` 前提被保留；时间有效性不排除初态 ID 重复；未声称 State 自带全局 NoDup |
| 外部策略是否被当作身体内部程序？ | 更新后 Constitution L142–146、Glossary “Internal Program Execution”、Method 同源段、RFC §4 与 Resolution §6 | 已精确补明 `ProgramPopulation θ` 初态、可达继承不变式及正分支条件；任意 State 上的外部 policy 不提供这一内部解释。详见第 3 节 |
| 目的、选择或伦理是否由增长最优直接推出？ | Constitution §4、Glossary “Purpose and Normativity”、RFC §4 区分研究者评价、内部功能、意图与规范理由 | 准确。期望增长、个体续存、有限期限最优及规范评价没有被合并；程序/环境和评价仍可为输入 |
| `canonical` 是否又默认为 `proved`，或整改被当成新 Lean 构建？ | Constitution L31–40；Method “Evidence Discipline”；RFC §5/§7；Resolution §7/“Evidence and Review Basis” | 准确。保留当前源/既有回执身份，没有 fresh PASS，没有把哲学/治理决定计为新增形式证明 |
| 冻结数学与应用限制是否被重新登记为任务？ | Constitution “Frozen Sources and Further Research”；Method “Bounded Research and Closure”；RFC §7；Resolution 最后两节 | 准确。冻结源、106 P-ID、生产 Lean、锁依赖与回执不改；只有明确反证、消费者义务或另立目标才触发新任务 |

## 3. 实际交叉意见与已验证修正

### A-B-R1：内部程序解释应保留完整前提

触发事实：C 在 B 证据候选的交叉审查中指出该前提尚未明写，主审要求 B 处理并复核 A 的相同语义。A 询问 B，拟用“`ProgramPopulation θ` 初态和沿相关转移保持”是否准确。

B 对固定源码的直接核对：`CoreRegenerativeGrowthPopulation.lean` 的端点包含：

```lean
theorem programPolicy_positive_branch_is_internal (p : Parameters) (theta : Bool)
    (t : ℕ) (s : State) (w : Branch s) (hg : ProgramPopulation theta s.population)
    (hw : 0 < branchWeight p (programPolicy theta) t s w) :
    (next t s w).population = internalGeneration t s.population w.2
```

这是当前人口和实际正分支上的语义桥。沿时间调用它，还需初始 `ProgramPopulation θ` 及 `CoreRegenerativeControlPopulation.step_outputs_program` / `reachable_program` 提供的继承不变式。`founder_program` 为指定 founder 正例给出初始责任。它不是任意 `State`、任意编码身体或所有零权分支上的无条件内部执行结论。[E1；历史通过证据 E2]

B 回复 A：原拟句方向正确，须限定本再生人口模型，并补正分支条件。A 随后在 Constitution、Method、Glossary、RFC、Resolution 同步写入这一限制；B 已回读五处。最终措辞说“调用当前内部执行结果须保留其前提”，没有宣称这些条件是所有可能内部执行概念的必要条件。**该项已解决，不需要新 Lean。**

### A-B-R2：RFC 的人口源链接指向不存在的路径

B 的相对链接核对发现 RFC evidence 表原目标为：

```text
formalization/ueot-core/UEOT/CoreRegenerativePopulation.lean
```

固定远端 tree 中实际路径为：

```text
formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativePopulation.lean
```

B 已向 A 和主审报告。A 修改后，B 重查其准确目标及六文件全部 15 个相对链接；当前均存在于固定远端 tree 或本轮六文件集合。**该项已解决。**

## 4. 最终核对字节

下列 SHA-256 对应 B 在上述修正后回读的 A 候选。若集成时改变实质措辞，应只核对改变的段落；修改 adoption/merge 状态需要符合主审实际事件，不由本记录代替。

| A 候选 | 已读 SHA-256 |
|---|---|
| `constitution/UEOT_CANONICAL_CLAIMS.yaml` | `aa3b56b5e9078837946163ab0340f5276a3d2e78db41d1bab164b865cf343bae` |
| `constitution/UEOT_CONSTITUTION.md` | `ed3f44ab300156d450bed78f7a1c1d574c20b713ad81385bca479ede6b7a4588` |
| `constitution/UEOT_GLOSSARY.md` | `029836ff6ec5fae78d402b3b01080bae32d29dd5fb9660532a025da762b1fc76` |
| `constitution/UEOT_METHOD.md` | `15a072a722c77e565a70bad3507e7dbb27a70f94a0b31c65932d2847f2514705` |
| `council/resolutions/20261113-core-claim-scope-reconciliation.md` | `4c80196087c2f6ce5b5e9b901d2b91cb1b3e23d810e1dae45768d2d576bf4495` |
| `research/rfcs/20261113-core-claim-scope-reconciliation.md` | `ce1a3ec3ecbe48e1d7703525f6df8f9fa8c9435f2ae4073b10089bc85e303dd1` |

机器清单：同目录 `A_CROSS_REVIEW_SOURCE_MANIFEST.json`。原先抽取的清单只留历史，不用它覆盖上表最终版本。

上述六项亦与 A 随后冻结的 `FINAL_CANDIDATE_MANIFEST.json` 逐项一致；B 复查时未见冻结后语义漂移。

## 5. B 自己候选的修正，不算 B 独立验收

C 的实质意见已加入 B 的 `MATHEMATICAL_EVIDENCE_AND_CONTRIBUTION.md` §4.2 及处置表：`ProgramPopulation θ` 初态、继承、实际正分支及 founder 正例。修正后文件 SHA-256 为 `b71d4a08176fedf70cac90fdafec2548ee3acee4b89dd34d8824d9369a656264`。

该项属于作者根据 C 审查所作的修正。对 B 两个候选的独立接受仍由 C/主审根据实际回读记录决定；此处不自我签发“独立通过”。矩阵勘误仍只有 `0≤β<1` → `0<β<1`，没有改变生产 Lean。

## 6. 交付裁决

就本次交叉审查范围，可以集成 A 的六份候选。两项实际修正均已落到可复核字节；没有通过多数意见替代数学判断，没有新增不必要的假设、证明或版本升级。本意见是数学语义审查结果，不是 architect adoption、Git 合并、新内核执行、完整原创性审查或经验验证结果。

## 7. 对主审结案 README 草案的终核

另应主审要求，B 只读复核 `repo/research/audits/core-closure-2026-11-13/README.md` 的数学段落及四种闭合。已读字节 SHA-256 为 `a61cc9f236b163e76141433bafcea8bb0c1473c632ee604a61709fe31fc1bd30`；文件明确处于集成候选，未报告 main 已合并。

**未发现数学范围内的实际错误或过度升级。** 具体判断如下：

- §2 的 E1/E2 区分与 Lean/Mathlib 锁定准确；§4 的 G3/D3 明写新执行未完成、Mac 离线、无 fresh Lean PASS。这不是将未运行改判成功。
- §5 分开 P-CORE 异源装配和真实同源消费者；增长保留概率域、允许策略、canonical 身体和期望人口评价；指数/期限/个体存续/伦理没有混用。最小统一指数与达到分类所需非空初态被保留；统一上界本身可容空初态，这一更宽事实不影响草案所述非空分类。
- §5 对 `ValidIdentity` 与 `ProgramPopulation θ` 分别提出责任，并保留正分支条件；没有从一般 State 推导全局身份唯一性或内部程序执行。
- §6 明确 Pliska/Rothblum–Whittle 只查摘要，保留与 UEOT 全部策略/执行语义比较的限度；未将可靠性或核心作用直接升为全球原创性。
- §7 的“形式闭合”明确基于已匹配的历史证据；结构闭合指条件桥和具体同源机制；解释闭合不声称哲学全部由 Lean 证明；范围闭合以正式协调为根据。四者没有用新执行状态或经验普适性相互替代。
- 草案把由原 B 转为 A 写为交叉终核及实际采用后的主审裁决，且限定“当前声明范围内达到合理闭合”；数学证据不反对这个有限升级。它并非将 D3 变为 PASS，也不是把历史 B 倒写为 A。实际采用/合并状态仍由主审据真实事件填写。

因此，B 对当前草案的数学结案没有新增修改要求。主审后续仅据实际事件修改采用状态时，无须因此再启动 Lean 或重做既有反例；若改变定理范围、量词或新执行声称，则应定点重核改变内容。
