# Bilingual Mathematical Terminology

## Editorial scope

This glossary records the terminology used for the mathematical edition based on source commit `3d443ec29eb17af1fc00699a74e2d42d73516d81`. It does not add definitions to the frozen Core, change any P-ID, or strengthen a theorem. The definition in the cited chapter governs whenever an English term has several meanings. Lean identifiers, module names, and literal API names remain unchanged.

## Foundational objects and identity

| 中文 | English | Semantic constraint |
|---|---|---|
| 客体／对象 | object | Use **object** consistently for the mathematical object concept; do not suggest an observer-independent uniquely identified ontology. |
| 操作对象 | operational object | A member of an explicitly specified certificate class; not an unconditional characterization of every natural object. |
| 强操作对象 | strong operational object | Retain the declared predictive, causal, historical, and nontriviality conditions. |
| 世界过程 | world process | A specified process model; consistency of its path law does not establish empirical validity. |
| 历史 | history | The recorded state/action history, with the declared information permissions. |
| 允许历史 | admissible history | Contains only permitted observations and past receipts. |
| 规范预测状态 | canonical predictive state | The measure-valued statistic of the declared response family, relative to its protocols and reference law. |
| 规范干预预测状态 | canonical interventional predictive state | “Interventional” requires the declared intervention kernels; observational conditionals alone are insufficient. |
| FFIPS | FFIPS; full-future interventional predictive state | “Full future” means the complete **declared** future record, not every future fact in the universe. |
| 预测核心 | predictive core | Preserve the registered target, reference measure, and protocol family. |
| 预测身份 | predictive identity | Equality of declared predictive responses; not physical identity by itself. |
| 嵌入因子 | embedded factor | A sub-σ-algebra on the same underlying probability space; abstract isomorphism alone is weaker. |
| 预测充分性 | predictive sufficiency | Recoverability of the declared future-response kernel; not causal closure. |
| 同一对象 | same object | Preserve the stated identity/continuation relation. Similarity, common ancestry, and equal distributions are insufficient. |
| 有向延续 | directed continuation | A time-directed relation carrying ancestry and transport; do not replace it by undirected connectedness. |
| 历史身份 | historical identity | Depends on directed continuation and the applicable historical certificates. |
| 发展运输 | developmental transport | A prespecified model of structural development with stated metric and external inputs. |
| 实例／token | instance / token | Distinguish an individual occurrence from its finite type. |
| 类型 | type | A classified state/body type, not a permanent individual identifier. |

## Probability, information, and dynamics

| 中文 | English | Semantic constraint |
|---|---|---|
| 概率核 | probability kernel | Use **kernel**, not “nucleus”; state the domain/codomain and measurability. |
| 推送／推前 | pushforward | Use the existing `#` notation; distinguish pushforward laws from equality of paths. |
| 正则条件概率 | regular conditional probability | Defined up to the relevant null sets unless a pointwise version is explicitly supplied. |
| 几乎处处 | almost everywhere / almost surely | Use **almost surely** for probability events, **almost everywhere** for general measures or time–source product measures. |
| 模零 | modulo null sets | Relative to a specified common reference measure. |
| 共同满事件 | common full-measure event | Do not infer it from an uncountable collection of separate almost-sure assertions. |
| 逐点 | pointwise | A statement for every declared point; it is stronger than an almost-sure version. |
| 可数协议族 | countable protocol family | Countability is an actual assumption of the common-version construction. |
| 可测选择 | measurable selection | Existence must be justified; set-valued nonemptiness does not by itself provide a measurable selector. |
| 解体 | disintegration | Keep its parameterization and standard-Borel assumptions explicit. |
| 数据处理 | data processing | Preservation inequalities under a common measurable/stochastic channel. |
| 总变差 | total variation (TV) | The convention is `sup_A |P(A)-Q(A)|`, half the finite ℓ¹ distance. |
| 相对熵 | relative entropy / KL divergence | Natural logarithms unless bits are explicitly stated. |
| 信息残差 | information residual | Usually conditional mutual information under a specified experiment law. |
| 动态闭合 | dynamical closure | A kernel factorization/commutation property; do not replace it with causal closure. |
| 强可合并性 | strong lumpability | The same macroscopic transition law for every microscopic initial law, or the equivalent pointwise row condition. |
| 交织 | intertwining | State the maps and kernels being intertwined. |
| 占据律 | occupation law | State the time horizon, averaging or discount weights, and normalization. Distinguish it from a one-time marginal law. |
| 占据测度 | occupation measure | May be unnormalized; finiteness and normalization are separate properties. Do not call it a probability law unless normalized. |
| 训练—部署联合律 | training–deployment joint law | Its conditional deployment kernel must match the data-selected actual source. |
| 同源 | from the same source / common-source | Indicates binding to the same actual source definitions and law, not a new mathematical category. |
| 原生 | native | Refers to an existing source construction or formal domain; do not infer physical nativeness. |
| 路径级 | path-level | May concern a full-path law or a property of individual paths; the theorem must specify which. |
| 逐路径 | pathwise | A statement about individual actual paths, with its declared exceptional set. It is stronger than an identity of path laws. |
| 律相等 | equality in law | Never replace with samplewise equality. |
| 缺损／缺陷 | defect | Keep metric, scale, and normalization; identical zero sets do not give equal budgets. |
| 校准 | calibration | A declared relation between scales, error quantities, or measurements. |

## Persistence, realization, and composition

| 中文 | English | Semantic constraint |
|---|---|---|
| 持续 | persistence | Retention over a declared horizon or indefinitely; do not silently pass from finite to infinite time. |
| 续存 | continuation / continued survival | Existing individual retains its identity; distinguish from a newborn individual. |
| 可行性 | viability | Existence of an admissible retaining policy, with its specified horizon and probability qualifier. |
| 可行核 | viability kernel | A set of viable states, not a probability kernel. Context determines the two uses of “kernel.” |
| 不变集／不变律 | invariant set / invariant law | Does not itself imply attraction, health, or recovery. |
| 不变核（确定性持续） | invariant core | An invariant set arising in the persistence argument, not a probability kernel. |
| 恢复 | recovery / restoration | Use **recovery** for probabilistic/analytic recovery properties; **restoration** for an executable target-restoration check. |
| 修复 | repair | An actual operation/program, with its source, cost, and implementation conditions. |
| 再生 | regeneration | A stronger organizational mechanism; not synonymous with recovery or reproduction. |
| 准平稳 | quasi-stationary | A law conditional on survival; distinguish QSD from the invariant law of the Doob transform. |
| killed 过程 | killed process | A substochastic/subprobability process stopped by killing, with the declared exit event. |
| 吸收 | absorption | Different from killing or exit unless the model identifies them. |
| 载体实现 | carrier realization | A specified readout/decoder realization; physical failure requires additional frame assumptions. |
| 访问擦除 | access erasure | Loss of read access; does not alone determine actual physical failure. |
| 毁损集 | damaging set | Specify whether access or mechanism damage is meant. |
| 极小载体 | minimal carrier | Inclusion-minimal, not minimum-cardinality unless stated. |
| 最小因子 | least factor | Least under the stated inclusion order; stronger than merely minimal. |
| blocker | blocker | The family of inclusion-minimal hitting sets of a clutter on a finite universe. |
| 反链／clutter | antichain / clutter | No member properly contains another. |
| 形成 | formation | A candidate/parent formation relation, distinct from binding and physical construction. |
| binding | binding | Retain this term where it names the registered map or compatibility condition; do not merge it with formation. |
| 父对象／子对象 | parent object / child object | In compositional contexts, do not automatically infer a biological parent–offspring relation. |
| 亲本／子代 | parent / offspring | In population contexts, retain actual genealogical links and distinct identities. |
| 繁殖 | reproduction | An actual offspring-generating event; not repair of the same object. |
| 遗传 | inheritance | Copying/transport of a declared program or trait with its actual mutation mechanism. |
| 选择反馈 | selection feedback | Requires the actual population/lineage source; deterministic selection in every finite population is not implied. |

## Evaluation, control, and low-dimensional factors

| 中文 | English | Semantic constraint |
|---|---|---|
| 评价桥 | value bridge / evaluation bridge | A declared connection from mechanism outcomes to an evaluation; not a normative conclusion. |
| 目的 | purpose | Mathematical policy ordering or its declared representation; does not by itself imply conscious intent. |
| GOD | optimal-action correspondence (GOD) | A set-valued optimizer correspondence for a stated policy/action class and evaluation. |
| GOA | long-term closed-loop structure (GOA) | Depending on the theorem: attractor, invariant law, occupation measure, or conditional-survival structure. Do not impose a unique point. |
| 最优策略类 | class of optimal policies | The optimizer family for the fixed evaluation and comparison class; distinguish it from all admissible policies. |
| 比较策略类 | policy comparison class | The policies over which an optimality claim is quantified; this class must remain exactly the one in the theorem. |
| 指定内部程序 | specified internal program | Optimality within its program family does not imply optimality among all admissible policies. |
| 达到 | attainment | An actual admissible policy achieves the bound; distinguish from an unattained supremum. |
| 弱最优 | weakly optimal | Ties are permitted; no canonical tie-breaking rule is implied. |
| 规范自由 | gauge freedom | Coordinate nonuniqueness in Π/Φ factors or rewards; not the same sense of “canonical” as in canonical prediction. |
| 双驱动 | dual drives | A modeled two-factor representation with independently checked rank/anchoring assumptions. |
| 共同瓶颈 | common bottleneck | A common factorization across the declared family, not separate low rank at each point/environment. |
| 独立锚 | independent anchor | An independently registered intervention or measurement anchor; low rank alone does not supply one. |
| 资源预算 | resource budget | Preserve whether it is pathwise, expected, discounted, per-prefix, or high-probability. |
| 预付可负担 | affordability before payment | Supply order and prepayment permissions are part of the model. |
| 不可识别性 | nonidentifiability | Equality of admissible observation laws prevents the claimed distinction; it is not simply lack of data. |

## Editorial rules applied to every proposition

1. Put assumptions before conclusions wherever this does not change the mathematical or structural order.
2. Retain all quantifiers, including “for every initial law,” “for each fixed time,” “on the reachable image,” and “on the same Good event.”
3. Distinguish `almost surely for every registered plan separately` from `one common almost-sure event for all plans`.
4. Distinguish `there exists an optimal policy` from `the specified returned program is optimal` and from `every admissible policy is optimal`.
5. Keep expected, pathwise, and almost-sure claims separate. A mean identity is not a martingale theorem; a marginal law is not a path-law identity.
6. Keep D/P/K/H/E/N/O meanings unchanged. A standard theorem is not relabeled a UEOT discovery; Lean acceptance is not empirical confirmation.
7. Preserve code identifiers, proposition numbers, explicit anchors, citations, and formula symbols. Translate Chinese prose within formula text commands only through an explicit finite whitelist.
8. Use **Proof**, **Corollary**, **Example**, and **Counterexample** according to their actual role. An interface contract remains conditional even when its algebraic consumer is formally proved.
