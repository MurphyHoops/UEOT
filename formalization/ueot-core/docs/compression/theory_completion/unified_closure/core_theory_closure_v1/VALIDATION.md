# Core 定本验证记录

**范围：本轮实际公共集成、端点信任、既有运行证据复用、两书身份与分离复核。** 数学内容分类为 `CLASSIFIED_CORE_CLOSED`；七项出口的解释及发布后的接续规则见 [FINAL_ACCEPTANCE.md](FINAL_ACCEPTANCE.md)。本文汇编实际回执，不充当独立审查者的签署，也不把发布前的验证记录改写成已经取得的发行／GI 接续回执。

本次验证使用声明的同源正类和原比较类。没有改变 stop、拒绝、信息权限、遗传或资源语义以保住结论。原全 Core 条件合同与 PR441、PR442、PR443 的完成状态保留；经验支持仍为 **UNVERIFIED**。

## 1. 本轮实际集成与编译

唯一新增生产导入边是：

```lean
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreTheoryClosure
```

该行位于 `UEOT/V3/Compression/TheoryCompletion.lean`，增加 77 字节；最终该入口为 27,710 字节，SHA256 为 `dc3759eff9c9f6fd13bba3acdf254c9f9f99bae1895e7bcda6226ecff54d4556`。十三个新数学模块的源码沿用已审准确版本，本轮没有为修复公共导入而重写它们。

| 实际动作 | 结果 | 准确证据 |
|---|---|---|
| `lake build UEOT` | exit 0；Lake 报告 9,754 jobs，原始日志包含十三个新模块及最终公共依赖链的构建。 | [INTEGRATION_BUILD.json](checks/INTEGRATION_BUILD.json)、[原始日志](checks/INTEGRATION_BUILD.log) |
| 仅 `import UEOT` 的公共消费者 | exit 0；19 个具体验证 `example` 与 5 个 `#check`，覆盖真实付费来源、共同程序、反馈、谱系及完整有限历史商。 | [PublicConsumer.lean](checks/PublicConsumer.lean)、[回执](checks/PublicConsumer.json)、[原始日志](checks/PublicConsumer.log) |
| 仅 `import UEOT` 的逐端点公理打印 | exit 0；59 个准确请求均返回，详情见第 3 节。 | [AxiomAudit.lean](checks/AxiomAudit.lean)、[进程回执](checks/AxiomAudit.json)、[原始输出](checks/AxiomAudit.log)、[结构化结果](checks/AXIOM_AUDIT.json) |

构建模式是 **`INCREMENTAL_EXISTING_LAKE_CACHE`**，工具链为 `leanprover/lean4:v4.33.1`，Lake manifest SHA256 为 `84542dad0540d0595b67e5b83d6b2d7bf96b4ca4aee9051f557ed73b0cb012d1`。9,754 是 Lake 报告的工作项数量，不表示同等数量的新模块，也不表示清缓存后的全仓重编译。

集成构建从 2026-11-07T18:33:15.511849+00:00 启动，成功日志最后写入于 18:36:37.252198+00:00，18:38:50.740725+00:00 读回 exit 0。消费者及公理进程于 18:41:08 UTC 附近读回 exit 0。这里区分日志写入时间与完成状态的实际观察时间，不将观察间隔全部算作编译时间。

关键原始身份：

| 文件 | SHA256 |
|---|---|
| `checks/INTEGRATION_BUILD.json` | `66ec18e2a55e08b6327aa5dec61557b8d1a954df41616600ae494d91b71063d3` |
| `checks/INTEGRATION_BUILD.log` | `3112f809a418b2f484d5095e901374d6d2c66e5d61403ae46f764f7370e9919a` |
| `checks/PublicConsumer.lean` | `2e77c69f870c355ef560e4f165495ecbca2ff3f921afff852494e58c4c39ac80` |
| `checks/PublicConsumer.json` | `7cbe7e2aa1318f48fb4620bcc1947fb901546cad5e8e90828e55fd1a33902df6` |
| `checks/PublicConsumer.log` | `a7ae1c417febbc652b0c5fa39ea9128dd46c60f1e553a7ecac9390087b167828` |
| `checks/AxiomAudit.lean` | `76f7be95d9dd1d86994f6c4548d49c7392de9724cacc71339148c297d500de05` |
| `checks/AxiomAudit.json` | `63c71fa224d0d8d8eaec58753c865417a588f601f9693fcdbdc42e1f8a567dfe` |
| `checks/AxiomAudit.log` | `08306c6cb0440636d465b4ed14ada4f287dd80b16c86e198cb3b6547917289b2` |

## 2. 公共源图与占位／信任标记检查

[PUBLIC_SOURCE_AUDIT.v2.json](checks/PUBLIC_SOURCE_AUDIT.v2.json) 在准确集成后扫描 1,048 个生产 Lean 文件、9,896,504 字节；SHA256 为 `5322fe7299ee355f5975e786fa35a975427b3c8063a368eaf26cc597cc8652bf`。其生产源清单承诺为 `eafedd3f23b1f359c87f7664f8db5b13446349ae6026eb6bc991dc2b4c447a07`。这是独立于上述实际 Lean 进程的**静态源码检查**。

| 现有公共根 | 可达生产模块数 | 十三个新增模块的可达数 | 准确解释 |
|---|---:|---:|---|
| `UEOT` | 1,048 | 13 | 所有生产模块从正式公共入口可达。 |
| `UEOT.V3` | 205 | 0 | 既有并行子集，本身不导入 Compression；这是原层级事实。 |
| `UEOT.V3.Compression` | 1,032 | 13 | 包含本轮新主线。 |
| `UEOT.V3.Compression.TheoryCompletion` | 820 | 13 | 唯一新增导入边所在的较低公共入口。 |

没有缺失内部 import，没有环，没有从 `UEOT` 不可达的生产模块。不能把“四个公共根得到检查”改写为“四个子根都应导出相同的全部模块”。

去除嵌套注释和字符串后，`sorry`、`admit`、显式 `axiom`、`unsafe`、`opaque`、`implemented_by`、`sorryAx` 的检查结果均为 0。`native_decide` 保持旧的 2 处，均在已发布的 `RegisterMechanismDecisionConsumer.lean`；本轮没有抹去或改称不存在。静态 token 扫描的口径不是完整 Lean 语义证明，实际类型检查由第 1 节进程承担。

## 3. 59 个实际端点的公理闭包

[AXIOM_AUDIT.json](checks/AXIOM_AUDIT.json) 的 SHA256 为 `c3ee10e18775a5bdc2e0cd17b1e08256d746477f065c4323345c8672b0696c63`。59 个请求、59 个唯一返回及原始输出逐项对应，未出现未预期依赖。

| 实际传递公理集合 | 端点数 |
|---|---:|
| 空集合 | 9 |
| `propext` | 5 |
| `propext`、`Quot.sound` | 4 |
| `propext`、`Classical.choice`、`Quot.sound` | 41 |
| 合计 | 59 |

因此，本次实际审计的 59 个新主端点只使用上述三种标准 Lean 依赖；这些端点的闭包没有旧 `native_decide` 或 `sorryAx`。这个结论只覆盖准确列出的 59 个端点，不扩大为所有历史声明的重新公理审计，也不把公共 import 图中旧的两处封闭数值信任删除。标准公理、Lean 内核与工具链信任仍按其本来含义保留。

## 4. 复用的实际来源运行与精确检查

已有十三个单模块成功回执均匹配当前源码 SHA。它们可以复用，但不替代本轮对最终依赖链的实际增量构建。原运行证据亦按准确源码身份复用，没有为本轮再跑旧的完整枚举。

| 既有证据 | 已验证内容 | 本轮处理 |
|---|---|---|
| [lean_native_execution.json](native_protocol/lean_native_execution.json) | 864 条公共请求与 288 条内部程序记录，共 1,152 条；另有两轮真实人口和四类因果 cut。 | 原始实际运行保留，未重新枚举。 |
| [native_source_check.json](native_protocol/native_source_check.json) | `PASS`；5,508 个付款前缀、最低余额 0；完整身体、身份、父指针与 ancestry；两轮 2→4→8；五类篡改负例均拒绝。 | 重新核对运行输出、源、人口模块、runner、checker 与 prototype 的准确关联。 |
| [source-feedback-probe.json](native_protocol/source-feedback-probe.json) | 65 个有限时域的精确矩；先 T=31 后 n=13,338 的有限例，及明确材料／供给上界。 | 复用已绑定的独立有理数检查；没有展开该规模全部人口路径。 |

三个 JSON 的 SHA256 分别为：

- 原生导出：`af8e82ff6a6f4b227cf4421b4b112a54c26fa3b071e16a8bf47497aeacada75b`。
- 独立来源检查：`3d04629bcfec6a7a11df763937111f1504f482834262758d75967e25ef0072b1`。
- 精确反馈探针：`441dd08048d8ec2c6fcc9774afcf26facbedb6ca979a8e9317b99f738dfcb0c0`。

[EXISTING_RECEIPT_REUSE_REVIEW.json](review/EXISTING_RECEIPT_REUSE_REVIEW.json) 给出分离的复用核对，SHA256 为 `fd5c737418a7d6a1a4d4a593e85064d2b933feea2b1f528d94ecbc875a16529c`。它明确没有重新编译、没有重新执行旧枚举、没有使用已消耗的原 G1 TOOL。

## 5. 两书实际字节与视觉范围

本轮仅重建发生附录 C 修订的哲学书。数学书 MD／TeX／PDF 与既有已审字节一致，复用原构建和视觉回执。

| 产物 | 数学书，238 页 | 哲学书，96 页 |
|---|---|---|
| Markdown SHA256 | `1a259fb130db79d97968e8e8cfe054acf0a50a1532486c838496dccfdb9b0bd8` | `837024acb8bc87047b6576f9ffde6e1b7c42df1d2e98da864189fb94fac7b73a` |
| TeX SHA256 | `5939276961f0c2350cf729841478a83394945b601a2dd79e5d82658191d956c3` | `40477fce874ed6dacccc8dd00eea5024cea6ef948c07f9d6f5d2c5552c427a35` |
| PDF SHA256 | `f3813ee21dd01e4bc56d880a5f65c557b9e6ed2b329c62e09c1b3da948cdf23a` | `c5ea00a7db17ef9109480efc98a105b9a9ae69ce7f165a6748c0fe8c873d41a8` |
| 本轮构建处理 | 字节未变，复用已审结果。 | 从准确新版 Markdown 经 Pandoc／XeLaTeX 重新生成。 |
| overfull hbox | 原准确构建记录为 0。 | 新准确构建记录为 0。 |

[BOOKS_FINAL_IDENTITY.json](checks/BOOKS_FINAL_IDENTITY.json) 是 2,332 字节的公开派生版，SHA256 为 `e50424318ac3e87e81be76aef95b011774c9dc39f60be5853389cd8cd1620c8e`。它只将 `visual_review.path` 规范为仓库相对路径，其余内容与内部原件一致，绑定两书当前身份与同一视觉回执。

[本轮视觉回执](../../../../../../../mathematics/review/CORE_THEORY_BOOKS_2026-11-08/ROOT_FINAL_VISUAL_REVIEW.json) 的 SHA256 为 `6176f31af64989dc2228dc32209849415e1520aa67ce1b0e3fb47758ec770633`。根执行者实际以整页查看哲学书第 **1、4、86—96 页，共 13 页**：封面、最终目录、附录 C 的当前入口、历史段落、表格、新同源接口及来源附录均在范围内；回执未观察到裁切、重叠、黑块字形或表格溢出。数学书复用[原视觉回执](../../../../../../../mathematics/review/CORE_THEORY_BOOKS_2026-11-06/ROOT_FINAL_VISUAL_REVIEW.json)，SHA256 为 `5fc84b2a02a04f9b528eb53380eed67eb282a0ce66186193b22e596e5d4a9728`。

这不是本轮逐页重审全部 334 页的声明。文档编译、必要页面检查、数学语义审查与最终发行字节读回分别登记；`BUILD.json` 中的编译状态不单独代替视觉回执。

## 6. 分离复核与事实时间

源与文稿作者、Mac 集成执行者及分离审查代理的职责分别保留。审查者没有把自己只读回执的行为说成亲自运行 Mac Lean 或重新查看全部 PDF。

| 独立审查回执 | 实际范围与结论 | SHA256 |
|---|---|---|
| [SEMANTIC_SEVEN_EXIT_REVIEW.json](review/SEMANTIC_SEVEN_EXIT_REVIEW.json) | 同源 S1—S5、七出口语义及书稿范围；未发现仍保留的正主张存在研究阻断。产生时公共验证与发行尚待完成，原时间状态保留。 | `96c3c49cb27775ffb21022f37c396d3f62e9c68ef9d6c84447c81af2e1977d31` |
| [PACKAGE_CONTENT_REVIEW.json](review/PACKAGE_CONTENT_REVIEW.json) | 精确七文件内容和身份、历史总纲及 247 个声明引用；无阻断意见。 | `e6ce2b3c1a6ed2e56192726efb87b9db2f08f1a6f277d9deb03c750a5755ad7b` |
| [ACTUAL_VALIDATION_REVIEW.json](review/ACTUAL_VALIDATION_REVIEW.json) | 44 项实际证据核对，包含原始构建／消费者日志、59 个原始公理返回、书稿与视觉回执身份及 G1 拒绝归因；通过。 | `6293d33f11fb7c5d510fa1ab345a56ff3a7c6544bb4609c142aa256c09072999` |
| [EXISTING_RECEIPT_REUSE_REVIEW.json](review/EXISTING_RECEIPT_REUSE_REVIEW.json) | 十三个旧单模块回执与旧来源运行的准确复用；通过，没有重复长流程。 | `fd5c737418a7d6a1a4d4a593e85064d2b933feea2b1f528d94ecbc875a16529c` |
| [PUBLIC_SOURCE_STATIC_REVIEW.json](review/PUBLIC_SOURCE_STATIC_REVIEW.json) | 17 项核对；全部 1,048 条生产路径与原冻结输入对应，唯一生产差异是已审的 77 字节 import，十三个数学模块不变，准确 v2 静态审计及四根范围通过。 | `d17b660de201cfd5ddcb2a866af4d2e4881d022e0e41973da708ea4fa2c72d1f` |

上述每份审查记录其当时取得的证据。`ACTUAL_VALIDATION_REVIEW` 原本单列待绑定的全量静态审计，已由准确 `PUBLIC_SOURCE_AUDIT.v2.json` 和随后独立的 `PUBLIC_SOURCE_STATIC_REVIEW.json` 接续确认；旧独审记录不回写成当时已审过尚未纳入其范围的文件。新的静态独审明确登记出口 1—6 的内容与验证已接受，第 7 仍须实际后继回执。本文件本身是作者汇编，不能反过来充当对自身的独立审查。

## 7. G1 原生结果与本轮外部集成的准确归因

[ORIGINAL_G1_CANDIDATE_OUTCOME.json](checks/ORIGINAL_G1_CANDIDATE_OUTCOME.json) 是 746 字节的公开净化分类版，SHA256 为 `e8da32cb68c57f9db8ae13c7a3394466d943a40769a2a6a176e5024bc6290ab0`。其中 `source_metadata_sha256` 绑定内部来源元数据；公开版保留拒绝原因、无补丁、`claim_consumption=NONE`、原固定请求已用 `1/1` 和外部集成归因，没有私有结果正文。实际允许读回的分类事实为：

| 字段 | 实际值 |
|---|---|
| 候选状态／原因 | `REJECTED / EDIT_ROOT_NOT_PUBLICLY_REACHABLE` |
| 读取字节 | 9,896,427，属于原冻结输入。 |
| 补丁 | 不存在。 |
| `claim_consumption` | `NONE` |
| 经验因果效果 | `NOT_EVALUATED` |
| 本轮重新执行原请求 | 否。 |
| 导出私有候选正文 | 否。 |

原工具的执行、结算、受控释放和同身份热冷重放完成，与其任务候选拒绝相容。任务要求四个根均能到达固定可编辑入口，而现有 `UEOT.V3` 是不导入该 Compression 分支的并行子集，故拒绝；没有原生补丁可供采纳。

本次一条 import 是在既有 Core 普通工程授权下完成的外部集成。原数学／书稿及 `native_protocol` 的 Lean 执行也保留外部 Core 会话来源。不得把这些结果改记为 GI 原生候选成功、跨项目泛化、经验增益或成本优势。这个结果不授权重跑原 request、清 STOP、重置账本、自动续期或增加 G2 预算。

## 8. 发布后回执怎样接续本记录

本记录和 [FINAL_ACCEPTANCE.md](FINAL_ACCEPTANCE.md) 固定已取得的内容与验证事实；[DELIVERY.json](DELIVERY.json) 绑定本包采用文件的实际字节。发行 commit／tree、远端逐文件读回、原 GI 的实时 CURRENT CAS 与独立完整召回，以及唯一 CONTINUE 更新，必须在那些操作真实完成后由独立后继回执绑定。

该后继回执应引用此交付清单及本包文件身份，而不要求把未来 commit 倒填进它自身将要改变的源码。旧审查中的 pending 状态保留为历史观察；整体当前七出口状态按 [FINAL_ACCEPTANCE.md](FINAL_ACCEPTANCE.md) 的后继证据规则判断。没有对应真实发布／接续回执时，本文不能单独证明第七项已完成。
