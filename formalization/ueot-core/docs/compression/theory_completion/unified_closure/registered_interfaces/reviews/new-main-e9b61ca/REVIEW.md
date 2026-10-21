# 新 main e9b61ca：独立 Git 对象范围复核

**结论：新 main 的完整 Core 树与旧 main 完全相同；提供的合并树精确等于新 main 全树叠加治理候选唯一的一处策略 blob。新 QM 与 physics 树均按对象身份完整保留。**

状态：`SOURCE_IDENTITY_AND_REPORTED_MERGE_TREE_CLEAR_NOT_CANONICAL_AUTHORIZATION`。本次只读核验，不是测试、构建或 canonical 授权收据。

## 1. 实际读取的对象

| 对象 | 完整身份 |
|---|---|
| old_main | `65db00a12d20be41cd6c8befacb9ba2e74a2a8a9` |
| new_main | `e9b61ca9c35955028c4bfa425dfa278fd1864029` |
| governance_head | `6777a727c1df0618ef7d52800e3528c37e7c48d4` |
| reported_merge_tree | `f3758e41c77fc90ddfa0b243a2f1d7adf5a2d421` |

本地实际 `refs/remotes/origin/main` 为 `e9b61ca9c35955028c4bfa425dfa278fd1864029`；新 main 与候选的 merge-base 仍为 `65db00a12d20be41cd6c8befacb9ba2e74a2a8a9`。旧 main 是新 main 祖先，治理候选尚非新 main 祖先。此次未重新查询 GitHub。

## 2. 255 项新 main 变更的范围

逐项比较完整 Git 路径、模式、对象类型和 blob ID，共 255 项变更；分类为 `formalization/ueot-qm/` 13 项, `physics/` 242 项。范围之外为零。

没有读取 QM 或 physics 的数学正文。比较它们的目录 tree ID 和完整路径对象元数据即可核对保留状态。详细逐项差异在 REVIEW.json。

## 3. 完整树身份

| 路径 | 旧 main | 新 main | 提供的合并树 |
|---|---|---|---|
| `formalization/ueot-core` | `6f930c629cae3b1a317faf48d096e0727367934f` | `6f930c629cae3b1a317faf48d096e0727367934f` | `5e83f3c31890176d02914feb6785e6731d2704c0` |
| `formalization/ueot-core/UEOT` | `73dda901d236295245839a75f683cd7839690fa8` | `73dda901d236295245839a75f683cd7839690fa8` | `73dda901d236295245839a75f683cd7839690fa8` |
| `formalization/ueot-core/scripts` | `686ddf1190a6f7d4eb3a4c5d58cd7ff8abefd49d` | `686ddf1190a6f7d4eb3a4c5d58cd7ff8abefd49d` | `686ddf1190a6f7d4eb3a4c5d58cd7ff8abefd49d` |
| `.github` | `c9758eaaeec0eec8e620aa1379e5360effdebf6a` | `c9758eaaeec0eec8e620aa1379e5360effdebf6a` | `c9758eaaeec0eec8e620aa1379e5360effdebf6a` |
| `.github/workflows` | `c60603e08d227bff053945156e93f3cf76cff136` | `c60603e08d227bff053945156e93f3cf76cff136` | `c60603e08d227bff053945156e93f3cf76cff136` |
| `philosophy` | `e4ba99b3970f793ef0ebc49f815db297d904ca37` | `e4ba99b3970f793ef0ebc49f815db297d904ca37` | `e4ba99b3970f793ef0ebc49f815db297d904ca37` |
| `mathematics` | `f1ab436d7cad4c53f28b78a50b2bd1cb4b8e6bc5` | `f1ab436d7cad4c53f28b78a50b2bd1cb4b8e6bc5` | `f1ab436d7cad4c53f28b78a50b2bd1cb4b8e6bc5` |
| `research/handoffs` | `3fd064b158470a811bc1ae1308a8250c46780350` | `3fd064b158470a811bc1ae1308a8250c46780350` | `3fd064b158470a811bc1ae1308a8250c46780350` |
| `formalization/ueot-qm` | `c13c2b44c66208120801e497caad68e695a69909` | `56743009bdecdf2978452d9d7fc6e18d64e642d0` | `56743009bdecdf2978452d9d7fc6e18d64e642d0` |
| `physics` | `7f65420c7675f82d625f6fc9fc2db77855729ee2` | `d91b0bedf6134f43fe3fadb5d2b2ef3e61eb0500` | `d91b0bedf6134f43fe3fadb5d2b2ef3e61eb0500` |

完整 Core 目录等同覆盖其中全部已跟踪内容，不只本轮新模块。Core 的 Lean 子树与 UEOT.lean、scripts、全部 .github/workflows，以及 philosophy、mathematics、research/handoffs 在此次 main 前进中均未变化。合并树的 Core 目录与治理候选的 Core 目录相同；其中唯一相对新 main 的差异为治理 JSON。

## 4. 依赖锁与六个消费者

工具链文件仍为 `leanprover/lean4:v4.33.1`。`lean-toolchain`、`lakefile.lean`、`lake-manifest.json` 在旧 main、新 main、治理候选和提供的合并树四个对象中分别字节一致；锁定包仍有 9 项，精确提交详见 JSON。

| 文件 | SHA256（四对象相同） |
|---|---|
| `formalization/ueot-core/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `formalization/ueot-core/lakefile.lean` | `7f083f896c58e521092721637c067a9bd892c4b2d5185bdd1b99fd5391f25986` |
| `formalization/ueot-core/lake-manifest.json` | `84542dad0540d0595b67e5b83d6b2d7bf96b4ca4aee9051f557ed73b0cb012d1` |
| `formalization/ueot-core/docs/compression/theory_completion/unified_closure/UMC_GLOBAL_MODULE_DAG_V4.json` | `09c5a6043f1d81cbd4577ff13782bd0c74686b3dd066216483ac01e22a0062b1` |
| `formalization/ueot-core/docs/compression/theory_completion/knowledge/README.md` | `6b485781d19fb3b489aa401d1bb5ddc828b0b3b01564f9d1d5baa7d66071b75a` |
| `formalization/ueot-core/docs/compression/theory_completion/knowledge/reuse/fkrg_reuse.py` | `bf83850f8b4bd082a18fd70acb215ae6676ebdbeaa21cad88552ca2406573674` |
| `formalization/ueot-core/docs/compression/theory_completion/knowledge/reuse/test_fkrg_reuse.py` | `f1579578748ba703f0cdc8b2fc34461ab1866b84a9b3cf7404092cc7a8f4b072` |
| `formalization/ueot-core/docs/compression/theory_completion/knowledge/reuse/README.md` | `a97011013eb8acc1ff7e9b5efa373c3d3b407a7ac49e150c9fcd2c7df2b82d6d` |
| `formalization/ueot-core/docs/compression/theory_completion/knowledge/reuse/REBUILD_CLONE_CANDIDATES.py` | `dad2975d8727d05dad632e0d7e4c8df76733426c54d4cb298813d478c02cb317` |

这是已提交的依赖环境文件与消费者身份核验；没有重新检查实际运行目录中的依赖 HEAD/干净状态，也没有替代已有完整构建身份协议。

## 5. 治理候选与合并树

候选从旧 main 只修改 `formalization/ueot-core/docs/compression/COMPRESSION_RESEARCH_TRACKS.json`，JSON 语义差异严格为下列三项：

- `/l2_existing_path_exceptions/0/branch_patterns/0`
- `/l2_existing_path_exceptions/0/exception_id`
- `/l2_existing_path_exceptions/0/reason`

六个既有路径的 allowlist 逐项未变，没有新增路径、放宽匹配或变更冻结/计数表面。新异常 ID 与分支匹配分别为 `TC-REGISTERED-INTERFACES-EVIDENCE-2026-10-21` 和 `^compression/theory-completion-registered-interfaces$`。reason 同步描述本批接口及已完成旧异常的退休。

没有重跑 `git merge-tree --write-tree`，避免写 Git 对象。独立检查了根智能体提供的结果 tree 对象，并在内存构造“新 main 所有已跟踪条目＋候选唯一策略条目”；该集合与提供合并树逐项完全相等，含路径、文件模式、对象类型、对象 ID。main 的 255 项变更与候选的一项变更没有相交路径，新 QM/physics 目录对象也分别与合并树完全相等。

这证明来源对象与结果内容符合这一无重叠文本集成，不证明 GitHub 分支保护规则允许合并。不能凭这个 tree 覆盖 GitHub 当前返回的 mergeable=false，也不能把生成 tree 当成已经合入 main。

## 6. 仍未获得的门槛

- 新 main 的策略 JSON 与旧 main 字节一致，仍保留旧 `TC-SUPPORT-VIABILITY-EVIDENCE-2026-10-20` 异常；候选的新异常尚未成为 canonical 授权。
- 此次没有得到 resulting-main 的 Lean、native、集成测试 PASS，也没有新的计数 FINAL 事件收据。
- 对已绑定证据的意义是：这一 main 前进本身没有更改任何已提交 Core 或依赖锁输入；后续实际重放候选仍须比较其完整实际源码/环境/证据身份，不能预先宣称未来产物已通过。
- 没有 checkout、commit、测试、远端写、Git 对象写；未读取或修改其他工作者的数学内容。
