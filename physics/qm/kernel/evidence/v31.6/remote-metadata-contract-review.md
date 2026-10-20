# v31.6 远端验收补录合同审查

结论：**源码只读审查 PASS；实际执行仍须通过脚本内的真实双 CI 门。** 已绑定根脚本 `/tmp/qm316_finalize_remote.py`，SHA-256 `8238c5e4fe1e1b6dcdac3bdc495d20eb52ad6bc5f19d5ac64af6c73f0b2378e6`。本审查没有执行补录脚本、修改仓库、操作远端或重跑 Lean/运行测试/PDF。

审查时 context：PR `PASS`，main `PENDING`。源 PR #345、源提交 `00bf88231328c09b9af58d0ff3c8eec977d73c53`、源树 `e84f47c4caa2b3b099660d981a8deaa2851d074e`、PR run `39380741012`。根端另已报告实际合入主线 `4ba7aa412d84fa193611578374a8693be1ff3337` 及运行中的 main run `39381585828`；脚本只能在实际 main 回执 PASS 后登记 MAIN_VERIFIED。

## 1. 已落实的关键门

第一处写入之前，脚本要求：两个 context 状态为 PASS；两份实际 CI 回执的 run/checkout/计数/所需步骤与来源对应；源及主线树 envelope 绑定相应 commit；实际树响应没有 truncated；70 个受验输入、56 个实际 Core 导入、三份正文与本地绑定字节逐项对应；原始 210 个发布路径的本地 bytes、SHA-256、Git blob 及远端双树全部对应，且各集合有精确唯一计数。

Git 整树比较只计算真实布尔值。接受依据是已列明的输入集合，不要求并行 Core 工作之外的整棵树相同。初稿中的 `all_published_qm_paths_identical` 已收窄成 `published_210_paths_identical` 与 `published_path_count=210`。

## 2. 精确写入位置

| 路径（仓库根相对） | 当前字段／变更 | 必须保留 |
|---|---|---|
| `physics/qm/kernel/evidence/v31.6/remote-main-reconciliation.json` | 新增实际 source/main 逐项比较、真实 tree bool | 不把比较结果写成新的 Lean 执行 |
| `physics/qm/kernel/evidence/v31.6/integration-verification.json` | 实际库名、科研基线、发布父提交、source/main commits/trees、PR/run/receipt、精确比对范围、MAIN_VERIFIED | 物理完备与新增实验始终 false；后续 metadata commit 独立 |
| `physics/qm/kernel/evidence/v31.6/remote-source-reconciliation.json` | main 状态及主线比较回执链接 | 原始 source readback 的 scope 和观察时间 |
| `physics/qm/status/CURRENT.json` | 当前 aggregate、acceptance marker、当前 integration、单列远端结果与元数据时间 | `integration.prior_version`、原 `local_checkpoint_state`、真实本地时间/历史 HEAD、全部科学边界 |
| `physics/qm/status/CLAIM_LEDGER_v31.6.json` | 当前 verification 的 remote identities、remote time、PR、reconciliation 链接 | 全部 claims、前提/限制、prior_version_verification、本地 checked_at、下一轮未证明状态 |
| `physics/qm/status/ACTIVE_RESEARCH_v31.6.json` | 当前发布状态及 source/main 身份 | v31.7 仍为审定待执行 |
| `physics/qm/README.md`、`physics/qm/ROADMAP.md`、`physics/qm/kernel/README.md`、`physics/qm/UEOT_QM_KERNEL_v31.6.md`、`formalization/ueot-qm/README.md` | 各一个当前状态；主报告追加准确远端段；Lean README 追加双 CI 事实 | 旧版本身份、计数、历史执行及科学限制 |
| `physics/qm/audits/CORE_SELECTION_DOOB_REVIEW_v31.6.md` | 开头验收状态句 | AI 审查的责任与数学范围 |
| `physics/qm/UEOT_QM_EXECUTION_v31.6.md` | 开头已完成标记及真实证据链接 | 原合同正文与前提 |

根脚本共 13 个确定写目标，不写 Lean、运行程序、Core、三个正式正文或任何原始实际执行文件。书稿的 10 项 metadata 单独由 B 处理，必须在根 integration 固定后计算其哈希。

## 3. 历史与科学边界

`source-manifest.json` 的 70 项、源集 `8a2cea35e060f5341f5672534d0717c605f5c441d998a08cc7677fb50a113115`、本地 `observed_checkout_commit=97d033ff83125822e9926f5bd36afd08dbd153ef` 和实际执行时间保持不变。科研基线 `427f512745ca70f82cba6a1388edcab904da8a42` 与发布父提交 `a7aa2f559e8bc3f5dfaabe7cc70fd212de5d5bd5` 分列。

`ci-scope-review.json` 的 `actual_ci_executed=false` 是当时静态审查范围，不能改写成新执行；`publication-docs-generator.py.txt` 也是生成当时的记录。所有旧 v31.5/v3.1 文件与当前文件内的 prior/edition_history 节点保留。573 项机器公理报告、84 见证审计及 CI 通过都不改变 `full_scientific_theory_verified=false`，不消除复量子选择、完整谱/现实三代、谱存在和无限条件过程等开放责任。

## 4. CI 证据的精确范围

A 的 parser 核对实际 runtime/lean job、完整所需步骤、实际 checkout、573 全名与允许基础、100 方法名、四见证 9/30/5/40、6/42 与 4/4 证书摘要以及两项归档成功。CI 日志打印 26 项来源 SHA；全部 70 输入和 56 Core 字节由根端实际 Git 树逐项回读连接到冻结本地清单。

`required_steps_success` 是 runtime/lean 两个非空列表的映射。归档上传成功不等于已下载并解析所有 artifact 内容，不能声称本审查逐项比较了 CI 的 79 个 olean 哈希。

## 5. 防止哈希自引用与错误基线

核内 integration 只绑定已执行的 source/main、固定清单与叶子回执；不要反向加入未来书稿 dossier/manifest/archive 的当前哈希。书稿哈希按外部 integration → remote binding → manifest/assembly/review → dossier → local release/metadata review → archive 的方向更新，archive 排除自身。后续 metadata commit 不可在同一自包含提交内预写自身 SHA，也不可把其新整树称作原科学 CI 受验树。

旧 `/tmp/qm315_finalize_evidence.py` 含重跑、旧 64/334/392/39/32 计数和旧书稿复制，不能直接执行。旧 prepare_metadata 仅可借用逐 blob 比对方法：最新远端 main 才是 metadata 合成基树；本地历史 HEAD 的 Git diff 不是发布基线。采用精确 metadata allowlist，保留并行 Core、所有历史证据及三个正式正文；最终读回仅核对相应发布字节，不重复数学验证。

全部已修正条目、字段列表及读入文件 SHA 见同名 JSON。书稿脚本的最终互审另记，不由本报告推定其已经执行。
