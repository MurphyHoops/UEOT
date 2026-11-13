# SQLite 事务合同：有限检验预注册

状态：最终预注册文本，尚无认证数据。正式冻结以首次包含本文件及配套源的独立 Git commit 为准；主审读回真实 SHA 并生成匹配授权后方可认证。禁止用本地文件名或未提交的状态字段冒充已经完成的远端冻结。

## 1. 唯一阶段问题及主张

独立维护的 SQLite 运行时，在本研究登记的有限软件配置、单写者事务、进程中断和备份替换中，消费实际来源、允许观察、业务身份和观测预算的候选检查器，是否能给出可复核的当前状态判定？相对于同信息、同动作和同预算的标准参考模型核对器，是否增加了判断能力？

主要主张 SQL-CONTRACT-01：对于本登记的全部 trial，足额且完整观测中的确定判定正确反映“此前 ACK 义务＋本次事务允许完整状态集合”；预登记的足额可判格必须给明确结论。一个有效的错误接受、错误拒绝或无理由弃权即可反驳该有限主张；执行不全不计为通过。

同一主张的主要比较量是候选与强基线在相同 fault artifact 上的决定差异。规则等价／无额外增益是预期允许且可结案的结果。结构弱基线及去外部历史消融只定位前提，不替代强比较。

本研究不估计自然故障率、硬件可靠率、未来任意负载正确率或物理系统普适性。SQLite 是独立目标；本团队写的驱动、候选、基线、检查器不是独立外部发明。

## 2. 历史来源及只读范围

源基准 main：d30dae2a87150acddd67a3039ceccc4fe96d2b21。Core 限定 A 冻结继承。原多数 worker pilot 与 20261008 SQLite copy/rename/inode 方法试验保持历史身份。本轮新增事务 ACK、故障恢复、强基线、资源与留出数据。

只用两项 Core 原则：任务相对观察不足的 no-go 前驱；同源、权限、身份与费用的消费者纪律。完整来源、假设与不适用项见 [A的源映射](reviews/A/CORE_TO_SYSTEM_MAP.md)。没有 SQLite 的新 Lean 实例化；C7 为预注册和失败归因规范。P-PRED、控制商、CSX-30 具体 Register 定理、增长、二维、GOD/GOA、C4 缺陷标定均不调用。

生产 Core、两书、工具链、Mathlib、P-ID 及计数生成器只读；没有数学源差额时不重复 Lean。

## 3. 目标与故障域

目标是 Mac 系统供应的 Python sqlite3 运行时。现场 probe：Python 3.9.6，SQLite 3.51.0，source_id `2025-06-12 13:14:41 f0ca7bba1c5e232e5d279fad6338121ab55af0c8c68c84cdfb18ba5114dcaapl`。每次执行重录实际环境和有效配置；不宣称与未修改的上游版本相同。

首轮只用 DELETE rollback journal，synchronous=FULL，逐连接读回 `delete` 与 `2`。执行SQL还设置 foreign_keys=ON、cache_size=5、cache_spill=ON、busy_timeout=1000；读回 page_size、locking_mode、fullfsync。worker 在初始化数据库提交后再次配置并读回，PRECOMMIT 记录真实页数及 cache 参数。源/二进制/编译选项以冻结 protocol.json 的 expected_environment 匹配；不匹配为执行失败。校准实测 page_size=4096、locking_mode=normal、fullfsync=0，fullfsync 未被本试验提高为额外硬件承诺。

父控制器的原始请求及实际 ACK 日志位于本次故障影响域外：kill 只命中本次 Popen 子进程，旧备份替换只命中本次目标文件。它们仍在同机/同卷，不承担断电、全卷损坏或恶意父进程容错。日志不损坏是显式工程前提。

只操作研究独占新目录中的数据库和子进程。SIGKILL 不等于断电、内核故障、VFS 模拟写重排或硬件损坏。旧合法备份覆盖是独立历史负对照，不是 SQLite crash bug。

## 4. 身份、任务与允许集合

保护的是指定 schema 下的完整业务状态、事务记录及此前已确认事务义务。实际实现以外部 run 上下文、非空唯一 txn-ID 序列、请求摘要和完整业务值共同绑定来源；没有独立 db-domain metadata 表。PID、路径、inode、SQL正常或 txn-ID 一项均不能代替该完整判断。每次事务更新全部注册业务键，并在同一个 BEGIN IMMEDIATE/COMMIT 中插入唯一 txn-ID。schema 是 business(id INTEGER PRIMARY KEY,value INTEGER NOT NULL,payload TEXT NOT NULL) 和 transactions(seq INTEGER PRIMARY KEY,txn_id TEXT NOT NULL UNIQUE,request_hash TEXT NOT NULL)。初值为 value=10000+key、重复 initial-xxxx 字符串；seq次更新为前值加((key+seq) mod7)-3，payload由txn-ID/key的SHA256片段重复至登记长度。请求摘要绑定seq、ID、长度和更新列表；txn-ID由固定namespace和run/seq作UUID5。具体字符串及规范JSON以冻结runner为执行定义。初态由worker实际写入并提交；没有额外‘关闭后独立核验S0’步骤。预期状态由故障前初态和实际请求独立计算，不读取故障后目标生成。

最后一笔受登记干预的事务执行之前的参考状态记 S0，完整应用该事务后的状态记 S1。允许结果为：

| ACK／提交知识 | 策略共同可用的成立证据 | 允许集合 |
|---|---|---|
| ACKED | 父实际收到 COMMIT 成功之后的匹配 ACK | {S1} |
| NOT_COMMITTED | 共同公开的 PRECOMMIT 屏障、未放行、SIGKILL 与 reap 证书 | {S0} |
| UNKNOWN | 已放行但没有实际收到完整 ACK | {S0,S1} |

内部 COMMIT_RETURNED 钩子只验证干预位置，不能用于缩小 UNKNOWN 的策略允许集。策略共同读取的请求/ACK/未提交证书与私有裁判事件分别保存。

`ACCEPT_CURRENT_ALLOWED` 只认证当前完整状态是允许集合成员；ACK 标签原样保留，不补造收到事件。REJECT 报告具体合同矛盾；UNRESOLVED 报告缺失观测、预算、超时或执行原因。新的 PID 可恢复旧业务义务，旧路径也可丢失义务。

## 5. 方法与公平基线

worker 退出、被回收后，在任何 SQLite 检查前保存完整 DB+sidecar 原件。候选、强基线、弱结构诊断、历史消融各自从同一原件独立克隆，独立子进程执行。最后裁判另用克隆。原件前后哈希必须一致。STALE_BACKUP 替换前另外保存同一 run、同一承诺 H 下的关闭后当前 D_new；C 在后置独立克隆中读取它，与旧而合法 D_old 比较固定结构响应投影。不能拿不同 run 的 NORMAL 数据替代这一个同合同见证。

SQLite 首次读取可能自动回滚 hot journal、同步并删除 journal。该能力属于 SQLite，双方共同可用。v2校准中已经观察到有效journal header、恢复副本DB哈希改变及journal消失；认证的每个PRECOMMIT独立报告header/文件变化，不由校准自动保证W1/W2都发生同一热恢复。若某格只有冷日志，则该格只支持未提交结果一致性，不补写hot恢复。

强基线：预登记的单写者顺序规范/完整业务历史核对方法族。请求与响应区分、未完成操作允许集合属于成熟方法；本研究不是运行 Knossos，也不验证任意并发线性化。候选的合同条件与其作逐分支对应。两者同输入、同预算、同查询/动作权限、同调参机会。

弱基线仅输出结构诊断 `STRUCTURE_OK`，不冒称完整业务 ACCEPT。去外部历史消融以相同观察费用读取但不消费历史义务；若旧合法备份上错误继续，只显示该前提的必要性。

## 6. 资源口径

主要有限预算是 N=1 的 SQLite progress handler 实际回调阈值：high=1,000,000，small=32，zero=0，后置裁判=10,000,000；这是逻辑观测工作代理，不是精确 VM 指令数或严格 CPU/磁盘界。零预算在打开前退出；小预算触发实际中断的阶段和回调数必须记录；不把一次 SQL 视为常数工作。

同时记录返回行、规范字节、按实际被复制文件长度累计的应用层逻辑复制读写字节（不是逐syscall或物理I/O测量）、重启次数和从 connect 前计起的墙钟。连接、自动恢复、内核 I/O、回调间未观测操作及解释器工作并不由回调预算完全覆盖。所有策略同口径；不发布严格物理资源保证或少量同机墙钟优越性。

上述阈值、payload、PRAGMA 及阶段边界已由下述校准固定；不使用认证数据调参。父进程的模型与摘要生成是双方共同的外部预处理，输入字节记录但其CPU/文件工作不折算进回调预算；C将逐值重建检验摘要桥。

当前Python 3.9.6/macOS的monotonic_ns只用于同一进程内的耗时和顺序；不将不同进程的单调时间戳相减来推断ACK时延。跨进程位置由发送、握手、实际接收和终止的因果链确定。UTC用于来源时点，非亚毫秒同步保证。

## 7. 场景、样本、留出与停止

七场景：NORMAL、PRECOMMIT_KILL、COMMIT_NO_ACK_KILL、POST_ACK_KILL、STALE_BACKUP、BUDGET_ZERO、BUDGET_SMALL。

已执行校准单独保留：v1 W0=8键、2笔历史事务、每payload12,288字节，七场景各一次；v2 W0=256键、2笔历史、payload4,096字节，只做PRECOMMIT_KILL及STALE_BACKUP各一次。v1没有hot恢复证据；一次有界的v2负载/初始化后配置修正取得有效header及恢复文件变化，保留此前负证据，不辨称已单独识别哪一修改造成该差异。

认证 W1=32键、4笔已确认历史、128字节payload；W2=97键、7笔已确认历史、4,096字节payload。各七场景、各两次全新重置，共28 trial；每次在历史后再执行一笔受登记干预的事务。四策略各用独立副本。W1/W2的负载与历史组合均未运行校准。主认证顺序seed=2026111302，C replication seed=2026111303；策略按序号 mod4轮换。固定namespace/UUID5生成的全部ID另列 RUN_ALLOCATION.json。重复检测实施不稳定，不提供 iid 可靠率或性能置信界。

C 认证后在同一 Mac 的 independent-C 目录独立进程重现 W2 七场景各一次；split=replication 产生新的七个 UUID run-id，与主认证28项不混计。使用同冻结源，但原始判读由 C 自写计算器从实际请求/ACK/屏障及完整返回值重建，不信任 B 的摘要成员标签或后置裁判结论。不是跨设备或外部人类复现。

worker单次等待15秒、observer进程30秒。总预算1800秒只在trial开始前检查，达到后不再启动新trial，其余逐项NOT_RUN；当前trial的收尾/OS I/O不受该阈值严格硬截止。冻结全部run-id、负载、种子；不得追加直到有利。不覆盖任何已有运行目录。所有失败、超时、取消、缺失与未达成注入均保留。

## 8. 结果分类（认证前固定）

| 主认证格 | 数量 | 预先要求的当前判定 | 失败的解释 |
|---|---:|---|---|
| NORMAL、PRECOMMIT_KILL、COMMIT_NO_ACK_KILL、POST_ACK_KILL | 16 | 足额完整观察下 ACCEPT_CURRENT_ALLOWED | 有效反证可拒绝应用主张；干预/配置失败另列 |
| STALE_BACKUP | 4 | REJECT_HISTORY | 若记录完整仍接受，为具体规则/映射反例 |
| BUDGET_ZERO | 4 | UNRESOLVED_BUDGET，且不尝试连接 | 属预先登记的信息/预算边界 |
| BUDGET_SMALL | 4 | 依实际回调与中断记录判断；阈值预期中断 | 若未触发则预算边界覆盖未达成，不能只因场景名强改判定 |

20个足额格、8个预算格均进入全尝试台账。支持主张还要求低预算边界的实际执行证据；没有故障达成或缺失运行不能从分母剔除。上表是事前义务，不是实测结果。

- SUPPORTED_SCOPED：登记尝试齐全、故障/配置/来源门通过、足额可判格全部正确且非空；预算格准确未决；没有合同反例。
- EQUIVALENT_NO_ADDED_DECISION_GAIN：上述有效输入中候选与强基线全部决定一致，并有规则对应；可与 SUPPORTED_SCOPED 同时成立。零观测差异不外推未列故障或证明认知便利。
- REJECTED_APPLICATION：有效故障与完整观测下出现确定合同反例。保留原错误及范围，不先归因 Core。
- UNRESOLVED_EXECUTION：关键来源、配置、oracle、干预或覆盖缺失，不能判断对应主张。不能从分母删掉后宣布PASS。

弱诊断与消融的反例另行报告。主张只作有限逻辑检验，不引入人为最小效应量；若报告任何定量增益，需另立提前登记的比较，而本协议不包含它。

## 9. 冻结、偏离与交付

必须先提交最终预注册、protocol、runner、初审/交叉裁决、文件哈希，然后记录实际 commit SHA 与时间；主审读取远端确认后发执行授权。认证原始回执包含该 SHA 和源哈希。变更必须保留旧源及全部结果另标版本，不事后改写原判准。

最终交付全部原始事件/错误/费用/快照哈希及必要原件、独立复算和复现、争议裁决、研究稿与重放入口，经单一研究分支审查合并回读。只清理本轮合并分支。全局自然经验 UNVERIFIED、外部操作者/人类认可和普适性边界保持。

## 10. 实际冻结源及校准核验

- runner/sqlite_study.py SHA-256：`bdbe87252da0b107602f7e30509b4b094f53d97a647ac9dc34cb378195dd92d9`。
- runner/protocol.json SHA-256：`f68c5e9b643738563eebdce032bf13126e63036b2b473f889840355af5e00566`；protocol_revision=2。
- v1校准在2026-11-13 21:25:38—21:25:40（Asia/Shanghai）实际执行7项，原controller退出0；C直接重哈希318文件并独立复算7项。
- v2定向校准在21:30:51—21:30:52实际执行2项，原controller退出0；C直接重哈希95文件、独立复算2项，并在独立克隆直接查询当前/旧备份与热日志恢复。
- 这9项校准均不属于28项主认证；完整原始证据、原始源码及变化记录随研究结果保留。没有W1/W2认证数据被用于选阈值或选择策略。
- 最终源清单与全部35个预定认证/复现ID由 REGISTRATION_SOURCE_MANIFEST.json 和 RUN_ALLOCATION.json 固定。实际授权文件记录本首次提交的SHA；该文件在真实提交读回后产生，因此不要求本预注册包含自己的SHA。
