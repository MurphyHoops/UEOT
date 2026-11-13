# B：SQLite 实现、强基线与有限运行提案

日期：2026-11-13。状态：**独立首轮设计；不是预注册，不含认证结果**。

本稿前已独立读本轮 EXECUTION_TASK_FULL、现行 C7 登记/外部模板、20261008 SQLite copy/rename/inode/update 方法 pilot 及官方 SQLite 文档；未读 A/C 首轮结论。本轮增量是事务 ACK、受控进程终止、恢复与历史核对、强基线和资源测量；不能称首次在 SQLite 上试验。主审给定现行 main 为 d30dae2a87150acddd67a3039ceccc4fe96d2b21，实际 runner 仍将重录 Apple vendor SQLite 身份。

## 1. 主要问题与判决

建议只检验：在声明的单写者有限事务、SIGKILL 和旧合法备份替换范围内，明示结构、历史身份、提交知识和预算的应用监测器能否避免错误“继续”，以及它相对于同信息标准参考模型核对器有无额外决策能力。

主要单位是独立重置 trial，结果为 decision、ack_class、history_membership、resource_status。不是 SQLite 普遍正确率或一般崩溃可靠率。

建议三值规则：

- ACCEPT：配置与观察完整、结构检查通过、业务表和事务表的完整规范状态与已确认历史一致，提交知识没有未决项且预算满足。
- REJECT_HISTORY / REJECT_STRUCTURE：预算内得到确定相反证据。
- UNRESOLVED：未知 ACK、预算耗尽、未完成观察、超时或协议/执行失败；原因分开登记。

UNKNOWN ACK 的完整观察可另记录是否属于“此前已确认状态／此前状态加本次完整事务”的允许集合，但不把未收到 ACK 的事务升级成 ACKED。建议此类主决策仍为 UNRESOLVED；若主审选择允许集合证书，应在预注册前明确不同语义，不能运行后改标准。

## 2. 隔离进程、故障域与不可变原件

Python 3.9.6 标准库实现 controller、SQLite worker、policy observer 三种真实进程。只 kill 本次 Popen PID；每个 trial 新目录，不触碰用户 DB、旧工作树或其他项目。

每 run 独立保存：

1. oracle：父原始请求、完整 ACK 接收、初态、工作负载、时间戳。
2. target：唯一受故障影响的 worker DB 与 sidecar。
3. postfault_raw：worker 已终止并 reap 后、任何 SQLite 打开前，对完整 DB/sidecar 逐文件复制并保存大小/SHA。
4. policy/候选、policy/强基线、policy/弱诊断、policy/消融：均从同一 postfault_raw 独立完整克隆；保持 db.sqlite-journal 相对基名。
5. adjudication：最后另克隆给独立裁判，不能先打开或恢复原件。

首次打开可自动执行 hot-journal recovery，所以不可先 integrity_check 原件再交给后续策略。运行后再次核原件哈希，任何变化均使证据门槛失败。克隆是实验准备成本，单列实际应用读写字节；不能假称控制器免费完成了物理恢复。

oracle 的“独立故障域”仅指本实验干预集合独立：SIGKILL 仅命中 worker，旧备份仅覆盖 target；oracle 仍在同一 Mac/卷，不承诺抗断电、全卷损坏或恶意父进程。父记录 flush/fsync，仍须公开这一信任前提。策略若消费 oracle 导出的摘要，强基线在相同时机获得同内容并支付同费用；摘要只从请求/ACK 生成，不读取故障后目标。

## 3. 请求、事务身份与提交知识

业务表为有限键集合的整数值及文本 payload。每个事务原子更新若干业务行，并插入 transactions 表的唯一 txn-ID、顺序号和请求摘要。txn-ID 由协议版本/split/工作负载/场景/重复/事务序号的 UUID5 派生，跨 trial 唯一，重放稳定。

父纯 Python 模型从初态及请求计算规范业务状态；不能用 worker 返回的值当 expected。C 可从原始请求/ACK 自行重建，不需要调用 B 的判决生成器。

worker 阶段为：实际配置读回 → BEGIN IMMEDIATE → 完整数据修改/txn-ID 插入 → PRECOMMIT_READY → 实际 COMMIT → COMMIT_RETURNED_NO_ACK → ACK。两种 READY 可以设阻塞屏障；父不发继续消息则 worker 不越过该屏障。内部 COMMIT_RETURNED 标记只用于证明干预位置，不泄漏给策略、不充当客户 ACK。

父仅把实际收到并完整解析的匹配 txn-ID ACK 记为 ACKED。先收到前笔 ACK 后才发下一笔，因此注入时最多一笔未决：

- ACKED：父有完整对应 ACK。
- NOT_COMMITTED：确认 PRECOMMIT 屏障、未发继续指令且 SIGKILL/reap 成功；不能只由“无 ACK”推出。
- UNKNOWN：已经允许 COMMIT，但无完整 ACK。允许前态/完整后态；不按最终数据补标签。

同名路径、合法 SQLite 结构和旧历史正确性，不足以表示当前已确认事务历史的身份。

## 4. 固定配置、环境与恢复范围

按主审裁定固定 journal_mode=DELETE、synchronous=FULL；每 worker 和每 policy 连接均查询读回，要求 delete / 2。另记录 foreign_keys、page_size、cache_size、cache_spill、locking_mode、busy_timeout、fullfsync。PRAGMA 设置正常退出不能替代读回。

环境存 sqlite_version()、sqlite_source_id()、compile_options、Python/executable/_sqlite3 路径和可读二进制 SHA、平台、实际加载库。主审测到 SQLite 3.51.0 的 Apple source-id 必须原文公开，不能称纯上游发行版。

允许动作仅为打开专属克隆并允许 SQLite 自恢复、登记有限查询、继续/隔离/未决。旧备份是独立负对照干预；不存在最新可信备份时，不假装能恢复已丢失的承诺数据。本轮无需新增主动修复搜索。SIGKILL 不等同断电、内核 crash、VFS 重排或控制器写损坏。

## 5. 公平策略与预期等价

强基线选择成熟的单写者参考模型历史核对方法族：明确成功/失败/不确定的调用，完整核对恢复状态是否符合顺序规范。Herlihy–Wing 顺序规范与 Jepsen/Knossos 官方 ok/fail/info 是方法来源；本次编写狭窄特例，不宣称运行 Knossos 或认证一般并发线性化。

强基线与候选均先看配置/观察覆盖，再结构检查、业务与 txn 表规范扫描，使用同一历史摘要、相同允许动作/预算/时机。候选的“源/观察有效、身份保真、资源许可”分别就是基线“正确配置与完整检查、同一事务/业务历史、同一成本门槛”。因此两者规则逐分支等价，预期应接受**无额外决策增益**结论。

认证仍建议分别在独立克隆执行两个独立编写的决策函数，以检查实际观察/恢复差异。少量同宿主 wall time 不作性能优越性检验。

弱诊断只输出可打开且 integrity_check 正常的 STRUCTURE_OK，不命名为完整业务 ACCEPT。身份消融承担相同观察成本、看到同样输入但决策故意不消费外部历史，只看结构、内部业务约束和资源。其错误继续仅用于定位身份约束作用，绝不当作强基线。

## 6. 可测资源与未测开销

不把“一 SQL”算一次完整成本。建议主要有限预算为 SQLite progress handler 的**实际 callback 调用次数**，N=1；每次调用累计一次，达到 B 时返回非零中断，后续 SQL 禁止。B=0 在策略打开目标前即 UNRESOLVED。

该单位不是精确 VM opcode、物理页或 I/O。官方把 N 定义为近似 VM 指令间隔，并允许 prepare 阶段回调。连接、自动恢复、内核工作和回调间内部操作无法由它给硬件上界。资源结论严格限于登记 callback 预算，不能称端到端 CPU/磁盘认证。

另保存每 SQL/阶段的 callback 起止、完整返回行数、规范序列化字节、输出字节、重启数、耗时；完整克隆/备份/原件保存的应用实际读写字节单列。大扫描由 callback/行/字节显现。摘要读取费用同候选/强基线计入记录。

初拟高预算 1,000,000 callback、低预算 32、零预算 0。校准可确认高预算可完成有限观察、低预算确实中断；最终值在预注册前固定。未经校准不能把“预算32一定中断”写作已观察事实。

## 7. 七场景、校准和42个认证 trial建议

| 场景 | 干预 | 提交知识 |
| --- | --- | --- |
| NORMAL | 正常 COMMIT/ACK、退出 | ACKED |
| PRECOMMIT_KILL | PRECOMMIT 屏障、未放行即 SIGKILL | NOT_COMMITTED |
| COMMIT_NO_ACK_KILL | COMMIT 返回后的 ACK 前屏障 SIGKILL | UNKNOWN |
| POST_ACK_KILL | 父记录 ACK 后终止仍活跃 worker | ACKED |
| STALE_BACKUP | worker 关闭/reap后以较旧合法备份替换目标 | ACKED 但历史应不符 |
| BUDGET_ZERO | 正常状态、观察预算0 | 观察未决 |
| BUDGET_SMALL | 正常状态、观察预算32 | 依实际中断判定 |

这些是协议屏障处受控干预，不声称随机覆盖微秒级内部磁盘提交点。无需为首轮额外增加竞态搜索。

校准建议 W0=8业务键/2已确认事务，七场景各1次，单独 calibration。失败与改版均保留；仅重跑受影响校准。

认证建议 W1=32键/4已确认事务、W2=97键/7事务/较长payload与重复触及相同键，二者×7场景×3预定重复=42重置 trial。W2 未用于校准。固定种子生成有限工作负载，每注入事务多行并带唯一 txn。每 trial 四策略独立克隆。三次重复检测实际执行不稳定，不当作总体 iid 或置信界。

用预定 seed 打乱42 trial顺序；策略次序循环轮换；不清空系统缓存，不比较冷缓存性能。具体 payload、事务序列、种子及run-id全部预注册。

## 8. 停止、认证锁与产物

建议 worker屏障15秒、observer30秒；超时只终止本次子进程。完整执行登记run-id，失败保留，未运行列NOT_RUN，不补更好样本。未达干预、oracle缺失、配置错误、原件变化都不能记成功。未知ACK、预算未决和执行失败分别计数。

认证入口必须要求主审实际预注册 commit SHA、预注册/runner SHA清单及放行文件；没有则拒绝认证。校准与认证目录/run-id分离，已有run目录不可覆盖。

拟实现 runner/sqlite_study.py、runner/protocol.json、runner/README.md。产出环境、原始parent/child事件、请求/ACK、进程退出码、postfault和每clone哈希、完整观察记录、策略结果、原始费用及 agents/B/EXECUTION_REPORT.md。C可独立解析而不共享结论函数。源码不添加未经选择的 Apache/MIT 许可，遵守现行 LICENSE_SCOPE。

## 9. 本轮已读取的官方/原始依据

- SQLite Atomic Commit，rollback、恢复及硬件前提：https://sqlite.org/atomiccommit.html
- SQLite PRAGMA，DELETE/FULL及integrity_check边界：https://sqlite.org/pragma.html 。当前官方明确FULL在rollback对断电持久性还依赖文件系统；EXTRA追加目录同步。本轮SIGKILL不能检验该强主张。
- SQLite progress callback，近似N/prepare/中断：https://sqlite.org/c3ref/progress_handler.html
- SQLite testing §3.3，特殊VFS crash测试比本试验更强：https://sqlite.org/testing.html
- SQLite backup API：https://sqlite.org/backup.html 和 https://sqlite.org/c3ref/backup_finish.html
- Herlihy–Wing (1990) 作者全文：https://www.cs.columbia.edu/~wing/publications/HerlihyWing90.pdf
- Jepsen/Knossos官方README Concepts：https://github.com/jepsen-io/knossos 。仅方法归因，不声称本次运行该实现。

官方页面在2026-11-13查阅。本稿尚未运行SQLite校准或认证。Core源、冻结合同与工具链保持只读。

