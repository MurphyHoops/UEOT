# B：SQLite 实际执行报告

记录日期：2026-11-13。当前阶段：**真实预注册后，唯一一次 28 项认证已全部完成；源、协议与分配没有调整。候选与强标准基线同判、同 SQL 回调数。两轮校准保留为校准，C 的独立复核与 7 项复现另行记录。**

本文件为认证后的执行记录。预注册时的原始版本另存 `PRE_CERTIFICATION_EXECUTION_REPORT.md`，SHA-256 为 `9bf4fead990d6ba2d3e6210abbd4054f4a82a987e48fa8b2d29ee8b02544e629`；已发布的预注册版本不被本报告覆盖。

本报告只记录实际发生的动作。新的 SQLite 工作不重开 Core、D3、工具链或既有数学任务；没有运行 Lean。Mac 操作全部通过 Desktop Commander Local Mac，目标是新建专属目录 /Users/murphyhoops/Documents/ueot-sqlite-study-20261113。

## 1. 实现身份与冻结状态

最终文件在本任务 runner 目录：

| 文件 | 字节 | SHA-256 |
| --- | ---: | --- |
| sqlite_study.py | 38046 | bdbe87252da0b107602f7e30509b4b094f53d97a647ac9dc34cb378195dd92d9 |
| protocol.json | 2368 | f68c5e9b643738563eebdce032bf13126e63036b2b473f889840355af5e00566 |
| README.md | 14871 | 2da9b70042ae648bd1926018930ff5b72ffe60d463f74fb7e1586a8394e389f0 |

FINAL_RUNNER_MANIFEST.json 保存该清单。最终 runner 与校准 v2 的 runner 字节相同；最终 protocol 相对于 v2 仅把状态改为 FROZEN_BEFORE_CERTIFICATION。真实 Git 预注册提交为 `26902c25152ca3676b4844d2156f028145f62fe2`，提交时间为 2026-11-13T13:41:29Z。主审在远端读回一致后于 13:41:55Z 签发本次执行授权，授权文件 SHA-256 为 `0dcd48bcb1cc55d6d595cfe6f721f9fd5b5bce3225e72f7c4dd352914bb1831a`。

固定认证分配为 W1/W2 × 7 场景 × 2 重复，共 28 个重置 trial；C 的独立复现分配为 W2 × 7 场景 × 1，共 7 个新 trial。W1/W2 未用于校准。B 只执行这 28 项认证，没有代跑 C 的复现。执行前独立生成分配并与 `RUN_ALLOCATION.json` 比较，执行后再次比较真实 `RUNS_PLANNED.json`，二者均精确一致；不是仅检查总数相同。

## 2. 实际环境

校准和本次 28 个认证 worker 的实际输出及固定身份检查：

- Python 3.9.6，构建信息为 Mar 6 2026、Clang 21.0.0。
- macOS-26.6.2-arm64-arm-64bit。
- SQLite 版本字符串 3.51.0。
- SQLite source ID：2025-06-12 13:14:41 f0ca7bba1c5e232e5d279fad6338121ab55af0c8c68c84cdfb18ba5114dcaapl。
- Python 二进制 SHA-256：9ea22c79baac7ee6906d807799f351ae5de25b74be3ead66370714ea5348ca9f。
- _sqlite3 模块 SHA-256：c16c8f766c567ec0437814f32b5a2f5a23f266ff603f1cb40cf21d1865e0c8c6。

完整路径、compile_options 和配置在原始环境记录中。该库是 Apple vendor variant，不称纯上游同名发行版。

实际有效 PRAGMA：journal_mode=delete、synchronous=2、foreign_keys=1、page_size=4096、cache_size=5、cache_spill=5、locking_mode=normal、busy_timeout=1000、fullfsync=0。v2 在初始化完成后重做读回，并在 PRECOMMIT 屏障记录实际页数和 cache 设置。环境身份在最终协议中被显式固定，后续不接受静默更换 vendor。

## 3. 校准 v1：七场景，原记录完整保留

第3、4章保留校准完成时的证据及当时的独立复核状态，包括当时尚待 C 查询的准确措辞。它们不是把后继已经完成的工作重新列为待办；实际认证与 C 后继结果见第8—14章。

实际时间为 2026-11-13T13:25:38.618977Z 至 13:25:40.527027Z；controller exit 0，7 个计划 trial 全完成，没有执行错误。源 SHA e8190f5b64a9c389bf7a6761bbbf2fd2e23d1211097c74b35ea41e3e9df5f5ce，协议 SHA cd83b24fbb3b5897fd45274ebb29d0310e78fee8aaf4a9e03b716f52531e1f63。W0 为 8 键、2 笔已确认历史、每行 payload 12288 字符。

| 场景 | 实际 ACK 类 | 候选＝强基线 | 弱诊断 | 身份消融 | 候选 callback |
| --- | --- | --- | --- | --- | ---: |
| NORMAL | ACKED | ACCEPT_CURRENT_ALLOWED | STRUCTURE_OK | ACCEPT_ABLATED | 350 |
| PRECOMMIT_KILL | NOT_COMMITTED | ACCEPT_CURRENT_ALLOWED | STRUCTURE_OK | ACCEPT_ABLATED | 330 |
| COMMIT_NO_ACK_KILL | UNKNOWN | ACCEPT_CURRENT_ALLOWED | STRUCTURE_OK | ACCEPT_ABLATED | 350 |
| POST_ACK_KILL | ACKED | ACCEPT_CURRENT_ALLOWED | STRUCTURE_OK | ACCEPT_ABLATED | 350 |
| STALE_BACKUP | ACKED | REJECT_HISTORY | STRUCTURE_OK | ACCEPT_ABLATED | 310 |
| BUDGET_ZERO | ACKED | UNRESOLVED_BUDGET | UNRESOLVED_BUDGET | UNRESOLVED_BUDGET | 0 |
| BUDGET_SMALL | ACKED | UNRESOLVED_BUDGET | UNRESOLVED_BUDGET | UNRESOLVED_BUDGET | 32 |

这张表来自实际 SUMMARY/observer 记录，不从场景名填入预期标签。全部 postfault 原件在策略观察期间保持哈希不变。

### v1 的关键负证据

PRECOMMIT 原始 journal 为 111320 bytes，但首 8 字节为零。前 28 字节为：

    0000000000000000000000009ffb213f0000001c0000020000001000

数据库和 journal 在观察副本打开前后均未变化。此运行支持“提交前杀进程后观察得到此前允许状态”，**不支持声称实际执行 hot-journal rollback**。该不足未被抹除或重命名为恢复成功。

预算 32 在首条 PRAGMA journal_mode=DELETE 内触发 OperationalError: interrupted；并非读完部分业务表后才停止。complete=false、history_membership=null，不把未观察到某行当缺失证据。预算 0 时 connect_attempted=false；实验准备/克隆仍有实际成本，不能称零物理工作。

UNKNOWN ACK 的当前状态属于预先允许集合，因此接受当前状态；ack_class 原样保持 UNKNOWN。没有倒改成“ACK 已收到”。

v1 STALE 未保留替换前当前数据库的完整字节，故不能单独以它宣称已经测到同一 H 下 D_new/D_old 的成对观察别名。v2 修复此证据保存缺口。

## 4. 校准 v2：只验证两个实际变化

主审允许一次针对性调整：W0 改为 256 键、2 笔历史、payload 4096 字符，只运行 PRECOMMIT_KILL 和 STALE_BACKUP。W1/W2 不变、不执行。另补环境固定、1800 秒停止启动后续 trial、剩余 NOT_RUN 记录，以及同 H 替换前当前快照。

实际时间为 2026-11-13T13:30:51.244455Z 至 13:30:52.219809Z，exit 0，2/2 完成。runner SHA bdbe87252da0b107602f7e30509b4b094f53d97a647ac9dc34cb378195dd92d9，校准协议 SHA 0ab41b5b47b2177accc78f68e10df01284daec831967d1fd21aeff6107917c20。

### 实际热日志路径见证

运行 8ab897cd-7537-5654-8603-440f253dd95c：

- PRECOMMIT 实际记录 page_count=292、cache_size=5、cache_spill=5、transaction_active=true。
- 父未发放行命令即 SIGKILL，取得 -9 并 reap。
- 原 DB 1196032 bytes，SHA 60d1d72a8722b0ee07d297146820335e001ef2f6417d7dc10e223718fcad6bf4。
- 原 journal 1198672 bytes，SHA a335ed84fefd438878795a96c99e3ddbcc5191c28dcda77d86449fb4d825e68f。
- 前 28 字节：

      d9d505f920a163d70000001cebfc1b95000001240000020000001000

- 候选克隆打开后 journal 消失，DB SHA 变为 84935fb3a24a5295518e827dac294911dea92c5d9b0da5053571d40dfb929b76。
- 完整 SQL 观察完成，状态摘要匹配 S0，候选/强基线均 ACCEPT_CURRENT_ALLOWED；候选 callback=3338。
- postfault 原件保持不变。

这形成 hot-header、独立 clone 文件变化和前态摘要匹配的实际证据链。完整业务行与参考状态保存在 Mac 原件，C 将独立逐值复算；B 的记录不是 C 独立验收。该见证仍仅为校准、单机进程中断、当前 vendor/config 的有限路径，不能冒充断电检验或认证负载上的结果。

### 同 H 当前／旧备份保存

运行 108848dd-74db-5f41-9315-052493eb1855：

- 替换前关闭的 D_new 保存于 pre_replacement_current，1196032 bytes，SHA 29c7318ef9c8160152b3fbec5e49d0cffcf2b2da83f91aba141ad7e8fbfc20e3。
- 复制成本实际记录应用读/写各1196032 bytes。
- 替换后 D_old 的 SHA 为 3bab1206aaba92171e00e94357203d711820523725b5c9dc66499904bf7172cd。
- 候选/强基线 REJECT_HISTORY，弱诊断 STRUCTURE_OK，身份消融 ACCEPT_ABLATED；候选 callback=3318。
- 两态使用同一 trial 的请求/ACK 合同。C 可后置独立克隆并查询 D_new，不改 D_old 原件。当前只声称字节已保存；尚未把 C 的后置查询写成已执行。

校准到此停止，不继续追逐更多故障、配置或优越性结果。

## 5. 公平性、资源与证据边界

候选与强基线是同一源文件中同一有限规则的两种拼写；各在独立 clone 中执行。它们不是两项独立发明，B 不能自称独立同行审查。全部校准判决一致与代码层规则对应相容，不提供 UEOT 新增控制增益。

主要预算单位为连接后安装的 SQL progress callback 数。B=32 的实际中断及不完整标志已经观测；不是严格硬件 I/O 上界。公共 oracle 状态重建、摘要加载/序列化、clone、connect、部分自动恢复、解释器和内核工作均在此硬计数之外。它们对强基线和候选同等，但共享口径不会使真实费用消失。观察耗时精确起于读取公共摘要之后、connect 之前。

1800 秒限制是到阈值后停止启动后续 trial；不是 OS 硬截止。当前 trial 的分阶段超时、清理和文件 I/O 仍可能继续。该分支仅做代码审查，不为增加检查数量额外制造超时试验。

策略输入白名单是代码/接口纪律，不是 OS 安全隔离。SHA256 是工程摘要，不是数学单射。无独立 db-domain 表；没有在故障前额外关闭并独立扫描完整 S0。初始化正确与父事件可信是明示工程前提，实际事务 ID、请求和完整观察行用于后续有限核对。

旧备份替换在干净关闭后发生，属于应用历史负对照；其结构正确、历史缺失不能归为 SQLite 自身 crash bug。恢复来自已有 SQLite rollback 机制，候选没有新增修复算法。

## 6. 保存位置与小包

所有原始 DB、sidecar、请求、parent/worker日志、完整 observer 行、每策略 clone 和完整manifest仍在：

    /Users/murphyhoops/Documents/ueot-sqlite-study-20261113/calibration/run-v1
    /Users/murphyhoops/Documents/ueot-sqlite-study-20261113/calibration/run-v2

对应不可覆盖的已执行源位于 runner/calibration-v1 和 runner/calibration-v2。

共享小包完整取回并校验：

| 包 | 大小 | SHA-256 |
| --- | ---: | --- |
| evidence/calibration-v1/v1-summary-evidence.zip | 32032 | f87fe2eba2363f5feb5063c43940813364f80a8339ee98333b4b131c7ef1be62 |
| evidence/calibration-v2/v2-summary-evidence.zip | 21654 | 59780da801bb747e38e01c4b832898a3f72441883d070ec4e881fc25aba7c9c2 |

每个包保存源/协议、实际 controller receipt/stdout/stderr、SUMMARY、RUN_MANIFEST、RUNS_PLANNED、FILE_MANIFEST和compact读回。小包不是全部DB二进制的云端副本；不能说B/C已在云端重哈希那些未转移的二进制。完整原始仍在Mac，由C独立读取。

## 7. B 对 A 的真实交叉质询及已收到答复

### B-A1：身份／初态是否被过度声称

B指出：A1曾写数据库域标识与关闭后验证S0，但实现没有db-domain表，也没有每trial前置关闭并独立查询已ACK前态；source绑定由请求/ACK、唯一txn序列和业务状态摘要构成，白名单非OS隔离，SHA非数学单射。询问C逐值比较与同H两态能支撑什么，以及应收窄哪些句子。

A正式接受措辞收窄：参考S0由初始化器、请求和实收ACK定义，初始化正确与事件记录可信为工程前提；不能补称已量测前态。C可检验观察到的完整后态是否满足参考合同，同H两态给弱结构投影不足的具体见证。它们不重建全部真实过去、不证明token同一，也不改变SHA的数学地位。无需新增domain表或额外初态试验；A1原文作为历史保留，后继采用准确解释。

### B-A2：资源与恢复是否越过实测范围

B指出：连接后callback预算未覆盖oracle模型、序列化、clone、connect/native恢复/内核；即使双方同成本，也不能由P2称完整资源可支付。v1没有hot，v2才有具体热日志链；只有SIGKILL。

A正式同意：预算结论严格限handler SQL计数，未覆盖项分别说明，不能称P2全资源履行。墙钟起点应说公共摘要读完后、connect前。v2证据经C核对后支持这一具体自动rollback路径，不支持所有崩溃、生物组织闭包或Core修复/GOD端点。A当时尚未亲读v2，按B/主审报告标明来源。

这两项是实际质询导致的解释收窄；没有通过新增Core端点或附加无消费者的工程结构处理。

## 8. 预注册后的唯一认证执行

主审 GO 后，B 将最终源、最终协议、授权、完整分配、README、预注册文本部署到 Mac `runner/preregistered-26902c25`，控制脚本核对这六个文件的完整 SHA-256。最终协议为 `f68c5e9b…`，没有误用校准草案 `0ab41b5b…`。控制脚本使用新输出目录及独占创建的开始记录，拒绝重复运行。

实际 controller 开始于 **13:47:32.731750Z**，结束于 **13:47:45.667683Z**，约 12.936 秒；PID 88629，真实子进程返回码 0。该时间是本次整批实际运行时间，不是可推广的硬期限或性能估计。原始输出为 `certification/run-v1`。

| 项目 | 实际结果 |
| --- | ---: |
| 预注册计划／实际尝试／完成 | 28／28／28 |
| 执行失败／未运行 | 0／0 |
| 不同 worker PID | 28 |
| 不同 observer PID，包括独立末位诊断副本 | 140 |
| worker 正常退出／SIGKILL 后 -9 | 16／12 |
| 候选／强标准基线判决分歧 | 0 |
| 每策略克隆在打开前与同一原件完全相同 | 全部成立 |
| postfault 原件在全部观察期间保持不变 | 28／28 |

认证 `FILE_MANIFEST.json` 的 SHA-256 为 `ed4da14df4cf913032e8e505118a52b783650d1118f94e4981d6e9d8beed7073`；B 后置只读处理在 Mac 重算其中 1,261 个文件的长度和 SHA-256，全部相同。该 manifest 不包含自身和位于上级的 controller 文件；完整包另有包含这些文件的总清单。

启动前确有一次 Desktop Commander `start_process` 请求返回 MCP 初始化错误，没有 PID 或 trial 开始证据。随后相同的拒绝重复 wrapper 唯一执行成功，开始记录、目录和 controller receipt 完整保留。此为连接层故障，不将其伪记为 SQLite trial 失败，也不隐瞒该工具失败。认证没有重跑。

## 9. 七场景实际结果与非空覆盖

下面每行均包含两个负载各两次，共 4 项；计数与标签来自完成后的原始输出。候选与强基线在完整业务行、事务行、判决、ACK 类、SQL 回调和完整性标志上逐项相同。

| 场景 | n | ACK 类 | 候选＝强标准基线 | 弱结构诊断 | 去外部历史消融 |
| --- | ---: | --- | --- | --- | --- |
| NORMAL | 4 | ACKED | ACCEPT_CURRENT_ALLOWED | STRUCTURE_OK | ACCEPT_ABLATED |
| PRECOMMIT_KILL | 4 | NOT_COMMITTED | ACCEPT_CURRENT_ALLOWED | STRUCTURE_OK | ACCEPT_ABLATED |
| COMMIT_NO_ACK_KILL | 4 | UNKNOWN | ACCEPT_CURRENT_ALLOWED | STRUCTURE_OK | ACCEPT_ABLATED |
| POST_ACK_KILL | 4 | ACKED | ACCEPT_CURRENT_ALLOWED | STRUCTURE_OK | ACCEPT_ABLATED |
| STALE_BACKUP | 4 | ACKED | REJECT_HISTORY | STRUCTURE_OK | ACCEPT_ABLATED |
| BUDGET_ZERO | 4 | ACKED | UNRESOLVED_BUDGET | UNRESOLVED_BUDGET | UNRESOLVED_BUDGET |
| BUDGET_SMALL | 4 | ACKED | UNRESOLVED_BUDGET | UNRESOLVED_BUDGET | UNRESOLVED_BUDGET |

候选总计 **16 接受、4 拒绝、8 未决**；20 个充分预算试验全部作出有内容的判决。因此该结果不依靠全弃权获得表面安全。ACK 总计 ACKED 20、UNKNOWN 4、NOT_COMMITTED 4。

### UNKNOWN 没有被事后升级

4 个 `COMMIT_NO_ACK_KILL` 的最终事务没有父 ACK 记录，公共输入和最终结果均保留 UNKNOWN。其允许集在观察前已定为 `{S0,S1}`；完整观察属于该集合，因而接受当前状态。隐藏审计消息 `COMMIT_RETURNED_NO_ACK` 不是策略的公共输入，不能利用它把 ACK 类偷偷改为已确认。实验说明此有限当前状态问题可被决定，不宣称未知历史 ACK 已被识别。

### 低预算的实际行为

4 个零预算 trial 的每个策略均不连接 SQLite，SQL 回调为 0；仍然已经发生 observer 启动、文件克隆和输入准备，故不是零工作。4 个小预算 trial 的各策略均在**首条 `PRAGMA journal_mode=DELETE` 内**到达 32 回调并抛出 `OperationalError: interrupted`；完整业务扫描尚未开始，返回业务行数为 0。所有相关结果 `complete=false`、`history_membership=null`，无缺失历史判定。Python 3.9 的错误对象未提供数值错误码，原记录为 null；不补写未观测的数值 `SQLITE_INTERRUPT`。

### 旧合法备份的作用

4 个 STALE 的旧数据库结构都正常，但没有满足本次同一请求／ACK 合同的业务与事务全态，候选和强基线同时拒绝。弱结构诊断保持 STRUCTURE_OK；去掉外部历史义务的消融接受。每一项都保存了干净关闭后的同合同 `D_new`，然后才进行旧备份替换，故存在可后置独立查询的成对原件。B 没有用其他 NORMAL trial 的不同 UUID 和合同冒充这一配对。直接 SQL 成对查询由 C／主审在他们自己的副本和报告中提供。

这支持“结构一致性不足以认证指定历史业务义务”的具体见证；没有发现 SQLite 违反其事务保证。替换是显式应用层干预。

## 10. 热日志恢复的真实覆盖范围

| 负载 | PRECOMMIT 数 | 实际 journal 大小 | 有效热头＋副本 DB 改变＋journal 消失＋完整 S0 | 结论 |
| --- | ---: | ---: | ---: | --- |
| W1：32 键、128 字符 payload | 2 | 16928 bytes | 0／2 | journal 头为零，DB 与 journal 在观察前后未变；仅支持未提交事务后的允许前态 |
| W2：97 键、4096 字符 payload | 2 | 462560 bytes | 2／2 | 支持这两条 SIGKILL 后实际自动 rollback 路径 |

W2 的 run ID 为 `b784e4fa-ed25-5b05-a94b-c0e29861811c` 与 `9186e6ac-13ef-5440-9e44-0a568ddde727`。两者原 DB 均 466944 bytes，journal 首八字节为 `d9d505f920a163d7`。完整 28 字节头、原 DB/journal 哈希及恢复后 DB 哈希在 `CERTIFICATION_COMPACT.json` 的 `hot_journal_observation`、`raw_files`、`policies.candidate.files_after` 中逐项保存；完整原件在相应 `postfault_raw`。

仅有非空 journal 或头魔数不能独立证明完整恢复。这里同时核对了原件不变、观察副本 DB 字节变化、日志删除和完整业务／事务值属于参考 S0；独立 C 的直接 SQL 验证另行给出。W1 的冷日志证据与校准 v1 的负证据均保留，**不把 4 个 PRECOMMIT 一律写成热日志恢复成功**。

此结论仅涉及 SIGKILL 后数据库新连接的恢复／检查。没有断电、硬件故障、文件系统故障、WAL、多写者竞争、网络 ACK 丢失模型或应用服务重启试验；不需要为本轮结案新增这些范围。

## 11. 实际资源、费用与强基线比较

### 回调数是实测代理，不是 SQL 条数

| 场景 | W1 每 trial 候选＝强基线 | W2 每 trial 候选＝强基线 |
| --- | ---: | ---: |
| NORMAL／COMMIT_NO_ACK_KILL／POST_ACK_KILL | 680 | 1531 |
| PRECOMMIT_KILL | 660 | 1511 |
| STALE_BACKUP | 600 | 1391 |
| BUDGET_ZERO | 0 | 0 |
| BUDGET_SMALL | 32 | 32 |

两个重复得到相同的上述回调数。每个查询都记录 SQL、回调前后计数、实际返回行和耗时；全扫描没有被包装成“1 条 SQL 所以固定成本”。W1 正常观察返回49行、W2返回117行，计入配置查询、完整性结果和业务／事务行，不把这些总行数误称业务键数。

| 28 项合计或分布 | 候选 | 强标准基线 |
| --- | ---: | ---: |
| SQL 回调总数 | 21718 | 21718 |
| 每 trial 回调 min／median／max | 0／680／1531 | 0／680／1531 |
| 实际返回总行数 | 1634 | 1634 |
| 返回值规范编码总 bytes | 4043354 | 4043354 |
| 公共摘要输入 bytes 总量 | 16876 | 16876 |
| 每策略克隆应用读 bytes | 7840256 | 7840256 |
| 每策略克隆应用写 bytes | 7840256 | 7840256 |
| 连接尝试次数 | 24 | 24 |
| observer 启动到退出累计秒数 | 1.739861 | 1.697348 |
| 启动到退出 min／median／max 秒 | 0.033656／0.059320／0.113967 | 0.035595／0.050470／0.112503 |
| 摘要加载后、connect 前至观察结束累计毫秒 | 80.076 | 95.240 |

墙钟读数是这次进程运行的描述，混合启动、调度、缓存和工作，不是独立测量的启动成本，也不是性能优越性检验。不得从某个累计秒数较小推出候选更快。弱结构诊断合计14428回调、240返回行、1380返回值bytes，承担的语义任务更弱；它不是可用来证明候选计算优势的公平强基线。消融与候选执行相同完整扫描，21718回调，区别在是否要求外部历史义务。

五组观察（四策略加末位诊断）各复制同一组原件；每组应用复制读/写各7840256 bytes。原件保存另花相同总量；四个 D_new 见证另有各983040 bytes 的应用复制读与写。这里没有把内核缓存命中、SQLite 自动恢复、日志 fsync、备份实现或物理设备传输折成这些应用字节量。

共同参考状态构造、摘要编码／加载、克隆、Python 启动、connect 和部分 native 恢复均未纳入 callback 硬上限。独立 observer PID 与退出码证明新进程实际运行；**应用写服务重启、重试提交、恢复后持续处理业务均未测试**。因此不能声称所有资源成本已支付、全过程可行性或完整 P2 资源合同已获实证验证。

### 新增能力裁决

**相对于同信息、同动作、同费用的强标准基线，新增决策能力为零（本次有限样本与代码规则范围）。** 28 项中决策、完整业务/事务观察和回调数逐项一致。候选是规范化合同的实现，未发明额外恢复机制，也未优于标准参考模型检查。

相对于弱结构与去历史消融的改善，来源是纳入了外部业务／ACK 历史义务。可靠性工程本来可以表达这些义务；本结果不证明 UEOT 超越该领域。可保留的收益是明示语义、未知 ACK 处理、共享观测／费用、有限执行与可审计反例，而非经验普适性或算法创新。

## 12. 后置处理、失败保全与全量交付

`collect_certification.py` 只读取已写出的 JSON、完整返回值和原始文件哈希，不打开数据库。B 为该 runner 和统计脚本的作者，故它不能替代 C 的独立重建。初版后处理曾把仅结构观察也纳入“完整业务状态成员”校验域，产生无意义的假值；原版本及其输出保留在 `exports/B-certification`。第二版只把此诊断范围限定到确实扫描了业务／事务的完整观察，弱结构的成员值为 null，未改任何 trial、原始输出、判决、源或协议，也未重跑实验。最终 compact 在 `exports/B-certification-v2`。

| 已取回包／原始包 | bytes | SHA-256 |
| --- | ---: | --- |
| 认证 compact＋controller／run 原始清单小包 | 90400 | 0ea787ca1b9934ae1c41b7a0be71c6fe45d014601fe88763721a6c3d70477d53 |
| 最终 CERTIFICATION_COMPACT.json | 786170 | c1a8d9b46a41f2f2128a92fe47c26be990b681daf8f31856a295de551aa809d4 |
| B 全量校准＋认证 tar.gz | 5460394 | be5a3ce3987af8dd0163895a630883b831410602a06bf27e236fa84c5311fe46 |
| 同一 tar 的已取回 xz 全量包 | 1193964 | a069a5b728c6574b8436d5fa07f9ebb0a9b9654432de4b25eb3a4715b2ba0533 |
| 完整原文件 manifest | 1708 文件条目 | b9628965ab20d7a67beffb58dff576837be77e317b487bad641603ba8a7004f2 |

全量包保存1708个原始文件、180424669 bytes，覆盖两轮校准与28认证的原始数据库、所有sidecar、每策略副本、旧备份、同H新快照、请求、ACK、完整SQL返回、进程记录、源码、协议、授权及后处理两个版本输出；不把 C 的独立产物混入 B 的执行来源。

Mac `gh api` 上传全量证据 blob 的尝试于13:53:20Z开始、13:54:14Z结束，实际返回 HTTP401 `Bad credentials`、exit1。没有证据表明创建了 blob，未修改任何 branch/ref；失败响应和stderr保留在 `evidence/full/export-receipts`。原上传receipt的scope句描述拟执行动作，不能凌驾其实际exit1／401而声称创建成功。该传输失败不影响认证运行。

随后把同一未压缩 tar 无损转为 xz，经5段 base64导出并于 **13:59:04Z** 在云端合并校验。包 SHA 与 Mac 完全相同，展开后的1708个文件逐长度／SHA-256全部通过，文件集合与原manifest精确相等；包括全部原始数据库和sidecar二进制。此时才可确切说B已在云端取得并重哈希这些二进制。完整包为 `evidence/full/B_RAW_CALIBRATION_AND_CERTIFICATION.tar.xz`，收据为 `evidence/full/RAW_ARCHIVE_TRANSFER_RECEIPT.json`，原字节在 `evidence/full/retrieved`；校验没有打开SQLite数据库或重复执行trial。

## 13. 认证后的 A→B 交叉质询

**A-RESULT-1：** 强标准方法同判、同观察/预算时，是否必须认定没有新增决策能力？弱结构／消融差额是否只能归于标准参考合同检查？

**B 答复：** 接受。两主方法为同一规则的两种写法，本次也没有分歧。成果定位为明确合同和审计执行，不能把其相对弱诊断的差额宣传成超过可靠性工程。源码判决函数、相同公共输入与实际结果链支持这一收窄。

**A-RESULT-2：** 自动 rollback 来自 SQLite，引入 observer 新PID是否不等于业务服务重启？A1 的 db-domain／应用重试等设计想法能否倒灌成已实现？

**B 答复：** 接受。`execute_observer` 仅启动 observer 子命令；所有 `policy/*/execution/process.json` 的 argv 都是打开副本、观察和判读，没有应用服务重启或重试事务。无独立 db-domain 表。不能将A1泛提案或未来能力写成实测行为。

**C 的最终质询：** 28主认证和7新复现能否仅分列；是否明确callback不涵盖父预处理、摘要、克隆、connect/native恢复与物理I/O；compact初版错误是否保留且只重读后处理？

**B 答复：** 三项均接受并据实确认。没有把7复现或后置直接SQL加入28分母；逻辑copy bytes不冒充物理I/O、0callback不冒充0工作。后处理v1和v2的结果域变化可逐代码核对，原实验manifest、源和协议均不变。

### 已实际读回的独立 C 后继

B 已读取 C 的机器回执，复算结果与本报告一致；这是 C 独立执行的证据归属，不能称由 B 代跑或独立审查自己的程序。C 的7项新复现得 **4接受、1拒绝、2未决**，与28主认证的16／4／8分列。C 主认证独立检查28/28无错误，复现7/7无错误；主认证后置直接SQL12个副本、复现后置直接SQL3个副本是验证动作，不增加trial数量。

| C证据文件（相对于 agents/C） | SHA-256 |
| --- | --- |
| CERTIFICATION_INDEPENDENT_CHECK.json | 6a91cb9822a1184f878b06a793857651405c96160557fcd0c2c77b3e4f1442b6 |
| REPLICATION_INDEPENDENT_CHECK.json | 20c621b9d9cac683d78c99d8d0008103a26bdc3ce6643b730a350610e2801b5d |
| C_EXECUTION_RECEIPT.json | ea5d8abb843d4884990a78db014667c42fdabbb770378c279ee9f62e20dc7f1b |
| C_FINAL_COMPACT.json | ca56849650e6ea2aa4583736f1f53a3b01bda949f37f1d4071ce7c6ec4e54687 |

## 14. B 的执行结论

已授权的28项认证已经完整执行，无须补跑或扩大样本。有限故障域内的合同判读、UNKNOWN 允许集、低预算停机、旧备份负对照、W2 实际热回滚以及可重放原件均有真实证据；W1没有热回滚见证、强基线没有增益、资源硬界只覆盖指定callback，这些限制同样构成结论。

本报告支持主审采用 **SUPPORTED_SCOPED 与 EQUIVALENT_NO_ADDED_DECISION_GAIN** 的有限实验定位；本报告已读回的独立 C 结果也与之相容。它不把全局 UEOT 的经验真实性从 UNVERIFIED 升级，不增设 Core 定理、不重开 Lean、不把标准 SQLite 恢复据为 UEOT 新算法。最终解释裁决和仓库采用由主审负责，B不代签。

