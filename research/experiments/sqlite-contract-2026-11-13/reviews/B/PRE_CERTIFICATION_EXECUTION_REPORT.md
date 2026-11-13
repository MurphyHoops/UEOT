# B：SQLite 实际执行报告

记录日期：2026-11-13。当前阶段：**两轮有限校准已完成；最终实现已冻结，等待实际预注册提交和主审放行。认证与 C 复现尚未执行。**

本报告只记录实际发生的动作。新的 SQLite 工作不重开 Core、D3、工具链或既有数学任务；没有运行 Lean。Mac 操作全部通过 Desktop Commander Local Mac，目标是新建专属目录 /Users/murphyhoops/Documents/ueot-sqlite-study-20261113。

## 1. 实现身份与冻结状态

最终文件在本任务 runner 目录：

| 文件 | 字节 | SHA-256 |
| --- | ---: | --- |
| sqlite_study.py | 38046 | bdbe87252da0b107602f7e30509b4b094f53d97a647ac9dc34cb378195dd92d9 |
| protocol.json | 2368 | f68c5e9b643738563eebdce032bf13126e63036b2b473f889840355af5e00566 |
| README.md | 14871 | 2da9b70042ae648bd1926018930ff5b72ffe60d463f74fb7e1586a8394e389f0 |

FINAL_RUNNER_MANIFEST.json 保存该清单。最终 runner 与校准 v2 的 runner 字节相同；最终 protocol 相对于 v2 仅把状态改为 FROZEN_BEFORE_CERTIFICATION。这不是已存在的 Git 预注册 SHA，也不是认证已经通过。认证入口还须收到匹配源/协议 SHA 的实际预注册授权。

固定认证分配为 W1/W2 × 7 场景 × 2 重复，共 28 个重置 trial；C 的独立复现分配为 W2 × 7 场景 × 1，共 7 个新 trial。W1/W2 未用于校准。两者均等待主审给出真实预注册 commit/go。

## 2. 实际环境

校准 worker 的实际输出：

- Python 3.9.6，构建信息为 Mar 6 2026、Clang 21.0.0。
- macOS-26.6.2-arm64-arm-64bit。
- SQLite 版本字符串 3.51.0。
- SQLite source ID：2025-06-12 13:14:41 f0ca7bba1c5e232e5d279fad6338121ab55af0c8c68c84cdfb18ba5114dcaapl。
- Python 二进制 SHA-256：9ea22c79baac7ee6906d807799f351ae5de25b74be3ead66370714ea5348ca9f。
- _sqlite3 模块 SHA-256：c16c8f766c567ec0437814f32b5a2f5a23f266ff603f1cb40cf21d1865e0c8c6。

完整路径、compile_options 和配置在原始环境记录中。该库是 Apple vendor variant，不称纯上游同名发行版。

实际有效 PRAGMA：journal_mode=delete、synchronous=2、foreign_keys=1、page_size=4096、cache_size=5、cache_spill=5、locking_mode=normal、busy_timeout=1000、fullfsync=0。v2 在初始化完成后重做读回，并在 PRECOMMIT 屏障记录实际页数和 cache 设置。环境身份在最终协议中被显式固定，后续不接受静默更换 vendor。

## 3. 校准 v1：七场景，原记录完整保留

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

## 8. 下一步执行门槛

只待：C对最终固定源的审查、主审独立裁决和真实预注册 Git commit，然后按主审准确 SHA/go 运行28个认证trial。C在自己的目录运行7个复现trial并独立计算关键原始结果。

在收到该门槛前，本报告不把认证、独立复现、最终主张支持或仓库采用写成完成。

