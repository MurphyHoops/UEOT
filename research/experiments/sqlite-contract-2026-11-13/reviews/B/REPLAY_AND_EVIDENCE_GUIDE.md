# B 原始证据、版本与重放入口

本目录属于实际预注册 `26902c25152ca3676b4844d2156f028145f62fe2` 的后继执行交付。认证只运行一次28项；校准7+2项和C独立复现7项分开记账。本文不授权或自动启动新的实验。

## 1. 首先核验完整原件

交付包为 `evidence/full/B_RAW_CALIBRATION_AND_CERTIFICATION.tar.xz`，1,193,964 bytes，SHA-256：

    a069a5b728c6574b8436d5fa07f9ebb0a9b9654432de4b25eb3a4715b2ba0533

可用标准Python只读复核全部文件，既不解压到原实验目录，也不打开数据库：

    python3 verify_raw_archive.py evidence/full/B_RAW_CALIBRATION_AND_CERTIFICATION.tar.xz

清单应包含1708个原文件、180424669 bytes，另有一份清单自身。云端已完成同等字节验证的实际回执为 `evidence/full/RAW_ARCHIVE_TRANSFER_RECEIPT.json`；本脚本是可复用入口，不把后来运行它冒称原认证。

## 2. 包内目录与历史版本

- `calibration/run-v1`：7项最初校准，含冷journal负证据及当时未保存D_new的限制。
- `calibration/run-v2`：2项有限校准，含实际热日志见证和D_new完整快照。
- `certification/run-v1`：唯一28项预注册认证，含全部原始数据库、sidecar、观察克隆、请求、ACK、完整返回行和清单。
- `runner/calibration-v1`、`runner/calibration-v2`：各自真实运行的源与协议。
- `runner/preregistered-26902c25`：最终实际运行的源、最终协议、真实授权、分配和预注册文本。
- `exports/B-certification`：后处理初版，保留将弱结构观察误置于全业务成员检查域的错误。
- `exports/B-certification-v2`：只收窄该后处理诊断域后的最终compact；实验未重跑，原字节未变。

包内最终runner的README及预注册报告仍写着“认证尚未执行”，因为它们是**执行前冻结文件**，应当保留其原字节。现行执行状态以本目录 `EXECUTION_REPORT.md`、真实controller receipt和最终原始结果为准。

Mac `gh` 上传失败的401响应、stderr和真实receipt在 `evidence/full/export-receipts`，单独保存，不倒写进此前冻结的原始包。`FIRST_START_TRANSPORT_ERROR.json`保存启动前的一次工具初始化错误；随后唯一控制脚本执行有真实开始/结束记录。没有认证重跑或删除失败trial。

## 3. 数据复算与实际执行重放的区别

无需再次运行数据库，即可从每trial的 `oracle/initial.json`、`requests.json`、`ack_events.json`及 `parent-events.jsonl`独立重建允许状态；用 `policy/*/execution/result.json`中的完整business/transactions逐值比较，不只信任摘要或最终判决。C使用自己编写的计算器进行了这项独立复核，来源在 `agents/C` 的报告和机器回执。

直接查询数据库时，必须先从同一 `postfault_raw` **完整复制数据库和所有sidecar** 到新目录；首次open可能自动恢复，不能先改原件，也不能让后一策略读到前一策略恢复后的对象。STALE的同合同新态在 `pre_replacement_current`，不能用不同trial的NORMAL代替。

实际执行的原命令在 `certification/v1-controller-receipt.json` 的argv。若另获独立重放授权，应使用包内固定源、固定最终协议、记录的Apple Python/SQLite二进制和**新的输出目录**，保持原认证结果不变：

    /Library/Developer/CommandLineTools/usr/bin/python3 runner/preregistered-26902c25/sqlite_study.py run --split certification --protocol runner/preregistered-26902c25/protocol.json --out NEW_REPLAY_DIRECTORY --authorization runner/preregistered-26902c25/CERTIFICATION_AUTHORIZATION.json

这会重新生成同一确定性分配的独立数据库，属于后继重放，不是新发现的原认证样本。环境字节固定检查失败必须保留失败，不能静默更换vendor、修改协议或绕开检查后仍称同一认证。

## 4. 应保留的结论边界

UNKNOWN仍为UNKNOWN；接受只认证当前态在允许集合内。callback预算不涵盖全部预处理、复制、连接/native恢复与物理I/O；0回调不是0工作。W1两次PRECOMMIT冷journal，W2两次有实际热回滚链。候选与强标准基线没有新增决策或回调成本优势；SQLite自身执行恢复，未测试应用服务重启。源码/协议保持预注册字节，不需新增Lean或扩大Core。
