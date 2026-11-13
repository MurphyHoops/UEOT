# 原始证据、离线重算与真实重跑入口

本目录的预注册提交为 `26902c25152ca3676b4844d2156f028145f62fe2`。本页给出三种不同操作：核验交付字节、重算已有数据、在固定运行时重新执行。前两项不会增加SQLite故障试验数。

## 1. 完整原始包

| 包 | 压缩字节 | 原始payload | SHA-256 |
|---|---:|---:|---|
| [B_RAW_CALIBRATION_AND_CERTIFICATION.tar.xz](raw/B_RAW_CALIBRATION_AND_CERTIFICATION.tar.xz) | 1,193,964 | 1,708文件，180,424,669字节 | a069a5b728c6574b8436d5fa07f9ebb0a9b9654432de4b25eb3a4715b2ba0533 |
| [C_ALL_ARTIFACTS.tar.xz](raw/C_ALL_ARTIFACTS.tar.xz) | 781,176 | 370文件，71,477,776字节 | ccad7253e193ccc0be930ced92543d4e6f2f101bd4d8616fba51a75394e071b7 |

包内另各有manifest自身，所以上表payload数不包含该manifest。包记录全部原始DB、journal、策略克隆、日志和完整返回值，而非仅保存文件哈希。它们是已有gzip/ZIP原件的无损xz封装；没有丢弃失败、修改数据或将额外分析当成实验。

B包含9项校准、唯一28项认证及各自源码/协议/授权、同H当前快照、后处理v1/v2。C包含7项新复现及其源、独立计算、直接克隆SQL读和执行日志。终稿、后置质询和最后采用回执产生较晚，位于本目录的reviews/evidence/adjudication中，不能声称已经存在于先导出的原始包内。

## 2. 首先只核验字节

从本研究目录执行：

```sh
python3 verification/verify_and_extract_archives.py
```

脚本检查两个压缩包、manifest哈希、精确成员集合，以及全部2,078个payload的长度和SHA-256；拒绝重复名、绝对路径、父目录逃逸、链接及非普通文件。它不连接SQLite、不修改原件。期望 `PASS_DELIVERED_BYTES`。首次实际交付核验见 [回执](evidence/DELIVERED_ARCHIVE_VERIFICATION.json)。

## 3. 新目录解包并离线重算

下面的 `replay-evidence` 和结果文件必须尚不存在；原件和旧结果不覆盖。

```sh
python3 verification/verify_and_extract_archives.py --extract-to replay-evidence --receipt archive-check.json
python3 verification/c_independent_check.py --root replay-evidence/B/certification/run-v1 --out certification-recheck.json --preregistration-commit 26902c25152ca3676b4844d2156f028145f62fe2
python3 verification/c_independent_check.py --root replay-evidence/C/replication/run-v1 --out replication-recheck.json --preregistration-commit 26902c25152ca3676b4844d2156f028145f62fe2
python3 verification/main_independent_analysis_v2.py --root replay-evidence/B/certification/run-v1 --allocation RUN_ALLOCATION.json --out main-recheck.json
```

C检查器不导入B运行器，从实际请求/ACK/门控及完整数据值重建允许状态。前两次数据复算应分别核1261、315个清单文件，得到28/28、7/7，无global errors；决策分布分别16/4/8、4/1/2。主审v2是另一份独立实现；其v1和四个错误解析记录仅供审查错误链，不用于最终结果。

主审已在取回完整包后实际执行上述字节核验及两个C离线入口，记录在 [交付重放回执](evidence/DELIVERED_OFFLINE_REPLAY_RECEIPT.json)。这是同一数据的云端再分析，既不是新的SQLite故障样本，也不是外部操作者复现。

## 4. 直接查库时的对象纪律

首次open可能自动回滚并删除hot journal。必须先把某一trial的整个 `postfault_raw`（DB及全部sidecar）复制到新的独占目录，再查询；不打开或修复原件。不同策略各用新克隆。STALE的对应当前态在同一trial的 `pre_replacement_current`；不能拿另一个run的NORMAL库代替。

C实际使用的后置直接读源码为 [c_direct_snapshot_read_v2.py](verification/c_direct_snapshot_read_v2.py)。它会创建新目录和新克隆；其运行记录在C原始包。它是对既有文件的额外SQL查询，不能增加主认证分母。若换了运行时，新的读取结果必须保留其实际运行时身份，不默认为原Mac字节完全相同的复现。

## 5. 固定运行时的真实执行重放

实际目标是Apple Python 3.9.6所链接的vendor SQLite 3.51.0，源码ID、Python和_sqlite3二进制哈希及编译选项在 `runner/protocol.json` 固定。DELETE/FULL有效值由worker及完成观察的连接读回；预算0/32的未完成检查须保持未决。其他平台/版本可以离线核数据，但会被这个实验的源身份门拒绝，不能静默去掉pin后仍称同一认证。

在具备该运行时且只使用新测试目录时，原认证命令为：

```sh
/Library/Developer/CommandLineTools/usr/bin/python3 runner/sqlite_study.py run --split certification --protocol runner/protocol.json --out NEW_CERTIFICATION_REPLAY --authorization evidence/CERTIFICATION_AUTHORIZATION.json
```

C原复现使用 `--split replication` 和另一个新输出目录。历史授权绑定真实预注册SHA及准确源哈希；本任务已经完成，本文不会自动启动新的试验。一次后继重放属于新的执行记录，不能回填本次28或7项；确定性ID分配仍然相同，因此尤其要保留新的运行目录和时点。

首次预注册的runner README、protocol及审查书保持原字节，其中“认证尚未执行”是准确历史状态。当前结果看 [综合稿](SQLITE_CONTRACT_STUDY_REPORT.zh-CN.md)、[实际执行报告](results/EXECUTION_REPORT.md)和 [完成台账](ADOPTION_AND_COMPLETION_LEDGER.md)。

## 6. 停止和解释边界

没有需要为这次无增益结果再跑的核心试验。新设备、WAL、断电、并发写者、主动恢复或受更强物理预算的任务，需有新的实际需求及独立注册；它们没有被本研究顺带验证。保持UNKNOWN、有限允许集合、共享信任和逻辑费用口径。全局自然经验UNVERIFIED和人类评议状态不随重放次数自动改变。
