# v31.6 CI 日志核验脚本合同

状态：**已准备并完成格式/拒绝控制检查；作者未执行最终 CI verifier 入口。**

脚本：`/tmp/qm316_verify_ci_logs.py`  
SHA256：`e2b71aff291a62ce5c2f706033e7854088c816553838311bf649bb651a11a243`  
字节数：23407

## 调用与输入

```bash
python3 /tmp/qm316_verify_ci_logs.py --kind pr --run 39380741012 --commit 00bf88231328c09b9af58d0ff3c8eec977d73c53
```

默认读取新工作树 `physics/qm/kernel/evidence/v31.6/ci/` 下同一前缀的 `run.json`、`jobs.json`、`lean.log`、`runtime.log`；主干验收改用 `--kind main` 及实际 run/commit。默认输出同前缀 `verification.json`。支持 `--repo-root`、`--ci-dir`、`--output`，兼容旧脚本的三个必填参数。

保留 root finalizer 的字段：`status`、`run_id`、`source_commit`、`generic_axiom_reports`、`runtime_test_methods`、`finite_witness_total_audits`、`build_jobs`。

## PASS 必要条件

1. Actual workflow run is completed/success; correct run id, commit, workflow path and PR/main event; main receipts require main branch push.
2. Exactly runtime and lean jobs, unique IDs/names; completed/success; every required step completed/success. Nonrequired housekeeping steps may be skipped. Required gates never may.
3. Each actual decoded log identifies its job and records the exact commit immediately after git log -1 --format=%H; uploads finalized for the same run id.
4. Frozen local manifest contains 70 unchanged inputs and source-set SHA256 8a2cea35e060f5341f5672534d0717c605f5c441d998a08cc7677fb50a113115. The CI record-source step prints 26 hashes, each exactly equal to the corresponding local manifest hash.
5. Actual installer output identifies official Lean 4.33.1 / commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
6. The actual lake build UEOTQM execution section contains one successful build summary with a positive number of jobs. Record observed jobs dynamically, with no equality requirement to local 8786.
7. 573 unique actual Lean axiom reports equal the accepted local complete name-to-axiom map. Compare all names and sorted dependency lists, not just totals. All 459 explicit theorem names from the reviewed 22-module inventory occur in that exact audited set. Duplicate/extra/missing/changed/unreviewed axiom reports fail.
8. 100 actual verbose unittest method successes match the 100 locally accepted method names; require Ran 100 tests and one OK result.
9. All four demo commands have actual Run sections and successful job-step metadata.
10. Exact-export gate emitted one parseable JSON PASS summary with no problems, exact 6/42 positive and 4 rejected true plus 4 accepted false/4 audits counts, and all actual named case progress lines.
11. Retained finite/quantum gate has the new required step name and exactly four PASS summaries 9/30/5/40 plus final gate PASS.
12. Both archive steps succeeded and upload-finalization log messages identify the requested run. Supplied inputs remain unchanged during this verifier execution.

## 证据范围

The 573 generic axiom reports and 100 runtime method names are directly parsed in full from actual job logs.

Four witness audit totals and exact-certificate audit totals are checked from actual gate summary output and successful step metadata; per-declaration details for these gates are captured by their subprocesses into artifacts and are not printed in job logs.

artifact_zip_downloaded=false and artifact_zip_contents_verified=false are explicit. Redirected demo JSON payloads are not parsed.

The 70-input check is local accepted-source identity, while 26 CI-printed hashes are checked directly. Complete remote tree/source reconciliation remains a separate root audit.

The CI artifact detailed 79 source/olean bindings and 56 Core dependencies are not independently parsed here; do not promote local records or successful gate summaries to a downloaded-artifact audit.

Preparation/parser smoke is not final CI acceptance. No main verifier entrypoint, Lean, remote call, or repository write was performed by this author during preparation.

## 已完成的准备检查

已用 root 下载的实际 PR 日志做纯解析格式核对：读得573条主公理报告、100个成功运行方法、四见证9/30/5/40、实例6/42及4/4；真实包构建任务数读得8786。完整 verifier 入口仍交 root 执行，未在仓库生成 verification 回执。

五个拒绝控制均被拒绝：未完成 job、被跳过的必需量子见证门、重复公理报告、缺失构建成功输出、缺少新增实量子见证。另用明确标注为合成的9001任务字符串确认动态计数不依赖8786。控制只检验解析和拒绝行为，不代表额外科学结果。

详细准备记录：`/tmp/qm316_ci_parser_smoke.json`。如 root 归档脚本到 kernel evidence，请使用 `.py.txt`，避免新增 `.py` 改变冻结的70源输入。
