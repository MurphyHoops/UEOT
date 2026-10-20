# v31.7 CI 日志解析器审查

**结论：解析器已准备并通过针对实际日志格式的解析测试；v31.7 新远端 CI 尚未验收。**

脚本：`/tmp/qm317_verify_ci_logs.py`。SHA256：`d8725a2382120b6777c48f960a54c05af8bc1fdc6c8740d0226d6f71bdfa03bd`。从实际 v31.6 脚本精确改造，基线脚本 SHA256：`e2b71aff291a62ce5c2f706033e7854088c816553838311bf649bb651a11a243`。所有写入均在 `/tmp`。

## 冻结合同

| 项目 | 要求 | 证据来源 |
|---|---:|---|
| 主包 | 29 模块、646 显式定理、855 审计 | 实际 CI 全名/依赖输出 + 冻结本地清单 |
| 具体见证 | 7 文件、151 审计 | 实际 CI 各文件总结 |
| 具体见证种类 | 110 定理、39 定义、2 缩写 | 实际本地详细回执、源 SHA 绑定 |
| 数值证书 | 6 正例/42 审计、4 真命题损坏证明拒绝、4 同数据假命题证明 | CI 进度和完整总结 |
| 可执行层 | 100 方法、4 示例命令 | CI 实际方法名/命令节与步骤结果 |
| 源清单 | 动态读取；当前为 80 | 最终本地 source-manifest.json |
| CI 直接打印的源 SHA | 33 | 当前 workflow 的 sha256sum 输出 |

当前实际本地冻结集合 SHA256：`b453ce5028eb1ef7d324326245ae5c6cc1a0bf3f40cabf691f25bb1aae7a5911`。80 没有硬编码为解析器合同，未来必须仍与最终 manifest 的真实长度和整个记录源选择精确一致。

## 检查逻辑

1. Actual repository/run/event/attempt and requested commit; exactly two successful jobs; every required gate step actually successful; actual checkout HEAD in both decoded logs.
2. Final dynamic v31.7 source manifest: exact source-recorder path selection, unique safe paths, all SHA256 and byte lengths, canonical source-set digest, local PASS reference agreement, before/after source immutability.
3. 33 actual printed CI SHA256 values (29 modules and four selected entry/configuration paths) exactly equal their accepted source entries; no claim that the full remote source manifest or 56 Core files were directly printed.
4. Official Lean 4.33.1 and full compiler commit; inherited dependency lock emitted PASS; actual positive Lake job count observed, not hard-coded to local 8793.
5. 29-module/646-explicit-theorem inventory bound to manifest source identities; exact 855 audit names and axiom lists equal accepted local map; duplicate names and nonstandard axioms rejected; successful check_axioms.py summary required.
6. Actual 100 successful runtime full method names equal accepted local names, exactly one OK and test total; all four demo command sections plus actual successful steps, with redirected JSON content explicitly outside inspection.
7. Actual exact-certificate progress and complete 6-positive/42-audit plus 4-corrupt-true rejections and 4-same-data-false witnesses summary; no detailed CI certificate artifact inspection implied.
8. Actual seven witness file summaries are exactly 9/30/5/40/20/22/25, total151; accepted local detailed receipt separately proves source-bound 110 theorem/39 def/2 abbrev breakdown. The CI log does not itself print the 151 names or kind split.
9. Actual artifact-finalization output and successful archive steps for both run-specific ZIP names; artifact IDs preserved. Artifact download/contents and remote-tree verification remain false.
10. Failures preserve verification_complete=false and return exit1 with an atomic error receipt; success can only occur at the end of full actual-input validation. No compiler, network or CI launching capability is used.

## 实际解析测试

共 14 项，记录在 `/tmp/qm317_ci_parser_tests.json`。原始 v31.6 远端日志未修改。保留的流程格式、100 个测试、实例总结、4 个命令和实际构建计数可以解析；旧 573 项主审计、4 份见证、26 项打印源分别被新合同拒绝。另以实际本地 855 项公理日志和 checker 输出测试逐名比较，以最终实际本地 80 源/七见证回执测试动态绑定。两项故意无效的内存内变体检查必需步骤缺失和重复公理名字，均明确标为解析器负控。

完整 CLI 负控只输入原始旧 PR 的实际 run/jobs/logs，结果 `/tmp/qm317_ci_parser_legacy_rejection.json` 为 FAIL，退出码 1，原因是旧日志只打印 26 个源 SHA。这个 FAIL 是预期拒绝，不是新 CI 执行失败。未构造任何新 CI 成功记录。

## 执行入口

待 root 已获得实际远端日志后，用现有兼容参数执行：`--kind pr|main --run <实际运行ID> --commit <实际40位SHA> --repo-root <v31.7工作区> --ci-dir <实际日志目录> --output <验收回执路径>`。输入命名仍是 `<kind>-<run>-run.json`、`-jobs.json`、`-runtime.log`、`-lean.log`。

## 不应扩大解释的范围

- No v31.7 remote CI logs have been supplied to this review; no new successful CI acceptance receipt exists or is inferred from these parser tests.
- An actual prior v31.6 successful run was deliberately presented to the new parser; it is rejected for26 rather than33 printed source hashes after all current local references are checked. Component tests additionally reject573 rather than855 main reports and four rather than seven witness summaries.
- CI artifact ZIP files, redirected demo JSON, detailed witness/certificate receipts, and CI source-manifest JSON are not downloaded or parsed. Local detailed receipts are inspected only as local accepted references.
- The separate remote-source-reconciliation must bind all80 scientific sources, the56 Core import sources and publication bytes by actual remote Git blobs. This parser does not assert entire-tree equality or remote Core source equality.
- Counts are declarations/audits/executable checks, not a count of physical laws. full_scientific_theory_verified remains false on every receipt.
- All new files are under/tmp. No repo source, Lean input, README, CI workflow, PDF or Markdown monograph was modified by this parser task. Archive Python source as.py.txt under kernel evidence to avoid changing the source-recorder selection.

本审查没有运行 Lean、编译、远端 API、CI 或产物下载，也没有改写已有执行回执。
