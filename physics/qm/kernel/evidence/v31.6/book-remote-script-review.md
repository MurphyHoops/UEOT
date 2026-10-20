# v3.2 书稿远端元数据脚本互审

**只读源码审查 PASS。** 最终绑定 `/tmp/qm316_finalize_book_remote.py`，SHA-256 `b2a039bf445797348245669abb7685c3dc44192da042cb0d5150311091d72f8e`。与根脚本 `8238c5e4fe1e1b6dcdac3bdc495d20eb52ad6bc5f19d5ac64af6c73f0b2378e6` 的字段接口一致。审查时 main 状态仍为 `PENDING`；这份审查不是实际执行通过回执，也没有代替源码 PR／主线 CI。

本审查完整阅读了两个脚本及当前书稿 metadata，进行 AST 与哈希引用分析，没有执行 book prepare/--apply、修改仓库或运行 Lean、测试、排印与视觉检查。

## 1. 门与写范围

脚本必须先取得实际双 PASS context、与其精确一致的 root integration、真实 PR/main CI 回执；source commit/tree、库、PR、run、源集、70 输入、56 Core 导入和三正文都明确绑定。整树 bool 由实际 ID 比较产生，可以为 false；它不替代实际受验文件相等。

`prepare()` 没有写点。默认模式只准备；唯一写循环位于 `--apply`、完整门检查及所有保护对象和原 metadata 并发比较之后。仅允许以下十项：

- `physics/qm/book/SOURCE_MANIFEST.json`
- `physics/qm/book/CHAPTER_DOSSIER.json`
- `physics/qm/book/README.md`
- `physics/qm/book/evidence/v3.2/source-assembly.json`
- `physics/qm/book/evidence/v3.2/dossier-review.json`
- `physics/qm/book/evidence/v3.2/dossier-review.md`
- `physics/qm/book/evidence/v3.2/local-release-gates.json`
- `physics/qm/book/evidence/v3.2/metadata-update-review.json`
- `physics/qm/book/evidence/v3.2/remote-release-binding.json`
- `physics/qm/book/evidence/v3.2/archive-manifest.json`

非目标书稿文件、70 科学输入、56 Core 输入、三个正式正文、原始本地执行及视觉回执均作保护对象。异常输出区别零写入拒绝与写入后失败，不能把部分写入误报为没有发生。

## 2. 哈希引用顺序

固定的核 integration／CI／本地执行回执先进入 `remote-release-binding.json`。随后更新书稿 SOURCE_MANIFEST、source-assembly、dossier-review，再将它们的最终哈希写入 CHAPTER_DOSSIER。最后生成 local-release-gates、metadata-update-review 和 archive-manifest。

原 archive 有 36 个成员；只新增 remote-release-binding，预期成员为 37，archive 自身不入清单。`prior_dossier_sha256`、旧 manifest SHA 及原 review 的历史哈希保持历史意义，不追写为当前哈希。没有要求生成包含自身的当前 hash，亦未把未来 metadata commit 当成已经跑过科学 CI 的提交。

## 3. 已修正问题

1. root integration 缺少 `repository` 导致 book 硬门不匹配；root 最终版已补齐。
2. 原“所有原 review 文件不变”布尔字段范围过宽，实际会更新 dossier-review.json/md。现已分为历史档案及原 PDF/视觉回执字节不变，以及 dossier review 原科学字段保留，并对计数、来源、正文切片、绑定、范围等增加相等断言。
3. 全局下一轮记录现指向 v31.7 三路合同：A 操作／纯化接口及复量子正例，B 记录与量子记忆，C 当前模型精确条件态动力学。旧对象完整保留；v31.7 仍标为审定待执行，不能计入 v31.6。
4. 出错信息现在通过写入计数准确区分前置拒绝和后置读回失败。

## 4. 保留的历史和科学责任

`edition_history`、11 份原材料身份、旧来源、原 `validation.local_checkpoint_status`、`exists_at_dossier_assembly=false` 以及所有章节正文／结果／历史字段均保留。当前路径表根据实际存在的根回执和本次精确准备文件刷新；“文件存在”仍不等于“该旧材料在本版重执行”。

MAIN_VERIFIED 只提升本版实际发布与验收身份；不会把全书物理完成、无条件复量子选择、现实三代、一般谱存在或无限条件化升级为已证。README 对当前 globalv31.7 规划的澄清不改 canonicalMD/PDF/TeX，也不构成重排印。

最终执行顺序应为：主线 CI 实际结束并被验收 → root 固定 integration → B 准备与应用 metadata → root 以最新 main tree 发布这些准确字节。任何上下文或原件不匹配都应保留当前拒绝结果并修正身份来源，不绕过门。
