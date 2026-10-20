# UEOT-QM v31.6 发布库存只读审查

**结论：** 旧 `/tmp/qm315_prepare_upload.py` 不应原样用作本轮发布清单。应从最新远端父树出发，对明确允许的 QM 路径逐文件比较实际 Git blob 与 mode；本地历史 Git status 只用于发现文件，不能定义本轮增量。

本审查只读取文件、Git 状态和已完成的验收记录；没有修改仓库、重跑 Lean/runtime、读取或操作远端、建立分支或提交。机器可读报告为 `/tmp/qm316_upload_inventory_review.json`，候选路径和历史保护路径分别为 `/tmp/qm316_upload_candidate_paths.txt`、`/tmp/qm316_upload_protected_history_paths.txt`。

## 1. 三种身份不得互换

| 身份 | 实际值 | 发布用途 |
|---|---|---|
| 本地历史 checkout HEAD | `97d033ff83125822e9926f5bd36afd08dbd153ef` | 仅说明本地 Git 历史；不是当前科学源基线 |
| 已发布科学基线 | `427f512745ca70f82cba6a1388edcab904da8a42` | 当前导入闭包与 Lean 验收记录明确登记的研究基线 |
| root 最近报告的远端 main | `a7aa2f559e8bc3f5dfaabe7cc70fd212de5d5bd5` | 发布前仍由 root 重新获取最新身份并作为完整父树；本审查没有远端复读 |

已读本轮最终 source manifest：**70** 源输入，`source_set_sha256 = 8a2cea35e060f5341f5672534d0717c605f5c441d998a08cc7677fb50a113115`。当前 Core 闭包记录 **56** 个实际导入源模块。发布文件数、源码输入数、导入闭包大小和公理目标数是不同统计。

## 2. 准确排除与保护规则

允许作为 QM 上传候选的范围只有：

```text
formalization/ueot-qm/**
physics/qm/**
.github/workflows/ueot-qm.yml
```

以下是本地构建/缓存，排除上传；排除不意味着删除远端对象：

```text
任何路径组件为 .lake 的目录及内容
任何路径组件为 __pycache__ 的目录及内容
任何路径组件为 .git 的目录及内容
*.pyc
*.pyo
formalization/ueot-qm/axiom-audit.log
formalization/ueot-qm/proof-axioms.json
```

最后两项仅排除**包根目录的重复副本**。已经逐字节核对，它们分别与以下应保留的正式证据副本一致：

```text
physics/qm/kernel/evidence/v31.6/axiom-audit.log
physics/qm/kernel/evidence/v31.6/proof-axioms.json
```

当前实际观察到两项非 QM 变更，必须保持最新远端版本，不进入此次 QM 上传，也不能用本地版本覆盖：

```text
.github/workflows/ueot-core-compression.yml
formalization/ueot-core/docs/compression/COMPRESSION_RESEARCH_TRACKS.json
```

同样保护其余 `formalization/ueot-core/**`、其他工作流及不在白名单中的远端工作。当前 Core 源只是被 QM 验证消费；不能因为本地编译产生了新 Core 产物而把它们纳入发布。远端父树若包含修改过的实际导入源，root 应对照 56 项闭包身份处理那个具体差异，同时保留其他 Core 工作。

## 3. 应保留的非源码成果

**保留 `physics/qm/kernel/evidence/v31.6/**` 的实际验收与审查材料。** 当前快照包括统一构建和公理原始日志/receipt、70 源身份及前后冻结记录、依赖和 Core 导入闭包、四见证的实际日志与 84 项报告、runtime/四 demo 输出、六份生成证书及其 manifest/42 项日志、四组损坏真检查失败和对应 false 检查的源与日志、三路 focused 报告和互审、发布元数据生成/审查材料。不能统一删除 `.log`、`.json` 或生成 `.lean`。

有意保存的 `focused/*/history/`、资源限制记录、旧失败编译和初始元数据审查仍应保留在历史标签下。它们的作用是解释过程，**不能改标为最终 PASS**。当前 `acceptance-progress.json` 已为 PASS，记录 8786 jobs、573 审计及本轮 source set；不再是运行中占位。

**保留正式著作的 PDF 和 TeX：**

```text
physics/qm/book/UEOT_PHYSICS.pdf
physics/qm/book/UEOT_PHYSICS.tex
```

它们是正式交付，不是应丢弃的编译缓存。连同当前 Markdown、CHAPTER_DOSSIER、SOURCE_MANIFEST、README，以及 `physics/qm/book/evidence/v3.2/**` 的结构/排版/视觉审查、XeLaTeX 日志与归档清单一起保留。书稿归档清单的 36 条身份包含 6 个书稿顶层交付和 30 个证据文件；manifest 自身额外保留，不能把目录内 31 个文件误认为缺少 6 项。

**不要排除整个 `book/build/`。** 当前其中只有这四个应保留的构建源文件，没有观察到未归档的 `.aux/.toc/.out` 产物：

```text
physics/qm/book/build/build_pdf.py
physics/qm/book/build/verify_book.py
physics/qm/book/build/header.tex
physics/qm/book/build/tables.lua
```

当前非 UTF-8 上传候选只有正式 PDF，应按二进制 base64 编码；其余已枚举候选均可 UTF-8 解码。

## 4. 历史内容如何处理

`physics/qm/kernel/evidence/v31.5/**` 及更早版本、`physics/qm/book/evidence/v3.1/**` 及更早版本，以及旧版顶层执行/内核报告、旧版 claim ledger 和 audit 报告，应保持远端既有对象。不能因为它们相对于本地 HEAD97d 显示 untracked 就作为 v31.6 新证据重新上传、改写或迁移。完整保护路径清单见 companion 文件。

这条规则**不适用**于本轮有明确来源的 `v3.2/prior-3.1/`、`v3.2/preacceptance/`、`v3.2/visual-history/` 和 `v31.6/focused/*/history/`。这些是本轮审计特意保存的历史快照，继续保留在各自标签中。

也不能按文件名里的旧版本字串一律删除。以下是仍在实际源合同中的活跃基线输入，上传与否只能由相对最新远端的 blob 差异决定：`Cesaro.lean`、`Mixture.lean`、`Survival.lean`、两个旧见证、`demo_v315.py`、`finite_dynamics.py`、`test_finite_dynamics.py` 与 runtime `__init__.py`。同理，`kernel/certificates/v31.3/` 仍是当前证书门使用的输入，不应因目录版本旧而排除。

## 5. 旧脚本的具体局限

旧脚本硬编码 `qm_v315_work` 和 qm315 输出名。它以本地 `git status --porcelain -z` 为唯一入口，递归展开整个 untracked 目录，并在任何非 QM authoring 路径上报错。本次两个 Core 相关修改会直接触发该错误。正确处理是明确保护它们，不是把上传范围扩大到所有 Git 变更。

它计算 Git blob SHA 的方法可继续复用，但缺少“与最新远端树比较、保留父树其余内容”的步骤。它还把本地旧 index 的 mode 当作来源；现有远端文件应以实际父树 mode 为准。当前状态没有重命名或删除；旧 NUL 解析并未正确处理重命名的第二个路径，也没有删除语义。因此不能把未选中的本地文件解释为远端删除。

## 6. 当前库存快照与 root 最后步骤

快照时间：`2026-10-20T05:46:57.292861+00:00`。当时 Git status 有 **1023** 项：

| 分类 | 数量 |
|---|---:|
| 非QM工作，保护远端 | 2 |
| 允许候选，待远端逐路径比较 | 219 |
| 编译/Python缓存，排除 | 666 |
| 包根目录重复公理输出，排除 | 2 |
| 旧版记录，保护远端 | 134 |

不以 Git status 作为权威、直接枚举白名单目录后，得到 **294** 个允许比较的候选文件，其中当前 QM 证据 **146**、当前书稿证据 **31**、正式 PDF/TeX **2**、源码/文档/活跃基线输入 **115**。**294 不是应提交的增量数量**：相同远端 blob 必须省略，并在完整父树中保留。

root 的最终流程应是：重新取得远端 main 的实际父提交和完整树；对允许候选逐路径比较 Git blob 与 mode；只添加明确的新文件或不同字节；保留所有其他远端路径；最后生成实际提交与发布库存。源清单、书稿与发布元数据仍在本地收尾中，因此提交前应重新枚举一次，不能把本报告的临时文件数当作冻结发布数。

不需要为了这个文件库存任务重跑已经完成的科学验收。最终发布证据继续区分 LOCAL PASS、source PR 验收和 resulting-main 验收；本地 HEAD97d 不能填入这两种远端身份。
