# 双语出版3.7元数据更新脚本交付

## 目的与实际准备状态

`update_publication_metadata.py` 只维护《UEOT物理学》的出版元数据，不修改物理核、Lean、数学/哲学书、正文、TeX、PDF、旧证据或科学主张对象。它读取已经安装的文件及既有回执，先生成 `SOURCE_MANIFEST.json`，再让 `CHAPTER_DOSSIER.json` 绑定其实际 SHA256，最后写独立更新回执。

A已经用正式冻结双稿和现已安装的四份TeX/PDF作隔离预览。两份PDF构建回执的实际 MD/TeX/PDF 哈希、三次零退出编译、67章/6附录、零排版/重跑警告及最终辅助文件一致性检查均通过。首次预览时唯一未就绪项目是主编尚在完成的 `evidence/v3.7/pdf-visual-review.json`，当时如实记为PENDING。随后该实际回执已经就绪，最新隔离运行得到 **PREVIEW_READY，pending_gates为空**；两份build及视觉身份均通过。A仍未更新正式元数据，也没有声称自己执行页面视觉。

隔离候选位于 `metadata-preview/`，仅用于查看结构，不应直接复制为最终文件。现在可由主编在正式目录执行脚本，让它重新读取最终实际身份。当前脚本与负向保护检查的哈希在 `METADATA_UPDATE_GUARD_CHECK.json`；最终科学A交付清单是更早独立交付，不包含本次新增的元数据工具。

## 建议执行方法

将脚本安装到仓库 `physics/qm/book/build/update_publication_metadata.py`，在仓库根目录执行：

```bash
python3 physics/qm/book/build/update_publication_metadata.py \
  --book-dir physics/qm/book \
  --expected-zh-sha256 fd651a93cc4f38b755409f184bab231c43e889f648efda852340f8b594fb9060 \
  --expected-en-sha256 437d4239be7a4239e701b760af1fcccdaf30f5b7ab976e9703c532990acb9a91 \
  --write
```

若先预览，去掉 `--write`。不带写入选项时只核对并输出摘要；也可用 `--output-dir /明确的隔离目录` 将候选两份JSON和预览回执写到其他目录。不能用 `--output-dir` 指向正式book目录来绕过安装检查。

正式写入模式要求所有实际资产和下列三份回执完整匹配：

- `evidence/v3.7/pdf-zh/pdf-build.json`
- `evidence/v3.7/pdf-en/pdf-build.json`
- `evidence/v3.7/pdf-visual-review.json`

前两份按当前 `build_pdf.py` 的v2结构读取。视觉回执按主编给定结构读取：顶层 `status` 可为 `PASS_WITH_STATED_SCOPE`；`editions.zh` 和 `editions.en` 各含 `pdf_sha256`、`source_sha256`、`pages`、`overview_pages_viewed`、`selected_full_pages_viewed`，另保留 `reviewer_reports` 和 `scope`。脚本只核对记录与文件身份，不声称自己看过页面或证明像素继承。

脚本从 Git **只读**取得固定基线 `925e3a8a411c0b1bab99dd9150bf005893656140` 的材料；不fetch、不切分支、不运行科学核。两份3.6快照必须逐字节等于该基线的相应JSON。`--baseline-commit` 仅供明确的后续维护，不应拿其他版本绕过本轮冻结身份。

## 严格保持的对象

以下内容作完整JSON值比较，包括全部旧状态和嵌套字段：

| 对象 | 保持要求 |
|---|---|
| 173个 `numbered_results` 对象 | 内容、顺序、历史来源、proof/empirical责任和旧状态全部原样保留；不在对象内部塞入英文标题。 |
| 12个 manifest `entries` 对象 | 完整保留；英文发行信息放在独立出版层，不重写原文献对象。 |
| `source_catalog` | 科学内容和历史状态完整保留。 |
| 科学身份及库存 | `current_code_identity`、科学manifest、remote code身份、verified inventory、Core边界等保留原对象。 |
| 历史完整档案 | `dossier-prior-v3.6.json` 和 `source-manifest-prior-v3.6.json` 不修改，并逐字节与固定Git基线核对。 |
| 第D附录程序 | 原3个Python围栏内payload，在最终中英文与原3.6中文之间逐字节相等。 |

改变任一结果对象、文献entry或source_catalog内容会立即阻断。`METADATA_UPDATE_GUARD_CHECK.json` 记录了实际执行的三个负向控制，均成功阻断对应篡改；另核查了预览中全部173对象、12entry、source_catalog及manifest→dossier身份绑定。

## 出版字段的更新及历史保存

顶层版本更新为3.7；当前正文身份读取实际文件。出版修订继承173项结果，新增科学结果数为0；研究3.6新增的12项仍保留其原 `origin` 和历史库存。

所有67章与6附录均按“稳定锚点起，至下一章/附录锚点前；最后附录至EOF”的原样UTF-8规则重算中文SHA和bytes。中文 `sections` 更新为实际二级编号标题；英文对应记录完整切片身份、标题、同序节号及结果标题。英文对应位于 `publication_3_7`，不修改科学结果对象。

旧的正文hash、节目录、`current_edition_action` 和 `current_edition_verification` 在每行 `body_revision_history` 中保存，并指向完整3.6快照。其它科学字段逐项保持不变。新的验证语义明确只验证出版文本与对应，不重新声明科学证明。

顶层被替换的canonical、derivatives、validation、release_acceptance等旧字段在 `publication_revision.prior_current_fields` 中完整保存。原edition_history保留并追加3.6档案入口。旧的状态字段、旧757/1123计数不会因本次元数据更新被改写成当前新执行。

当前六份Markdown/TeX/PDF均读取实际SHA和bytes；只有build回执与三种资产逐一匹配时，派生文件才获得当前source绑定。英文派生文件放入 `derivatives.english`，原中文 `derivatives.pdf` / `derivatives.latex` 路径保持兼容。

正式 `book/review` 内的报告读取**实际集成字节**。A原交付manifest仍是交付时身份，不用来错误要求相对链接适配后的矩阵保持原SHA。`review-integration.json` 和当前出版检查回执如存在，也从正式路径读取；不复制旧的临时目录身份作为当前报告身份。

## 科学验收与新出版状态分离

- v31.10科学来源保留 `MAIN_VERIFIED`；研究库存49模块、959显式定理、1285命名请求、19语义/数值控制、95精确检查来自既有受验对象。
- 本出版没有重新运行重型科学检查。757属于三个继承程序的历史3.0执行；1123属于v31.9命名请求前缀；不能覆盖当前1285总量。
- 新双语出版的 `remote_publication` 和顶层当前发布阶段始终为PENDING，PR/提交/CI身份不猜测。
- 如果以后这个出版层已经登记PR或CI身份，脚本拒绝把它清空或降回PENDING。届时需专门的远端状态更新，不能把本预PR工具当作覆盖器。

`legacy_program_reuse.appendix_d_exact_bytes_unchanged` 在本版收窄为实际判断，当前为false；新增 `program_blocks_exact_bytes_unchanged=true` 明确仅三个程序payload保真。周围散文确有编辑，旧整篇D不变的3.6断言仍在历史对象里，不冒称当前条件。

## 哈希方向与执行顺序

固定方向是：

`实际MD/TeX/PDF、独立build/visual回执、旧完整快照 → SOURCE_MANIFEST → CHAPTER_DOSSIER → publication-metadata-update.json → local-acceptance.json`

两份元数据仅按路径指向下游的 `publication-metadata-update.json` 和 `local-acceptance.json`，不会把这些文件的hash或变化状态写回元数据。这样主编可以在元数据最后固定后生成/刷新terminal验收，而不形成hash循环。已有local-acceptance若存在，脚本只在**外部更新回执**记录它的观察状态，提醒最后重新绑定。

正式写入时所有预检先结束，输入文件若在准备期间发生改变会阻断。之后以原子文件替换写manifest，再写绑定该manifest的dossier，最后写 `evidence/v3.7/publication-metadata-update.json`。两文件无法构成一个跨文件的原子事务；若进程恰在二者之间中断，需重新运行并核对回执，不应提交半更新状态。完整3.6快照始终在场。

## 潜在风险与边界

1. **晚改文件。** MD、PDF、TeX、build/visual、review报告若在元数据写完后再改，现有hash会失效；应重跑正确范围的出版元数据核对，并最后刷新local-acceptance。
2. **视觉范围。** 元数据程序只能识别回执和PDF/MD是否一致，不能替代实际页面观看。中文像素等价继承必须由视觉回执如实叙述；本脚本不自发推断。
3. **旧字段的历史含义。** 173科学对象和source_catalog内的旧pending/current用词按原版保存。当前状态必须读新的出版层和明确的科学复用层，不能批量替换旧字符串。
4. **新PR状态。** 本工具有意不填新PR号或CI通过状态。root的实际GitHub交付需有后续远端回执。
5. **预览不是安装。** 隔离 `metadata-preview` 中的候选带实际预览时的输入和状态；最新为PREVIEW_READY，但正式发布仍应运行脚本读取最终资产，不直接拷贝候选。

该脚本没有改变任何原科学结论，不证明所有公式，不重新许可第三方材料，也不把内部审查称为外部同行评议。
