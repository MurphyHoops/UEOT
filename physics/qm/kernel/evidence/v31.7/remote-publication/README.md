# v31.7 实际远端验收与发布来源

科学源通过 [PR #347](https://github.com/MurphyHoops/UEOT/pull/347) 发布。实际源码提交为 `a89bc691e698391d03ff7b705cc76def1fa3512e`；[PR 运行 39402444333](https://github.com/MurphyHoops/UEOT/actions/runs/39402444333) 完成成功。合入后的独立受验 main 提交为 `87091d1ad4592c4467fa3acc3ac75d67c0edac54`；[push 运行 39404249860](https://github.com/MurphyHoops/UEOT/actions/runs/39404249860) 完成成功。两份实际提交的整树均为 `89fea2ddfcbc7c41a5fc1512f5ed7cf8a40e109d`。

本次后续提交保存已经发生的验收，更新当前状态及书籍远端导航。它自身的提交身份与上述科学受验提交分开。原本地证据、80 项受验源、56 项递归 Core 源和《UEOT物理学》3.3 的 Markdown、PDF、TeX 均保持原字节；没有因元数据收尾重新运行本地科学证明或排印。

## 证据组织

- [集成回执](../integration-verification.json)连接实际 PR/main 身份、两份日志验收和逐项文件核对。
- [CI 目录](../ci/)保存两次实际 run/jobs JSON、解码后的两个 job 日志以及原解析器产生的验收回执。
- `C_ci_pr_39402444333_review.json`、`C_ci_main_39404249860_review.json`记录独立针对性日志审查；`C_ci_remote_tree_review.json`记录实际源码树与冻结载荷的独立核对。
- `qm317_source_remote_tree.json`为完整源码树 API 回读；`qm317_main_remote_tree.json`为完整主线树回读，并由实际主线提交回读绑定 `commit` 字段。对应提交、合并、分支和树创建回执一起保留。基树及[244 文件清单](../publication-inventory.json)保留原身份。
- 以 `.py.txt` 结尾的文件是实际使用过的辅助脚本归档，保留原字节供审计；它们不加入受验科学源集。原运行日志中的绝对路径记录执行当时的真实环境。
- `qm317_root_metadata_apply.json`与`qm317_book_metadata_apply.json`是实际元数据执行回执；书籍当前输出的哈希由[独立书籍发布回执](../../../../book/evidence/v3.3/remote-publication.json)单向绑定。当前导航仅按路径引用该回执，避免自哈希循环。

`qm317_book_metadata_correction.json`另记录实际执行后的窄修正：书籍台账的当前合同状态改为 `MAIN_VERIFIED`，并明确内嵌结果和章节检查中的旧待验字段属于原本地组装 checkpoint。原 131 个结果对象、章节对象、两份原 apply 回执及旧本地证据均保留；当前书籍台账哈希由修正后的书籍远端回执绑定。

## 验收边界

两次实际 CI 均包括 29 个公共模块、646 条显式 theorem、855 个唯一命名公理目标、100 个运行测试方法、七组见证共 151 项审计、六个精确证书及 42 个审计，以及四个篡改真证明拒绝和四个同数据假值证明接受。允许公理仅为 `propext`、`Classical.choice`、`Quot.sound`。实际构建均报告 8793 jobs；普通 Lean linter 和 runner 警告仍存在。

日志中的 artifact 上传步骤已核验，未下载 artifact ZIP，也未声称独立检查 ZIP 内的详细文件。三份正式正文的身份绑定不扩大原视觉审查范围：仍是全书总览加已记录的指定完整页审查，没有新增 203 页逐页完整精读。

这些是有限形式化、精确计算与发布身份的验收，不新增物理实验，不证明完整自然理论，不把三代条件结论或 v31.8 尚未形式化的合同计入 v31.7 已证成果。
