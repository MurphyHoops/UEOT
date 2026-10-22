# Operations #366：已接受原始证据归档

本目录逐字节保留本批 operations 授权的 **23 个原始文件，共 190,844 字节**。
来源为 `/workspace/scratch/534b0448126c/tmp/core-path-realization-ops`。
[MANIFEST.json](MANIFEST.json) 对每个文件记录原绝对路径、归档相对路径、两侧
字节数与 SHA-256；复制后同时核对目标和仍在原目录的源字节，全部一致。

本次清单 SHA-256：
`412b3788f6d455ecf9a995d122f9a287e724aea0daa182b24740273b7a4878f3`。

## 已核对的身份和状态

| 项目 | 实际原记录 |
|---|---|
| 起始 main | `50a91fb9c81e0f5e698ce2cc02ec1a44c9583b04` |
| 独审后的 operations candidate | `91366e9cf38815788978aeaf010f3016942d31dd` |
| 已接受 resulting main | `d503586107974c56e0773b4ea106b41a7d144b43` |
| candidate / main 共同树 | `08e1f9869bdad2c8b1d2a95a602711ffaa1eb92b` |
| [PR run 39707070048](https://github.com/MurphyHoops/UEOT/actions/runs/39707070048) | governance `success`；proof `skipped` |
| [main run 39707704830](https://github.com/MurphyHoops/UEOT/actions/runs/39707704830) | exact head 为上述 resulting main；governance `success`；proof `skipped` |

原 candidate review 与 root committed-head review、各自实际 governance 日志、
PR 合并响应、main run API 以及 accepted-base 记录互相匹配。operations diff
只变更同一政策文件中的三个字符串，六个已授权路径的列表保持原值。
这里的两个 proof job 均为 **SKIPPED，不能作为 Lean 构建通过证据**。

## 原文件分组

| 子目录 | 保留的原材料 |
|---|---|
| `accepted-base/` | 精确基线接受 JSON 与云端科学分支 fast-forward 原日志 |
| `local-review/` | 原候选树自审、root committed-head 独审、两次 governance 原输出、候选树、实际 patch、changed-path 输入和 commit 输出 |
| `cloud-push-failure/` | 云端认证失败的原日志、执行收据与 push 前的远端引用快照 |
| `mac-push-tool/` | 原始 `MAC_PUSH_TOOL_OUTPUT.json` 工具返回，保留 Mac 执行报告和其中的来源摘要 |
| `github-api/` | 原 PR premerge / runs / jobs / merge 响应与 main runs / jobs 响应 |
| `github-logs/` | PR 和 main 的完整原始 governance 日志工具包装 JSON |

Mac push 文件是当时捕获的工具返回，内含
`PATH_REALIZATION_OPS_MAC_PUSH_V1`、精确 head/tree、exit `0` 及原日志/引用快照的
摘要。它不是重新生成的 Mac 文件系统日志；其中引用的独立 Mac 文件不由本归档
重构。GitHub 原工具包装中已存在的重复字段也不作删改。

## 原始失败和阶段状态保持原样

云端 `PUSH.log` 保留 `could not read Username` 认证失败；其执行收据的 exit
code 为 **128**，原 `state` 仍是 `PUSH_RETURNED_PENDING_REMOTE_VERIFICATION`。
后续 Mac push 成功单独记录，没有把这次云端失败改成通过。

`LOCAL_TREE_REVIEW.json` 的 `COMMIT_AND_PUBLICATION_PENDING`、独审待完成说明，
以及原 premerge API 的 `state=open`、`merged=false` 和临时 PR merge SHA 均保持
原字节。后续 root 独审、实际合并和 accepted-base 文件记录各自的新阶段，不能
回填覆盖较早快照。清单中的 `derived_checks` 是只读交叉核对摘要，不替代这些
原记录。

未复制 Git bundle、临时 Git index、含传输/请求内容的 driver，或重复正文的
较早 PR creation 响应。候选自审所引用的 preparation driver 摘要仍留在原自审
JSON 中；其代码未作为本次执行结果归档。完整排除清单及理由见 MANIFEST。

## Mac 退休与对齐：待 root 导入独立目录

**本次状态：`PENDING_ROOT_IMPORT`。** Mac 的 operations 分支退休和 main/工作树
对齐原始结果文件，须由 root 从实际 Mac 归档导入
`mac-retirement-alignment/`，另写逐字节来源清单。

当前没有用 `align_and_retire_mac.py`、退休前 open-PR 快照、Mac push 工具返回
或本云端接受记录代替退休/对齐的原始执行证据。待补目录尚未创建。
后续补件在该独立目录记载；本清单中的 PENDING 是本次归档时的历史状态。

本次归档没有修改 Lean、六条 live 路径、政策、原始收据或 GitHub 状态。
科学批次的 full build、native、canonical 与最终发布各有自己的执行材料，
不由 operations 的 governance 成功推得。
