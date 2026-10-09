# UEOT 本地分支与 worktree 逐项保存性审计（2026-10-09）

- 基线：main 6fa4c39d2a41，活动研究 4b4a4eca97ff；仅本地快照。
- 83 个分支：main 已包含 61；活动研究 1；图上尚未并入 21。
- 25 个 worktree；有已跟踪文件修改的工作树数 0。
- 当前代码查不到的历史 Lean 声明名有 1 个（不代表语义缺失）。

## 图上未并入分支逐项
| 分支 | 独有提交 | 比较路径数 | 历史声明名缺失数 | 处理 |
|---|---:|---:|---:|---|
| backup/endogenous-object-pre-main-rebase | 1 | 3 | 0 | 保留，不得整支覆盖现有源码 |
| backup/p7-p12-pre-stack-rewrite | 8 | 17 | 1 | 保留，不得整支覆盖现有源码 |
| compression/contractive-fixed-point | 1 | 3 | 0 | 保留，不得整支覆盖现有源码 |
| compression/m-pe-01-main-integration | 1 | 4 | 0 | 保留，不得整支覆盖现有源码 |
| compression/m-qd-01-prediction-minimality | 1 | 5 | 0 | 保留，不得整支覆盖现有源码 |
| compression/m-qd-01-structured-quotient | 1 | 4 | 0 | 保留，不得整支覆盖现有源码 |
| compression/m-tc-01-cross-scale | 1 | 5 | 0 | 保留，不得整支覆盖现有源码 |
| compression/recursive-sufficient-state | 1 | 3 | 0 | 保留，不得整支覆盖现有源码 |
| compression/second-order-mpe-normalization | 1 | 3 | 0 | 保留，不得整支覆盖现有源码 |
| compression/teleological-equivalence | 1 | 3 | 0 | 保留，不得整支覆盖现有源码 |
| compression/value-alignment | 1 | 3 | 0 | 保留，不得整支覆盖现有源码 |
| formal/pctl03-diffusion-hjb | 2 | 2 | 0 | 保留，不得整支覆盖现有源码 |
| formal/pkl04-finite-ctmc-path-kl | 1 | 15 | 0 | 保留，不得整支覆盖现有源码 |
| formal/pkl05-girsanov-path-kl | 5 | 2 | 0 | 保留，不得整支覆盖现有源码 |
| formal/pqsd04-reversible-spectral-qsd | 3 | 2 | 0 | 保留，不得整支覆盖现有源码 |
| local/post-reflection-scientific-audit | 5 | 11 | 0 | 保留，不得整支覆盖现有源码 |
| local/recovery-pre-main-sync-20261008 | 1 | 12 | 0 | 保留，不得整支覆盖现有源码 |
| local/scientific-closure-governance-validation | 13 | 69 | 0 | 保留，不得整支覆盖现有源码 |
| ops/compression-finalization-receipt | 2 | 8 | 0 | 保留，不得整支覆盖现有源码 |
| ops/compression-gate-a-final-audit | 1 | 3 | 0 | 保留，不得整支覆盖现有源码 |
| ops/compression-track-s-infinite-governance | 1 | 6 | 0 | 保留，不得整支覆盖现有源码 |

## 已核对的几个关键真实内容差异
- 旧 endogenous-object 备份的两个实质 Lean 源已由主线强化：当前主线新增 infinite all-times persistence、wrong-controller no-repair 和 nonempty constitutive persistence certificates。旧备份不能反向覆盖。
- 旧 P7-P12 分支存在 objectScaleMap_does_not_determine_wilsonian_flow，主线主动收窄到 wilsonianCouplingFlow_nontrivial_of_twoCouplings；这是去掉未经证明的尺度映射兼容暗示，不恢复旧的强名称。
- formal/p* 等旧分支的具体主要 Lean 证明已在 main；不可因旧 Git SHA 不可达而重复插入，或覆盖主线引入的根导入。
- 旧 ops/scientific-governance 分支可能保留有价值的历史审计文件，但当前安全合同和账本更新，不做整体 cherry-pick。

## 整理决策
1. 61 个已进入 main 的分支：保留 Git 证明来源，不重复集成。
2. 21 个图上分叉的旧分支：仅对当前源码实际缺失的、语义审计通过的定理作选择性迁移。本轮无已确认可以整支合并的分支。
3. 所有 detached review worktree 保留；其已跟踪内容干净不等于 untracked 内容可删除。
4. 继续在活动 UMC 本地分支建立数学桥并编译；不改冻结 106/106、四生成器、P12 PARTIAL 和远端 main。

## 审计方法限制
- Same Lean theorem name does NOT prove that body, hypotheses or meaning agree.
- Non-ancestry can reflect squash, cherry-pick or later improvements.
- Local main/origin-main snapshot, no remote fetch.
- No branch, worktree, stash, local files, or remote refs are deleted or changed.
