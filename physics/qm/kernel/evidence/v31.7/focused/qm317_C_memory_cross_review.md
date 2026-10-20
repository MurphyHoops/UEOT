# v31.7 B 路最终只读交叉审查

**结论：未发现科学或形式化范围阻塞。三份最终源均已绑定作者冻结 SHA；本审查不另行编译。**

## 冻结源

- `/workspace/scratch/474cf6b1f047/qm_v317_work/formalization/ueot-qm/UEOTQM/RectangularChannels.lean`
  SHA256：`b097d5cb5eb5b141d051d8f65c7aff31c0d3a1b2f8d688548d8edf74f6a7a9a7`。
- `/workspace/scratch/474cf6b1f047/qm_v317_work/formalization/ueot-qm/UEOTQM/ClassicalQuantumMemory.lean`
  SHA256：`200996515d4a4cfdf066b844e8d4904ed52f380f876feca162d6dc6f1f26cf80`。
- `/workspace/scratch/474cf6b1f047/qm_v317_work/formalization/ueot-qm/scripts/witnesses/ClassicalQuantumMemoryExamples.lean`
  SHA256：`edd43b953001002b2f2aaa44a424da0e1beb0b5a0201ff7a6fba54bb405ce8e9`。

## 核对结果

### actual rectangular finite CPTP

Complex linearity, positivity, trace preservation, pullback effects and effectDistance contraction are proved from finite Kraus completeness; arbitrary finite identity amplification has an explicit all-complex-matrix entry formula and derived positivity.

### single-step classical record plus quantum memory

The constructed tagged Kraus family gives a diagonal classical block containing the actual instrument branch, not a freely supplied density. Actual discard maps recover channel memory and the diagonal old probability law. Positive-mass posterior and zero-mass zero-block statements have their proper domains.

### finite adaptive protocol

Leaf aliases the pre-existing Protocol.Leaf, and KrausPath uses the actual leaf-dependent finite product of Kraus choices. Later operators multiply on the left. path_complete is proved recursively from the actual instrument completeness equations; path_branch_eq_recordOperator is a full operator equality on all complex X, with the original chronological Protocol.word.

### whole-protocol channel and margins

The actual rectangular channel has full leaf blocks equal to pre-existing recordOperator, arbitrary finite amplification, actual discard marginals and old leafProbability entries. Event effects and total variation are derived through all finite events; tagged defect is the actual whole-protocol supremum, not an assumed or invented per-step budget.

### legal record-deletion negative control

Both complete certain-label instruments have the identity memory channel on every input, while tagged total variation, joint effect distance and tagged defect equal one. The same two-step controller selects the common later operation library using the observed first label. feedbackLaterZero_iff proves the tested event depends only on the second label; its probabilities are one and zero in the two actual models.

### final dependent-type fix

The final proof preserves the existing leaf carrier and event. erw resolves definitional transparency for membership, and explicit-f Finset.sum_pair.trans handles the sum without rebuilding Sigma/DecidableEq types. The final accepted witness remains the same actual feedback construction.

## 证据与边界

实际作者回执 `/tmp/qm317_memory_witness_5.json` 记录 exit 0；审查独立重读原始日志，精确得到 22 个唯一名字，与最终源请求相同，依赖均限于标准基础公理。原始日志 SHA256：`44e166ac1f1e02c9f993e6e08c4a59142f4ca92f7bfbbc49a33e15c8e9279619`。主模块既有成功日志为 `/tmp/qm317_rectangular_build_3.log`（8726 jobs）和 `/tmp/qm317_memory_build_6.log`（8732 jobs）；本审查不据此覆盖 root 的统一验收。

- The negative control proves later record/control probabilities differ. The unconditional quantum memory channel remains the identity throughout this witness; it does not prove different final memory states.
- The defect bound is for the whole actual finite protocol. A sum of local step budgets and diamond-norm bounds are not supplied.
- The arbitrary finite ancillary construction is a finite Kraus certificate of complete positivity; this review does not expand it to infinite systems.
- This is a read-only scientific/source review with accepted author logs bound by SHA. No Lean compilation was launched by this review, and no root unified or remote CI PASS is inferred.
- Independent operational principles and empirical completeness are not obtained from these channel constructions.

本审查只写 `/tmp` 报告；未更改 B 源码、公共审计、CI 或总著。
