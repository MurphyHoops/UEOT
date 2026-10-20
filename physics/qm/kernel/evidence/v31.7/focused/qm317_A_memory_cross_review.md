# A → B 独立交叉审查

**主源码数学与范围：PASS。** 本审查只读源码与作者实际成功日志，没有启动额外 Lean。具体见证仍等待最终退出 0，不能把失败候选日志计为验收。

## 源身份

- `/workspace/scratch/474cf6b1f047/qm_v317_work/formalization/ueot-qm/UEOTQM/RectangularChannels.lean` — SHA-256 `b097d5cb5eb5b141d051d8f65c7aff31c0d3a1b2f8d688548d8edf74f6a7a9a7`，13889 bytes。
- `/workspace/scratch/474cf6b1f047/qm_v317_work/formalization/ueot-qm/UEOTQM/ClassicalQuantumMemory.lean` — SHA-256 `200996515d4a4cfdf066b844e8d4904ed52f380f876feca162d6dc6f1f26cf80`，21786 bytes。

## 审查结论

- **kraus_direction_completeness：PASS。** K : Matrix output input C; completeness is sum K†K = input identity. State positivity and complex trace are derived for all inputs.
- **actual_complete_positivity：PASS。** K tensor I is a concrete rectangular channel for every finite ancilla; positivity quantifies over every joint PSD matrix. amplify_operator_apply identifies all auxiliary coherences.
- **record_blocks_marginals：PASS。** Tagged channel acts on every complex input; diagonal blocks are the original Instrument.branch and off-diagonal labels vanish. The two actual partial traces respectively yield Instrument.channel and the diagonal original probabilities.
- **zero_probability：PASS。** Positive branch normalization equals existing posterior. Zero probability is equivalent to zero block; no arbitrary physical posterior is introduced.
- **finite_adaptive_protocol：PASS。** KrausPath is indexed by the original dependent leaf of any finite complete tree, with arbitrary leaf depth. Chronological products, input completeness, and equality to recordOperator on the exact original word are proved.
- **actual_leaf_marginal：PASS。** The density diagonal after discarding memory is the original Adaptive.leafProbability. Record-discarding sums the actual unnormalized leaf memory operators.
- **explicit_amplified_blocks：PASS。** Added single-step and ProtocolMemory channel_amplify_operator_apply compose the generic amplification identity with the exact original branch/record block formula, with explicit ((label,i),a) carrier.
- **event_tv_defect：PASS。** Actual block-diagonal event effects identify event probabilities. Sharp TV uses all-event equivalence rather than summed singleton bounds. Defect is an actual sSup over every input density, with the correct larger output carrier.
- **scope_of_budget：PASS。** The current protocol defect is a whole-protocol supremum. Fixed-depth stepwise accumulation and reduction to primitive action defects are explicitly separate, not proved here.
- **scientific_boundary：PASS。** No diamond metric identification, arbitrary environment error claim, infinite protocol, universal selection, or reconstruction conclusion is introduced.

## 已落实的补强

新增单步和任意有限协议的显式辅助放大块等式；新增偏迹之后复对角矩阵的每个元素等于原有真实实概率。这些均由原有实际通道与块恒等式推得，没有输入结论字段。

## 验证和边界

已回读 `qm317_rectangular_build_3.log` 与 `qm317_memory_build_6.log` 的实际成功结尾（8726、8732 含缓存 jobs）。主源码没有阻塞发现。作者独立见证尚未收到最终成功状态，待冻结后追加单独绑定。当前全协议缺陷不是逐步预算；固定深度累计误差及原始动作缺陷压缩仍须独立证明。


## Final concrete witness acceptance

The final witness is frozen at SHA256 `edd43b953001002b2f2aaa44a424da0e1beb0b5a0201ff7a6fba54bb405ce8e9`. Round5 actually completed with exit code0 (author session69930); the source, log, and completion receipt identities were independently rechecked without running Lean. All22 complete declaration names were independently parsed and matched to the source audit lines, with only `propext`, `Classical.choice`, and `Quot.sound`. Historical failed rounds remain failed records, not acceptance.

Both instruments are complete, with the same identity memory channel on all states. Retained record TV and the tagged channel defect are exactly one although the old unlabelled defect is zero. The complete two-step feedback protocol retains the original dependent leaf carrier and uses its actual later-event probabilities; no fabricated record distribution or replacement outcome type is used. The later event, its real event effect, and full leaf TV all attain the unit gap. No additional mathematical or scope blocker remains.

Final status: **PASS_FINAL_MAIN_AND_WITNESS_SOURCE_REVIEW**.
