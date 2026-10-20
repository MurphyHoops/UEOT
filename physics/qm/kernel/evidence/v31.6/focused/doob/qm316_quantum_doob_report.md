# QuantumDoob 子任务最终报告

**状态：新增主模块与精确见证均已在官方 Lean 下通过，两个源文件已冻结。** 主包公共公理验收与发布由 root 统一执行，本子任务未重复运行主模块独立公理进程。

## 源与计数

| 文件 | SHA256 | 显式声明 | 公共审计目标 |
|---|---|---:|---:|
| `UEOTQM/QuantumDoob.lean` | `345f06df8a70a0c38637cc90d1ee6f7d7c09a8e5715bd9a05943b0bc05bd8350` | 42 | 43 |
| `scripts/witnesses/QuantumDoobExamples.lean` | `5fbe70aca27378fead77fdb52658bb048463eff3b1e7e1299a43e5f40e2d456a` | 40 | 40 |

主模块 42 项 = 32 theorem + 9 def + 1 structure；另审结构构造器 `InvertibleFilter.mk`，合计 43 主包命名目标。见证 40 项 = 28 theorem + 12 def；40 项全部逐名打印公理。清单完整存于同名 JSON 报告及 `/tmp/qm316_quantum_doob_targets.json`。

## 实际验证

- `/tmp/lean-4.33.1-linux/bin/lake build +UEOTQM.QuantumDoob`：**EXIT 0**；最终日志 `/tmp/qm316_quantum_doob_focused.log`，含正式 Lake 依赖轨迹。新模块构建行报告 422 秒，前置旧模块警告属于缓存重放。
- `/tmp/lean-4.33.1-linux/bin/lake env lean scripts/witnesses/QuantumDoobExamples.lean`：**EXIT 0**；最终日志 `/tmp/qm316_quantum_doob_witness.log`。无 warning/error。
- 最终见证公理结果：**40/40** 唯一目标，全部仅依赖 `propext`、`Classical.choice`、`Quot.sound`；没有 `sorryAx`。
- 两个最终源未发现 `sorry`、`admit`、`unsafe`、`native_decide` 或新 `axiom` 声明。
- 中间失败轮已完整保留，命令、退出码与日志 SHA 在 JSON 中；这些失败日志不作为验收证书。

## 核心结果

- Actual recordOperator for n repeats of a selected branch; right eigenoperator powers and normalized-density QSD survival/conditioning; rate in [0,1].
- Explicit two-sided inverse filter; positive filtered mass proved for every Density using PSD zero-trace and invertibility.
- Left Heisenberg eigenmetric implies weighted Gram completeness, then an actual ordinary square-root Kraus Doob Instrument.
- All-complex-operator one-step and finite-iterate conjugacy; real-trace eigenmetric law on every complex operator.
- Every initial Density has positive finite success probability under the positive-rate left eigenmetric, and its actual finite conditional state, after normalized filtering, equals actual Doob iteration.
- An additional right eigen-Density yields an actual channelState fixed point and invariant repeated Unit-outcome record operators.
- Complete rational two-dimensional source with noncommuting Kraus and retained E01 coherence, verified left/right eigen-equations and exact full-matrix Doob formula.
- Failure completion, QSD-versus-filtered state, and non-eigen initial survival-rate controls.

## 解释和责任边界

- This extends the existing finite complex Kraus QM sector. It contains no direct UEOT Core theorem application selecting or deriving that quantum sector.
- The Doob output type is Unit; the proved record identities concern repeats of the selected success branch, not arbitrary fine-grained monitored Kraus words or arbitrary operation libraries.
- InvertibleFilter.state is generally nonlinear. The witness filtered mass 8/5 is a normalization factor, not a source probability.
- The named eigenmetric_successMass theorem uses real mass = Re(trace) on arbitrary complex operators; the witness transformed_branch_formula uses the full complex trace.
- Spectral-data existence, universal availability of a positive invertible eigenmetric, spectral-radius identity, uniqueness, irreducibility, mixing and infinite conditioned limits are not proved.
- Generic source QSD right eigenrelation and positive rate are explicit inputs; target completeness, positive filtered normalization, conditional-state stationarity, and Doob state stationarity are proved outputs.
- No frozen Core, shared exports/audit/CI, main manuscript, Git metadata, remote repository or publication path was modified by this child.

## 有理见证的关键常数

成功 Gram 为 diag(3/8,9/64)，失败 Gram 为 diag(5/8,55/64)。源密度为 (1/5)[[1,2],[2,4]]，r=3/16，S=diag(2,1)，T=diag(1/2,1)，H=diag(4,1)。两个谱等式均在实际 Kraus 上核验。过滤归一因子为 8/5，过滤态为 |+⟩⟨+|。对所有复矩阵 X，新实际通道严格等于 (1/3)X + (tr X/3)[[1,1],[1,1]]。

K1K2≠K2K1；Φ(E01)=E01/16，故本例保留输入相干。删去失败族失去完备性；原 QSD 与过滤态不同；均匀态一步成功率 33/128 不等于 3/16。所有这些控制均有专用 Lean 定理。

## 日志绑定

- `/tmp/qm316_quantum_doob_focused.log`：SHA256 `c323489d095454a5f3d7c096cfd26597828c7d4998c32ceca28b1de407a0f092`，12150 bytes。
- `/tmp/qm316_quantum_doob_witness.log`：SHA256 `18b22411e7f6fbc286adfa3f4943c8ad26f75f3416e71c6eb74546e271e423f1`，4233 bytes。
- `/tmp/qm316_quantum_doob_round2_failed.log`：SHA256 `37b261bd65ba307565ee367502f48ba8705fc4b4ea1aadd6ad7312629e623a65`，1082 bytes。
- `/tmp/qm316_quantum_doob_witness_round1_failed.log`：SHA256 `188d663464e05ead04e7d7dd625e055eddeec8ea573caa430f60e48cffbe6ae6`，12043 bytes。

## 配套审查

A 的 ClassicalSector / CorePurificationBoundary 只读数学与接口审查已写 `/tmp/qm316_classical_cross_review.md/json`；最终 Core 冻结绑定待其作者确认。第56章候选已回读并核对所选成功词、归一化、谱前提、实迹/复迹以及 Core 责任边界；修订后无阻断。完整推导说明见 `/tmp/qm316_quantum_doob_math_notes.md`。

## 最终交叉审查与统合入口

ClassicalSector 最终 SHA `fed2036fce7ca658a74b7457316f6950727924c0f8abc0931a5d5f7ffe33bbb5` 与 CorePurificationBoundary 最终 SHA `53d957159fa6cf743c4e146e7d146385af81b7ec9c5a12204f90e488d870bce4` 已绑定只读交叉审查，无数学范围阻塞。见 `/tmp/qm316_classical_cross_review.md/json`。

公共入口的独立源码复扫已确认 459 显式 theorem 全覆盖、573 主审计目标无重复、四见证 62 theorem + 22 def = 84 独立目标；见 `/tmp/qm316_integration_source_review.md/json`。源码审查不代替根端统一编译/实际公理日志/综合见证 receipt。第56章独立审查见 `/tmp/qm316_ch56_source_review.md/json`，数学范围通过，末段下一轮任务优先级已由 root 对齐并完成最终复核绑定。
