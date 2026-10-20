# v31.7 C：同一非交换量子存活模型的精确动力学

状态：**三个源文件已冻结，聚焦 Lean 与相应公理检查均通过；root 统一验收与发布另行执行。**

## 文件与计数

| 文件 | 定理 | 定义 | 显式审计目标 | SHA256 |
|---|---:|---:|---:|---|
| `UEOTQM/QuantumDoobModel.lean` | 17 | 12 | 29 | `cf5df67eb83e3c14e20699947a1c2e922af53a19c6483d40b788e234c9e8b5f3` |
| `UEOTQM/QuantumDoobDynamics.lean` | 43 | 5 | 48 | `ee227ea4dcba6e9f2dafe33df614c382610f7468596d923489fc63e76a1556e3` |
| `scripts/witnesses/QuantumDoobDynamicsExamples.lean` | 20 | 5 | 25 | `40d1af7c59ccbca3902b84004f3d9ec7ba29f690a1789879f1c3e5fd351cf2a6` |

公共两模块合计 **60 theorem、17 def、77 目标**；新独立见证 **20 theorem、5 def、25 目标**。没有新增结构、全局命名实例或结论字段。计数是源码声明数，不把提取旧模型当作新物理发现。

`QuantumDoobModel` 与原 `scripts/witnesses/QuantumDoobExamples.lean` 的 27 个同名声明在去注释和空白后正文逐一相同；仅增加 `plus` 与 `plus_matrix` 作为公共接口。旧见证仍为 SHA `5fbe70aca27378fead77fdb52658bb048463eff3b1e7e1299a43e5f40e2d456a`。模型来源明细见 `/tmp/qm317_doob_model_provenance.json`。主包不导入 scripts/witnesses。

## 实际证明的核心结果

固定原 r=3/16、S=diag(2,1)、T=diag(1/2,1)、rho=(1/5)[[1,2],[2,4]] 与 plus=(1/2)[[1,1],[1,1]]。源的成功 Kraus 仍不交换，且保留非对角输入相干。

1. `doob_successOperator_formula` 对所有复算符给出实际 D^n(X)=a_n X+(1-a_n)tr(X)plus，其中 a_n=(1/3)^n；复迹未替换为实部。`doob_iterateState_matrix` 对接实际完整通道轨道。`doob_stationary_unique` 直接由矩阵等式推出唯一性；`doob_matrix_tendsto` 给整个矩阵轨道的通常有限维拓扑极限。
2. `effectDistance_eq_of_matrix_sub_smul` 从每个真实效应概率差与 supremum 两边不等式证明精确缩放。`doob_effectDistance_exact` 因而给 d(D^nτ,D^nυ)=a_n d(τ,υ)，不假设距离分离或与其他矩阵范数同一。
3. `filterMass_bounds` 从完整 PSD 对角元与迹一证明 1≤c≤4，随后 b=(5/8)c 与 z=a+(1-a)b 均位于 [5/8,5/2]。c 是滤波归一因子，不是成功概率。
4. `source_successOperator_formula` 先用既有 finite intertwining 回拉所有复算符；`source_successOperator_density` 给实际源 Φ^nτ=r^n[aτ+(1-a)bρ]。`source_successMass_formula` 与 `source_response_formula` 对接实际有限全成功记录：m_n=r^n z。上下界为 (5/8)r^n≤m_n≤(5/2)r^n，且每个有限 n 严格正。
5. `source_conditionalState_matrix` 与 `conditioned` 使用已有 actual conditionalState，给 τ|n=(a/z)τ+((1-a)b/z)ρ。`conditioned_effectDistance_exact` 证明精确 (a/z) 距离缩放；`conditioned_effectDistance_le` 给 (8/5)3^-n 统一界。矩阵与全效应距离两个极限均已通过。
6. `source_successMass_tendsto_zero` 同时证明真实有限成功概率序列趋于零。因此条件分布收敛不意味着无条件持续概率有正下界。这里未构造无限路径事件。
7. 独立见证核对 I/2 的 c=5/2、b=25/16、m_1=33/128≠3/16，实际一步条件态为 [[3/11,10/33],[10/33,8/11]]。另对纯虚非对角复输入检查两步相干保留系数 1/9。
8. 负控使用一个成功 I/2、三个失败 I/2 的完整仪器及 H=I、r=1/4。`identityDoob_branch` 对所有复矩阵等于输入；所有密度态及其迭代固定。`identityDoob_not_unique_stationary` 与 `identityDoob_not_common_limit` 排除唯一平稳态和公共吸引极限。源成功质量仍为 (1/4)^n，有限条件态等于输入。正左特征数据本身不保证吸引性。

## 验证与证据

全部官方 Lean 调用均使用 `/tmp/lean-4.33.1-linux/bin/lake`、共享 `flock /tmp/qm317-lean.lock` 与明确的受限进程路径兼容权限；未运行全包构建。

- 模型：`/tmp/qm317_doob_model_focused.log/json`，Lake 聚焦构建 exit 0。
- 动力学：`/tmp/qm317_doob_dynamics_round4.log/json`，exit 0，8730 jobs，45.65 秒含调度。
- 见证：`/tmp/qm317_doob_witness_round3.log/json`，exit 0，29.95 秒。receipt 已绑定最终源 SHA、实际日志 SHA、25 个完整目标名及实际公理输出；恰好25项、无遗漏/重复、均仅标准 propext/Classical.choice/Quot.sound。
- 公共77目标：`/tmp/qm317_C_public_targets.json`、`/tmp/qm317_C_public_axiom_targets.lean`。独立导入打印在 root 停止重复审计指令到达前已发出，现已返回 PASS；`/tmp/qm317_C_public_axioms.log/json` 保存77项完整实际输出，未重编译主模块。此项不替代 root 统一门。
- 失败历史：Dynamics round1–3 与 witness round1–2 均保留原日志和退出码。其残留 sorryAx 是 Lean 对失败声明的错误恢复，最终源没有 sorry/axiom/admit/native_decide，最终两个审计均无 sorryAx。

## 严格边界

本次完成同一指定量子实现中重复指定成功分支的动力学，不完成任意结果词的闭式，也不证明 Core 自动推出复量子理论、一般 Perron 存在或谱半径识别、一般 QSD 唯一、无限路径 Q 过程或无限维结论。合同中的“本指定源任意特征率 QSD 唯一”属于可选项，本轮未新增该命名定理。滤波态归一化通常非线性；过滤谱数据与唯一吸引是不同责任。形式验收不等于该模型已获得实验验证。

本代理未修改公共 exports、主审计、CI、Core、总著或远端 Git。
