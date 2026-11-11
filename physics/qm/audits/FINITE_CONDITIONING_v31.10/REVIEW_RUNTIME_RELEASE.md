# 有限条件量子参考程序：发布范围与验收记录

审阅日期：2026-11-11 UTC。审阅者：`/root/qft_generations_audit`。

**发布判断：当前运行源码与最终 Linux 证据一致，已达到本轮有限模型的科学参考实现验收目标。** 本次只读核对源码、JSON、日志及身份，未重复执行科学测试，未操作 Mac，未修改运行源码。

## 1. 可直接使用的发布元数据

```yaml
component: finite_visible_record_quantum_conditioning_reference
runtime_evidence_status: PASS_CURRENT_SOURCE_AND_RETAINED_EVIDENCE
scope: finite_fixed_source_tree_original_visible_records_terminal_quantum_CQ
semantic_tests_passed: 19
exact_finite_symbolic_checks_passed: 95
numerical_reference: PASS_DIAGNOSTIC_ONLY
source_files_bound: 9
source_hashes_match_current_files: true
gate_log_hashes_match: true
frozen_model_plan_hashes_match: true
linux_execution_completed_utc: "2026-11-11T05:05:10.930622+00:00"
linux_python: "3.12.14"
linux_numpy: "2.3.5"
linux_scipy: "1.17.0"
linux_sympy: "1.14.0"
ci_requested_python_series: "3.12"
ci_requested_package_pins_match_tested_linux: true
mac_execution: REPORTED_PASS_BY_RELEASE_OWNER_RECEIPTS_NOT_INSPECTED_HERE
updated_ci_workflow: NOT_INSPECTED_HERE_BASELINE_ONLY
general_lean_proof_evidence: SEPARATE_BUILD_AND_AXIOM_RECEIPTS_REQUIRED
real_hardware_data: false
hardware_cost_advantage_claim: false
```

这里的 `PASS` 只表示上述明确层次的验收。SymPy 精确有限见证、浮点数值参考、一般 Lean 定理及真实设备证据分别登记；19 或 95 不是一般定理或自然界实验的计数。

## 2. 当前身份及日志核对

`runtime/evidence_final/execution_receipt.json` 记录的九份源文件 SHA256 均与当前 `closure_candidates/runtime/` 相同；执行期间源码未改变。三个 gate 均为 PASS、返回码均为 0，其实际日志 SHA256 与回执一致。测试日志确实包含 `Ran 19 tests` 和 `OK`，精确 JSON 中 95 项状态均为 `PASS_EXACT_SYMBOLIC`。

精确证书的 checker hash 与当前 `exact_witnesses.py` 一致，两份冻结模型的 hash 与原 JSON 文件一致。数值 JSON 的七项源身份也全部匹配。没有使用旧诊断目录代替当前证据。

| 当前证据文件 | SHA256 |
|---|---|
| `execution_receipt.json` | `608526fbf881ba69222b16fac607e49e01a2ec19a9312c8a6cba384f165dd622` |
| `exact_witnesses.json` | `26f47f9a501f6cf9567e686b310523cd01ae73c91801655e202010402e2c86ad` |
| `runtime_results.json` | `cb9db5e2168664e96616932dcb9692531ee0342db4aca4123069b71385aa9f32` |

运行目录中应发布九份源文件及所需最终证据；缓存及 `evidence_initial/`、`evidence_debug/`、`evidence_fast/` 等旧诊断不作为当前通过证据。

## 3. 是否满足本轮有限链条

**满足，且包含一个同一模型贯通的正实现和一个精确终止于允许库障碍的模型。** 原仪器与预先固定接受树生成后向效应；实际可见分支内求和隐藏 Kraus；支撑逆构造完整条件仪器；初始态仅按原接受质量归一一次；比较包含所有原叶记录和末态矩阵块。允许库按带标签 Choi 家族检查共同随机权重；正实现执行真实混合仪器；负结果另有精确分离泛函。早停调用次数、初始化尺度和条件误差具有独立数值或精确见证。

### 3.1 同一来源贯通实现和成本的正例

原 Kraus 为成功 Z/2、X/2，失败标签下有两个隐藏 I/2。三次连续成功：

\[
H_t=2^{-(3-t)}I,\qquad p_G=1/8,\qquad\widetilde\rho_0=\rho.
\]

允许动作 A0 为确定标签 0+Z，A1 为确定标签 1+X；精确权重均为 1/2。八个完整接受记录的条件量子块逐块相等。初态无需另行筛选。

在原完整仪器一次调用、允许 Pauli 动作一次调用均计一单位的约定下：

\[
\mu_{\rm original}=7/4,\quad
C_{\rm original/accepted}=14,\quad
C_{\rm target}=3+3r,\quad
3+3r<14\ \text{是此动作预算内的比较条件}.
\]

r≥0 为每次额外随机化成本，准备、失败重置、控制、辅助系统与校准费用须按同一资源合同另行加入。此处没有测得硬件优势。Z、X 虽反对易，其共轭通道交换；本正例不提供 CP 分支不交换的证据。

### 3.2 非标量、真正非交换模型及原库障碍

源成功 Kraus：K0=diag(1/2,1/4)，K1=[[1,1],[1,−1]]/4；失败隐藏 Kraus 为 diag(3/4,3/4)、diag(1/4,1/2)。初态为 [[1,−i],[i,1]]/2。三次连续成功：

\[
H_0=\frac1{4096}\begin{pmatrix}183&27\\27&51\end{pmatrix},\quad
p_G=117/4096,\quad
\mu=701/512,\quad C_{\rm accepted}=5608/117.
\]

共有 15 条原可见叶，其中 8 条接受。各时刻正定下界 η 为 3/512、9/256、3/16、1，由精确主子式检查认证。实际两条成功 CP 分支在 P0=diag(1,0) 上的交换子为

\[
\begin{pmatrix}0&-1/128\\-1/128&-3/256\end{pmatrix}\ne0.
\]

最大初始效应特征值为 c=(117+3√565)/4096，合法尺度族滤波成功率为 39/(39+√565)。该数值不是免费制备新初态的声明。

当允许库仅含原完整仪器时，精确分离泛函为负失败概率：目标值 0，所有允许混合在 I/2 上为 −23/32；原失败概率对任意密度态至少为 5/8。故此库的单轮随机化不能实现目标条件仪器。结论不延伸到额外筛选、扩充动作库或任意长电路。

## 4. 其他验收边界与精确值

| 边界 | 保留的结果及范围 |
|---|---|
| 奇异正事件 | H=P0、ρ=I/2、p=1/2；两个合法补全在过滤后的支撑输入给相同完整 CQ。 |
| 补空间泄漏 | 同一两个补全在 P1 输入上的可见 TV=1；不能丢弃泄漏误差。 |
| 零事件 | 输入 P1 的接受质量为 0；明确拒绝，不构造任意条件态。 |
| 隐藏 Kraus | 将一个 Kraus 重分解为 3/5 与 4/5 倍的两项，实际可见分支不变；隐藏指标不进记录。 |
| 标签交换 | 总通道可保持相同，但确定输入上的可见记录 TV=1。 |
| 同一观察权限 | 分离泛函 p(0\|x0)−p(0\|x1)：目标值 1，任意共享权重的库混合值 0。 |
| 合法目标处于库外 | 恒等通道与“Z 去相干/去相干后 X 翻转”库：Re Choi[0,3] 分别为 1/0；输入 \|+⟩ 的固定态距离对任意混合为 1/2。 |
| 未知输入非仿射性 | H=diag(1/2,1/8) 对 I/2 的归一输出 diag(4/5,1/5)，与分别过滤后平均的距离为 3/10。 |
| 秩一边缘例外 | rank(H)=1 的系统输出可用确定替换通道实现；保留 Bell 参考时二者联合态距离为 1/2。非零标量 H 保留全联合态。 |
| 变深度早停 | 另一明确源树 p=3/4、单次成本 3/2、每成功成本 2；不是以最大深度除 p。 |
| 锐条件误差 | 完整源 TV=1/10000，p=1/1000，q=11/10000，条件 TV=1/11=ε/max(p,q)；拒绝质量保留。 |
| 小正谱 | 不把正特征值截零；最小/最大正谱比低于 1e−12 时显式拒绝当前浮点逆根。统一小尺度 1e−20 I 保持完整支持。 |
| 对角退化及控制器改变 | 对角模型匹配经典条件路径；改变未来接受/控制树后重算效应，不能复用旧 H。 |

最后两项的运行判断是浮点语义检查，不属于精确支持识别算法的全称认证。所有 LP 输出也仅为数值状态；上述正权重与负分离值的精确检查另行保存。

## 5. Linux、Mac 与 CI 的证据界面

拟用 CI 包版本 `numpy==2.3.5 scipy==1.17.0 sympy==1.14.0` 与本次亲自核对的 Linux 实际执行完全一致。CI `python-version: "3.12"` 匹配已测试的 3.12 系列；本次实际补丁版本是 3.12.14，系列选择并不冻结未来补丁版本。

发布负责人报告实际 Mac 已通过 19 tests、95 exact checks，环境为 Python 3.14.4、NumPy 2.5.4、SciPy 1.18.1、SymPy 1.14.0。**本审阅者尚未取得或阅读该 Mac 回执，故不对其源哈希、日志或环境作独立确认。** 报告与已核对的 Linux 证据应分别登记，不能让一个平台的 receipt 代替另一个平台。

本次只读取 `closure_sources/.github/workflows/ueot-qm.yml` 的旧基线：已有 Python 3.12、独立 runtime/Lean jobs 和 always 归档，但未含新增有限条件 runtime 的依赖安装、执行与触发路径。负责人 Mac 中的新工作流不在本次审阅材料内，因此这里不宣称已审阅最终 CI 集成。最终集成需对应：两个事件的实际 runtime 路径触发、上述依赖版本、`verify_runtime.py --output-dir` 的正确调用、非零退出使 gate 失败，以及完整证据目录的 always 归档。这些是已知接线要求，不需要为本审阅扩大测试范围。

## 6. 发布描述应保留的限制

本交付证明或检查有限、固定原控制器、有限维复量子模型中的条件链。数值 PSD、谱与完整性残差只是诊断；原始浮点残差不能充当严格误差上界。单轮允许库实现、支撑任务、固定初态和最终输出任务不互相替代。未知输入恢复、保留外部参考及补空间泄漏各有单独资源或误差责任。

可发布的结论为：**一般书面/Lean 数学链由其各自证据支持；本参考程序提供相同来源的正实现、精确允许库障碍与关键边界见证，并按实际早停计算资源。** 本记录不宣称已经由 Core 唯一导出量子域，不覆盖无界树、任意反事实干预、任意电路可控性或新的自然规律，也不提供硬件成本或设备精度数据。
