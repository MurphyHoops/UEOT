# 共同实验中的接口推进与两部著作反馈

**本目录保存已由 Lean 内核检查的研究适配、精确的后续命题和独立哲学论证。**
固定逐行样本量已经接到实际选择后的联合风险端点；事件包络已可只在共同 Good
事件上的受选候选处要求。它们位于研究文档目录，尚未加入生产 import 图或原生声明账本。
生产模块数仍为 **659（648 个维护模块、11 个改编上游模块）**。

当前研究起点是实际 canonical main
`6b3ba80ec418ff04c4b6e2cd5c321b654540e9d1`。
此前治理、Core 数学和两部独立著作分别通过
[#349](https://github.com/MurphyHoops/UEOT/pull/349)、
[#351](https://github.com/MurphyHoops/UEOT/pull/351)、
[#352](https://github.com/MurphyHoops/UEOT/pull/352) 完成合并与实际 main 验证。
恢复入口为 [发布交接](PUBLICATION_HANDOFF_2026-10-20.md)；成熟生产数学入口为
[支持可行与注册联合风险闭环](../SUPPORT_VIABILITY_CLOSURE_V1.md)。

## 1. 已检查的数学推进

| 研究文件 | 已证内容 | 保留的范围 |
|---|---|---|
| [VariableRegisteredSamples.lean](VariableRegisteredSamples.lean) | 同一概率实验上的逐行校准；坐标为 `Σ j, Fin (N j)` 的真实乘积实验，附源行法律及独立性证明 | 有限注册集与有限状态；每个非空行 `N j > 0`，分配在数据前固定；通用校准不要求行间独立 |
| [VariableRegisteredJoint.lean](VariableRegisteredJoint.lean) | 从上述校准推出真实注册 Good 的坏概率，再用同一源和受选策略的拟合、占据、包络及预算得到实际联合风险界 | 当前联合端点仍要求有限训练空间、状态、行动和观察；候选类型可无限；时刻半径 `rho n` |
| [GoodSelectedEnvelope.lean](GoodSelectedEnvelope.lean) | 将不在 Good 上被选的候选包络补为全集，复用现有注册联合风险与可行策略端点 | 同一 Good、固定微观事件与相同策略身份；是非计算性集合适配，不是新的可执行检查器 |
| [VariableRegisteredSamplesBoundaryTail.lean](VariableRegisteredSamplesBoundaryTail.lean) | 不等样本数 `1,2` 的真实产品校准实例和空注册集实例 | 检查依赖样本下标与空集边界；不宣称新的数值自适应部署见证 |

主分类均为 **ADAPTER / INTERFACE**：统计集中、路径 TV 和联合概率分解复用已证明的
Core 定理。新证明给出缺少的实际样本类型与同源风险连接；不扩大冻结计数型命题。

### 同一个 Good 与实际联合实验

对每个预注册行 \(j\)，在采样前固定 \(N_j>0\)，每行内部独立且每个样本的真实
边缘律为 \(P_j\)。以这些实际样本形成经验 PMF \(\widehat P_j(\omega)\)，得到

\[
G=\{\omega:\forall j,\;\operatorname{TV}(P_j,\widehat P_j(\omega))
\leq\rho(n_j)\},\qquad
\mu(G^c)\leq\alpha
=\sum_j 2^{|X|}\,2e^{-2N_j\rho(n_j)^2}.
\]

Lean 的有限事件因子写为 `Fintype.card (Finset X)`。\(\alpha\) 不必小于一；界在大预算
时可能平凡。对同一个 \(G\) 上的受选候选，源—经验校准与实际经验拟合推出真实行误差，
再代入该受选策略自己的未认证行占据和参考风险检查。对固定 \(\beta\in[0,1]\)，
构造的训练—实际部署联合实验满足

\[
J\{(\omega,h):h\in E\}\leq
\min\bigl(1,\alpha+(1-\alpha)\beta\bigr).
\]

这条证明内部推出 \(\mu(G^c)\leq\alpha\) 和 Good 上的真实行误差；调用者仍须提供真实
采样法律及所选模型的拟合、占据、事件包络和数值检查。选择可以依赖记录；注册、样本量、
源机制与共同微观事件预先固定。重复同一个 Bernoulli 样本不会因为复制了多次便获得
独立样本的集中率。空注册集给出 \(\alpha=0\)，不推出零占据或零失败。

[联合风险精确规格](VARIABLE_REGISTERED_JOINT_SPEC.md) 展开全部量词和已有 Lean 调用；
[Good 包络论证](GOOD_SELECTED_ENVELOPE.md) 给出严格性例与遗漏额外坏事件预算的反例。
可行策略版包络适配继续使用 `viableFamilyPolicy` 为自己推导的零占据。
逐行样本量联合适配不声称其一般受选策略等于另一个经典选择所得的可行策略。

## 2. 实际验证

| 执行 | 实际结果 | 原始收据 |
|---|---|---|
| Good 包络最终源码 | PASS，3.511 秒；两个终端标准公理闭包 | [attempt-2](research_evidence/attempt-2/STATUS.json)、[日志](research_evidence/attempt-2/GoodSelectedEnvelope.lean.log) |
| 逐行样本校准最终源码 | PASS，6.911 秒；两个终端标准公理闭包 | [attempt-2](research_evidence/attempt-2/STATUS.json)、[日志](research_evidence/attempt-2/VariableRegisteredSamples.lean.log) |
| 不等样本数与空注册集 | PASS，34.119 秒 | [boundary-1](research_evidence/boundary-1/STATUS.json)、[日志](research_evidence/boundary-1/boundary.log) |
| 逐行样本量到实际联合风险 | 首次 PASS，6.422 秒；含前置校准的四个输出终端标准公理闭包 | [joint-1](research_evidence/joint-1/STATUS.json)、[日志](research_evidence/joint-1/joint.log) |

标准公理闭包为 `propext`、`Classical.choice`、`Quot.sound`。
校准首轮因 Sigma 坐标类型未明确而失败，原始
[状态](research_evidence/attempt-1/STATUS.json) 与
[错误日志](research_evidence/attempt-1/VariableRegisteredSamples.lean.log) 原样保留。
修复为显式 `SampleCoordinate N` 类型注解，后续通过独立记录。

编译使用 Mac 已核对的 Lean `leanprover/lean4:v4.33.1` 与 mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`。
[执行绑定](research_evidence/EXECUTION_BINDING.json) 记录全部九个已安装依赖的实际 Git
revision 与已跟踪文件干净状态，以及完整源码、日志和组合文件身份。
[BUILD.json](BUILD.json) 绑定本目录的实际源码字节。
原始 [研究执行档案](research_evidence/interface-research-evidence-v1.tar.gz) 包含首次失败源码、
最终源码、四组状态、完整日志和两种组合文件；无需凭叙述重建曾执行的输入。

独立审查分开保留：

- [Good 包络语义审查](research_evidence/GOOD_ENVELOPE_REVIEW.md)。
- [最终源码绑定与逐行校准量词审查](research_evidence/FINAL_SOURCE_BINDING.json)。
- [逐行联合风险审查](research_evidence/VARIABLE_JOINT_REVIEW.md)。
- [统一有限例与哲学反馈审读](research_evidence/BOOKS_RESEARCH_REVIEW.md)，及
  [三项修订的最终文本绑定](research_evidence/PHILOSOPHY_REVISION_BINDING.json)。

旧审查中尚未提供的日志字段和当时的待发布状态不改写；后续实际执行记录补足其范围。
生产的 102 个公开源声明、219 个原生声明、163 条新增证明边和 17 组复用提示审查
仍属于此前九模块收尾，不能自动计入本目录的新研究声明。

### 复现聚焦检查

从 `formalization/ueot-core` 项目目录运行，在临时目录构造组合文件即可；生产 `.olean`
和入口无需修改。以下配方保留实际组合顺序与换行：

```python
from pathlib import Path
from tempfile import TemporaryDirectory
import subprocess

research_dir = Path("docs/compression/theory_completion/unified_closure/interface_research_v1")
samples = (research_dir / "VariableRegisteredSamples.lean").read_bytes()
with TemporaryDirectory(prefix="ueot-interface-check-") as tmp:
    checks = {
        "GoodSelectedEnvelope.lean": (research_dir / "GoodSelectedEnvelope.lean").read_bytes(),
        "VariableRegisteredSamples.lean": samples,
        "VariableRegisteredSamplesBoundaryCheck.lean": samples + b"\n" +
            (research_dir / "VariableRegisteredSamplesBoundaryTail.lean").read_bytes(),
        "VariableRegisteredJointCheck.lean":
            b"import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredDeploymentRisk\n" +
            samples + b"\n" + (research_dir / "VariableRegisteredJoint.lean").read_bytes(),
    }
    for name, contents in checks.items():
        source = Path(tmp) / name
        source.write_bytes(contents)
        subprocess.run(["lake", "env", "lean", str(source)], check=True)
```

## 3. 有限观察像仍有真实的证明责任

[接口研究](INTERFACE_RESEARCH.md) 区分参考核也闭合于同一个有限载体的方案与允许参考
越界的方案。若实际只观察到 \(0\)，参考行为
\(\tfrac12\delta_0+\tfrac12\delta_1\)，丢弃 \(1\) 后重新归一化会把真实 TV
\(1/2\) 错写为零。

[有限观察逃逸论证](FINITE_OBSERVATION_ESCAPE.md) 已给出一侧有限载体的双向 TV 等式：
用事件与补事件证明反向不等式；再通过同一有限集合上的全部未逃逸历史原子质量相等，
将有限吸收参考的路径 TV 精确带回原始参考过程。该书面证明保留任意参考核的外部质量，
并继续使用原始参考事件概率；完整路径与末状态被明确区分。
其编码、因果核及路径原子归纳仍须落实到 Lean。当前生产及本目录已编译联合风险原型
均保留 `[Fintype Y]`。
逐行样本量也未推广为随机停时或数据依赖分配；若各行半径不同，还须明确到既有时刻预算
的上界桥，或使用实际占据加权的逐行误差端点。

## 4. 从共同源反哺两部独立著作

[数学伴随稿](UNIFIED_FINITE_SOURCE_EXAMPLE.md) 固定实际
`survivalMicroKernel` / `conflictRewardControl`，逐步连接商、受限最优、修复、支持和风险。
[Lean 来源表](UNIFIED_FINITE_SOURCE_LEAN_MAP.md) 区分实际已有声明、新的书面推导和仍需
程序、可信执行器、时钟等附加输入的桥。

新书面例中，两步曾失效风险 \(15/64\)、终点失败 \(1/8\)、失效后恢复 \(7/64\)
属于每个历史条件下中断动作概率固定为 \(1/8\) 的同一个源；它们尚未成为新数值 Lean 见证。
生产注册自适应见证的 \(9/64\) 与现行数学书另一模型的 \(8/5\) 保留各自来源。

[哲学研究稿《可以被保持的组织》](UNIFIED_FINITE_SOURCE_PHILOSOPHY.md) 独立论证有范围的
客体描述、活动中的持续、目的的实现条件与价值理由，以及恢复未来能力和历史责任的关系。
它不把控制最优性当成价值的充分理由，也不把可修复性当作所有意义的必要条件。
两部已出版书稿仍各有独立的 MD、TeX、PDF；后续书稿修订应把这些论证融入相应章节，
并同步维护来源与 API 范围。

## 5. 本次证据复用的边界

编译项目的完整历史 Core Git 树为 `624c9a0d4b26d9c3e6489c45050d66e96129b3dc`。
新增本目录以后，包含文档的 Core 目录树会改变；生产 `UEOT` 源树仍为
`73dda901d236295245839a75f683cd7839690fa8`，全量生产 source-tree SHA256 为
`91621694fadc223f63b76298a6eaf10078e59bd87c9dbc798726a6e366b1f357`。
全部生产源、入口、依赖锁和工具链均保持，现行两书六项正文产物也保持字节相同。

此前完整 `lake build UEOT`、实际 canonical 授权、89 项 base parser tests、包含真实
fast-audit 的 30 项 FKRG 测试，以及两书全页版面审查，见发布交接及 `release_evidence/`。
自动治理通过与 Lean 未运行分开表达；这些本地或手动证据不充当计数型 FINAL push-event 收据。
冻结 106 P-ID 仍为 **11 generated / 89 adapters / 6 boundaries**。

下一步从这些已证研究接口进入适当的生产登记，并完成有限观察范围的真实桥；统一主线继续
按 MINCORE → H0 → P-ID → TheoryCompletion 逐箭头核对。有限时域可行不推出无限存活，
零未认证占据不推出零运行失败，正概率历史与同一策略条件不能删除。
经验源适用性、意识、伦理和完整自然理论不由上述条件数学自动获得证明。
