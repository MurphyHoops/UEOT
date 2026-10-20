# C 对 A 纯化与操作接口的最终交叉审查

**PASS：两份最终冻结主源码未发现数学阻塞或主张越界。** 本报告只读实际源码，并读取作者真实 focused PASS 日志；未重跑 Lean、未修改 A 或共享源码。具体 Bell/负控见证现已追加只读审查；root 统一门仍另行验收。

| 源 | 最终 SHA256 | 作者已通过日志 |
|---|---|---|
| `UEOTQM/QuantumPurification.lean` | `fb0692ed93c14aa7182cb09b3e205060f493f005672d16a69fc6e8da59ca5b6d` | `/tmp/qm317_A_purification_round2.log` |
| `UEOTQM/OperationalSystems.lean` | `cb764474361fa833390fbe33e3d1b363a05c78639e0819d5d5de4648c1b5b55e` | `/tmp/qm317_A_operational_round3.log` |

## 完整状态与凸极点

`QuantumPurification.IsPure` 对完整现有 Density 的全部分解量化。`vectorState_isPure` 是秩一归一态在该完整集合中极端的证明，并未把秩一改写成纯性的定义。PSD 的 Gram 因子来自实际正锥的 C⋆ 等价定理，输入不含额外 Gram、纯性或边际见证。

压缩零论证将正压缩写成 B†B，真实迹零推出 B=0，再得到支持块消失。凸分解的两个压缩均非负，其零和迫使分别为零；sandwich 与迹一迫使两分量等于原态。`purificationVector` 使用实际积载体，`purification_marginal` 调用矩形 Kraus 偏迹。空载体若有 Density 则由迹一矛盾，未预先偷加不合法状态。

## 操作语言与三个完整适配

FiniteSystem 的复合载体确为 A×B。Presentation 只提供操作；Laws 的七条基本规律分别对 classicalModel/complexModel/realModel 证明。PurificationExistence、LocalTomography 是独立候选 Prop，均不是呈现构造器的输入字段。

经典模型是全单纯形及全部随机核；复模型是全部 PSD 迹一矩阵、全部合法效应及有限矩形 Kraus 过程；实模型是完整的逐项实 PSD 迹一子空间、实效应及真实 Kraus 过程。并未用“任意正映射”偷代完全正过程。偏迹由 B 的实际 RectangularChannel 提供，其放大正性范围为任意有限辅助空间的全部联合 PSD 输入。

`complex_pure_iff` 只桥接相同完整态的两种极点写法；`complex_purification` 使用已经证明的任意 Density 构造。`classical_not_purification` 保留任意有限辅助系统；`core_first_marginal_no_purifies` 调用真实旧 Core firstQuotientState 边际反例，未把有限接口提升为 Core 全局重建定理。`real_not_localTomography` 仍是全实局部产品效应下的反例，未宣称实量子纯化失败。

## 边界与验收

不存在“这些候选原则由 Core 推出”或“它们唯一选择复量子理论”的定理。未证明纯化的辅助酉唯一性、纯态当且仅当秩一或完整范畴相干性；这些均未被当前模块冒称。主源 SHA 与作者最终声明相同，两个实际日志均包含完整成功结尾。A 的具体正负控见证仍按独立门处理。

## 最终具体见证追加审查

`QuantumPurificationExamples.lean` 最终 SHA `57b764a8d9b7787509a0f8a5e92f04a86abc5f3f4db58f3c441be2e29a1c3e34`，作者 `/tmp/qm317_A_witness_round3.log` 的20条实际公理打印全名精确匹配且仅标准基础公理。本审查未重新编译。

Bell振幅(1+i)/2仅引入整体相位，实际外积为通常Bell投影；其完整Density极点与偏迹I/2均调用已证明主API。普通经典扩张存在/任意有限纯扩张不存在的区分保留；singleton假纯是独立受限谓词，未更改主模型全状态空间。解除实局部效应限制后的复乘积区分仍在同一操作接口中成立。三项约定负控与Bell正控均未发现范围问题。
