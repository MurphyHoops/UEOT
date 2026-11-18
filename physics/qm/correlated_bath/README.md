# 相关双模浴：从不可识别的 Ramsey 曲线到完整记录和局域场响应

科学基线为第70章提交 `44b6cd200cd01eccf15d4dc817311388d317a1af`。本研究增加一条有限的同源链：对未知涨落与耦合构造精确等价对，加入有校准成本的带符号干预，用冻结试验对同一源的两棵控制树给出可复算的完整误差，并把其中的干预相位接到局域量子场。复量子、Fock 表示、仪器模型、制备相位、频率和相对耦合均为独立输入。

| 科学出口 | 可复核结果 |
|---|---|
| 自由 Ramsey 与响应 | 全部自由 Ramsey 时长只识别 u=λ²(2n+1)、v=λ²c。两组参数共享整条曲线；带符号的因果断开相位增加对 w=λ² 的访问。原时序 Bell 事件在该等价纤维上确实变化。 [解析与冻结试验](inference/INFERENCE.md) |
| 完整 CQ 与量词 | 对四种停止记录、任意输入和有限参考，校准覆盖事件内的半 diamond 上界为 **0.033892297103、0.035357047207**。有限名义表示以有理 CP/TP 仪器发布。 [联合域证明](certificate/PROOF.md) · [精确回执](certificate/joint-result.json) |
| 终端检验 | 指定 Bell 输入与八格读出、含每格偏差及40位取整，上界 **0.046090140889、0.047554890993**。原时序和交换间隔的冻结留出均未拒绝，独立相位留出选择了生成备择，违约读出被拒绝。 [计数与判决](inference/holdout_results.json) |
| 另一条有限化路径 | 真实 Fock 边界传播与相关初态尾组成统一界。K=16 时含有界算术和物理化的同参数上界 0.027602916940。该预算针对另一条预测实现，与直接 Weyl 的名义有理实现分别计算。 [定理与量词](dynamics/DYNAMICS.md) · [计算](dynamics/observed.json) |
| 量子选择 | 在全体纯态上要求连续可逆传递排除非平凡经典单纯形和标准直和；实、复单系统都存活。一个仅有可分复合态的模型仍能满足传递和局部层析但缺少普遍纯化。 [候选、反模型与 CDP 对照](selection/SELECTION.md) |
| 局域场 | 由同一个局域 KG 源精确匹配两低模。两模留下 0.001330794 rad 的类空伪相位，完整场因微因果使其消失；同地相位从两模 0.163731618 变为场 0.209161320。 [空间剖面、功与尾界](field/FIELD.md) |
| 其他物理责任 | 已算等隙能量交换、三色/五色荷电规则、两个中性介子通道的无预测反例、线丛粘合与零模、两引力作用量及相同膨胀背景的不同扰动。 [前提、观测和失效条件](sectors/RESULTS.md) |

[完整有序合成数据资格和统计设计](inference/INFERENCE.md)。720,000 次校准与408,000 次独立留出，共1,128,000条合成记录。99%校准覆盖和留出检验有各自的失败概率。校准集合仍容许不同符号的浴相关 c。三方交审实测了未旋回制备时钟的误差、非冻结协议替换、仅 Bell 可见的探测器误差和取整余项。[A审B及整合](selection/REVIEW.md) · [B审C](dynamics/REVIEW.md) · [C审A](inference/REVIEW.md)

**经验状态为匹配器件 NOT_CERTIFIED。同信息、同操作、同预算的强标准基线为 EQUIVALENT_NO_ADDED_GAIN。** 设备还需真实的有序校准/留出、制备和相位时钟、SPAM、泄漏、漂移与控制误差。以上正结果是有限物理前提下的条件结论，多个明确反例限制它们向全局统一的推广。此前的Lean执行身份属于原证明库，本研究新增的是书面推导、定向区间、可执行检查和合成试验。

## Reproduction

From a Git checkout containing the scientific baseline above, use Python 3.14 with NumPy 2.5.4, SciPy 1.18.1, mpmath 1.3.0 and SymPy 1.14.0. From the repository root, run the following with fresh receipt paths.

```sh
python -B physics/qm/correlated_bath/portable_replay.py --repo . --receipt /tmp/ueot-correlated-replay.json
UEOT_UPSTREAM_REPO="$PWD" OPENBLAS_NUM_THREADS=1 python -B physics/qm/correlated_bath/dynamics/verify_dynamics.py --receipt /tmp/ueot-correlated-dynamics.json
python -B physics/qm/correlated_bath/verify_extensions.py
```

The first command regenerates ordered synthetic records and scores the frozen predictions. The second checks finite oscillator evolution and the rational channel repair. The third compares the field calculation and three sector programs with the archived observations. In `field/observed.json`, binary endpoint tuples encode closed interval bounds.
