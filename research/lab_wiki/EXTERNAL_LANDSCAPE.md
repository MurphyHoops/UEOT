# 外部前沿研究与可复用成果备忘（`[EXT]` 只读参考库）

> **认识论与门禁铁律（`[EXT / UNVERIFIED-BY-UEOT]`）**
> 本文件仅用于为 UEOT 各并行团队记录外部最新科研进展、公开代码库及未来可能的数学接口位置。
> **任何外部宣称或外部 Lean 代码在未通过本仓库 [gatekeeper.py](gatekeeper.py) 全套独立定义核验与无逃逸审计（`sorryAx = 0`）之前，一律标记为 `[EXT / UNVERIFIED-BY-UEOT]`**：
> 1. 严禁直接写入 [VERIFIED_LEMMAS.md](VERIFIED_LEMMAS.md) 或 `validation/physics_unification/VALIDATION_LEDGER.json`；
> 2. 严禁据此单方面解除 UEOT 的 `IR-X`、`noBulkTransition`、`UV-X`、`CHIRAL-X`、`H2dMinimalIrreducibleCore`、`physical_unification = "OPEN"` 或 `device_certified = false` 诚实边界锁。

---

## 1. OpenAI 4D 量子杨–米尔斯存在性（`UV-X` 半场）Lean 4 发布（`2026-10 / 2026-11`）

- **认识论标签**：`[EXT / UNVERIFIED-BY-UEOT]`
- **外部代码标识**：`OpenAI-YM-20261028`（约 100 万行 Lean 4 代码，超 9,000 个文件）
- **关键时间线**：
  - `2026-09-09`：内部模型生成纯杨–米尔斯存在性自然语言证明草案（`2026-09-18` 扩展至含费米子 QCD 草案）；
  - `2026-10-16`：内部 Lean 4 形式化编译通过；`2026-10-26` 对外公开宣布；
  - `2026-11-10 ~ 2026-11-11`：经独立托管委员会公布初步评估并向公众释放 Lean 4 代码仓库。
- **独立托管委员会**：David Gross（主席）、Arthur Jaffe、Michael Douglas、Igor Klebanov、Nikita Nekrasov。

### 1.1 宣称覆盖范围 vs 明确未解决边界

| 问题组成部分 | OpenAI-YM 覆盖情况 | 与 UEOT 板块对应关系 |
| :--- | :--- | :--- |
| **存在性（短距离 / 标度极限构造）** | **宣称已形式化证毕**：基于 4D Wilson 格点规范理论、Tadeusz Bałaban 1980 年代多尺度重整化群（RG）与 Osterwalder–Schrader 重构，对任意紧单规范群构造出满足 Wightman 公理的 4 维相对论量子场论（另伴 QCD 与标准模型相关草案）。 | 对应 UEOT 路线中的 **`UV-X`（存在性 / 连续极限构造）** 维度。 |
| **质量间隙（$\Delta > 0$）与色禁闭** | **明确未证明（Out of Scope）**：克雷研究所千禧年大奖仍未闭合。 | 正好对应 UEOT 主力军团当前主攻的 **`IR-X`（质量间隙）**。 |
| **无限体积极限唯一性与体相变排除** | **明确未证明（Open）**：依托弱耦合渐近自由与紧致性抽子列可绕过中耦合全局唯一性，故未给出无限体积极限唯一性，也未排除中耦合多相行为。 | 正好对应 UEOT 的 **`noBulkTransition`**、7 路反例分离与 `O-MI13` 两相共存难题。 |

### 1.2 学界审计与可读性解密追踪（复用前必查清单）

由于 `OpenAI-YM-20261028` 释放时未附带人类可读完整数学专著，且代码内充斥机器生成代号（如 *Treasury*、*Jewel*、*Sheet*、*sails*），学界目前正将其作为待核验的原始材料进行逐行审计与反译：

1. **核心反译/审计项目**：
   - `hairer/humanise-yang-mills`（Martin Hairer 牵头）：构建从终极定理到引理的依赖图，并将 Lean 证明转写为可审阅的标准数学专著与定义审计；
   - `yang-mills-informalization`（Scott Armstrong 维护，与 Hairer 团队协同）：自动化依赖图拆解与自然语言草稿汇编。
2. **重要审慎声音**：
   - Peter Woit（*Not Even Wrong*, `2026-10-26` & `2026-11-11`）批评其初期透明度不足并警示自动化形式化与公开同行评议之间的张力；
   - Terence Tao 等学者在 `2026` 年多次警示 AI 批量生成证明造成的验证瓶颈，强调机器编译通过不等于原始物理/数学定义无隐藏偏差。

### 1.3 UEOT 未来团队可复用接口与 4 条前置门禁

1. **当前战略分工定位**：
   - UEOT 的 `IR-X` + `noBulkTransition` 主攻的是 OpenAI **尚未解决的下半场（质量间隙、中耦合非微扰区间与无限体积极限唯一性）**，两者呈互补接力关系，而非重复造轮子；
   - UEOT 核心长板在于人类可读的结构性新数学（如 `Cycles 12–16` 几何分解、Dimensional Schur-Peeling、7 路反例零泄露照妖镜与 40 位算术认证）以及统一物理接口（见 [OPEN_SPECS.md](OPEN_SPECS.md) 与 [MULTI_TEAM_CHARTER.md](MULTI_TEAM_CHARTER.md)）。
2. **未来 `UV-X` 团队若拟桥接复用 OpenAI 存在性成果，必须先全部满足以下 4 项准入条件**：
   - **条件 A（定义与公理独立清零）**：待 `hairer/humanise-yang-mills` 完成人类可读定理陈述与定义核验，并在 UEOT 工具链中独立验证标准公理集、零 `sorryAx`、无隐含有限环面/人为截断前提；
   - **条件 B（格点作用量与测度接口严格匹配）**：确认其 4D Wilson 格点标度极限与无限体积极限子列挑选方式，能与 UEOT `IR-X` 的关联衰减界、反射正性及 `noBulkTransition` 假设严丝合缝对接；
   - **条件 C（通过 UEOT 7 路反例证伪校验）**：确认引入的紫外控制引理在离散格距尺度上不会误证出 4D $U(1)$、`BC140`、5D $SU(2)$ 或 4D $SU(5)$ 闭合（严守五条禁止伪类比红线）；
   - **条件 D（本地全量门禁留档）**：以独立 PR 接入 UEOT 形式化仓库并通过 `python3 -B research/lab_wiki/gatekeeper.py --mode full` 后，方可写入 [VERIFIED_LEMMAS.md](VERIFIED_LEMMAS.md)。

---

## 2. OpenAI 散射振幅发现备忘（`GPT-5.2`, `2026-02 / 2026-03`）

- **认识论标签**：`[EXT / UNVERIFIED-BY-UEOT]`
- **代表论文**：
  - *"Single-minus gluon tree amplitudes are nonzero"*（IAS / Harvard / Cambridge / Vanderbilt / OpenAI，`2026-02`）；
  - 姊妹篇：*"Single-minus graviton tree amplitudes are nonzero"*（`2026-03`）。
- **核心结论（参考备用）**：在半共线（half-collinear）/ Klein 空间或复动量运动学下，单负螺旋度树图胶子及引力子散射振幅并不恒为零，模型给出分段常数闭合公式并由推理系统检验其满足 Berends–Giele 递推关系与 Weinberg 软定理。
- **UEOT 潜在复用场景**：供未来推进 **`H1`（因果自旋-2 引力子 / 散射振幅与边界 S-矩阵一致性）** 的独立赛道在核验具体运动学特征（Euclidean vs Lorentzian/Kleinian signature）后按需参考，不得直接混淆用于欧氏 4D 格点质量间隙论证。
