# AI Agent Playbook: 如何维护 `research/lab_wiki/` 与召开 AI 组会

**所有参与 UEOT 探索、证明、数值验证或对抗审稿的 AI Agent，在动手修改代码或提出新猜想之前，必须先阅读本手册。**

---

## 1. 启动前必读清单（Pre-Flight）

每次开始新任务或加入 Swarm 时，按顺序读取：
1. [OPEN_SPECS.md](OPEN_SPECS.md) — 确认当前 `SPEC-ID` 的形式化目标、允许前提（`C/B/S/P/E/O/X`）和证伪标准。
2. [VERIFIED_LEMMAS.md](VERIFIED_LEMMAS.md) — 复用已经通过门禁的引理，避免重复造轮子。
3. [DEAD_ENDS.md](DEAD_ENDS.md) — **重点检查**已有反例与失败路线，严禁在未满足 `Reopen Condition` 时重走死路。
4. `MEETING_MINUTES/` 中最新一期纪要 — 了解上一轮组会的裁决与当前分配。

---

## 2. 四种标准 Agent 角色

| 角色 | 职责 | 写入权限 | 禁止事项 |
| :--- | :--- | :--- | :--- |
| **Explorer（探索组）** | 在独立 worktree 中针对指定 `SPEC-ID` 尝试数学证明、Lean 4 拆解或数值构造 | 独立分支代码、`DEAD_ENDS.md`（追加失败记录）、向组会提交进展摘要 | 不得跳过门禁直接改写 `VERIFIED_LEMMAS.md`；不得偷偷引入 `axiom`/`sorry`/`opaque`/`native_decide` |
| **Red-Team Referee（红队审稿）** | 专门找漏洞：检查隐含物理公设、边界条件退化、量词范围、数值外推误差与伪收敛 | `DEAD_ENDS.md`（登记被证伪路线）、组会纪要中的红队质询栏 | 不得只做礼貌性附和；每轮组会必须对每个候选方案给出明确的 **PASS / BLOCKED / FALSIFIED** 裁决及理由 |
| **Gatekeeper（自动门禁）** | 由 [gatekeeper.py](gatekeeper.py) 客观执行，不依赖主观判断 | `receipts/latest_gate.json`（仅 `--write-receipt` 时） | 永不放行带 `sorryAx`、`Lean.ofReduceBool` 或未复核数值的条目 |
| **Coordinator / Chair（主持人）** | 组织组会、裁决路线去留、合并已验证引理、更新 `OPEN_SPECS.md` 状态与提交正式 PR | 全部 Wiki 文件（受门禁约束） | 不得将红队标为 `BLOCKED` 的路线直接晋升 |

---

## 3. 单轮「AI 组会」标准 SOP

建议每完成一个子里程碑（或每 2–4 小时周期）召开一轮组会：

1. **Step 1 — 会前同步（Sync）**
   - 各 Explorer 在各自工作树运行 `python3 -B research/lab_wiki/gatekeeper.py --mode fast`（若涉及 Lean 证明则跑 `--mode lean`）。
   - 向主持人提交三段式汇报：**① 尝试路线与最新进展**、**② 新产出的可复核引理/数值脚本**、**③ 遇到的卡点或失败路径**。
2. **Step 2 — 红队质询（Adversarial Critique）**
   - Red-Team Referee 逐一审查各组提交，重点核对：
     - 是否新增了未在 `OPEN_SPECS.md` 声明的物理假设（`S/P/E/O/X`）？
     - Lean 声明是否出现「空洞前提（vacuous hypothesis）」或偷换定义？
     - 数值检查是否仅在单点成立而未覆盖整个声明域？
3. **Step 3 — 纪要落盘与止损（Record & Prune）**
   - 复制 [MEETING_MINUTES/TEMPLATE.md](MEETING_MINUTES/TEMPLATE.md) 为 `MEETING_MINUTES/YYYY-MM-DD-round-NN.md`。
   - 将所有被证伪或陷入死循环的路线追加写入 [DEAD_ENDS.md](DEAD_ENDS.md)。
   - 仅将通过 `gatekeeper.py --mode lean`（或 `--mode full`）的成果追加写入 [VERIFIED_LEMMAS.md](VERIFIED_LEMMAS.md)。
4. **Step 4 — 门禁验收（Gate Check）**
   - 主持人运行：
     ```bash
     python3 -B research/lab_wiki/gatekeeper.py --mode fast --write-receipt
     ```
   - 确认返回码为 `0` 后，再分发下一轮任务。

---

## 4. 硬性维护规范（Machine-Checked by `gatekeeper.py`）

为了保证自动门禁能机器校验本 Wiki，维护时必须遵守以下格式约定：

1. **`OPEN_SPECS.md`**：
   - 每个开放任务必须使用唯一 ID：`SPEC-YYYYMMDD-NN`（例如 `SPEC-20261124-01`）。
   - 必须包含字段：`Status`（`OPEN` / `IN_PROGRESS` / `CLOSED` / `DROPPED`）、`Target`（Lean 模块或物理脚本）、`Falsification Criterion`（明确失败标准）。
2. **`VERIFIED_LEMMAS.md`**：
   - 每条记录必须使用唯一 ID：`LEMMA-YYYYMMDD-NN`。
   - 表格中必须给出仓库内**真实存在的**文件路径（`File` 列），且 `Gate Status` 必须为 `PASS`。
   - **禁止**在 `VERIFIED_LEMMAS.md` 中出现 `TODO`、`TBD`、`PENDING`、`sorry`、`admit` 等占位词（`gatekeeper.py` 会直接报错拦截）。
3. **`DEAD_ENDS.md`**：
   - 每条记录必须使用唯一 ID：`DEAD-YYYYMMDD-NN`。
   - **只追加，不删除**；如果后续因为新引理/新工具重新打开，将状态改为 `REOPENED` 并注明依据，保留历史教训。
4. **禁止物理前提偷渡**：
   - 任何新引入的物理输入必须按 UEOT 规则标明依赖类别（`C` 核心 / `B` 背景 / `S` 新公设 / `P` 物理输入 / `E` 实验 / `O` 观测 / `X` 外部定理），不得将条件性恢复包装成无条件推导。

---

## 5. Swarm / `/teamwork` 开组会 Prompt 模板

### Explorer Agent Brief 模板
> 你是 UEOT 研究组的 **Explorer-A**。先阅读 `research/lab_wiki/AGENT_PLAYBOOK.md`、`OPEN_SPECS.md`、`VERIFIED_LEMMAS.md` 和 `DEAD_ENDS.md`。你的目标是攻克 `SPEC-YYYYMMDD-NN`（路线：<指定路线>）。在独立工作树内工作：若构造出 Lean 4 证明或数值验证脚本，先运行 `python3 -B research/lab_wiki/gatekeeper.py --mode lean` 自检；若路线受阻或发现反例，整理清晰失败原因供写入 `DEAD_ENDS.md`。完成本轮后向主持人汇报三段式进展。

### Red-Team Referee Brief 模板
> 你是 UEOT 研究组的 **Red-Team Referee**。阅读 `research/lab_wiki/AGENT_PLAYBOOK.md` 与本轮各 Explorer 的产出。你的唯一目标是**证伪和找漏洞**：检查隐含物理前提、Lean 定理前提是否空洞、数值证书是否缺边界/误差预算、`check_no_escapes.py` 与 `ExhaustiveAxiomAudit.lean` 是否真实通过。对每个候选方案给出 `PASS` / `BLOCKED` / `FALSIFIED` 裁决与具体证据。
