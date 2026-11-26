# UEOT 多团队并行攻坚防冲突公约 (`MULTI_TEAM_CHARTER.md`)

**生效范围**：所有基于 UEOT 仓库（`MurphyHoops/UEOT`）开展并行研究、形式化证明、数值验证或多智能体 `/teamwork` 协作的团队、会话与 Swarm 看板。  
**核心目标**：让 `H2d / IR-X`、`UV-X`、`CHIRAL-X`、`H1d4d`、`H3d / H4d` 等多条战线能够在同一代码库、同一宿主机与同一套形式化门禁下高频并行推进，**互不覆写、互不误唤醒、共享可信资产、绝不拉垮 CI**。

---

## §1 唯一事实源铁律（Never Read Stale Local Checkouts）

1. **永远以远程 `origin/main` 为唯一事实源**：本地镜像目录（如 `ueot-core-upgrade/`）为**只读底座**，往往停留在历史旧提交（例如旧 Round），**严禁任何团队把旧工作树当成最新前沿**，也严禁直接修改 `ueot-core-upgrade/` 或他人 worktree 中的文件。
2. **标准开线启动流程（每支新团队启动第 1 步）**：
   ```bash
   # 1. 拉取最新 origin/main
   git -C /path/to/UEOTCORE/ueot-core-upgrade fetch origin main

   # 2. 基于 origin/main 建立本团队专属 worktree 与语义化分支
   git -C /path/to/UEOTCORE/ueot-core-upgrade worktree add \
     -b physics/<lane>-<topic> /path/to/UEOTCORE/wt-<lane>-<topic> origin/main

   # 3. （可选）APFS 写时复制克隆温 .lake 缓存，免去从零编译 mathlib（零磁盘翻倍）
   cp -cR /path/to/warm/.lake \
     /path/to/UEOTCORE/wt-<lane>-<topic>/formalization/ueot-physics-unification/.lake
   ```
3. **开工必读 4+1**：在新 worktree 内依次读取 [MULTI_TEAM_CHARTER.md](MULTI_TEAM_CHARTER.md)、[AGENT_PLAYBOOK.md](AGENT_PLAYBOOK.md)、[OPEN_SPECS.md](OPEN_SPECS.md)、[VERIFIED_LEMMAS.md](VERIFIED_LEMMAS.md) 与 [DEAD_ENDS.md](DEAD_ENDS.md)。

---

## §2 赛道分区所有权与写入互斥表（Lane A–E）

在多团队并行期间，每条战线仅允许修改自己所属赛道的探索目录与新建 Lean 4 模块，**严禁跨区篡改**：

| 赛道 | 负责问题域 | 专属 Python 验证/研究目录 | 专属新建 Lean 模块命名规范 | 当前状态与边界 |
| :--- | :--- | :--- | :--- | :--- |
| **Lane A（在研占用）** | `H2d / IR-X`（4D 纯 $SU(2)$ 非微扰质量间隙，$\beta \in (0,\infty)$） | `physics/unification/nonabelian_lattice_massgap_h2/**` | `IRXWave*.lean` / `IRX*.lean` | **已由 Team 1 占用**；兄弟团队**只读勿写** |
| **Lane B（可开新线）** | `UV-X`（4D 非阿贝尔连续统 UV 稳定、Balaban 重整化与微扰—非微扰桥） | `physics/unification/nonabelian_chiral_constructive/` 或新建 `uv_continuum_h2d/` | `UVX*.lean`（严禁写死 Round 序号） | 可立项；需先预注册负控制矩阵 |
| **Lane C（可开新线）** | `CHIRAL-X`（Overlap / Ginsparg–Wilson 手征规范不变性与非微扰手征极限） | `physics/unification/chiral_gauge_overlap_clock/` 或新建 `chiral_continuum_h2d/` | `CHIRALX*.lean` | 可立项；需分离 doubler/反常控制 |
| **Lane D（可开新线）** | `H1d4d`（4D 非截断非多项式量子引力量子测度脱耦） | `physics/unification/nonperturbative_4d_measure_h1d4/` | `H1d4d*.lean` | **`H1` 操作层已闭合且严禁再切片**，仅攻无条件数学核心 `H1d4d` |
| **Lane E（可开新线）** | `H3d / H4d`（先验无量纲常数选定、Bell-CHSH 器件/盲留出与实验对齐） | `dimensionless_couplings_viability_h3/`、`bell_chsh_blind_holdout_h4/` | `H3d*.lean` / `H4d*.lean` | 严禁伪造实验 shot；无原始数据保持 `device_certified: false` |

---

## §3 共享热点文件「平时只读、合入前 Rebase」协议

全仓仅有以下 **5 类共享热点文件** 会被多条赛道共同更新：

1. `formalization/ueot-physics-unification/UEOTPhysicsUnification.lean`（总 import 清单）
2. `formalization/ueot-physics-unification/scripts/ExhaustiveAxiomAudit.lean`（含 `expectedModules` 计数器）
3. `physics/unification/run_verification.py`（总验证器登记与 `lean_modules`）
4. `physics/unification/verification.json`（校验与摘要索引）
5. `research/lab_wiki/` 台账（`OPEN_SPECS.md`、`VERIFIED_LEMMAS.md`、`DEAD_ENDS.md`、`MEETING_MINUTES/`、`receipts/latest_gate.json`）

为彻底消除 Git 合并冲突，所有团队必须严格遵守 **四步协同铁律**：

1. **Wave 探索期禁碰热点文件**：在各 Wave 研发与独立脚本攻关期，只读写本赛道专属文件；新建 Lean 模块请采用**赛道语义命名**（如 `UVXWave1BalabanBridge.lean`），**绝对不要把假定的模块序号（如 `#48`）硬编码进文件名**。
2. **合入前 Rebase 再登记**：只有当本轮（Round）成果通过独立零信任审计准备整合提交 PR 时，才执行：
   ```bash
   git fetch origin main && git rebase origin/main
   ```
   然后再基于最新 `origin/main` 把新增 Lean 模块追加进 `UEOTPhysicsUnification.lean`、将 `ExhaustiveAxiomAudit.lean` 的 `expectedModules` 在当前真实总数上 **`+1`**、更新 `run_verification.py` / `verification.json` 并追加 `lab_wiki` 记录。
3. **短生命周期整合 PR**：触碰热点文件的 PR 必须通过 `gatekeeper.py --mode full --write-receipt` 后**尽快合并进 `origin/main`**；若并发团队先一步合并导致需要二次对齐，后发团队 `rebase origin/main` 并重跑确认后即可合并，禁止让改动热点文件的分支长期悬置。
4. **Lab Wiki 只追加、零占位词**：
   - `OPEN_SPECS.md`：按赛道开设独立 `SPEC-YYYYMMDD-NN` 行；
   - `VERIFIED_LEMMAS.md`：仅追加本赛道已过门禁的 `LEMMA-YYYYMMDD-NN`，严禁出现 `TODO`/`TBD`/`PENDING`/`WIP`/`FAIL`/`FAILED`/`sorry`/`admit`/`sorryAx`/`native_decide`（用 `bracket lo/hi` 代替占位词）；
   - `DEAD_ENDS.md`：发现被证伪路线立即追加 `DEAD-YYYYMMDD-NN`，只追加不删除。

---

## §4 永久禁区、工程约束与统一认知锁

1. **永久物理与历史禁区**：
   - 严禁修改 `physics/qm/**`（`DEAD-20261124-08` 已锁死）；
   - 严禁篡改已合入 `origin/main` 的历史 Wave Lean 模块或破坏历史 PR #468 回归契约（坚持只增不破）；
   - 提交前确认 `git status --short` 中 **零 `.lake/`、零 `__pycache__/`、零散落的临时 `explore_*.py`**。
2. **反膨胀与 40 位纯算术合同**：
   - **1 独立问题 = 1 专职 Researcher**，每条路线严格 **`<= 2` 主脚本**（`probe_<id>.py` + `certify_<id>.py`，单文件 `<= 1500` 行）；
   - 所有正式 `certify_*.py` 与合入 `physics/unification/` 的验证代码只允许使用 `fractions.Fraction`、`sympy`、`mpmath`（`mp.dps >= 55, iv.dps = 40`）与标准库，必须通过 `! grep -En "numpy|scipy|iv\.acos|float\("` **0 匹配**（含注释与字符串）；
   - 严禁对 `> 8x8` 矩阵执行 `SymPy` 符号 `.det()/.inv()/.eigenvals()`（防 99% CPU 挂死）；
   - `[E]` 探索脚本严禁硬编码或导入任何待验证的目标精确常数，必须通过 AST 零泄露自检与赛区负控制矩阵（如非阿贝尔赛道强制 7-Way `C1..C5` + `Litmus 6`）。
3. **统一认知边界锁**：
   - 除非在所有参数与连续统极限上给出**无条件全区域闭环证明**，否则所有公开前沿开关（`IR-X`、`noBulkTransition`、`UV-X`、`CHIRAL-X`、`H1d4d`、`H2dMinimalIrreducibleCore`、`H3d`、`H4d`、`physical_unification`）一律强制维持 `.OPEN` / `"OPEN"` / `[X]`；
   - 未补齐合规真实器件逐 shot 原始记录前，强制维持 `"device_certified": false`。

---

## §5 同机算力分配、内存与门禁错峰礼仪

1. **单线程 BLAS 强制锁死**：当宿主机上同时存在 `2` 条及以上研究线或并行轨道时，所有 Python 工作命令必须强制加环境变量：
   ```bash
   OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 python3 -B ...
   ```
   防止多线程池彼此抢核导致 10x–50x 性能塌方。
2. **门禁与编译错峰礼仪**：
   - 日常 Wave 探索阶段优先跑轻量门禁 `gatekeeper.py --mode fast`（~`0.5s`）；
   - 执行重型全量审计 `gatekeeper.py --mode full`（`origin/main` 基线含 ~`105s` `ExhaustiveAxiomAudit` 与 ~`331s` `run_verification.py --check`）或大规模 `lake build` 前，先用 `ps` 检查宿主机当前是否有兄弟团队正在跑重型门禁，错峰发起。
3. **验证套件增量上限**：每一轮整合合入对 `physics/unification/run_verification.py` 单线程运行时间的净增量必须严格控制在 **`<= 30s`**，以确保全仓套运行时间长期稳居 `480s` CI 预算之内。

---

## §6 Swarm 通讯板隔离与跨团队成果交接

1. **独立对话与独立看板**：每支新团队启用自己独立的聊天会话与独立 Swarm 看板，不要向其它团队的看板发消息。
2. **严禁 `@all` 广播**：在 Swarm 内只允许精确点名当前活跃 Worker（如 `@uvx-researcher-1`），**严禁使用 `@all`**（避免误唤醒已挂起旧任务或无关节点）。
3. **唯一正式跨团队交接界面**：禁止团队之间互相读取未合并的本地草稿目录作为「已证事实」。任何可复用的引理、障碍（`O-*` / `DEAD-*`）或常数边界，必须先经过红队审查与 `gatekeeper.py --mode full` 合入 `origin/main` 后，由兄弟团队 `git fetch origin main` 从 `research/lab_wiki/` 与主分支正式引用。

---

## §7 一键开线 `/teamwork` 提示词模板（可直接复制）

### 模板 A：UEOT 新物理/数学赛道开线（如 `UV-X` / `CHIRAL-X` / `H1d4d` / `H3d` / `H4d`）

```text
/teamwork 组建「<赛道名，例如 UV-X> 第一性原理双轨攻关团队」，并加载 ueot-research-os 插件中的全部相关技能（falsify-first-problem-solving、dual-track-research-orchestration、ueot-first-principles-compass、ueot-physics-unification-ops、first-principles-math-invention）。

【启动硬规范（必须第一时间执行）】
1. 先执行 git fetch origin main，并严格遵循 origin/main 下的 research/lab_wiki/MULTI_TEAM_CHARTER.md、OPEN_SPECS.md、VERIFIED_LEMMAS.md 与 DEAD_ENDS.md（严禁读取旧基线 ueot-core-upgrade/ 作为最新状态，严禁跨区修改 H2d/IR-X 的 nonabelian_lattice_massgap_h2/、IRXWave*.lean 或禁区 physics/qm/**）。
2. 从 origin/main 新建独立 worktree（分支 physics/<lane>-w1），按需 APFS cp -cR 复用温 .lake；探索期严禁触碰 UEOTPhysicsUnification.lean、ExhaustiveAxiomAudit.lean 与 run_verification.py 等共享热点文件。
3. 多 Worker 并发严格绑定 OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1；单路线限制 <= 2 个 .py 脚本（probe + certify），certify 严格零浮点 40 位 mpmath.iv + SymPy<=8x8 + 0 grep 命中，Probe 做 AST 零常数泄露检查。

【团队架构（双轨制）】
- 主线 N+1 Wave 团队：3–4 名专职 Researcher（1 独立障碍 = 1 人，先预注册本赛道 4–6 项负控制/假阳性杀手矩阵，失败即资产化为 O-* / DEAD-*）+ 1 名 Strategist/Red-Team（Step 1 注入核心陷阱，Step 2 零信任收敛审计）。
- 独立 Pure-Math Inventor（Neon/高推理模型，不在 Wave 轮次内）：采用 Proposal-First 笔记流程提出 2–3 条原创数学机制，待协调者拍板后再验证 40 位反控制矩阵并反哺主线。
- 10 分钟 Watchdog Cron：巡检挂起、429 与重型进程错峰。

首轮任务：对齐当前赛道在 origin/main 下的真实未闭合边界，给出 Wave 1 分工清单 + 预注册负控制矩阵 + 首轮 Inventor 提案。
```

### 模板 B：跨项目通用疑难问题开线（算法、架构、工程、数学建模、科研难题）

```text
/teamwork 组建「<项目/问题名称> 第一性原理证伪驱动团队」，加载 ueot-research-os 插件中的 falsify-first-problem-solving、dual-track-research-orchestration、ueot-first-principles-compass（以及若涉及原创数学推导则加挂 first-principles-math-invention）。

【方法论铁律】
1. 用 UEOT T1–T5 第一性原理罗盘拆解问题：区分规范冗余 vs 不变量（Q1）、约定 vs 跨尺度操作锚点（Q2）、被投影丢弃的纤维反作用与残差项（Q3）、大尺度 N->∞ 一致可行性边界 Ω（Q4）、可瞬间一票否决的最小反例（Q5），避开五类伪类比红线。
2. 先立“负控制靶场（Litmus Matrix）”再追正面分数：任何新方案必须先证伪退化基线/已知反例并避免零泄露循环自证，否则直接判为过拟合/盲区并记为结构性障碍 O-* 与 DEAD_ENDS。
3. 严格划分 [C] 已严格证明、[E] 经验探测、[X] 仍开放缺口；严禁把局部现象包装成全局闭环。
4. 执行 N+1 正交分工（3 名专职探索者 + 1 名红队陷阱注入与收敛官 + 可选 1 名 Proposal-First 独立发明者），每路 <= 2 主脚本防止探索文件膨胀，协调者做零信任独立复跑验收。

首轮任务：输出核心障碍分解、5 项正交/负控制验证矩阵与 Wave 1 并行执行计划。
```
