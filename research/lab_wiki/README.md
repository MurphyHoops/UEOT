# UEOT AI Lab Wiki & Conference System (`research/lab_wiki/`)

本目录位于主分支 `main` 下，实现面向 UEOT 大统一研究的 **「多智能体共享 Wiki + 对抗式组会 + 自动形式化门禁」** 工作流（借鉴 DeepMind `arXiv:2611.09822` 的多智能体协作与 Lean 4 门禁范式，直接接入 UEOT 现有的 `formalization/`、`physics/unification/`、`validation/` 与 `council/` 治理体系）。

> **核心铁律（No Gate Pass, No Promotion）**
> 任何在组会中达成的「思路」「共识」或「推导」，在通过 [gatekeeper.py](gatekeeper.py) 对应的 Lean 4 内核审计与数值复核之前，都只能停留在探索态，**严禁写入** `VERIFIED_LEMMAS.md` 或晋升为正式定理/规范主张。

---

## 目录结构

| 文件 / 目录 | 角色 | 谁来维护 |
| :--- | :--- | :--- |
| [AGENT_PLAYBOOK.md](AGENT_PLAYBOOK.md) | **AI 维护手册（必读）**：角色分工、组会流程、写入规范与 Prompt 模板 | 架构维护者 / 协调者 |
| [OPEN_SPECS.md](OPEN_SPECS.md) | **开放规格清单**：直接对齐 `main` 当前未闭合前沿（如 Wave 10 `H1d4`）的 Lean 签名、数值阈值与证伪标准 | 协调者 / 探索 Agent |
| [VERIFIED_LEMMAS.md](VERIFIED_LEMMAS.md) | **已验证引理库**：仅收录通过 `gatekeeper.py` 的 Lean 4 引理与数值证书 | 仅限门禁通过后追加 |
| [DEAD_ENDS.md](DEAD_ENDS.md) | **死胡同与反例库**：被证伪、发散、或隐含额外公设的路线（只追加，不删除） | 所有 Agent / 红队审稿 |
| [MEETING_MINUTES/TEMPLATE.md](MEETING_MINUTES/TEMPLATE.md) | **组会纪要模板**：每轮多智能体交叉质询与任务重分配的标准记录格式 | 组会主持人（Chair） |
| [gatekeeper.py](gatekeeper.py) | **自动门禁检查入口**：一键校验 Wiki 规范、Lean 依赖、无逃逸扫描、内核公理审计与数值验证 | CI / 所有 Agent |

---

## 快速使用（自动门禁命令）

在仓库根目录执行：

```bash
# 1. 轻量门禁（~0.5秒）：检查 Wiki 规范 + Lean 依赖锁 + 注释感知无逃逸扫描（零 sorry/axiom/opaque）
python3 -B research/lab_wiki/gatekeeper.py --mode fast

# 2. Lean 4 完整门禁：在 fast 基础上执行 lake build + ExhaustiveAxiomAudit.lean
python3 -B research/lab_wiki/gatekeeper.py --mode lean

# 3. 全量晋升门禁：在 lean 基础上执行 physics/unification/run_verification.py --check
python3 -B research/lab_wiki/gatekeeper.py --mode full

# 4. 生成/更新门禁回执 JSON（默认写入 research/lab_wiki/receipts/latest_gate.json）
python3 -B research/lab_wiki/gatekeeper.py --mode fast --write-receipt
```

---

## 与 UEOT 治理体系的衔接

- 本目录位于 `research/` 下，属于**探索与攻坚层**，不替代 [council/README.md](../../council/README.md) 的正式决议，也不替代 [validation/README.md](../../validation/README.md) 的验证台账。
- 当 `OPEN_SPECS.md` 中的某项任务完成 Lean 4 证明与数值复核、且通过 `gatekeeper.py --mode full` 后，由协调者整理成 PR / RFC 提交正式合并与决议登记。
