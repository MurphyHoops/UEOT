# Lab Meeting Minutes — Round NN (YYYY-MM-DD)

- **Round**: `NN`
- **Date**: `YYYY-MM-DD`
- **Target Spec(s)**: `SPEC-YYYYMMDD-NN`
- **Chair**: `<Coordinator>`
- **Participants**: `Explorer-A`, `Explorer-B`, `Red-Team Referee`
- **Base Commit**: `<git rev-parse --short HEAD>`

---

## 1. 各组会前进展摘要

### Explorer-A
- **Route**:
- **Artifacts**:
- **Self-Check (`gatekeeper.py`)**:

### Explorer-B
- **Route**:
- **Artifacts**:
- **Self-Check (`gatekeeper.py`)**:

---

## 2. 红队质询与裁决（Red-Team Critique）

| Candidate | Verdict (`PASS` / `BLOCKED` / `FALSIFIED`) | Hidden Premises / Bugs / Counterexamples | Required Action |
| :--- | :--- | :--- | :--- |
| Explorer-A |  |  |  |
| Explorer-B |  |  |  |

---

## 3. Wiki 更新记录

- **Promoted to `VERIFIED_LEMMAS.md`**:（仅列通过门禁的 `LEMMA-ID`，无则填 `None`）
- **Logged to `DEAD_ENDS.md`**:（新增的 `DEAD-ID`，无则填 `None`）
- **Updated in `OPEN_SPECS.md`**:

---

## 4. 下一轮分工（Next Round Assignments）

1. **Explorer-A**:
2. **Explorer-B**:
3. **Red-Team Referee**:

---

## 5. 自动门禁回执（Gatekeeper Receipt）

- **Command**: `python3 -B research/lab_wiki/gatekeeper.py --mode <fast|lean|full> --write-receipt`
- **Result**: `PASS` / `FAIL`
- **Receipt Path**: `research/lab_wiki/receipts/latest_gate.json`
