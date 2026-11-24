# UEOT Verified Lemmas & Certificates (`VERIFIED_LEMMAS.md`)

> **准入铁律**：只有通过 `python3 -B research/lab_wiki/gatekeeper.py --mode lean`（涉及数值证书时需 `--mode full`）的引理与证书，才允许写入本表。  
> `gatekeeper.py` 会自动校验本表中引用的文件路径必须真实存在，且严禁出现 `TODO`、`TBD`、`PENDING`、`sorry`、`admit` 等未完成标记。

---

## 已验证清单（对齐 `origin/main` @ `e824ef0b`）

| Lemma-ID | Spec-ID | Lean Symbol / Verification Suite | File | Gate Mode | Gate Status | Commit |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `LEMMA-20261124-01` | `WAVE9-H1D` | `h1d_frontier_sharp_decomposition_and_honest_open_core` (`H1d1 ∧ H1d2 ∧ H1d3` closed; `H1d4` isolated `OPEN`) | `formalization/ueot-physics-unification/UEOTPhysicsUnification/Nonperturbative4DQuantumGravityH1d.lean` | `full` | `PASS` | `8b72be9c` |
| `LEMMA-20261124-02` | `WAVE9-H1D` | `nonperturbative_4d_qg_h1d` 40-digit `mpmath.iv` + `sympy` certificate (`P-H1D-FRG-01`..`C-H1D-CORE-04`) | `physics/unification/nonperturbative_4d_qg_h1d/certificate.json` | `full` | `PASS` | `8b72be9c` |
| `LEMMA-20261124-03` | `PAPER4-V2` | Paper 4 v2.0 correlated-bath response metrology standalone verification | `publications/papers/correlated-bath-response-metrology/VALIDATION.json` | `full` | `PASS` | `397dd224` |
| `LEMMA-20261124-04` | `SPEC-20261124-01` | `h1d4_final_sharp_reduction_and_operational_vs_mathematical_split` (`H1d4a..c` closed, `H1` operationally closed; `H1d4d` `OPEN`) | `formalization/ueot-physics-unification/UEOTPhysicsUnification/Nonperturbative4DMeasureLimitH1d4.lean` | `full` | `PASS` | `1ff5170f` |
| `LEMMA-20261124-05` | `SPEC-20261124-01` | `nonperturbative_4d_measure_h1d4` 40-digit `mpmath.iv` + `sympy` certificate (`P-H1D4-BANACH-01`..`C-H1D4-FINAL-04`) | `physics/unification/nonperturbative_4d_measure_h1d4/certificate.json` | `full` | `PASS` | `1ff5170f` |
| `LEMMA-20261124-06` | `PAPER4-V3` | Paper 4 v3.0 PRA submission outward bounds, dual-engine LaTeX & standalone verification | `publications/papers/correlated-bath-response-metrology/submissions/pra/VALIDATION_PRA.json` | `full` | `PASS` | `e824ef0b` |

---

## 追加说明

- `Lemma-ID` 格式：`LEMMA-YYYYMMDD-NN`。
- `File` 列必须使用相对于仓库根目录的路径，且指向真实存在的 `.lean` 或 `.py` / `.json` 文件。
- 每次新增正式证明后，请同时在对应组会纪要中附上 `gatekeeper.py --write-receipt` 的执行摘要。
