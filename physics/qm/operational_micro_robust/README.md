# Operational, microscopic and robust increment

This executable companion implements the frozen v31.11 model in [the common contract](../audits/OPERATIONAL_MICRO_ROBUST_v31.11/SHARED_MODEL.md). The scientific statement is [chapter 67](../book/UEOT_PHYSICS.md#ch-67); state and evidence are indexed by [CURRENT](../status/CURRENT.json).

Run from a repository checkout with Python, NumPy, SciPy and SymPy:

```bash
python3 physics/qm/operational_micro_robust/run_verification.py
```

The runner binds consumed files before and after execution and writes actual command outcomes to `../kernel/evidence/v31.11/runtime/execution_receipt.json`. It executes the new narrow controls only. The certificate producer and exact checker do not import one another. The primary source-to-CQ calculation independently constructs the original seven-leaf source using the unchanged chapter-66 interpreter. B's separate arithmetic checker independently checks the candidate and the design/calibration distinction.

## Frozen responsibilities

- `frozen_model.json` records the model, design interval, allowed visible history, precision, statistical allocation and synthetic seeds. No unknown true parameter is supplied to deployment.
- `robust_certificate.py` proposes the fixed adaptive policy; `exact_checker.py` independently recomputes its error bounds and negative controls.
- `check_operational_controls.py` distinguishes actual CP maps, Kraus refinements, visible labels, raw event probabilities, and restricted tests.
- `check_micro_truncation.py` derives finite source operations, checks the microscopic truncation cases, and includes nonzero physical preparation failure and an energy-preserving leakage counterexample.
- `verify_integration.py` checks the actual original source, backward effects, full seven-record CQ output, allowed policy, exact minimax arithmetic, and single-excitation long-time result. Its floating finite example has support G≤1; the general energy-tail bound is analytic.
- `synthetic_calibration.py` preserves logical trial order, separate calibration and holdout, and a deliberately invalid correlated-trial control. `--analyze-only` analyzes files matching this frozen schema; externally supplied device records require independent provenance and protocol checks before they can be called empirical evidence.
- `DATA_AND_COST_CONTRACT.json` lists the missing actual data and cost fields.

The output remains theoretical and synthetic. Flag data alone do not identify the phase/interaction nuisance parameters, verify source/action gate identity, or measure the full CQ trace distance. A finite record tester cannot certify unmeasured terminal quantum blocks. The geometric retry formula requires genuinely fresh independent resets; unknown inputs are not free repeatable resources.
