# Replaying the v31.14 persistent-bath verification

Run from any working directory with Python 3.10 or newer and the project dependencies (`numpy`, `scipy`, `sympy`, `mpmath`, `h5py`):

```bash
python physics/qm/persistent_bath/run_verification.py --output-dir /absolute/path/to/a/new_run
```

The output directory must be absent or empty and must lie outside the canonical `persistent_bath` source directory and immutable `authored` archive. An earlier run is never overwritten. The default input layout is:

```text
physics/qm/persistent_bath/          # runner, all A/B/C .py modules, frozen contracts
physics/qm/kernel/evidence/v31.14/authored/a/
physics/qm/kernel/evidence/v31.14/authored/b/
physics/qm/kernel/evidence/v31.14/authored/c/  # original nominal, plans, receipts, .npz data, external/ member
```

`--source-dir` and `--evidence-dir` can override these roots. Paths are resolved from the runner location, not an earlier scratch workspace. If a fixed input exists both canonically and in the authored archive, its bytes must agree.

The runner copies sources and immutable inputs into the new run's `work_a`, `work_b`, and `work_c`, then executes the finite operation checks, dynamics convergence, eight fresh interval/physical-Choi certificates, the strict memory event, A's independent certificate review, C's generation-probability audit and frozen holdout, the final exact certificate, and the predeclared external processed observable. Archived calibration/holdout arrays are actually read and identity-checked. The 1,600,000 synthetic rows remain historical reused rows; **no new shots are generated**. Original nominal, holdout plan, receipts and canonical files remain unchanged.

Optional calibration-only replay:

```bash
python physics/qm/persistent_bath/run_verification.py --output-dir /absolute/path/to/another_new_run --calibration-readback
```

This recomputes only the estimator in `calibration_readback/`, compares its scientific fields against the original nominal, and never uses the recomputation to replace the frozen nominal or refit holdout. Neither truth nor holdout data are copied into that estimator directory.

`runtime.json` is the final execution receipt. It records every command, actual wall/child-CPU time, stdout/stderr hashes, source/input/output hashes, immutable-input checks at command boundaries, failures and actual Git context. A successful run reports `status: "PASS"` and `inputs_stable_during_execution: true`. Partial failure results and logs are retained. This is computational verification of a conditional synthetic source and the stated processed external observable; it makes no new Lean, matched-device, or method-superiority claim.
