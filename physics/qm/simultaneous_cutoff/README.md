# Simultaneous dynamics and calibrated finite predictions

This is the v31.13 runtime for [Chapter 69](../book/UEOT_PHYSICS.md#ch-69). It computes an actual compressed Hamiltonian, preserves the original complete source and finite reference, and joins controlled Galerkin error to a data-chosen nominal parameter. It does not assume a finite cutoff is a physically available gate.

The [shared contract](../audits/SIMULTANEOUS_CUTOFF_v31.13/SHARED_MODEL.md) and [frozen model](frozen_model.json) state all parameters, observations, records, preparation failure and precision. `FROZEN_CERTIFICATE_PLAN.json` separately freezes iid sample sizes, seeds, thresholds and finite testers. Synthetic streams and their provenance remain distinct from the analyzer inputs; the analyzer does not read hidden truth.

Run the complete scoped pipeline with Python 3, NumPy, SciPy, SymPy and mpmath:

```bash
python physics/qm/simultaneous_cutoff/run_verification.py --output-dir /tmp/ueot-simultaneous
```

The commands distinguish source/scalar identities, finite floating diagnostics, independent exact rational calibration, synthetic held-out checks and outward-integer numerical output. The large `K=4175` interval prediction is actually evaluated sparsely for one specified entangled `G<=1` input. It does not assert numerical evaluation for all states or a dense exponentiation of the entire carrier. Its exact normalized integer vectors are a reusable CQ output; ordinary matrix-exponential diagnostics are not its accuracy certificate.

The complete finite-map sufficient bound is below `0.041930158795` in the final synthetic instance. A separate interval output certificate establishes the reserved `1e-8` numerical allowance for its stated input. Widened calibration gives an insufficient bound, source flags do not identify the force, and a deliberately unshared force is rejected by the fixed two-pulse tester. These are mathematical and synthetic controls, not hardware observations.

For real execution the missing records are ordered source/calibration/holdout outcomes, trial timing and reset identity, independent detector offset and response calibration, same-pulse tests, low-spectral filter/reset/reference verification, leakage/failure logs and full resource costs. A finite tester validates only its declared response family. The complete-CQ certificate additionally depends on the stated physical model and independently established nuisance bounds.

All historical receipts retain their own authors, checkouts and scope. The new runner identifies its actual local or GitHub environment; checker authorship is not executor identity. No new Lean source or real device data is present.
