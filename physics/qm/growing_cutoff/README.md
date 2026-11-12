# v31.12: separated-pulse growth and controlled blue-pulse omission

This is the executable companion to [Chapter 68](../book/UEOT_PHYSICS.md#ch-68) and the [shared source contract](../audits/GROWING_CUTOFF_v31.12/SHARED_MODEL.md). It extends the v31.11 probe–oscillator model by an externally driven blue pulse **after** each selected red pulse. Complex quantum structure, Fock representation, ideal flags, exact effective gates and a physical low-spectral filter are explicit inputs.

## Reproduce the new increment

From the repository root, with Python, NumPy, SciPy and SymPy installed:

```bash
python physics/qm/growing_cutoff/run_verification.py --output-dir /tmp/ueot-qm-growing-cutoff
python physics/qm/growing_cutoff/verify_inherited_evidence.py --output /tmp/ueot-qm-proof-reuse.json
```

`run_verification.py` executes four groups and records the actual local or GitHub environment, checked-out commit, worktree condition, input hashes, command return codes, output hashes and logs. It never labels a remote process as one of the checker authors. Original independent-agent scripts and receipts are retained under the audit's `reviewer_originals/` directory; copied checkers have explicit attribution and separately bound new executions.

| Group | Responsibility | Evidence limit |
|---|---|---|
| `verify_integration.py` | Original seven-leaf instrument, growing rectangular maps, untouched reference, accepted CPTP target, physical filtering, labels, costs and negative controls | Nine finite parameter instances; floating checks with frozen tolerance, not universal proofs |
| `check_operational_growth.py` | Independent operation-composition and observation-interface controls | Finite witnesses; analytic interface proof is separate |
| `check_micro_growth.py` | Independent blue-block support, source columns and growth controls | Finite numerical controls, not a spectral-theorem implementation |
| `exact_checker.py` | Rational path identities, uniform robust policy, radical interval certificate and cost identities | Exact arithmetic for the declared algebraic quantities, not device calibration |

The primary numerical model starts at cutoff 1 with reference dimension 2 and ends in cutoff 5. The nonzero-filter-failure control uses input cutoff 2, filter cutoff 1 and final cutoff 6, with a deliberately selected tail mass 1/4096. Neither is a numerical run of the analytic cutoff 4095. The latter enters a universal paper bound derived from a mean-excitation constraint.

## Exact certificate and physical premises

For mean excitation at most 1, cutoff 4095, independent blue-area guarantee `abs(beta) <= 1/100`, and the same visible-history policy as v31.11, the full-output error of the omitted-blue deployment is bounded by

`1/50 + (1 + sqrt(16381))/8192 + sqrt(2)/100 < 1/20`.

The rational upper enclosure is `4988777535926672699 / 10^20`. The remaining error allowance is only about `0.000112224640733273`; no measured gate, effective-model, filter or readout error is available to certify a real device within this allowance. All failures, stop labels, system states and finite untouched references are retained in the compared CQ output.

The source has two slots and seven stopping records. Its backward acceptance effect is derived as `s^2 I`, so its complete conditional target is CPTP. An actual attempt including filtering succeeds with `s_N s^2`; the compiler delivers with probability `s_N`. A fresh-reset retry formula uses the corresponding actual success probability, and one-time calibration is amortized separately. Unknown inputs have no free repeatability assumption.

Flag probabilities contain no information about blue pulse area. The exact beta=0 versus beta=pi/2 terminal-state control demonstrates this limitation; it intentionally falls outside the independent small-pulse premise. Simultaneous red+blue evolution also has an infinite-tail counterexample, so the separated-pulse finite-support theorem is not generalized to simultaneous Rabi dynamics.

## Evidence reuse and exclusions

`verify_inherited_evidence.py` pins the historical v31.11 receipts, checks 158 proof/configuration inputs and 13 old runtime inputs, and compares the complete proof/tool inventory with its actually verified commit. It may reuse that original Lean execution only for identical source. A mismatch selects the retained full CI build; it does not accept a changed proof by name. No new Lean source or theorem is added in v31.12. Paper, exact, floating, synthetic and empirical evidence remain distinct.

The interrupted unpublished v31.12 bytes were unavailable during recovery. This implementation and its receipts were reconstructed and actually checked anew. It is not a reconstruction of a lost execution identity. No real device data, empirical closure, independent complex-sector selection or complete QFT/particle/gravity theory is claimed.
