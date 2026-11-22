# Three-Channel Flavor Cyclic Lock & SPAM/Leakage Calibration (`P-FLAVOR-04`, `P-SPAM-05`)

```text
Result ID: P-FLAVOR-04, P-SPAM-05
Core dependencies: Finite quantitative transport
Bridge dependencies: Quark-field U(1)^3 rephasing-invariant Bargmann Wilson product; 3-outcome affine detector inversion
Sector inputs: Single-Z' rank-one left-handed down-quark neutral current; 3-outcome {0, 1, leak} probe readout
Standard physical inputs: Complex Delta F = 2 mixing amplitudes (K, B_d, B_s); Hoeffding finite-shot concentration
Effective assumptions: Time-stationary SPAM/leakage matrix across interleaved calibration and intervention shots
Formal status: Pure-kernel Lean 4 theorems (FlavorCyclicAndSPAMContract.lean, 0 sorryAx) + 40-digit outward-interval certificate
Observable/benchmark: Exact 2-channel surjectivity vs 3-channel Im(C_ds C_sb C_bd) = 0 lock; 99% CL 200k-shot calibrated error < 0.0139 < uncalibrated bias 0.0235
Falsification condition: Nonzero Im(C_ds C_sb C_bd) or negative Re(C_ds C_sb C_bd) falsifies any single-boson hermitian rank-one Delta F = 2 extension
```

Closes `sectors/RESULTS.md` §3 (`PREMISES` Row 11) and `PREMISES_AND_RESPONSIBILITIES.md` §5 Row 2.

Evidence: [verify_flavor_spam.py](verify_flavor_spam.py) · [result.json](result.json)
