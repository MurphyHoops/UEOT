# Matched Hardware Certification Contract for Correlated Persistent Bath & Two-Copy Selection

Status: `PREREGISTERED_CONTRACT` (Hardware status remains `NOT_CERTIFIED` until raw shot-level device data satisfying all gates below are archived).  
Covers Result IDs: `P-MICRO-10`, `C-QMEM-02`, `P-QMEM-03`, `P-ROB-08`, `C-QSEL-05`.

## 1. Required Physical Platform Capabilities

A candidate experimental run (e.g., superconducting transmon dispersively coupled to two high-$Q$ 3D microwave cavities, or trapped-ion spin coupled to two axial/radial motional modes) must independently demonstrate:
1. **Mid-circuit bath-preserving probe reset**: Resetting the probe qubit $S$ between segments $a$ and $b$ without resetting the bosonic bath displacement or cross-mode phase $N_{12} = c$.
2. **Phase-locked preparation clock**: Deterministic shot-to-shot phase reference between non-degenerate mode frequencies $(\omega_1, \omega_2)$ and the $X/Y$ readout axes.
3. **Complete nonselective shot accounting**: Every triggered start must be recorded (`f`, `pf`, `ppf`, `ppp`, leakage `L`, or hardware timeout `T`); postselected success-only tables are automatically rejected.

## 2. Mandatory Raw Shot-Level HDF5 Schema

Each experimental submission under `validation/physics_unification/raw/` must supply:
- `shot_id` (`uint64`, strictly increasing `0 .. N_total - 1`, zero dropped triggers)
- `timestamp_ns` (`uint64`, hardware FPGA monotonic clock)
- `block_id` & `setting_code` (`uint16`, randomized interleaved calibration and blinded holdout blocks)
- `initial_sign` (`int8`, $s \in \{-1, 0, +1\}$)
- `reset_telemetry` (`uint8`, raw mid-circuit readout / herald code confirming probe reset)
- `leakage_flag` (`uint8`, qutrit $|f\rangle$-state check at terminal readout)
- `outcome_code` (`uint8`, full stopping-tree or 8-cell Bell-reference outcome)

## 3. Dual Acceptance Thresholds (Power + Global Error)

1. **Calibration Coverage & Non-Empty Confidence Polytope**: Joint $99\%$ confidence region $\Theta_{0.99}$ for $(\lambda, n, c, \eta, \delta_{\mathrm{phase}})$ from calibration blocks alone must be non-empty; an empty set triggers `MODEL_SPECIFICATION_REJECTED` (never vacuous pass).
2. **Single-Event Discrimination Power**: Total combined statistical + SPAM + phase-drift uncertainty on the signed $Y$ contrast must be strictly smaller than half the predicted separation between the free-Ramsey-degenerate benchmark pair.
3. **Blinded Holdout & Strong Standard Baseline**: Frozen holdout blocks (unseen during parameter estimation) must pass simultaneous CDF envelopes while the paired standard joint-unitary / process-tensor baseline on identical data and budget is reported alongside (`EQUIVALENT_NO_ADDED_GAIN` vs resource separation).
