# N4-A — P-STAT-08 finite-sample calibration bridge (Lean-verified)

**Scope:** post-Core additive research. **Reuse first:** existing `BoundedLossTwoSided.measure_exists_candidate_bad_le` (Hoeffding + finite union bound) and `FiniteCandidatePStat08`; existing N3 `wrong_unique_implies_calibration_failure`. There is no reproof of the concentration inequality.

`SISCStatisticalCandidateCalibration.lean` constructs a *data-dependent* N3 protocol by replacing each candidate's C2 certificate with its empirical validation loss estimate, nonnegative statistical radius `u` and zero drift radius. It proves:

1. If every empirical candidate loss lies within `u` of its true expected loss, and **the expected loss really equals the N3 post-action candidate mismatch**, then the constructed N3 protocol is `Calibrated`.
2. Under iid validation samples, measurable bounded [0,1] losses and matching laws, the probability that N3 is uncalibrated is bounded by
   `|C| · 2 exp(-2 N u²)`.
3. Under those same explicitly registered conditions, the probability of outputting a unique candidate while another genuinely compatible *registered causal candidate* exists is bounded by the same expression.

**Important model gap:** `SampleLossMatchesRegisteredRisk` is an explicit separate equality assumption, *not* a theorem. N3's risk is `Σ_j |E(read_j)-prediction_j|`. The average sample absolute residual `E|read_j-prediction_j|` is generally **not** equal to `|E(read_j)-prediction_j|`. This proof is valid only for a candidate loss whose expected value really matches the N3 target; this must be justified in each application.

The next N4-B stage removes that candidate-risk matching assumption by estimating the underlying response-coordinate means directly and applying the global Lipschitz bound for absolute residual differences. This can yield a union bound depending on the number of observed coordinates `|O|` rather than the total candidate count `|C|`, assuming correctly specified microtransition observation laws and iid bounded coordinate samples.

Statistical statements are conditional on a true sampling model; causal provenance, registry completeness, physical objecthood, repairs, GOD/GOA and correlated-data concentration remain separate.
