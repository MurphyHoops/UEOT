# N4-B — measured-coordinate confidence for N3: validated risk without Jensen error

**Result:** Exact Lean 4 formal proof reusing the frozen P-STAT-08 two-sided finite union bound and the N3/C2 abstaining candidate resolver. No original concentration theorem is claimed; the new content is the **typed bridge from measured response-coordinate means to N3's actual post-action risk**, its simultaneous confidence law, and the full false-decision certificates.

## 1. Why N4-A did not finish the scientific inference

N4-A proved a correct generic finite candidate validation result only under the explicit requirement that the expected candidate validation loss **equal** the N3 risk. This is not automatic:

`E|Y-r| ≠ |EY-r|` in general.

For uniformly random Boolean Y and candidate prediction r=1/2, `E|Y-r|=1/2` while `|EY-r|=0`. The new module `SISCMeanResponseCalibration.lean` contains an exact Lean-checked negative control for this inequality. This prevents the invalid shortcut of substituting mean absolute errors for absolute errors of means.

## 2. A derived coordinate-wise calibration bridge

For finite observation coordinates `j∈O`, assume actual sampled post-action microstates `Y_n` are IID with law `dataLaw`; registered per-state responses `read(y,j)` are measurable and bounded in [0,1]. The protocol-specific *law matching condition* is **separately stated**:

`E_dataLaw[read(Y,j)] = Σ_y K(x,a,y) read(y,j)`.

The candidate's ground truth risk is the N3 L1 **mean-response** mismatch:

`Risk(c) = Σ_j | E_dataLaw[read(Y,j)] - candidatePrediction(c,j) |`.

Define coordinate means `hat m_j = N⁻¹ Σ_n read(Y_n,j)`, and **then** compute

`hat Risk(c) = Σ_j |hat m_j - candidatePrediction(c,j)|`.

The new `finite_absolute_response_risk_lipschitz` theorem proves

`|Σ_j |hat m_j-pred(c,j)| - Σ_j |m_j-pred(c,j)|| ≤ Σ_j |hat m_j-m_j|`.

Thus, whenever **all** registered observation coordinates satisfy `|hat m_j-m_j|≤u`, every registered candidate's empirical risk interval has error at most `|O|u`, simultaneously. This holds regardless of how many candidates are registered and does not assume candidatewise expected absolute losses represent N3 risk.

## 3. A real finite-sample statistical guarantee

Reusing the existing `BoundedLossTwoSided.measure_exists_candidate_bad_le` with the finite index type **O** gives:

`Pr[any N3 candidate interval uncalibrated] ≤ |O| · 2 exp(-2 N u²)`.

The theorem `measure_bad_coordinate_calibration_le` is machine checked under precise IID, bounded, measurable coordinate and post-action law-matching conditions.

More importantly, without assuming the data-dependent winner was fixed before sample collection, Lean proves:

- `measure_unsound_unique_coordinate_protocol_le`: probability of **any** unsound unique claim is bounded by the same factor. Unsound includes (a) the selected label itself not being compatible, or (b) another compatible registered causal label being excluded.
- `measure_false_uncovered_coordinate_protocol_le`: probability of reporting **uncovered** despite an actually compatible registered causal candidate is also bounded.
- `measure_wrong_unique_coordinate_protocol_le`: the original alternative-compatible special case is retained.
- `empirical_coordinate_protocol_calibrated_of_uniform`: the deterministic good-event bridge to existing N3 C2 certificates.

The major practical fact is that the confidence penalty depends on **number of measured coordinates `|O|`**, rather than candidate registry size `|C|`, because the same coordinate means control **all** L1 candidate risks.

## 4. Boundaries (scientific and mathematical)

- This result is **finite, IID**. The repository has `C2SamplingBudget` for arithmetic of correlated blocks, but no substitution of that budget for an actual β-mixing or martingale tail theorem is valid. Cross-correlated **coordinates measured on the same sample** are allowed: finite union bounds do not require independence among coordinates. Only the temporal sample draws are assumed independent.
- `PostActionCoordinateLawMatchesKernel` is an explicit model-validity contract; the proof does not pretend finite data identify K or its causal provenance. Strongly misspecified K can invalidate that condition.
- The observation coordinate list is nonempty and risk is an expectation-vector mismatch. Experiments distinguishing only distributional tails require richer probes or full trace laws.
- A **small alpha** requires a meaningful N and u, and the probability bound may be vacuous if the bound exceeds 1. A statistical radius larger than the separation gap may force abstention rather than discovery. No guaranteed discovery probability or universal object identity is claimed.
- Causal admissibility, candidate universe coverage, physical boundary/persistence/repair and GOD/GOA remain independently open.

**Status:** Local conditional mathematical proof. No counted Core modification, no independent physical validation, no cloud push.
