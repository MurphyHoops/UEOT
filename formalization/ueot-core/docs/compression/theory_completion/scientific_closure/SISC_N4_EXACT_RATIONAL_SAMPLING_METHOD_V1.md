# N4: exact-rational exhaustive binomial cross-check of statistical calibration and discovery power

**Source:** `evidence/sisc_n4_coordinate_calibration_method.py`. Synthetic deterministic verification, not external data, not an independent Lean kernel audit.

The test uses one Bernoulli post-action microscopic state `Y`, true `P(Y=1)=1/3`, and two registered coordinates `(Y,1-Y)`. Those coordinates are perfectly correlated within each observation; only *successive draws in time* are assumed IID. The true post-action expectation vector is therefore `(1/3, 2/3)`, exactly matching the declared source K.

Three candidate response vectors are registered: true `(1/3,2/3)`, bad_a `(4/5,1/5)` and bad_b `(1/10,9/10)`. Threshold is `1/4` and each candidate's C2 interval is built from the L1 **empirical-coordinate-mean** risk, never an expected absolute residual.

## Test A — probability of a wrong or premature finite decision

With N=300 IID samples and per-coordinate error radius u=1/10, enumerate all 301 possible binomial counts. Every count is weighted by its **exact rational binomial probability**; no Monte Carlo noise.

- C2 total candidate radius: `2u=1/5`.
- Frozen P-STAT finite-coordinate Hoeffding union bound: **0.0099150087**.
- Exact probability that the coordinate good event fails: **0.00018389015**.
- Exact probability of *any* candidate interval miscalibration: **0.00018389015**.
- Probability of unsound unique identification: **5.7460159 × 10^-20**.
- Probability of false uncovered status: **6.9794583 × 10^-16**.

Crucially, the test includes rare outlier samples that actually cause wrong unique/uncovered outcomes: the high-probability mathematical guarantee is a **probability bound**, not a deterministic promise that error is impossible.

The software also explicitly verifies `E|Y-1/2| != |EY-1/2|` to prevent using a wrong loss target.

## Test B — a provable-margin discovery-power regime

With N=2000 and u=1/20, per-candidate C2 radius is 1/10. The registered true candidate is at risk 0 and satisfies `0+2r≤1/4`; both alternatives have true risks greater than `1/4+2r`. Thus **all** strong-margin hypotheses of the N4-C Lean theorem hold.

After exhaustive exact-rational enumeration of all 2001 binomial counts:

- Frozen Hoeffding union bound for failure to identify true candidate: **0.00018159972**.
- Exact model probability of non-recovery: **1.0835929 × 10^-8**.
- Exact model probability of unique recovery: approximately **0.99999999**.
- Every sample count inside the simultaneous coordinate good event returns `unique(true)`.

The exact-rational model probabilities are aggregated without Monte Carlo; decimal display is only for readability. These are illustrative synthetic systems, not measurements of a physical UEOT object.

**Scientific interpretation:** the N4 statistical work establishes both (i) a calibrated *safety* bound for false decisions and (ii) a conditional *power* bound when the registered physical/model candidates are actually separable relative to the sample budget. If the margins or causal candidate coverage fail, the correct outcome can remain `ambiguous` and neither theorem licenses forced object identity.
