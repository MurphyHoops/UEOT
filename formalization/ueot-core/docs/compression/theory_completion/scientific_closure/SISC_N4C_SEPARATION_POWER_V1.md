# N4-C — statistical power from explicit risk separation (Lean)

**Local source:** `SISCSeparationPower.lean`. Reuses the same N3 abstaining C2 resolver, the N4-B coordinate-mean calibration bound, and all existing finite-state and statistical interfaces. It does not duplicate P4.1's exact ERM risk-gap theorem: ERM always selects a minimizer, while a **certified abstaining candidate resolver** must additionally prove all alternatives rejected and the retained candidate fully certified.

## Detection power requires two-sided margin, not only a false-positive bound

Fix one registered and causally admitted candidate c. Let `risk(c)` be the true post-action expected-response risk, `t` the tolerance threshold, and `r` an upper bound on **every** registered candidate's C2 total interval radius.

If

`risk(c)+2r ≤ t`

and for every other registered, causally admitted candidate d ≠ c,

`t+2r < risk(d)`,

then whenever the simultaneous risk calibration good event holds, the N3 resolver **must output `unique(c)`**.

Lean proves the two necessary C2 lemmas independently:

- `candidate_certified_of_two_radius_margin` — margin inside threshold forces C2 certification.
- `candidate_rejected_of_two_radius_margin` — margin outside threshold forces C2 rejection.

The theorem `registered_unique_identified_of_calibrated_margin` constructs the singleton possible set, identifies the unchosen unique result and proves that the output equals `unique(c)`.

## Full probabilistic power after observed coordinate means

For N IID post-action microstate samples with bounded measurable coordinates and a correctly matched sample law, N4-B constructs a C2 radius

`r = |O|u`.

Theorems `coordinate_protocol_unique_of_calibration_and_margin` and
`measure_failure_to_identify_separated_candidate_le` then prove:

`Pr[resolver(sample) ≠ unique(c)] ≤ 2|O| exp(-2 N u²)`

under the **explicit** inside/outside gap conditions above.

This is a genuinely stronger decision guarantee than simply bounding an incorrect unique label: it also controls the probability of unnecessary abstention **when physical/model separation is adequate**. When the candidate risk gap is insufficient relative to r, the theorem deliberately says nothing about successful unique recovery; abstention may be correct.

## Limits

- `causal` and candidate registration remain independent scientific inputs and are not inferred from a chosen transporter.
- The gap is strict on the outside; finite estimated responses do not establish such a separation merely by appearing different.
- The risk is a finite expectation-vector mismatch, not necessarily a complete distributional fingerprint.
- IID temporally sampled observations, [0,1] values and post-action law matching remain explicit assumptions. Correlated temporal observations require a different sampling theorem.
- This is proof about identifying registered operational candidates, not a universal law of physical SameObject or objecthood.

**Status:** local Lean mathematics, no external physics evidence, no frozen Core change and no GitHub push.
