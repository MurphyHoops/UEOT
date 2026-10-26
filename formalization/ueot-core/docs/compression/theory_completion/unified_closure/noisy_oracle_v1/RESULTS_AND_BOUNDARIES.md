# R2: finite samples, noisy selection, and an actual controller's risk

This increment follows R1/#373 and the scoped registry update #374. Its base is
`d048429a1f713246dd7a69aa278f71c4d0df1677`. It adds three Lean modules and three
public-root imports. The complete source has 699 reachable modules, fingerprint
`4b5145e874601392568293c1d561684e6d0478f2676dc20accf04a8080c3261d`.
Frozen 106/106, four counted generators, and 11/89/6 retain their existing scope.

## The exact-support obstruction

`FixedSampleSupportNoGo` uses the existing independent product-row experiment
for a Bernoulli source with unknown parameter p. For each fixed positive sample
count N, the certification rule is an arbitrary PMF-valued function of the
whole record, fixed across p. This includes randomized rules.

If its probability of certifying p=0 at the zero source is rho, then its false
certification probability at any positive source is at least rho(1-p)^N.
For rho>alpha>=0, the proof constructs

    p = (rho-alpha)/(2*rho*N), with 0<p<1,

and derives false certification probability greater than alpha. Consequently a
uniformly alpha-valid exact-zero certificate has power at most alpha at p=0.
This is a quantified statistical obstruction, rather than only an example of
one possible unseen transition. It does not address stopping-time experiments,
known positive-mass gaps, or an externally supplied exact support relation.

## What the runtime computes

`NoisyFiniteRiskOracle` takes a fixed registered allocation of N responses from
every finite state-action row. The runtime receives the raw responses, finite
candidate observations, an R1 executable program for each candidate, rational
row radius u, defect threshold tau, risk cap beta, horizon T, and a finite
Boolean event. It receives no true transition probabilities or empirical-fit
proof. All counts, empirical masses, total variation, representatives, history
probabilities, and acceptance decisions use executable rational arithmetic.

The empirical defect is the maximum empirical row TV over equal-observation
input pairs, retaining the same microscopic output alphabet. The oracle says
PASS when estimate+2u<=tau, FAIL when tau<estimate-2u, and AMBIGUOUS otherwise.
The existing C3 scan queries in order and continues only after FAIL. The actual
finite selector returns the first PASS; AMBIGUOUS and exhaustion both produce
no selected program. An empty family is handled without deployment.

For that selected program, the reference process uses empirical rows at
computed observation-fibre representatives. Its history probability checks
the actual R1 program's action and memory. The Boolean certificate requires
positive N, valid nonnegative scalars with beta<=1, an actual PASS, and

    min(1, referenceRisk + T*min(1, u+empiricalDefect)) <= beta.

The proof identifies that rational reference sum with the existing reference
process for this same controller, derives the fit bound on the simultaneous
row-TV event, and proves the computed certificate bounds its actual finite
source risk. The exact-support R1 theorem separately supplies the returned
program's all-time physical safety.

## Training, selection, and deployment

The statistical experiment is the existing fixed product of independent source
responses, followed by this actual selector and deployment on the same unknown
source. Its common simultaneous calibration event covers all registered rows;
there is no candidate-count factor or separately assumed post-selection fit.
Let B be the existing confidence budget capped at one. The new theorem proves

    Pr(training accepted AND deployment fails) <= min(1, B+(1-B)*beta).

This is a joint probability, not a conditional-on-acceptance guarantee. No
acceptance-power or completeness theorem is claimed. Budget rejection means
that no certificate was obtained; it does not prove excessive actual risk.

## A model where the numerical decision matters

The witness has start and goal safe states plus a proper absorbing cemetery,
one Unit action, and two observation candidates: merge start/goal, or retain
the full state. Both numerical sources have the same declared exact support.
From start, progress to goal has unknown p in {1/4,1/8}; goal is absorbing.
The controller is synthesized from the structural table independently of p.
It stays outside the cemetery for all time under either source.

The statistical bad event is missing goal after two steps. Its actual source
probability is proved from the causal path law to be (1-p)^2, hence 9/16 or
49/64. The latter exceeds beta=7/10. On the simultaneous calibration event
the alternate p=1/8 source cannot obtain a selected deployment certificate;
its erroneous-acceptance probability is at most B. This rules out a prior
family whose members all satisfy the requested numerical cap automatically.

The registered allocation is N=4096 per row, u=1/20, tau=1/8, T=2. Lean proves
that its B=min(1,48*exp(-512/25)) is strictly below one. Four-sample and
eight-sample fixtures are deterministic runtime regressions, not random draws
or nontrivial-confidence experiments.

## Preserved actual draw and replay

`SAMPLE_FINITE_SOURCE.py` was run once for the p=1/4 model using Python's OS
CSPRNG backend. Every response from all three rows is retained. The ideal
independent uniform backend is an explicit source-matching assumption; neither
Lean nor inspection of one dataset verifies the operating-system RNG or an
external scientific source. The certificate code reads only count and rows.

The preserved start row contains 1018 goal responses out of 4096. The final
runtime replay selects candidate 1 with query trace [0,1]: coarse defect
1539/2048 fails, fine defect 0 passes, and the fine reference risk is
2368521/4194304. Its computed budget is 13939757/20971520, below 7/10, so the
certificate is accepted. No resampling was used to obtain this result.

The executable assertions cover the real finite selector, 9/16 and 49/64
reference risks, 53/80 fixture budget, over-cap rejection, insufficient budget,
AMBIGUOUS stopping, zero samples, and an empty candidate family. A separate
malformed allocation is actually rejected with nonzero exit status. Historical
runtime-01 records its then-pending proof status; runtime-02 preserves a syntax
failure; runtime-03 is the final successful replay and parser-negative check.

## Remaining limits

Exact support, initial support, structural certification, finite registration,
and correspondence between model and actual source remain explicit inputs.
Finite samples have not supplied exact support or zero-danger certification.
The finite risk concerns the specified event and horizon, while the physical
safety statement uses the separate structural assumptions. The runtime
enumerates histories and is intended for small registered horizons.
External scientific evidence remains UNVERIFIED, and strong world closure
remains NOT_ESTABLISHED. Local build, native export/replay, source ownership,
axiom and publication evidence are recorded separately after actual execution.
