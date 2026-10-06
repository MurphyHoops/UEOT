# P3 Statistical Consistency — Local Closure Audit

Status: **LOCAL THEOREM PROGRAM COMPLETE; REMOTE INTEGRATION PENDING**
Track: `TC / P3`
Tracker: `#276`
Canonical source base: `main@026c2e5023850031e5cf5598df691325666b674d`
Local scientific head before this audit record: `9af8ce33c3ec998ca58c92ef2bfe3fa518dab464`

P3 is L1 additive research. It does not mutate the counted Core ledger, the
106-theorem coverage state, or the frozen minimal compression core
`{M-QD-01, M-TC-01, M-PE-01, M-OI-01}`.

## 1. Final architecture

P3 is not one monolithic probability theorem. The final architecture has three
parallel layers and one terminal composition layer.

1. **Confidence / probability layer** — changing sample spaces are allowed.
2. **Finite identification layer** — predictive classes and carrier/blocker
   families are recovered under finite response estimation.
3. **Fixed-source control layer** — estimator errors imply structural defects,
   which exactify one fixed encoder and then feed the existing control/GOD/GOA
   machinery.
4. **Terminal layer** — composes only interfaces for which an actual bridge has
   been proved; it does not identify the control encoder from raw data.

This separation is intentional. In particular, P3 does not force all sample
sizes onto one probability space and does not pretend that finite predictive or
carrier recovery already solves P4 Inverse Objecthood.

## 2. Stage results

| Stage | Result | Claim class | Main surface |
|---|---|---|---|
| P3.0 | changing-sample-space high-probability contract | THEOREM / ADAPTER_INTERFACE | `ConfidenceSchedule`, `ChangingSampleEventContract`, `bad_probability_tendsto_zero` |
| P3.1 | explicit confidence schedule with vanishing frozen P-STAT-01/P-STAT-08 radii | THEOREM | `alphaSchedule`, `pStat01Radius_alphaSchedule_tendsto_zero`, `pStat08Radius_alphaSchedule_tendsto_zero` |
| P3.2 | eventual exact predictive equivalence recovery | THEOREM | `eventually_exact_predictive_recovery_canonical` |
| P3.3 | eventual exact carrier + blocker recovery | THEOREM | `eventually_exact_carrier_and_blocker_recovery`, `eventually_canonical_response_recovery` |
| P3.4 | estimator error -> reward/transition fibre defects | ADAPTER_INTERFACE + THEOREM | `RealizedControlEstimator`, `reward_fiber_bound`, `transition_fiber_bound` |
| P3.5 | vanishing estimator error -> exact control quotient | THEOREM | `exactControlQuotient_of_realizedEstimator`, `p_quo_01_of_realizedEstimator` |
| P3.6 | exact value + set-valued GOD; gap-conditioned selector recovery | THEOREM / CONDITIONAL_THEOREM | `exact_bellmanGODCorrespondence_eq`, `eventually_estimatedGreedy_eq_canonical` |
| P3.7 | isolation-conditioned GOA consistency | CONDITIONAL_THEOREM | `eventually_goa_consistent_of_realizedEstimator` |
| P3.8 | terminal layered synthesis | THEOREM / CONDITIONAL_THEOREM | `p3_exact_structural_value_god_closure`, `p3_policy_goa_terminal_closure` |

## 3. Recompression decisions

### 3.1 Changing sample spaces remain genuinely changing

`ChangingSampleEventContract` is indexed by `Ω : ℕ → Type*`. Each sample size
may therefore have its own probability space and good event. Its certified bad
event probability tends to zero.

P3 **does not** infer an almost-sure eventual statement on one common sample
path. Such a statement needs additional coupling/common-space data. The absence
of that coupling is a declared boundary, not an omitted proof.

### 3.2 Finite predictive separation is canonical, not an external parameter

For finite history/protocol families of probability response laws, distinct
predictive classes have strictly positive protocol TV distance. Taking the
finite minimum over pairwise gaps gives `canonicalPredictiveGap > 0`.

Therefore the final finite P3.2 theorem does not retain an unnecessary external
predictive-separation constant. A genuine zero-separation issue returns in more
general infinite/noncompact or observationally nonseparating settings; P3 makes
no claim there.

### 3.3 Finite carrier separation is also canonical

For a finite carrier universe, the minimum over all positive true response
defects supplies the carrier threshold. If no positive defect exists, the exact
carrier family is already the whole candidate family and the fallback threshold
is harmless. Thus no independent finite carrier-gap hypothesis remains.

### 3.4 Structural defects are derived from estimator errors

`RealizedControlEstimator` does not assume terminal quotient defects vanish.
For one fixed source model and one fixed encoder, if each micro cell is within
reward/transition radii of its estimated macro cell, then two micro states in
the same encoder fibre differ by at most twice those radii. Since the radii tend
to zero, the fixed true fibre defects vanish.

The estimated macro model itself may vary with sample size and is not assumed
to converge. Exactification targets the canonical representative macro model.

### 3.5 Reward estimation is an explicit adapter boundary

Response-law TV estimation does not by itself identify reward semantics.
`RealizedControlEstimator.reward_estimation` is therefore an explicit
source/domain adapter. P3 does not hide a reward-identification theorem that has
not been supplied.

### 3.6 Value, GOD, selector and GOA are different strength levels

After exactification:

- optimal values descend exactly;
- optimal action values descend exactly;
- the entire Bellman-optimal **GOD correspondence** is exactly preserved.

No positive action gap is needed for those statements. A positive action gap is
needed only to identify one canonical `greedyAction` eventually. Tied optimal
actions therefore remain honestly set-valued.

Unique/stable GOA convergence additionally requires the declared Dobrushin
isolation certificate on the canonical greedy closed loop. P3 does not infer a
unique GOA from control optimality alone.

### 3.7 Predictive/carrier recovery is not yet inverse object discovery

P3.2 and P3.3 are parallel finite identification surfaces. P3 does **not** prove
that the recovered predictive relation or carrier family equals the supplied
control encoder `C`. Establishing that bridge from observations/interventions is
a P4 Inverse Objecthood task.

Likewise, P2 already supplies same-object Objecthood -> control/GOD/GOA
semantics. P3 keeps the literal source model and encoder fixed; it does not
rediscover the P2 Objecthood anchor from raw observations.

## 4. Nonclaims retained after audit

P3 does not prove:

- arbitrary real-world or raw-trajectory object discovery;
- P4 Inverse Objecthood;
- a common-probability-space almost-sure consistency theorem from marginal
  confidence bounds alone;
- reward identification from response TV alone;
- canonical selector identity without a positive action gap;
- unique/stable GOA without an isolation/stability certificate;
- consistency when estimator bias/radii fail to vanish;
- high-probability asymptotic closure when the failure bound fails to vanish;
- infinite-state statistical consistency;
- uniqueness of purpose or of a universal Π/Φ decomposition.

## 5. Local validation evidence

At scientific head `9af8ce33c3ec998ca58c92ef2bfe3fa518dab464`:

- full P3 proof-escape scan: **CLEAR**;
- `git diff --check main...HEAD`: **PASS**;
- exact Track-TC governance validator: **PASS**;
- full governance regression suite: **PASS**;
- representative axiom audit:
  `p3_marginal_failure_tendsto_zero`,
  `eventually_exact_predictive_recovery_canonical`,
  `eventually_canonical_response_recovery`,
  `exactControlQuotient_of_realizedEstimator`,
  `p3_exact_structural_value_god_closure`,
  `eventually_estimatedGreedy_eq_canonical`,
  `eventually_goa_consistent_of_realizedEstimator`, and
  `p3_policy_goa_terminal_closure`
  depend only on `[propext, Classical.choice, Quot.sound]`;
- `lake build UEOT.V3.Compression`: **PASS, 9188 jobs**;
- `lake build UEOT`: **PASS, 9207 jobs**.

Earlier P3.0–P3.7 checkpoints were also compiled in detached worktrees while
reusing only the untracked Lake dependency/build cache. No theorem source was
read from an uncommitted author worktree during those detached checks.

## 6. Remote gate still pending

This document does **not** mark P3 closed. `THEORY_COMPLETION_STATUS.json`
correctly remains `P3 = ACTIVE` until the one final branch push, exact-head
independent review, required CI, merge, resulting-main regression, tracker
closure and branch retirement all succeed.
