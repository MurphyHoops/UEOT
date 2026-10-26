# R2 consumer delta and tests — prepared, not applied

Scope root: `/Users/murphyhoops/Documents/ueotlean-worktrees/core-books-handoff-20261020/total-kernel-memory-20261023/formalization/ueot-core/docs/compression/theory_completion/knowledge`

Baseline `d048429a1f713246dd7a69aa278f71c4d0df1677`; frozen source
`4b5145e874601392568293c1d561684e6d0478f2676dc20accf04a8080c3261d`.
FROZEN_INPUTS_01 identifies exactly three added modules, 43 lexical public
candidates and 17 lexical-hinted candidates. These are freeze facts; successful
native export, private/generated counts, fixed replay, exact registered edge
sets and final artifact SHA-256s are pending.

## Exactly five files, guarded against intervening edits

| File under scope root | Current original SHA-256 |
| --- | --- |
| `README.md` | `5d7d416c120221e2089a2c43436b9d4bf24797447e0d4d29706357284b73562d` |
| `reuse/fkrg_reuse.py` | `fb5d25ac27f97bfec80922f2cb9ae7528a338ded4c901bdf9c213022f34e7c87` |
| `reuse/test_fkrg_reuse.py` | `283409893a6eb01f8f74dee2656ebdb86714e9db1f8150ad4d4d6d7bc249c129` |
| `reuse/REBUILD_CLONE_CANDIDATES.py` | `9c997a0bc8ebfd0e737ce4d462ce46f637da6ae88887b56ba4f1fc1e0bc0689b` |
| `reuse/README.md` | `76b1fd287f521d8a0d299eeed7d40e9825ae8f0db1b7f98216c1fddf905950d9` |

1. `reuse/fkrg_reuse.py`: append `NOISY_ORACLE_REUSE_OVERLAY_V1.json` and
   `VERIFY_NOISY_ORACLE_OVERLAY_TYPES.lean` to the two artifact lists; append
   actual registered-overlay/fixed-certificate digests to the two SHA lists.
   Add `noisy-oracle` to the `status().source_of_truth` overlay text. Do not
   change old entries, historical evidence, clone SHA or ledger SHA.
2. `reuse/test_fkrg_reuse.py`: change only current live census assertions:
   modules 696→699; maintained 685→688; public 4390→4433; overlay nodes 597→640;
   hints 155→172; layers 13→14 (including the general length assertion);
   live-source set length 696→699. Let E be the actual independently exported
   new registered-edge count: overlay edges 928→928+E, graph edges 5815→5815+E.
   Do not guess E or modify historical tests for indices 0–12. Add the four
   tests specified below; expected suite size 62→66.
3. `reuse/REBUILD_CLONE_CANDIDATES.py`: docstring only, 699=688+11,
   fourteen layers, append noisy-oracle. Scanner/normalization/68-row asset
   comparison are unchanged. Actual scan may fail; retain its real result
   and do not rewrite the clone asset or weaken assertions.
4. `README.md`: update the current top census/source summary and add the
   thirteenth historical census to the history sentence. Append layer-14
   summary before startup protocol. Preserve all prior layer summaries.
5. `reuse/README.md`: update top/current statistics and the two later
   current-source census references; append Layer 14 before run commands;
   change the current example certificate to VERIFY_NOISY_ORACLE_OVERLAY_TYPES.
   Add actual native/certificate/registered-overlay hash table, three-module
   native ownership, observed direct edges, and receipt links. Preserve the
   whole historical Layer 13 and preceding layers.

Expected additive totals, conditional on actual registration of all 43 frozen
public candidates: 699=688+11 modules; 4433 public; 640 overlay nodes; 14 layers;
172 lexical hint groups; cross raw-type comparisons 43*4390=188770; internal
43*42/2=903. Native/private/generated and edge totals remain PENDING_NATIVE.

## Four meaningful additions

### test_noisy_oracle_native_ownership_and_registered_edges

Use overlay index 13. Pin baseline/source identity, three exact physical owners,
role `UNCOUNTED_FINITE_SAMPLE_SUPPORT_BOUNDARY_AND_NOISY_RISK`, unchanged counted
classification, and actual native SHA. Independently reconstruct registered
edges by intersecting every public proof's complete direct constants with the
live registry. Require exact equality to both native public dependencies and
overlay certified edges. Check every native record, including private/generated
records, owner/type/universes/unique constants/standard-only axiom closure.
Compare the complete 43-name frozen set and actual public set. Lock actual
native/private/generated counts only after inspecting the native evidence.
Validate 188770/903 comparisons and zero actual collisions, never inferred PASS.

### test_noisy_oracle_same_source_semantic_reuse

After native arrives, inspect and pin exact compiled dependency sets for these
endpoints (the following are source-level expected routes, not observed edges):

- NoGo `no_uniform_exact_zero_certificate` →
  `exists_positive_source_false_certification` →
  `certificationProbability_at_zero` / `certificationProbability_ge_zeroPower`.
  Follow the latter to `certificationProbability_eq_sum` and
  `trainingLaw_zeroRecord`, retaining the actual product-sampling proof route.
  Inspect the native type for the arbitrary `Record N → PMF Bool` rule,
  fixed positive N, power at p=0 and the uniformly quantified positive p;
  no deterministic-only or all-zero-detector restriction is introduced.
- `calibrated_defect_error` → existing P-STAT-02 responseDefect_error and the
  rational/PMF empirical-defect equality. Inspect private interval-conversion
  dependencies behind certified/rejected soundness in the full native census.
- `selectCandidate_first_on_good` → the actual Option(Fin count) selector's
  equivalence, first non-rejected scan, and certified/rejected soundness.
  Earlier ambiguity stops selection; it is not skipped.
- `training_calibration` → existing product_experiment_calibration for the
  same P subsequently deployed. The single common row-TV event controls every
  candidate; there is no extra candidate-count factor.
- `synthesized_actual_risk_le_budget_on_good` → R1 returned-program
  zero-uncovered, calibrated reference-row bound and existing actual risk
  transport; no assumed empirical fit or risk conclusion substitutes for this.
- `selected_accepts_and_failure_joint_le` → training_calibration,
  actual accepts-risk theorem and existing selectedTrainingDeployment_failure_le.
  Its event is accepted AND actual failure under joint training/deployment;
  its bound is min(1, α+(1−α)β), not risk conditional on acceptance.

### test_noisy_oracle_witnesses_and_preserved_runtime

Inspect and pin actual witness routes: computed_certificate_controls_actual_process
uses the generic actual-risk-and-safety theorem and original source support;
selected_model_joint_risk uses the genuine selected training/deployment theorem;
alternate_model_exceeds_cap uses actualGoalRisk_formula, and the acceptance
probability bound follows alternate_model_rejects_on_good plus training_calibration.
Native private synthesis/initial/support/envelope helpers stay visible in full
proof evidence even if absent from the public graph.

The actual source risk is (1−p)^2: p=1/8 gives 49/64>7/10. On the common Good
event it must fail the selected risk check; its overall erroneous acceptance
is bounded by the training calibration-failure probability. Distinguish that
Lean theorem from the deterministic eighthSamples regression.

Once root archives runtime-03 and sampling-01, verify exact raw script/sampler/
dataset/log hashes and parse the one R2_SAMPLED_RESULT line against receipt.result.
Do not resample. Observed runtime receipt: schema NOISY_ORACLE_ACTUAL_RUNTIME_V2,
state ACTUAL_RUNTIME_PASS, exit 0, N=4096, selected Fin2 index=1, queries=[0,1],
accepted=true, empirical progress 509/2048, coarse defect 1539/2048, fine defect0,
reference risk2368521/4194304, budget13939757/20971520, β=7/10.
Check 3 rows with the registered allocation, dataset SHA
0d5e5bc9b4f11656986bddb880c493ff2bbd81bf530183af77e3c185c553f6f3,
script SHA818494098bb06d4b2aa05591b99c28d104509cc9ae10c04b929a7fa37d4324f3,
sampler SHA5f579f5c112916a45aadbbde1f9587862e8cf8a91d26ec44f852d09edfafe15c,
log SHA954bef3665a8b6f8c1adcf38ac775ef13086ac632aa612870223ff4158cc9d54.
Retain the actual regression marker: first trace, reference9/16, budget53/80,
contrasting49/64 rejection, ambiguity stop, insufficient budget, zero samples
and empty family rejection. Verify NEGATIVE_RECEIPT says EXPECTED_REJECTION_PASS,
exit1, expected error 'registered sample allocation changed', and its actual
log hash26b2467d72ad780aabdbbbbc6a9f7ea203649ca4285777464f19d7efa2368cdd.
N=0 parser rejection is a separate negative execution, not a failed positive run.

### test_noisy_oracle_registration_preserves_raw_execution

Reuse R1's independent raw-byte verification: metadata additions only
lexical_pr_preflight/registration_provenance; removal recovers raw overlay;
all archived input hashes match; registered copy exactly equals consumer file;
receipt names NOISY_ORACLE and pins actual overlay hash; pending preflight remains
pending historical data. Actual native/fixed execution exits/log hashes and full
JSON equality must match; frozen source has699modules and43public/17hinted;
lexical base4390→candidate4433 and no separate candidate Git preflight is claimed.
Exact archive folder and registration SHA await root's actual registration.

## Documentation boundaries

Fixed-sample NoGo concerns exact support certification with arbitrary randomized
rules at fixed N, not all statistical inference. Numerical-risk certification
requires the explicit structural-support contract, actual same-source product
training and calibrated row-TV event. Finite runtime output does not establish
the ideal independent-uniform sampling backend or external scientific validity.
Safety and finite goal risk are distinct conclusions. No infinite numerical-risk
closure, conditional-on-acceptance risk guarantee, empirical support recovery,
zero-failure deterministic guarantee or complexity/sample optimality is claimed.

## Exact consumer commands after actual registration and application

Working directory: /Users/murphyhoops/Documents/ueotlean-worktrees/core-books-handoff-20261020/total-kernel-memory-20261023

```sh
python3 -B formalization/ueot-core/docs/compression/theory_completion/knowledge/reuse/test_fkrg_reuse.py -k noisy_oracle
python3 -B formalization/ueot-core/docs/compression/theory_completion/knowledge/reuse/test_fkrg_reuse.py
python3 -B formalization/ueot-core/docs/compression/theory_completion/knowledge/reuse/REBUILD_CLONE_CANDIDATES.py
python3 -B formalization/ueot-core/docs/compression/theory_completion/knowledge/reuse/fkrg_reuse.py --json status
git diff --check -- formalization/ueot-core/docs/compression/theory_completion/knowledge/README.md formalization/ueot-core/docs/compression/theory_completion/knowledge/reuse/README.md formalization/ueot-core/docs/compression/theory_completion/knowledge/reuse/fkrg_reuse.py formalization/ueot-core/docs/compression/theory_completion/knowledge/reuse/test_fkrg_reuse.py formalization/ueot-core/docs/compression/theory_completion/knowledge/reuse/REBUILD_CLONE_CANDIDATES.py
```

These tests read existing runtime/native evidence; they do not rerun Lean or
sample a second dataset. Actual build/native/fixed replay remains root's gate.
No formal consumer file has been edited by this preparation.
