# B → C independent cross-review

Reviewer: native research agent B in the current recovery session. Date: 2026-11-12, Asia/Shanghai. This is internal AI review, not external human peer review. The files are newly reconstructed from the published v31.11 baseline; no missing prior v31.12 execution is claimed recovered.

## Reviewed material

- `recovery_reviews/c/C_ROBUST_CERTIFICATE_AND_DATA.md`
- `recovery_reviews/c/exact_checker.py`
- The root frozen contract and `physics/qm/growing_cutoff/frozen_model.json`.
- The actual growing-carrier implementation `model.py` and its `verify_integration.py` consumer.
- B's independently derived analytic proof `B_MICRO_GROWTH.md` and finite diagnostic implementation.

## Attack 1: does the complete certificate really cover filtering, reference and nonconserving dynamics?

The strongest numerical claim is an all-declared-input model bound below 0.05 when the blue pulse is omitted. I attempted to invalidate it through four substitutions: replacing the physical filter by a normalized projection, replacing the failure-conditioned reference by the unconditional one, using the source's expected pulse count instead of the deployed policy's count, and applying the old loose preparation bound.

The final C argument avoids all four substitutions. Its filter map is a complete pass/fail instrument and the failure branch resets only S while retaining the actual subnormalized reference state. The sharp filter term is `(delta+sqrt(4delta−3delta²))/2`, independently rederived by B from a pure-state two-dimensional block and partial-trace contraction. Low-spectral conditioning cannot increase the mean of the filtered observable; this is correctly limited to the actual G cutoff, not arbitrary heralding. The no-blue reference-prefix telescoping keeps each local defect's input energy within the original bound. It is the deployed Q law, whose expected number of selected blue actions is exactly one, that weights the resulting error.

The complete target is the normalized conditional channel of the same original source, and its actual success effect is `s(q)^2 I`. Hence it is CPTP on every normal input in the declared domain and contracts preparation error directly. The general state-dependent posterior theorem is not silently used without its positive-probability assumptions. The three original failure labels remain zero blocks of this target and nonzero branches of the raw source; these are explicitly distinguished.

The final sufficient bound is

`1/50+(1+sqrt(16381))/8192+sqrt(2)/100 = 0.04988777535926672669…`.

The remaining margin is about `0.0001122246407332733`. The older loose filter bound would exceed 0.05. This difference is handled correctly as sufficiency of a sharper proved bound, not as removal of failed data or physical impossibility of the looser estimate.

**Verdict:** PASS in the explicitly stated ideal segmented model with an independent `|beta|<=0.01` premise. No real-device precision certificate is established.

## Attack 2: can logical flag calibration secretly certify beta or justify the claimed cost denominator?

The original source's seven record probabilities have no beta dependence. I checked C's proposed negative control: for vacuum input and record `01`, beta=pi/2 produces `|e,1>` while beta=0 leaves vacuum. These are orthogonal, and the common compiled block weight is `156/625>0.05`, despite identical flag probabilities. The counterexample therefore proves failure of a flag-only accuracy certificate. It does not show that the matched-blue implementation fails, nor that every beta in the design's independently bounded interval is bad. C preserves those distinctions.

The q-confidence calculation retains iid and fixed-parameter assumptions, and does not claim that q coverage proves shared gates or beta membership. The deployment quantifier still chooses one policy from calibration and requires it to work for every member of the declared joint set. Full-design minimax optimality is not imported into a narrower realized confidence set.

The complete source attempt includes the physical filter, giving success `s_N s²`, not `s²`. C's blue count `s_N s q(1+s)` for measured-flag/feed-forward realization differs correctly from the number of scheduled coherent-control slots. The cost identity uses a genuine fresh independent retry law, preserves unknown-input limitations, and amortizes one-time calibration separately. One minor clarification was requested: the `c_other` inside the `s_N{...}` term is the expected cost conditional on passing the filter; filter-failure recording belongs in the filter/failure terms. This is a bookkeeping clarification, not a failure of the stated theorem.

**Verdict:** PASS. Beta remains an independently constrained nuisance parameter; hardware cost advantage and hardware-membership coverage remain unverified.

## Executed independent checks

B ran C's independent rational checker against the actual root frozen model. All 23 checks passed. The receipt `c_checker_independent_run.json` retains the actual model/checker hashes. The checker derives record weights and brackets the square roots with integer arithmetic; it does not import the producer or quantum simulator. Its interval encloses a proved upper-bound formula, not an observed physical error or a statistical confidence interval. Larger-pulse and weaker-bound failures are correctly classified as insufficient certification.

B separately compared root's actual blue columns and ordered label-one columns to B's independent implementation at four cutoffs and four pulse areas. The basis ordering was explicitly converted by physical basis labels; all 16 comparisons passed, maximum ordered-gate residual `2.8362171184066936e-16`. Receipt: `root_columns_independent_check.json`. Root's V1 is blue-after-red, and the edge completion in its finite ambient matrix is used only on columns whose complete blue blocks are present. It is not mistaken for the infinite oscillator unitary on all boundary vectors.

B's separate 100-check finite diagnostic passed and is recorded in `independent-growth-check.json`. It includes all seven source records, an entangled reference, exact complete-record TV agreement, physical-filter reference retention, actual CP-order distance one, a nonzero fixed-cutoff mass-loss control, and the sign of the sharp-versus-loose threshold decision. Those are finite floating diagnostics; they do not machine-prove the unbounded operator or trace-class statements.

## Disposition

No blocking mathematical or computational inconsistency was found in the reviewed C certificate. B accepts it for integration subject to root binding the final file bytes, retaining the explicit no-real-data status, and including all stated independent physical inputs. The source-model assumptions cannot be relabelled as measured device guarantees. The reviewed increment closes the segmented finite-growth and conditional omission arrows only; it does not close simultaneous Rabi dynamics, generic leakage, continuous QFT, particles, gravity, or empirical physics.
