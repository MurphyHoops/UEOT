# B's independent review of C: dynamics, calibration and held-out scope

Reviewer: native agent B, not author of C's estimator/classifier. Date: 2026-11-14 (client timezone). This is separated AI review, not external human peer review.

## Material read

`CALIBRATION_CONTRACT.json`, `FROZEN_HOLDOUT_PLAN.json`, `NOMINAL_MODEL.json`, `common_c.py`, `calibrate.py`, `evaluate_holdout.py`, `interval_source.py`, both generation receipts, `generate_synthetic.py`, `HOLDOUT_RESULTS.json` and their source bindings. The actual C generator and result bind dynamics SHA256 `3eb805d8ec9f8010583023f8a57812c759fba4fcc48c27c36a9079367f664001`, which matches B's source. No calibration/holdout data were regenerated during this review.

## Supported conclusions

1. The calibration coherence is the correct frozen-vacuum expression
   exp(-4 lambda²[(1-cos t)+(4/25)(1-cos(3t/2))]). The coefficient 4/25 is the square of c2/omega2, not c2². The t=0 setting identifies the shared positive visibility eta, and the t=3/2 setting identifies positive lambda within the declared interval. It does not identify an unconstrained temperature, bath displacement, detector family, control error or sign outside that model.
2. The declared independent physical inputs are necessary. Known frequencies/relative couplings, vacuum, source controls, Pauli preparations/measurements, iid stationary trials and a shared symmetric detector law are not outputs of these two settings.
3. C estimates lambda/eta only from calibration. The data-bound nominal file is hashed before holdout generation; the classifier consumes the frozen nominal and complete holdout arrays without reading the truth file or refitting on holdout. The truth is read only by generation and the separate generation-verification audit.
4. All eight record/outcome cells are retained per Pauli setting. The detector acts with probabilities (w_r +/- eta m_r)/2 and has total tester error at most |delta eta|/2. R is untouched during dynamics and is accessed only for the explicitly allowed terminal readout.
5. The same 51/10 source parameter constant and K20 truncation bound apply to the swapped times: the same controls are used and their total evolution time is still 23/12. No frequency, coupling, vacuum or control premise changes.
6. The lambda mesh covers the complete outer confidence interval. Its largest event error is bounded by (51/10)*mesh/2, and eta endpoints suffice because event probability is affine in eta. C evaluates every grid point with an independent interval history-pair implementation. It does not infer the prediction enclosure from agreement of floating backends.
7. The exact confidence region is the domain intersected with both measured-expectation inequalities; the displayed lambda/eta rectangle is correctly called an outer set. Use of this larger set makes holdout rejection conservative, rather than falsely making it an exact joint region.
8. The two calibration Bernoulli intervals use the correct simultaneous Hoeffding union allocation. The 96 heldout event indicators use their simultaneous allocation; within-setting cell dependence does not invalidate a union bound. Under all stationary-model and sampling assumptions, calibration failure plus simultaneous holdout failure is bounded by 0.02. A realized `NOT_REJECTED` is not proof of the full model.
9. Both normal families are not rejected; the deliberately changed eta=.70 generator is rejected by an entire confidence-set comparison. Reset-bath differences are correctly labeled nominal ablation diagnostics, not composite-model exclusion or the sole strong baseline.
10. The standard persistent joint backend and the standard influence-functional backend are the same physical model with the same inference inputs. `EQUIVALENT_NO_ADDED_GAIN` is the appropriate gain classification here.

## Concrete correction requested

The underlying classifier uses exact `Fraction` bounds and its decisions are sound. Some JSON values named "upper" or "envelope" are nevertheless rendered by `decimal_string`, which rounds to nearest rather than outward. For example the exact parameter bound is

`(51/10) * 0.007170144244 = 0.0365677356444`,

whereas the frozen nominal display is `0.036567735644`. Mesh-adjusted envelope endpoints can likewise be rounded inward by less than 5e-13. This is a metadata/representation error, not a reversal of the heldout decisions. B requested a supplemental exact-fraction/outward-decimal certificate and a correction receipt, preserving the original frozen nominal hash and not resampling or refitting. Acceptance of the final published numerical certificate is conditional on this correction being incorporated. The correct conservative final tester bound can be rounded outward to 0.040451414205 when using K20=0.00001344, physical numerical repair=1e-8 and the declared eta radius.

## Numerical integration with B

The eight B interval Choi certificates bind generator lambda=3/10 and nominal lambda=37414264899/125000000000, both time orders, and both Weyl/K20-Galerkin stored backends. Each has raw all-input half-diamond bound 1e-12 and an exactly rational CP/TP fixed-policy terminal instrument within 1e-8 of the exact source. `physical_prediction.py` evaluates the Bell-input XX, XY, YZ and ZZ probabilities from these repaired matrices by exact fractions, so this specific readout has no unbudgeted subsequent floating contraction. These additional representation checks do not alter C's frozen data or estimator.

## Boundaries retained

The experiment has synthetic shots only. It does not validate a real device, identify arbitrary SPAM, reconstruct an arbitrary process tensor from four Paulis, establish an infinite-mode limit, prove thermalization, or demonstrate an empirical advantage over standard quantum theory. Full-state certification is conditional on the independently supplied parametric Hamiltonian/instrument contract. B's approval applies to those precise quantifiers, with the display correction above resolved in the final receipt.
