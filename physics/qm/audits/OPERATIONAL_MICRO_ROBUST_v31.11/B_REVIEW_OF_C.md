# B → C independent internal cross-review

Reviewer: native research agent B. Date: 2026-11-11. This is an internal AI
research review, not external human peer review. No Mac or shared repository
was modified by B.

## Decision

**PASS within the corrected, explicitly ideal shared-source model.** No
remaining theorem blocker was found in the reviewed domain. Hardware model
membership, source/library pulse equality, measured costs, and a full-CQ
experimental test remain unverified.

## Two strongest claims attacked

1. **General robust certificate and its quantifier order.** I independently
   reconstructed the three-term trace-norm argument. One data-dependent
   policy is fixed before the unknown theta is quantified; every component
   is a complete labelled output on the same input/reference domain. The
   weighting term is sum w_a eta_a, not an average-gate-fidelity or Choi-entry
   proxy. If used locally at several nodes, a separate hybrid/contractivity
   proof is required, as the draft states. The corrected separating witness
   fixes one legal input x* and one full-output effect; this gives a lower
   bound on the declared worst-input distance. It does not quantify over an
   unspecified scalar 'map output'.
2. **Shared-source all-input/reference cancellation and minimax deployment.**
   I reconstructed all word probabilities from the complete source and
   independently verified the successful target is a CPTP map because the
   actual backward effect is s^2 I. Each word difference is a scalar times
   the same density, including the untouched reference; direct-sum trace
   norms therefore give exactly the classical word TV. This is a universal
   mathematical argument, not tomography on the finite witness. The legal
   adaptive policy gives TV=max(|t|,delta^2-t^2)+(delta^2-t^2) and radius
   delta=1/50 on the full design interval. The first-label endpoint
   separation proves the lower bound in the stated information class.

## Findings and actual resolutions

| Finding | Why it mattered | Resolution checked |
|---|---|---|
| The full design interval and realized calibration set were liable to be conflated. | The lower bound .02 uses both .48 and .52. The reported calibration interval has width .02, so both design endpoints cannot belong to it. A narrower set can admit .01 or better; transferring the lower bound would be false. | Draft, candidate and checker now explicitly bind minimax and .01 impossibility to the full design region Theta*. The calibrated subset receives only the inherited upper guarantee, with no claim of data-optimality. |
| An effect in the separation formula acted on protocol notation without a fixed input. | An effect evaluates a state, not an unspecified map. | The draft now fixes x* in the common input/reference family and uses Tr[E F(x*)]. |
| The calibration formula initially displayed only q. | Calling it a joint theta certificate could imply flags identify phase, exchange or hardware gate matching. | The draft and analysis now give Cq × Phi_allowed × Alpha_allowed with s=1−q/2. Phase/exchange remain nuisance domains; source/library gate identity is not calibrated by raw flags. |
| Normalized projection could hide physical filter failures. | sqrt(delta) alone does not compare complete physical preparation with its ideal always-pass target. | The integrated calculation retains the fail record and uses sqrt(delta)+delta; adaptive full-output upper bound is 3673/102400=0.035869140625. Exact support G≤1 needs no filter failure. |

The observed-label policy is permitted to condition only on its first
visible selected label. Its probability law must remain q-independent during
execution. An extra q-dependent source query, intermediate quantum readout,
or parameter-dependent oracle would change the optimization class; no
minimax result is claimed for that enlarged class.

## Independent checks actually performed

- Read the revised C proof, producer, independent checker and synthetic
  analysis source, along with their model/candidate objects.
- Recomputed the exact policy, endpoint lower bound, attained endpoint
  radius, central error, raw success floor and full filter-plus-policy
  bound using a separate B script that imports none of C's implementation.
- Constructed a concrete smaller-interval counterexample to lower-bound
  transfer: the interval [.49,.51] has the corresponding adaptive radius
  .01, disproving any assertion that the full-design .02 radius persists.
- Nine B-side exact rational checks passed. The script and source-bound
  receipt are `research_b/review_c_exact.py` and
  `research_b/C_INDEPENDENT_CHECK.json`. Their finite evaluations accompany
  the analytic uniform inequality proof; they do not prove universal
  quantifiers by sampling.
- C's reported 27-check receipt and synthetic records were inspected as
  separately identified C execution, not relabelled as a B execution.

The synthetic calibration interval [.4861,.5061] is indeed strictly inside
the design region. Passing those finite record testers is not complete
quantum tomography or physical model validation. Coverage assumes fixed
parameters and the declared iid flag model; it does not follow from correct
one-shot marginals alone. The common-latent-flag failure control exposes that
premise explicitly.

## Reviewed bytes

| File under `research_c/` | SHA-256 |
|---|---|
| `C_ROBUST_CALIBRATION.md` | `0e253c0fd01c7f5b43587cfffba48c52dcbc734e8f68a59a2ff54eed640051ba` |
| `robust_certificate.py` | `a6fc896288e1716a1048cf26c685b25aa6152e2febeaf10ee8c6c94d8f8353eb` |
| `exact_checker.py` | `3f838e85d76bf73426b540066446a13ba59363d0b414ce50758843b364b55d2e` |
| `synthetic_calibration.py` | `90cf1a54057a5885bc4a3407f2e9773003e3730e583eaedce921e12affa51e76` |
| `frozen_model.json` | `33fff2dd4298816553ce0009c022c314600c644df2167355d6c3f366721572ab` |
| `candidate.json` | `38c9695e5567b19cdd73ab4b14fe8ccb50a464959caa04eb0d31f9c107160124` |
| `exact_check_receipt.json` | `cdc8fbc522a5e6a810d78cb2aa17783b837109b67367f6f155aa062761605a4e` |
| `synthetic_output/synthetic_analysis.json` | `1409cdbef6e2bd796f126a19011b4858ea7dc74ced4c7f852450c18a1418edf5` |

Scientific changes after these identities need a bounded follow-up review;
path-only relocation or additional delivery metadata does not manufacture a
new scientific execution identity.
