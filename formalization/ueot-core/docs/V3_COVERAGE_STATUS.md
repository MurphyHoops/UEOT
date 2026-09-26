# UEOT Core v3.0 Lean Coverage Status

This file is the **authoritative source-level P-ID ledger** for the frozen
`UEOT_Core_Mathematics_v3.0_Complete.md` specification.

## Verification contract

- source P-IDs: **106**
- canonical source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`
- Lean: **4.33.1**
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- official target: `lake build UEOT`
- integration branch: `main`
- canonical source object: project File Library
- exact canonical source bytes in public repo: pending synchronization

A P-ID is counted `proved` only after frozen-source semantic matching, official
import reachability, feature/integration/post-main CI gates, prohibited-proof
audit, safe main integration, and the separate ledger lifecycle. Feature-green,
clean-integration-green, proof-PR-green, or proof-main-green alone never changes
the FULL-GREEN count.

## Current source-level coverage

| status | count |
|---|---:|
| **proved, staged by this ledger checkpoint** | **106** |
| **partial** | **0** |
| **pending / not yet counted** | **0** |
| **total** | **106** |

This branch stages **106/106** after P-CTL-03 completed source-semantic, feature,
clean-integration, proof-PR, proof-main, and proof resulting-main gates.
**106/106 is not called FULL-GREEN until this final ledger checkpoint itself passes
branch CI, PR CI, lands on `main`, and the resulting-main CI succeeds.**

`pending` means only “not yet counted proved”; it does not mean no relevant
mathematics or Lean code exists.

## Proved P-ID set

- **Carrier / representation:** P-CAR-01, P-CAR-02, P-CAR-03, P-CAR-04
- **Resolution:** P-RES-01, P-RES-02, P-RES-03, P-RES-04, P-RES-05, P-RES-06
- **Prediction:** P-PRED-01, P-PRED-02, P-PRED-03
- **Dynamics:** P-DYN-01, P-DYN-02, P-DYN-03, P-DYN-04
- **Statistics:** P-STAT-01, P-STAT-02, P-STAT-03, P-STAT-04, P-STAT-05, P-STAT-06, P-STAT-07, P-STAT-08, P-STAT-09
- **Invariant / identifiability:** P-INV-01, P-INV-02, P-INV-03, P-INV-04, P-INV-05
- **Quotient:** P-QUO-01, P-QUO-02, P-QUO-03, P-QUO-04, P-QUO-05
- **Control:** P-CTL-01, P-CTL-02, P-CTL-03
- **Refinement / agency:** P-REF-01, P-REF-02, P-REF-03, P-REF-04, P-REF-05
- **Telescoping reward:** P-TEL-01
- **Bridge:** P-BRG-01, P-BRG-02
- **Metric:** P-MET-01, P-MET-02
- **Internal/external factorization:** P-INT-01, P-INT-02, P-INT-03
- **Information:** P-INFO-01, P-INFO-02, P-INFO-03, P-INFO-04, P-INFO-05
- **Process:** P-PROC-01
- **Recovery:** P-REC-01, P-REC-02, P-REC-03, P-REC-04
- **QSD:** P-QSD-01, P-QSD-02, P-QSD-03, P-QSD-04
- **Persistence:** P-PER-01, P-PER-02, P-PER-03, P-PER-04
- **Transport / identity:** P-ID-01, P-ID-02
- **Representation covariance:** P-FAC-01
- **Omega / integrity:** P-OMG-01, P-OMG-02
- **Dual-drive / alignment:** P-DDH-01, P-DDH-02, P-DDH-03, P-DDH-04, P-DDH-05, P-ALI-01, P-ALI-02, P-ALI-03
- **Composition:** P-COMP-01, P-COMP-02, P-COMP-03, P-COMP-04, P-COMP-05, P-COMP-06, P-COMP-07
- **KL / path information:** P-KL-01, P-KL-02, P-KL-03, P-KL-04, P-KL-05
- **Evolution:** P-EVO-01, P-EVO-02, P-EVO-03, P-EVO-04
- **Process interface:** P-API-01
- **Algorithmic quotient:** P-ALG-01
- **GOA:** P-GOA-01, P-GOA-02, P-GOA-03, P-GOA-04
- **Core assembly:** P-CORE-01

Count check: `105 + P-CTL-03 = 106`.

## Newly staged promotion — P-CTL-03

Frozen Core 3 §19.4 requires classical continuous-time diffusion HJB
verification. For a feasible controlled diffusion, a bounded `C²` candidate
`V`, discount `rho > 0`, the HJB equation, and a measurable maximizing
selector whose closed-loop SDE is well-defined, the standard
localization/integrability/stochastic-integral hypotheses imply that `V` is
the infinite-horizon discounted optimal value and the selector is optimal.

The formalization preserves that contract:

1. the theorem is continuous-time and diffusion-facing; it is not replaced by
   a finite/discrete MDP;
2. `V` is explicitly bounded and `C²`, with positive discount;
3. the HJB residual is pointwise nonpositive for every admissible action and
   exactly zero on the measurable maximizing selector;
4. because pinned Mathlib has no full controlled-SDE Itô stack, the
   process-specific `ItoRun` interface records only the finite-horizon
   expectation output of the Appendix-C-licensed Itô/localization argument,
   together with the source integrability hypotheses;
5. no value upper bound, selector optimality, or infinite-horizon conclusion
   is stored in that stochastic-calculus interface;
6. Lean proves the finite-horizon HJB inequality/equality, proves the bounded
   discounted terminal term tends to zero, and passes to the infinite reward;
7. every admissible control is therefore dominated by `V`, while the
   maximizing selector attains `V`.

Canonical theorem surface:
- `UEOT.V3.DiffusionHJBVerification.p_ctl_03`.

Supporting module:
- `UEOT/V3/DiffusionHJBVerification.lean`.

Promotion evidence:
- frozen §19.4 and Appendix C source contract rechecked against the canonical source;
- final feature head `c1f2f922b3f27c2d67cdb33a8158cc12d7d62f33`;
- feature root CI `36246442641`: success;
- clean integration head `9f4374c165d7d442fbe7c2bc16ce1ca5bab8941c`
  from `main@9923223189e2ede79a2129a5efe86471a222028d`;
- feature/integration tree identity:
  `5a104e5f1f3e7d83782a1cb0e22ab070b094e29a`;
- clean integration root CI `36246910887`: success;
- proof PR #143 exact-head root CI `36247419494`: success;
- proof main `f12282642faf9477ed6afe3df4e630f5f38295ac`;
- proof resulting-main root CI `36247887665`: success;
- final local `lake build UEOT`: success (`9011/9011` jobs);
- focused module build: success (`3225/3225` jobs);
- `git diff --check`: clean;
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`,
  `native_decide=0`, new `axiom=0`, escape-hatch `opaque=0`);
- audited `#print axioms` for `p_ctl_03`: only `propext`,
  `Classical.choice`, `Quot.sound`.

**Status: PROVED / PROOF-COMPLETE, staged for counting by this final ledger checkpoint.**

## Previous FULL-GREEN checkpoint — 105/106

P-QSD-04 and all earlier counted P-IDs form the authoritative 105/106 baseline.
Its ledger landed at `main@9923223189e2ede79a2129a5efe86471a222028d`
with ledger resulting-main CI `36245730807` success.

All 105 previously counted P-IDs remain closed absent a substantive
frozen-source mismatch or CI regression. P-CTL-03 is proof-complete on the
current proof main but is not counted FULL-GREEN until this independent final
ledger lifecycle completes.

## Final frontier after this ledger closes

No theorem P-ID remains after a successful 106/106 ledger lifecycle.
Once branch CI, PR CI, merge, and exact resulting-main CI all succeed, the
frozen Core v3 source-theorem ledger is **106/106 FULL-GREEN**.

That source-proof completion remains distinct from the separate reproducibility
task of synchronizing the exact canonical source bytes into the public repo.

## Reproducibility task

The exact canonical source bytes are still not synchronized into the public
repository. Source theorem proof status remains distinct from that artifact
synchronization task.

## Completion rule

UEOT Core v3.0 is machine-complete only when all **106** frozen-source P-IDs pass
the source-theorem proof contract. Helpers, source audits, feature-green
branches, proof-main commits, or ledger staging do not count on their own.
