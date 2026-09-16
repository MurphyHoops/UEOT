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
audit, safe main integration, and ledger synchronization. Feature-green or
proof-main work alone never changes the full-green count.

## Current source-level coverage

| status | count |
|---|---:|
| **proved, staged by this ledger checkpoint** | **82** |
| **partial** | **0** |
| **pending / not yet counted** | **24** |
| **total** | **106** |

This branch stages **82/106** after P-COMP-02 completed source-semantic, feature,
clean-integration, PR and proof-main gates, including successful resulting-main
CI. **82/106 is not called full-green until this ledger checkpoint itself passes
branch CI, PR CI, lands on `main`, and the resulting main CI succeeds.**

`pending` means only “not yet counted proved”; it does not mean no relevant
mathematics or Lean code exists.

## Proved P-ID set

- **Carrier / representation:** P-CAR-01, P-CAR-02, P-CAR-03, P-CAR-04
- **Resolution:** P-RES-01, P-RES-02, P-RES-03, P-RES-04, P-RES-05, P-RES-06
- **Prediction:** P-PRED-01, P-PRED-02, P-PRED-03
- **Dynamics:** P-DYN-01, P-DYN-02, P-DYN-03, P-DYN-04
- **Statistics:** P-STAT-01, P-STAT-02, P-STAT-03, P-STAT-04, P-STAT-05, P-STAT-06, P-STAT-07, P-STAT-08, P-STAT-09
- **Invariant / identifiability:** P-INV-01, P-INV-02, P-INV-03, P-INV-04, P-INV-05
- **Quotient:** P-QUO-03
- **Refinement / agency:** P-REF-01, P-REF-02, P-REF-03, P-REF-04, P-REF-05
- **Telescoping reward:** P-TEL-01
- **Bridge:** P-BRG-01, P-BRG-02
- **Metric:** P-MET-01, P-MET-02
- **Internal/external factorization:** P-INT-01, P-INT-02, P-INT-03
- **Information:** P-INFO-01, P-INFO-02, P-INFO-03, P-INFO-04, P-INFO-05
- **Process:** P-PROC-01
- **Recovery:** P-REC-01, P-REC-02, P-REC-03, P-REC-04
- **QSD:** P-QSD-02, P-QSD-03
- **Persistence:** P-PER-01, P-PER-03, P-PER-04
- **Transport / identity:** P-ID-01, P-ID-02
- **Representation covariance:** P-FAC-01
- **Omega / integrity:** P-OMG-01, P-OMG-02
- **Dual-drive / alignment:** P-DDH-01, P-ALI-02, P-ALI-03
- **Composition:** P-COMP-01, P-COMP-02, P-COMP-03, P-COMP-04, P-COMP-05, P-COMP-06, P-COMP-07
- **KL / path information:** P-KL-01, P-KL-02, P-KL-03
- **Evolution:** P-EVO-01, P-EVO-02
- **Process interface:** P-API-01
- **Algorithmic quotient:** P-ALG-01

Count check: `81 + P-COMP-02 = 82`.

## Newly staged promotion — P-COMP-02

Frozen Core 3 P-COMP-02 compares an original record probability law `P` with a
declared implementable-cut record law `Q=P_cut^π` on the same measurable record
space using the genuine Jensen-Shannon divergence

`JS(P,Q) = 1/2 KL(P || M) + 1/2 KL(Q || M)`, with `M=(P+Q)/2`.

The Lean implementation stays at that general-measure source scope. It proves
that the midpoint is a probability measure, derives `P ≤ 2M` and `Q ≤ 2M`, and
uses those inequalities to obtain absolute continuity and the almost-everywhere
Radon--Nikodym density bound by two. Integrability of the KL integrand is proved
before converting `ℝ≥0∞` KL values to real integrals, so the argument never uses
an invalid inference through `ENNReal.toReal ⊤ = 0`. The exact pointwise affine
bound on Mathlib's `klFun` over `[0,2]` then integrates to `KL ≤ log 2`.

The source-strength conclusions are machine checked:
- `0 ≤ JS(P,Q) ≤ log 2`;
- `JS(P,Q)=0 ↔ P=Q`, via KL converse Gibbs rather than a postulate;
- for a finite declared cut family, the exact minimum JS is positive iff every
  declared cut changes the declared record law.

The frozen-source interpretation guard is retained: a zero observed cut effect
does **not** imply absence of microscopic coupling without additional
observation-completeness / cut-faithfulness assumptions.

Canonical theorem surface:
- `UEOT.V3.CompositionInterventionJS.jsDiv_mem_Icc_logTwo`;
- `UEOT.V3.CompositionInterventionJS.jsDiv_eq_zero_iff`;
- `UEOT.V3.CompositionInterventionJS.cutJSMargin_pos_iff`.

Promotion evidence:
- feature branch: `formal/pcomp01-multiblock-v1`;
- final feature head: `2bd7642058f6da329ff8e0fb2a8fa5d1b72adb50`;
- feature official root CI `35077241084`: success;
- source-semantic audit: complete;
- prohibited-proof audit: clean (`sorry=0`, `admit=0`, `native_decide=0`, unsourced `axiom=0`);
- clean integration branch: `formal/pcomp01-main-integration-v1`;
- clean integration head: `2bd7642058f6da329ff8e0fb2a8fa5d1b72adb50`;
- clean integration official root CI `35077915553`: success;
- proof PR #91;
- PR-triggered CI `35079990097`: success;
- proof main commit `61135398787bb49e1a19f54903dcb75beea870d4`;
- proof resulting-main CI `35080641545`: success.

**Status: PROVED / PROOF-COMPLETE, staged for counting by this ledger
checkpoint.**

## Previous full-green checkpoint — 81/106

P-COMP-01 is already counted in the authoritative **81/106 full-green**
baseline at `main@0797123efc63f39ffd2169b1e9b9e86472419919`, whose ledger
resulting-main CI `35067746154` succeeded. P-COMP-01 itself landed at
`main@c5ae119adad2e533205f58e9b95d8ffc5d6713df` and its proof resulting-main CI
`35015386126` succeeded.

All previously counted P-IDs remain closed absent a substantive frozen-source
mismatch or CI regression. Source-facing wrapper work must not be double-counted
as new P-IDs.

## Grounded pending fronts

After this staged promotion, **24** P-IDs remain not yet counted and require
fresh source-first audits. Known non-quick fronts include:

- P-PER-02: Polish-space Feller semigroup + tight occupation laws + Prokhorov/Portmanteau weak-convergence infrastructure;
- P-ALI-01: global exact-one-form / closed-loop integral theorem on connected smooth manifolds;
- P-DDH-02/03: finite exponential-family calculus and KL variational duality;
- P-KL-04/05: CTMC compensator / Girsanov-level stochastic analysis;
- P-EVO-03/04: Perron-Frobenius asymptotics / martingale foundations;
- P-DDH-04/05: genuine rank/stacked-Jacobian and singular-value perturbation;
- P-QSD-01/04: source-locked distinct non-A results.

P-QUO-01 and P-QUO-02 are candidates for fresh source-to-main audits because
current main contains structured-quotient and finite-stable-partition
infrastructure, but neither may be counted without an explicit bridge to the
frozen controlled Bellman/value-policy statements.

P-EVO-03 specifically requires the full K-PF-01 primitive nonnegative-matrix
Perron-Frobenius asymptotic package; an assumed-convergence surrogate is not
countable.

## Reproducibility task

The exact canonical source bytes are still not present in the public repository.
Synchronizing those exact bytes and independently recomputing the SHA-256 is
separate from theorem proof status.

## Completion rule

UEOT Core v3.0 is machine-complete only when all **106** frozen-source P-IDs pass
the source-theorem proof contract; helpers, feature-green branches, source
audits or proof-main commits never count on their own.
