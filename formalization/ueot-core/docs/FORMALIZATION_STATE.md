# UEOT Core Lean — Live Formalization State

> Recovery entry point. Machine-readable lane state is `PID_STATUS.yaml`.
> Integrated source-count truth is `V3_COVERAGE_STATUS.md`.

Last synchronized: **2026-09-13**

## Environment

- canonical source: `UEOT_Core_Mathematics_v3.0_Complete.md`
- source P-IDs: **106**
- canonical source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`
- canonical source object: available for semantic audit in the project File Library
- exact source bytes in public repo: **pending synchronization**
- current audit did **not** recompute the SHA from local raw bytes
- Lean: **4.33.1**
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- official target: `lake build UEOT`
- integration branch: `main`

## Current checkpoint

| state | count |
|---|---:|
| integrated proved | **53** |
| active proof | **1** |
| blocked | **1** |
| pending unclassified | **51** |
| total | **106** |

The authoritative source-level ledger is **53 proved / 53 pending**.

The newest promotion is **P-ID-02**, which was already source-faithfully
formalized and merged through PR #54. The previous ledger had not synchronized
that completed promotion. This was found by the source-to-main audit rather than
by adding a duplicate proof stack.

## P-ID-02 [PROVED / COUNTED]

Frozen source target:

`e_(t+1) <= L_t e_t + epsilon_t`

and

`e_n <= (prod_(j<n) L_j)e_0 + sum_(k<n) epsilon_k prod_(j=k+1)^(n-1) L_j`,

with the immediate contraction corollary for `L_t <= L < 1` and
`epsilon_t <= epsilon`.

Canonical source-facing theorems:

- `UEOT.V3.DevelopmentTransport.development_error_step`;
- `UEOT.V3.DevelopmentTransport.development_pipeline`;
- `UEOT.V3.DevelopmentTransport.development_pipeline_uniform_geom`;
- `UEOT.V3.DevelopmentTransport.development_pipeline_uniform_contraction`.

Source audit confirms:

- `PseudoMetricSpace` covers the source's metric-or-pseudometric scope;
- both actual and reference trajectories use the same declared `Psi_t`, as the
  source requires for the stated theorem;
- `hL0` is the explicit nonnegative Lipschitz-constant convention;
- the exact product-sum bound is preserved;
- the `L<1` geometric corollary is present;
- differing external inputs are explicitly excluded from the same-input claim,
  matching the source warning that an input-sensitivity term is then required.

Promotion evidence:

- feature head `90bbc7cb405e3ba51180862fb4b41f0ff201d7ef`;
- full-target feature CI `34716348615`: success;
- PR #54;
- main merge `4a29c2d5aa6a805d867e1934f6013aa49f1dc431`;
- post-main full-target CI `34717095993`: success.

No duplicate P-ID-02 implementation should be opened absent a genuine source
mismatch or CI regression.

## P-INFO-02 / P-INFO-04 [PROVED / COUNTED]

These remain frozen closed after canonical-source semantic audit and green
post-main CI.

- P-INFO-02 canonical theorem:
  `UEOT.V3.InformationPInfo02.p_info_02_ennreal`, PR #46, post-main CI
  `34692828935` success.
- P-INFO-04 canonical theorems:
  `UEOT.V3.InformationPInfo04.p_info_04` and
  `UEOT.V3.InformationConditionalBinaryMutualEntropy.p_info_04_conditional_binary`,
  final conditional PR #51, post-main CI `34706528781` success.

## P-INFO-03 [ACTIVE PROOF]

Frozen target:
`R_obj(0)=H(C|U)` for discrete canonical predictive core
`C=P(Y∈·|H,U)` with `H(C|U)<∞`, allowing genuinely randomized encoders
`P(M|H,U)` that cannot access future `Y`.

Verified foundation already in the active branch includes:

- genuine countable conditional entropy by `U`-disintegration;
- generic KL conditional mutual information;
- generic conditional KL fiber decomposition;
- kernel-level random-encoder joint-law geometry;
- recoverable countable-discrete MI/entropy identity;
- conditional recoverability infrastructure;
- zero-TV infrastructure.

The generic-CMI layer is independently official-CI green on
`formal/pinfo03-generic-cmi-isolated`, run `34707458047`.

Current active branch:
`formal/pinfo03-countable-conditional`.
Current head at this synchronization:
`3ad766b6f50590e70caed8ac293067f2146d68d2`.
Current full-target CI: `34734186954` in progress.

Two concrete downstream elaboration failures from the previous run were repaired:

1. `InformationDiscreteLawCode` now uses explicit code arguments and explicit
   classical decidability instead of invalid field notation;
2. `InformationConditionalStatistic` now opens the canonical
   `UEOT.V3.InformationCore` namespace containing `mutualInfo`.

Remaining source-critical chain:

1. machine-check the repaired law-code decoder and conditional-statistic layer;
2. prove that zero predictive-law distortion yields measurable recovery of the
   discrete predictive core from `(M,U)`;
3. expose the source-faithful random-encoder feasible class and rate objective;
4. prove the conditional DPI lower bound;
5. prove attainability by `M=C`;
6. expose exact source-facing `R_obj(0)=H(C|U)`;
7. clean-port -> CI -> PR -> main -> post-main -> ledger sync.

## P-INT-01 [BLOCKED]

Frozen target:
`Y_f^+ ⟂ H | (M,U) ↔ C^f = Psi(M,U) a.s.`.

It remains blocked on P-INFO-03's general countable conditional-information and
predictive-core recovery interface. Do not create a second conditional
information stack.

## Parallel source-to-main audit

The audit now covers the remaining **51 unclassified P-IDs**. The P-ID-02
promotion demonstrates why this lane is necessary: a fully merged,
source-faithful theorem can otherwise remain hidden behind a stale ledger.

For each remaining P-ID classify:

- **A:** source-facing theorem already exists on main; audit and promote;
- **B:** substantial infrastructure exists but a precise source obligation is
  missing;
- **C:** genuinely unformalized source mathematics.

Module names alone never justify promotion.

## Public canonical-source synchronization [REPRODUCIBILITY TASK]

The exact canonical source bytes are still not present in the public repository.
Required for third-party self-contained reproduction:

1. synchronize exact bytes without regeneration;
2. independently recompute SHA-256;
3. verify the frozen manifest value.

This is separate from theorem proof status.

## Mandatory recovery procedure

1. Read `PID_STATUS.yaml`, this file, then `V3_COVERAGE_STATUS.md`.
2. Fetch current main SHA and relevant Actions runs.
3. Distinguish source audit, theorem closure, official import reachability,
   feature CI, main integration, post-main CI, ledger counting, and public
   source-artifact reproducibility.
4. Read the frozen source statement before writing Lean.
5. Audit existing main code before creating new infrastructure.
6. Never use `sorry`, unsourced axioms, `native_decide`, or kernel-skipping
   devices as proof completion.
7. While CI runs, advance another independent audit/proof lane.

## Repository truth hierarchy

1. frozen canonical source specification;
2. `docs/V3_COVERAGE_STATUS.md`;
3. `docs/PID_STATUS.yaml`;
4. `docs/FORMALIZATION_STATE.md`;
5. `UEOT/V3.lean`;
6. `docs/PARALLEL_FORMALIZATION_ROADMAP.md`.
